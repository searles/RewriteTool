package at.searles.kart.terms.rewriting

import at.searles.kart.terms.{Term, Var, Fun, TermList}

import scala.annotation.tailrec

object Transformations {

	def toCtr(trs: CTRS): CTRS = {

		val defs = trs.defined() // defined symbols

		// find new variable prefix that does not yet occur in trs
		val prefix = "ctr"

		// mapping from rule to constructor rule
		def toConstructorRule(rule: ConditionalRule): ConditionalRule = {
			val ur = rule.u

			val counter = Stream.from(1).iterator
			val target = new TermList

			// find all terms that cause rule not to be a constructor rule
			val definedSubterms = ur.lhs.findOutermost(ur.lhs.noRoot {
				case fun@Fun(f, _, _) if defs contains f => true
				case _ => false
			})

			// create conditions and substitute them by new variables
			val conditions =
				definedSubterms.foldLeft(List.empty[(Var, Term)])((cs, t) => {
					val v = target.createVar(prefix + "#" + counter.next)
					val u = target.insert(t)
					t.link = v // set links
					(v, u) :: cs
				})

			// extract lhs
			val lPrime = target.insert(ur.lhs).asInstanceOf[Fun]

			// and unsubstitute
			definedSubterms.foreach(_.link = null) // unset links

			// now, build rule
			ConditionalRule.make(lPrime, ur.rhs, conditions.foldRight(rule.cs)((c, cs) => new Reducibility(c._1, c._2) :: cs))
		}

		new CTRS(trs.rules.map(toConstructorRule))
	}

	// the next one just verifies whether a CTRS is oriented
	/*def toOrientedCTRS(ctrs: CTRS): Option[CTRS] = {
		def transform(rule: ConditionalRule): Option[ConditionalRule] = rule.r match {
			case Left(ur) => Some(rule)
			case Right(cr) =>
				transform(cr.mantissa) match {
					case Some(m) => cr.c match {
						case Reducibility(_, _) => Some(rule)
						case _ => None // FIXME: add joinability
					}
					case None => None
				}
		}

		val transformedRules = ctrs.rules.map(transform)

		if(transformedRules.forall(_.isDefined)) {
			Some(ctrs)
		} else {
			None
		}
	}*/

	// U(rule <= cs) =

	def unravel(ctrs: CTRS): TRS = {
		def unravel(rule: ConditionalRule, prefix: String): List[Rule] =
			rule.cs.foldLeft(List(rule.u))( // FIXME: foldleft or foldright?
				(rules, c) => {
					val index = rules.length

					val topRule = rules.head // rule to be split up

					val l1 = new TermList().insert(topRule.lhs).asInstanceOf[Fun] // l is kept
					val r2 = new TermList().insert(topRule.rhs) // r is also kept

					val symbol = prefix + "#" + index // fixme: use constant instead of #

					val vars = l1.vars.map{ case Var(id, _) => id }

					c match {
						case Reducibility(s, t) =>
							val args1 = l1.parent.insert(s) :: vars.map(l1.parent.createVar)
							val r1 = l1.parent.createFun(symbol, args1.toArray)

							val args2 = r2.parent.insert(t) :: vars.map(r2.parent.createVar)
							val l2 = r2.parent.createFun(symbol, args2.toArray)

							Rule.make(l2, r2) :: Rule.make(l1, r1) :: rules.tail
						case Joinability(s, t) => sys.error("not implemented")
					}
				}
			)

		val indices = Stream.from(1).iterator
		new TRS(ctrs.rules.flatMap(rule => unravel(rule, "U" + indices.next()).reverse))
	}

	/*def structurePreserving(ctrs: CTRS): TRS = {
		// This is a generalization of ABH03 to DCTRSs

		/*
		* for all f in defined symbols
		*     arity of f
		*     Rf = all conditional(!) rules with root symbol f.
		*
		*     let phiX(t) = mapping for f
		*     let phiBot(t) = mapping for f
		*     let phi(l -> r <= s1 -> t1, ..., sn -> tn) =
		*         phiX(l) -> phiBot(r) <= phiBot(s1) -> phiX(t1), ..., phiBot(sn) -> phiX(tn)
		*
		*     let split(f(X, z1, ..., z_|Rf|) -> r <= s1 -> t1, ..., sn -> tn, i) =
		*
		*
		*         (<s1>_1, <t1>_1), (<s2, vars(last term)>_2, <t2, vars(...)>_2,), ..., (
		*
		*
		*     let T(r) = phi(r) if r not in Rf
		*              = split(phi(r), index of r in Rf) otherwise
		*
		*
		*
		*     let R' = phi(r)
		*
		*     R = all rules.
		*
		*     R' = phi(R) where phi(R) = union r in R phi(r)
		*
		*/

		val botLabel = "bot"
		val tupelLabel = "tp"
		val prefix = "cv" // prefix for new variables

		// Step 1: fetch defined symbols
		val defined = ctrs.defined()

		// now for a looooong foldleft.
		// Result is a list of ConditionalRules all of which are in fact unconditional

		val transformed = defined.foldLeft(ctrs.rules)((rules, f) => {

			// FIXME: Put this into its own function

			val ruleSplit = rules.foldRight((List.empty[ConditionalRule], List.empty[ConditionalRule]))(
				(rule, pairs) => rule match {
					case ConditionalRule(r, cs) if (r.lhs.f == f) && cs.nonEmpty => (rule :: pairs._1, pairs._2)
					case _ => (pairs._1, rule :: pairs._2)
				}
			)

			val fRules = ruleSplit._1
			val gRules = ruleSplit._2

			val fRuleCount = fRules.length

			if(fRuleCount == 0) {
				rules // no conditional rules to transform for f
			} else {
				val fArity = fRules.head.underlying.lhs.args.length // FIXME: We do not consider symbols with same name and different arity.

				def phibot(t: Term, list: TermList): Term = t match {
					case Fun(g, args, _) if f != g => // phibot(g(...)) = g(phibot(...))
						val nargs = args.map(phibot(_, list))
						list.createFun(g, nargs)
					case Fun(g, args, _) if f == g => // phibot(f(...)) = f(phibot(...), bot, ..., bot)
						val bot: Term = list.createFun(botLabel, Array.empty[Term])
						val nargs = new Array[Term](args.length + fRuleCount)
						nargs.indices.foreach(i => if (i < args.length) {
							nargs.update(i, phibot(args(i), list))
						} else {
							nargs.update(i, bot)
						})

						list.createFun(f, nargs)
					case Var(id, _) => list.createVar(id)
					case _ => sys.error("not implemented")
				}

				def phiX(t: Term, list: TermList, suffix: Iterator[Int]): Term = t match {
					case Fun(g, args, _) if f != g =>
						val nargs = args.map(phiX(_, list, suffix))
						list.createFun(g, nargs)
					case Fun(g, args, _) if f == g =>
						val nargs = new Array[Term](args.length + fRuleCount)
						// fill in variables
						nargs.indices.foreach(i => if (i < args.length) {
							nargs.update(i, phiX(args(i), list, suffix))
						} else {
							nargs.update(i, list.createVar(prefix + "#" + suffix.next))
						})

						list.createFun(f, nargs)

					case Var(id, _) => list.createVar(id)
					case _ => sys.error("not implemented")
				}

				// suffix is for PhiX.

				def auxphi(rule: ConditionalRule, suffix: Iterator[Int]): ConditionalRule = {
					val list = new TermList
					val lhs = phiX(rule.underlying.lhs, list, suffix).asInstanceOf[Fun]
					val rhs = phibot(rule.underlying.lhs, list)

					// DELME val m = auxphi(cr.mantissa, suffix) // new mantissa

					// transform rule

					// FIXME: FoldLeft or right?
					val cs = rule.cs.foldRight(List.empty[Condition])(
						(cs, c) => {
							c match {
								case Reducibility(s, t) => new Reducibility(phiX(s, m.list, suffix), phibot(t, m.list)) :: cs
								case _ => sys.error("not implemented")
							}
						}
					)

					ConditionalRule.make(lhs, rhs, cs)
				}

				def phi(rule: ConditionalRule) = auxphi(rule, Stream.from(1).iterator)
				// number of conditional arguments required for f
				// with this knowledge, we can next do stuff.

				// finally, mappings to split up the conditions of all f-rules

				// returns the split of the conditional rule. p is the position where
				// the condition is inserted

				// l -> r <= s1 ->* t1, ..., sn ->* tn
				// ==> l[bot]_p -> l[<sn, vars(t*)>]_p <= s1 ->* t1, ...
				//     l[<tn, vars(t*)>]_p -> r
				// and then call recursively.

				// ==>
				// l[bot]_p -> l[<sn, vars(t*)>]_p <= s1 ->* t1, ..., sm ->* tm (where m = n-1)
				// l[bot]_p -> l[<sm, vars(t*)>]_p <= s1->* t1, ..., sm-1 ->* tm-1
				// l[<sm, vars(t*)>]_p -> l[<sn, vars(t*)>]_p

				// or, other way:
				// l -> r <= s1 ->* t1, t2 -> t2...
				// l[bot] -> l[<s1] --> no, because of variables.

				// lhsBot = lhs[bot]_p
				// Will reuse lhsBot.parent
				def splitRule(rule: ConditionalRule, p: Int): List[Rule] = {
					// First, for terms (t0 -> sn+1 <= s1 -> t1 etc...)
					val ss = (rule.underlying.rhs :: rule.cs.foldLeft(List.empty[Term])(
						(l, c) => c match {
							case Reducibility(s, t) => s :: l
						}
					)).reverse

					// I ignore the lhs
					val ts = rule.cs.foldLeft(List.empty[Term])(
						(l, c) => c match {
							case Reducibility(s, t) => t :: l
						}
					).reverse

					// First I check which variables should be encoded.
					val lhsVars = rule.underlying.lhs.vars.map(_.id).toSet

					// I add the empty set to the first condition because of t0.
					val extraVars = Set.empty[Term] :: ts.map(_.vars.map(_.id).toSet.filter(!lhsVars.contains)) // deterministic extra variables
					val neededVars = ss.zip(extraVars).map {
							case (s, vs) => vs ++ s.vars.map(_.id).toSet.filter(!lhsVars.contains)
						} // extra variables required for a certain condition.

					// A variable x is encoded in a <>i-condition if
					// there is a j < i st x in extraVars[j], and a k > i st x in neededVars.
					// the case j <= i cannot be dealt with, while k == i is not needed since
					// the variable is immediately consumed (interesting for inversion btw)

					// Hence, I use integration, for extra variables forward,
					// for needed variables backwards.
					// the intersection of both are the conditions to be encoded.

					@tailrec def integrateRight(l: List[Set]): List[Set] = l match {
						case h :: t => h ++ t.flatten :: integrateRight(t)
					}

					@tailrec def integrateLeft(l: List[Set]): List[Set] = l match {
						case h :: t :: tt => h :: integrate(t ++ h :: tt)
						case h :: _ => h
						case _ => sys.error("not for empty lists")
					}

					val allNeeded = integrateRight(neededVars)
					val allExtra = integrateLeft(extraVars)

					// Examples:

					// f(x) -> z <= x -> y, y -> z
					// allNeeded = [ {y, z}, {y, z}, z]
					// allExtra = [ {}, {y}, {y, z} ]

					// assert: first of allExtra is empty.

					// encoded = [ {}, {}, {}]

					// encode: delete first of allNeeded and ignore last of allExtra
					// [{y,z},   {z}]
					// [{},      {y}, {y,z}]


					// f(x) -> g(y,z) <= x -> y, y -> z
					// allNeeded = [ {y, z}, {y, z}, {y, z}]
					// allExtra = [ {}, {y}, {y, z} ]
					// encoded = [ ]

					// okay, the intersection of allNeeded and allExtra where we drop
					// the first of allNeeded and the last of allExtra
					// FIXME: change so that the previous is not necessary anymore

					val encodedVars = allNeeded.tail.zip(allExtra.reverse.tail.reverse).map {
						case (e, n) => e.intersect(n)
					}

					val list = new TermList

					val bot = list.createFun("bot", Array.empty[Term])

					val lhs = rule.underlying.lhs.replace(bot, p)


					// FIXME: Finish!

					List.empty[Rule]
				}


				/*def auxSplitRule(rule: ConditionalRule, p: Int): (Term, List[Rule], Int) = {
					rule.cs.foldRight()
						case List.empty =>
					}


					val msplit = rule.mantissa.r match {
						case Left(_) => (new TermList().createFun(botLabel, Array.empty[Term]), List.empty[Rule], 1)
						case Right(rho) => auxSplitRule(rho, p)
					}

					// msplit._1 contains termlist for rule!
					val u = msplit._1 // conditional term on lhs

					// step 1: build lhs of rule: l[u]_p
					val l = rule.lhs().replace(u, p) // new rule is created in u.parent.

					// step 2: build rhs of rule: l[u']_p where u' = tp#index(s, vars)
					// 		2.a: get new function symbol
					val sym = tupelLabel + "#" + msplit._3

					//     	2.b: get variables to be encoded + conditional term
					rule.c match {
						case Reducibility(s, t) =>
							val vArgs = s :: u.vars
							val v = u.parent.createFun(sym, vArgs.toArray)

							val r = l.replace(v, p)

							val transformedRule = new Rule(l.asInstanceOf[Fun], r)

							// next we prepare the term that will be returned and
							// used for the next rule
							val nextUArg = new TermList().insert(t) // first, the rhs of the condition
						val nextU = v.replace(nextUArg, 0)

							(nextU, transformedRule :: msplit._2, msplit._3 + 1)
						case _ => sys.error("not implemented")
					}
				}

				def splitRule(rule: ConditionalRule, p: Int): List[Rule] = {
					val msplit = auxSplitRule(rule, p)
					// add last rule
					val u = msplit._1 // conditional term on lhs

					// build lhs of rule: l[u]_p
					val l = rule.lhs().replace(u, p) //fixme could avoid cast if replace would return subtype

					val r = l.parent.insert(rule.rhs())

					Rule(l.asInstanceOf[Fun], r) :: msplit._2 // reverse order
				}*/

				// Everything is in place. Let's transform the system

				// first, conditional f-rules
				val transformedFRules = fRules.map(phi).foldLeft((List.empty[Rule], fArity))(
					(pair, rule) => {
						rule.r match {
							case Right(r) => (pair._1 ++ splitRule(r, pair._2), pair._2 + 1)
							case _ => sys.error("implementation error!")
						}
					}
				)

				// then all other rules. add the transformed fRules afterwards
				transformedFRules._1.foldLeft(gRules.map(phi))(
					(transformedRules, rule) => new ConditionalRule(rule) :: transformedRules
				)
			}
		})


		new TRS(transformed.map(r => r.underlying))
	}*/
}
