package at.searles.kart.provers

import at.searles.kart.terms.{Var, Fun, TermList, Term}
import at.searles.kart.terms.rewriting.{TRS, Rule}

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap

/**
 * Design:
 *     classes: ArgumentFiltering
 *     types: DP = Pair[Term, Term]
 *     algorithms: findArgumentFiltering(List[DP])
 *     hence:
 *         * package object DependencyPairs
 *
 */

case class DP(l: Fun, r: Fun) extends Ordered[DP] {
	assert (l.parent eq r.parent)

	override def equals(o: Any): Boolean = o match {
		case dp: DP => this.compare(dp) == 0
		case _ => false
	}

	override def compare(dp :DP): Int = {
		assert(l.parent eq dp.l.parent)
		l.compare(dp.l) match {
			case 0 => r.compare(dp.r)
			case i => i
		}
	}
}

object DependencyPairs {
	def dpGraph(dps: Set[DP], defined: Set[String]): Map[DP, Set[DP]] = {
		dps.foldLeft(Map.empty[DP, Set[DP]])(
			(map, dp0) => map +
				(dp0 -> dps.foldLeft(Set.empty[DP])((set, dp1) => if (isConnected(dp0, dp1, defined)) set + dp1 else set))
		)
	}

	def isConnected(dp0: DP, dp1: DP, defined: Set[String]): Boolean = {
		val tmp = new TermList
		val t0 = tmp.insert(dp0.r).con(defined, "con").lin("lin")
		val t1 = tmp insert dp1.l

		// since we only use this termlist once, no need to ununify
		t0.unification(t1)
	}
}

class DependencyPairs(rules: List[Rule]) {
	val list = new TermList // term list to contain all dependency pairs
	val defined = rules.map(_.lhs.f).toSet

	// DP(l -> r) = l# -> s# where r = C[s], root(s) defined and s
	// is NOT a proper subterm of l.

	// return all subterms of the rhs that give rise to a DP
	def dpTerms(rule: Rule): List[Fun] = {

		// mark proper subterms of lhs so that it would not be considered in DFS-find.
		rule.lhs.foreach(_.mark = true)

		val ret = rule.rhs.findAll {
			case fun@Fun(f, _, _) if defined.contains(f) => true
			case _ => false
		}.asInstanceOf[List[Fun]]

		// unmark
		rule.lhs.foreach(_.mark = false)

		ret
	}

	private def toDPTerm(fun: Fun): Fun = {
		val newargs = fun.args.map(list.insert) // fixme can be more efficient by using merge (don't forget unmerge)
		list.createFun(fun.f + "#", newargs)
	}

	def toDP(l: Fun, r: Fun): DP = DP(toDPTerm(l), toDPTerm(r))

	val dps = rules.foldLeft(Set.empty[DP])((set, rule) => dpTerms(rule).foldLeft(set)((set2, r) => set2 + toDP(rule.lhs, r)))

	def dpGraph() = DependencyPairs.dpGraph(dps, defined)

	def dpGraph(dps: Set[DP]) = DependencyPairs.dpGraph(dps, defined)
}

package object GraphAlgorithms {
	// FIXME: functionalize!
	def tarjan[V](graph: Map[V, Set[V]]): List[List[V]] = {
		var index = 0
		var S = List.empty[V]

		var indices = Map.empty[V, Int]
		var lowlink = Map.empty[V, Int]

		var ret = List.empty[List[V]]

		graph.keySet.foreach(v => if (!indices.contains(v)) strongconnect(v))

		def strongconnect(v: V): Unit = {
			indices += (v -> index)
			lowlink += (v -> index)
			index += 1

			S = v :: S

			graph(v).foreach(w => {
				if (!indices.contains(w)) {
					strongconnect(w)
					lowlink += (v -> lowlink(v).min(lowlink(w)))
				} else if (S.contains(w)) {
					lowlink += (v -> lowlink(v).min(lowlink(w)))
				}
			})

			if (lowlink(v) == indices(v)) {
				// span splits list into two parts
				// (combination of takeWhile/dropWhile)
				var scc = S.span(w => v != w)

				// if scc contains only one element that is not cyclic, do not add it.
				ret = if (scc._1.isEmpty && !graph(v).contains(v)) ret else (v :: scc._1) :: ret

				S = scc._2.tail
			}
		}

		ret
	}

}

object EmptyArgumentFiltering extends ArgumentFiltering(TreeMap.empty[String, Either[Int, List[Int]]])

class ArgumentFiltering(val filtering: TreeMap[String, Either[Int, List[Int]]]) extends (Term => Term) {

	override def toString(): String = filtering.foldRight("")((entry, str) =>
		entry._1 + ": " + (entry._2 match {
			case Left(p) => p
			case Right(ps) => "{" + ps.mkString(", ") + "}"
		}) + (if(str == "") "" else ", ") + str
	)

	override def apply(t: Term): Term = t match {
		case fun@Fun(f, args, _) =>
			val e = filtering(f)
			if(e.isLeft) {
				// this one is easy
				this(args(e.left.get))
			} else {
				// call applyAF on all arguments in e.right.get
				val newargs = e.right.get.map(i => this(args(i)))
				t.parent.createFun(f, newargs.toArray)
			}
		case v@Var(_, _) => v
		case _ => sys.error("not supported")
	}

	def satisfiesSubtermCriterion(t: Term, subterm: Term): Boolean = {
		if(t.parent != subterm.parent) sys.error("must have same parent: " + t + " and " + subterm)
		this(t).hasSubterm(this(subterm))
	}

	def contains(f: String): Boolean = filtering.contains(f)

	// returns list of args of fun that are filtered
	def filteredArgs(fun: Fun): List[Term] = {
		val e = filtering(fun.f) ;
		if(e.isLeft) fun.args(e.left.get) :: Nil
		else e.right.get.map(fun.args(_))
	}

	// the following two create a new
	// next one should be operator
	def +(f: String, pos: Int): ArgumentFiltering = {
		new ArgumentFiltering(filtering + (f -> Left(pos)))
	}

	def +(f: String, poss: List[Int]): ArgumentFiltering = {
		new ArgumentFiltering(filtering + (f -> Right(poss)))
	}
}

package object ArgumentFilteringSubtermSimple {
	// From MiddeldorpHirokawa04


	// Algorithm 1: findSimpleArgumentFiltering
	// * for all function symbols that are created by the dependency pair framework
	//   pick one argument position. If we can simplify one scc, we can remove this pair.


	// So, we start from a list of dependency pairs (most likely an scc).
	//   function returns the remaining pairs of the scc and the argument filtering
	//   or none if none could be found.

	def findSimpleArgumentFiltering(pairs: List[DP]): Option[(List[DP], ArgumentFiltering)] = {
		auxFindSimpleAF(pairs, Nil, Nil, EmptyArgumentFiltering)
	}

	// pairs: remaining pairs to be processed
	// equalPairs: those DPs that were already processed and for which af(l) = af(r).
	// af: Argument Filtering so far.
	def auxFindSimpleAF(pairs: List[DP], equal: List[DP], strict: List[DP],
						af: ArgumentFiltering): Option[(List[DP], ArgumentFiltering)] = pairs match {
		case Nil => if (strict.isEmpty) None else Some(equal, af) // everything was processed
		case dp :: tail =>
			// go through all arguments
			@tailrec def loop(i: Int, t: Fun): Option[(List[DP], ArgumentFiltering)] =
				if(i >= t.length) None else {
					auxFindSimpleAF(pairs, equal, strict, af + (t.f, i)) match {
						case some@Some(_) => some
						case None => loop(i + 1, t)
					}
				}

			// function of (i, af) => B
			if(!af.contains(dp.l.f)) loop(0, dp.l)
			else if(!af.contains(dp.r.f)) loop(0, dp.r)
			else {
				val lPrime = dp.l.args(af.filtering(dp.l.f).left.get)
				val rPrime = dp.r.args(af.filtering(dp.r.f).left.get)

				val isSubterm = lPrime.hasSubterm(rPrime)
				val isEq = lPrime eq rPrime

				if(lPrime.hasSubterm(rPrime)) auxFindSimpleAF(tail, equal, dp :: strict, af)
				else if(lPrime.eq(rPrime)) auxFindSimpleAF(tail, dp :: equal, strict, af)
				else None
			}
	}





	/*def findArgumentFiltering(terms: List[Term], pi: ArgumentFiltering,
							  afCheck: ArgumentFiltering => Boolean): Option[ArgumentFiltering] = terms match {
		case (fun@Fun(f, args, _)) :: tail if pi.contains(f) =>
			findArgumentFiltering(pi.filteredArgs(fun).foldRight(tail)(_ :: _), pi, afCheck)
		case fun@Fun(f, args, _) :: _ if !pi.contains(f) => // go through all filterings for f (some-heuristics)
			val arity = args.length
			// first, list of all elements
			// next, empty list
			// finally,  every single number

			// first call for empty filtering
			val emptyPi = findArgumentFiltering(terms, pi + (f, List.empty[Int]), afCheck)
			if(emptyPi != None) {
				emptyPi
			} else if(arity > 0) {
				// next call for all single filterings

				// they are enumerated in the following function
				@tailrec def loop(i: Int): Option[ArgumentFiltering] = {
					if (i < arity) {
						val nextPi = pi + (f, i)
						findArgumentFiltering(terms, nextPi, afCheck) match {
							case Some(af) => Some(af)
							case None => loop(i + 1)
						}
					} else {
						None
					}
				}

				loop(0) match {
					case None => {
						// final case: full filtering
						findArgumentFiltering(terms, pi + (f, (0 until arity).toList), afCheck)
					}
					case s => s
				}
			} else {
				None
			}
		case Var(_, _) :: tail => findArgumentFiltering(tail, pi, afCheck)
		case Nil => if(afCheck(pi)) Some(pi) else None // we found an AF.
		case u => sys.error("not supported: " + u)
	}



	def find(pairs: List[Pair[Term, Term]]): Option[ArgumentFiltering] = {
		def subtermCriterion(af: ArgumentFiltering): Boolean =
			pairs.forall(pair => af.satisfiesSubtermCriterion(pair._1, pair._2))

		// collect all terms in DPs
		val terms: List[Term] = pairs.foldRight(List.empty[Term])((pair, terms) => pair._1 :: pair._2 :: terms)
		findArgumentFiltering(terms, EmptyArgumentFiltering, subtermCriterion)
	}

	// works in the following way: Add all terms you want to check to ts
	// check the first term and add its subterms to top of list, call recursively
	// until list is empty, then call afCheck. If afCheck is true, the argument filtering
	// is returned, otherwise the next one is done.
	def findArgumentFiltering(terms: List[Term], pi: ArgumentFiltering,
							  afCheck: ArgumentFiltering => Boolean): Option[ArgumentFiltering] = terms match {
		case (fun@Fun(f, args, _)) :: tail if pi.contains(f) =>
			findArgumentFiltering(pi.filteredArgs(fun).foldRight(tail)(_ :: _), pi, afCheck)
		case fun@Fun(f, args, _) :: _ if !pi.contains(f) => // go through all filterings for f (some-heuristics)
			val arity = args.length
			// first, list of all elements
			// next, empty list
			// finally,  every single number

			// first call for empty filtering
			val emptyPi = findArgumentFiltering(terms, pi + (f, List.empty[Int]), afCheck)
			if(emptyPi != None) {
				emptyPi
			} else if(arity > 0) {
				// next call for all single filterings

				// they are enumerated in the following function
				@tailrec def loop(i: Int): Option[ArgumentFiltering] = {
					if (i < arity) {
						val nextPi = pi + (f, i)
						findArgumentFiltering(terms, nextPi, afCheck) match {
							case Some(af) => Some(af)
							case None => loop(i + 1)
						}
					} else {
						None
					}
				}

				loop(0) match {
					case None => {
						// final case: full filtering
						findArgumentFiltering(terms, pi + (f, (0 until arity).toList), afCheck)
					}
					case s => s
				}
			} else {
				None
			}
		case Var(_, _) :: tail => findArgumentFiltering(tail, pi, afCheck)
		case Nil => if(afCheck(pi)) Some(pi) else None // we found an AF.
		case u => sys.error("not supported: " + u)
	}*/
}

package object Termination {
	def simpleDP(dps: List[DP], definedFuns: Set[String]): Option[Boolean] = {
		// FIXME: This jumping from lists to Sets is not nice.
		val dpGraph = DependencyPairs.dpGraph(dps.toSet, definedFuns)

		dpGraph.foreach(entry => Logging.i("dp-graph", entry.toString()))

		val sccs = GraphAlgorithms.tarjan(dpGraph)

		// FIXME: non-termination here.
		val status = sccs.map(scc => {
			ArgumentFilteringSubtermSimple.findSimpleArgumentFiltering(scc) match {
				case Some(pair) => // found argument-filtering
					Logging.i("af", pair._2 + " for " + scc + ", " + pair._1 + " remaining")
					simpleDP(pair._1, definedFuns)
				case None => Logging.i("af", "no filtering found for " + scc); None
			}}
		)

		status.foldLeft(Some(true): Option[Boolean])((ret, s) => s match {
			case Some(true) => ret
			case Some(false) => sys.error("not implemented")
			case None => None
		})
	}

	def terminationTest(rules: List[Rule]): Option[Boolean] = {
		val deppairs = new DependencyPairs(rules)

		deppairs.dps.foreach(dp => Logging.i("dps", dp.toString))

		simpleDP(deppairs.dps.toList, deppairs.defined)
	}
}