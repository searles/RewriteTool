package at.searles.kart.provers

import at.searles.kart.terms._

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
package object DependencyPairs {
	type DP = Pair[Term, Term]

	// convert the lhs of the rule and the given subterm to a dp
	// be sure to only use these functions to create a Dependency Pair, otherwise
	// they might not be equal
	private def getDPInstance(lhs: Fun, subterm: Term, defined: Set[String]): Option[DP] = subterm match {
		case fun@Fun(f, _, _) if defined.contains(f) =>
			val termlist = new TermList()
			val l = convertTermToDP(lhs, termlist)
			val r = convertTermToDP(fun, termlist)
			Some(new DP(l, r))
		case _ => None
	}

	// convert the fun into a DP-term (call only if fun is rooted by a defined symbol)
	private def convertTermToDP(fun: Fun, target: TermList): Term = {
		val newargs = fun.args.map(target.insert(_)) // fixme can be more efficient by using merge (don't forget unmerge)
		target.createFun(fun.f + "#", newargs)
	}

	def ruleToDP(rule: Rule, defined: Set[String]): List[DP] = {
		rule.lhs match {
			case lhs: Fun => rule.rhs.subterms().map(getDPInstance(lhs, _, defined)).flatten
			case _ => sys.error("lhs must be fun")
		}
	}

	def dpGraph(dps: List[DP], defined: Set[String]): Map[DP, Set[DP]] = {
		dps.foldLeft(List.empty[(DP, Set[DP])])(
			(map, dp0) => (dp0,
				dps.foldLeft(List.empty[DP])(
					(lst, dp1) => if (isConnected(dp0, dp1, defined)) dp1 :: lst else lst
				).toSet
				) :: map
		).toMap
	}

	// simple approximation whether two DPs are connected using unification
	def isConnected(dp0: DP, dp1: DP, defined: Set[String]): Boolean = {
		val sPrime = dp0._2.con(defined).lin()

		if (sPrime.unification(dp1._1)) {
			sPrime.ununify(dp1._1); true
		}
		else false
	}
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

class ArgumentFiltering protected (val map: TreeMap[String, Either[Int, List[Int]]]) extends (Term => Term) {

	override def toString: String = map.foldRight("")((entry, str) =>
		entry._1 + ": " + (entry._2 match {
			case Left(p) => p
			case Right(ps) => "{" + ps.mkString(", ") + "}"
		}) + (if(str == "") "" else ", ") + str
	)

	override def apply(t: Term): Term = t match {
		case fun@Fun(f, args, _) => {
			val e = map(f)
			if(e.isLeft) {
				// this one is easy
				this(args(e.left.get))
			} else {
				// call applyAF on all arguments in e.right.get
				val newargs = e.right.get.map(i => this(args(i)))
				t.parent.createFun(f, newargs.toArray)
			}
		}
		case v@Var(_, _) => v
		case _ => sys.error("not supported")
	}

	def satisfiesSubtermCriterion(t: Term, subterm: Term): Boolean = {
		if(t.parent != subterm.parent) sys.error("must have same parent: " + t + " and " + subterm)
		this(t).hasSubterm(this(subterm))
	}

	def contains(f: String): Boolean = map.contains(f)

	// returns list of args of fun that are filtered
	def filteredArgs(fun: Fun): List[Term] = {
		val e = map(fun.f) ;
		if(e.isLeft) fun.args(e.left.get) :: Nil
		else e.right.get.map(fun.args(_))
	}

	// the following two create a new
	// next one should be operator
	def +(f: String, pos: Int): ArgumentFiltering = {
		new ArgumentFiltering(map + (f -> Left(pos)))
	}

	def +(f: String, poss: List[Int]): ArgumentFiltering = {
		new ArgumentFiltering(map + (f -> Right(poss)))
	}
}

package object AFAlgorithms {
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
	}
}