package at.searles.scart.terms.rewriting

import at.searles.scart.provers.Logging
import at.searles.scart.terms._

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable

class RuleParsers extends TermParsers {
	def rule : Parser[Rule] = {
		term ~ ("->" ~> term) ^^ {
			case lhs ~ rhs => Rule.make(lhs, rhs)
		}
	}
}

object TRSParser extends RuleParsers {

	def trs : Parser[TRS] =
		rep(rule) ^^ { case rs => new TRS(rs) }

	def parse(str: String): Option[TRS] =
		parseAll(trs, str) match {
			case TRSParser.Success(rs, _) => Some(rs)
			case TRSParser.NoSuccess(_, _) => None
		}

}

class TRS(val rules : List[Rule]) extends (Term => Term) {
	override def toString(): String = rules.mkString(";\n")

	def apply(t: Term, target: TermList): Term = {
		recapply(t, target, rules)
	}

	def apply(t: Term) = apply(t, t.parent)

	@tailrec private def recapply(t: Term, target: TermList, rules: List[Rule]): Term = rules match {
		case rule :: rest =>
			val u = rule.apply(t, target)
			if(u ne null) u
			else recapply(t, target, rest)
		case _ => null
	}

	def applyAll(t: Term, target: TermList): Set[Term] =
		rules.foldLeft(Set.empty[Term])((reducts, rule) => rule.apply(t, target) match {
			case null => reducts
			case u => reducts + u
		})

	def develop(t: Term): Set[Term] = {
		// First develop root position.
		val subtermDevels = (0 until t.length).foldLeft(Set(t))((set, p) => {
			val tpDevels = develop(t(p))
			set.flatMap(u => tpDevels.map(u.replace(_, p)))
		})

		val rootDevels = rules.foldLeft(Set.empty[Term])((reducts, rule) => {
			val tDevels = rule.develop(t, this)
			reducts ++ tDevels
		})

		//Logging.d("devel", t + " develops to " + rootDevels + " and " + subtermDevels)

		rootDevels ++ subtermDevels
	}

	def defined(): Set[String] = rules.foldLeft(Set.empty[String])(_ + _.lhs.f)

	def isNF(t: Term): Boolean =
		// checks whether there is any rule st
		// a subterm of t matches the lhs.
		t.findFirst((u: Term) => {
			rules.exists(rule => {
				if(rule.lhs.matching(u)) {
					rule.lhs.unmatch()
					true
				} else false
			})
		}).isEmpty


}

object Rule {
	def make(l: Term, r: Term) = {
		val list = new TermList
		val rhs = list.insert(r)
		val lhs = list.insert(l)

		Rule(lhs.asInstanceOf[Fun], rhs)
	}
}

case class Rule private(lhs: Fun, rhs: Term) {

	val list = lhs.parent

	override def toString: String = lhs + " -> " + rhs

	def apply(t: Term): Term = apply(t, t.parent)

	def apply(t: Term, target: TermList): Term = if(lhs matching t) {
		val ret = target.insert(rhs)
		list.foreach(_.link = null) // clear
		ret
	} else null

	def develop(t: Term, trs: TRS): Set[Term] = {
		// FIXME: What about non-rl rules?
		// defined inductively as
		// -o-> contains -=->
		// only go into subterms if we found a match

		//Logging.d("rule-devel", "try to match " + t + " with " + lhs)

		if(lhs matching t) {
			//Logging.d("rule-devel", this + " can develop " + t)

			val r = t.parent.insert(rhs)

			if(r.parent ne t.parent) {
				// FIXME DELME This must be a bug???
				sys.error("I think you caught a StackOverflow before and now the data structures are tangled up?")
			}

			lhs.unmatch()

			// Get variable positions
			val rhsVpos = rhs.traverse((t, pos) => t match {
				case v: Var => Some(pos)
				case _ => None
			}).flatten

			// Develop root position.
			rhsVpos.foldLeft(Set(r))((set, p) => {
				val rpDevels = trs.develop(r(p))
				set.flatMap(u => rpDevels.map(u.replace(_, p)))
			})

			// ===


			/*val descs = rhs.vars // descendants inside the term

			assert(descs.forall(_.link ne null))

			// FIXME: Error message if rhs contains extra variables
			val devDescs = descs.map(v => trs.develop(v.link)) // all their developments

			val allAssignments  = descs.zip(devDescs)

			// the following aux-method creates all permutations using the rem-mapping.
			def aux(rem: List[(Term, Set[Term])]): Set[Term] = rem match {
					case hd :: tl => hd._2.foldLeft(Set.empty[Term])((l, t) => {
						hd._1.link = t // pick one reduct
						aux(tl) ++ l
					})
					case Nil => Set(t.parent.insert(rhs)) // insert rhs.
				}

			val ret = aux(allAssignments)

			lhs.unmatch()

			ret*/
		} else Set.empty[Term]
	}

	def isLL: Boolean = lhs.isLinear

	def isColl: Boolean = rhs.isInstanceOf[Var]

	def isRL: Boolean = rhs.isLinear

	def isConstructor(defined: List[String]): Boolean = {
		lhs.args.forall(_.findFirst({
			case Fun(f, _, _) => defined.contains(f)
			case _ => false
		}).isEmpty)
	}

	def renaming(blacklist: Set[String]): Rule = list.renaming(blacklist, this,
		(list: TermList) => Rule.make(list.insert(lhs), list.insert(rhs)))
	/*{
		// FIXME Bug in here!
		val sigma = list.renaming(blacklist)

		if (sigma.nonEmpty) {
			// create TermList, add variables and link them
			val tl = new TermList
			sigma.foreach(entry => entry._1.link = tl.createVar(entry._2))

			// now create rule
			val ret =

			// and clean up
			sigma.foreach(entry => entry._1.link = null)
			ret
		} else {
			// no renaming necessary
			this
		}
	}*/
}

