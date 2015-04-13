import scala.annotation.tailrec

/**
 * Created by searles on 09.04.15.
 */
class TRS(val rules : List[RWRule]) {

	override def toString() : String = rules.mkString("; ")

	def apply(t: Term): Term = tailrecapply(t, rules)
		/*rules.find(_.applicable(t, this)) match {
			case (Some(rule)) => rule.rhs(t.parent)
			case (None) => null
		}*/

	@tailrec private def tailrecapply(t: Term, rs: List[RWRule]): Term = {
		if(rs.isEmpty) null
		else if(rs.head.applicable(t, this)) rs.head.rhs(t.parent)
		else tailrecapply(t, rs.tail)
	}
}


trait RWRule {
	def applicable(t: Term, trs: TRS): Boolean
	def rhs(target: TermList): Term
}

class Rule(val list: TermList, val lhs: Term, val rhs: Term) extends RWRule {
	override def toString() : String = lhs + " -> " + rhs

	def applicable(t: Term, trs: TRS): Boolean = lhs matching t

	def rhs(target: TermList): Term = {
		val ret = target insert rhs;
		lhs unmatch;
		ret
	}
}

class ConditionalRule(val list: TermList, val lhs: Term, val rhs: Term, val cs: List[Condition]) extends RWRule {

	override def toString() : String = lhs + " -> " + rhs + " <= " + cs.mkString(", ")

	def applicable(t: Term, trs: TRS): Boolean =
		if(lhs matching t) {
			if(cs.forall(_.satisfied(t.parent, trs))) {
				true
			} else {
				lhs unmatch ;
				cs.foreach(_.t.unmatch) // also call unmatch on all rhs's of conditions
				false
			}
		} else false

	def rhs(target: TermList): Term = {
		val ret = target insert rhs;
		lhs unmatch;
		cs.foreach(_.t.unmatch) // also call unmatch on all rhs's of conditions
		ret
	}
}

class Condition(val list: TermList, val s: Term, val t: Term) {
	override def toString() : String = s + " ->* " + t

	def satisfied(target: TermList, trs: TRS): Boolean = {
		// it is assumed that there is a matcher used already
		val sPrime = target insert s;

		// store links in termlist and clear them
		val backup = list.terms.map (term => { val ret = term.link ; term.link = null; ret })

		val u = sPrime map trs

		// restore links
		(list.terms, backup).zipped.foreach{_.link = _}

		t matching u
	}
}

object RuleFactory {
	def rule(str: String) : Option[RWRule] =
		TermParsers.parseAll(TermParsers.rule, str) match {
			case TermParsers.Success(r, _) => Some(r)
			case TermParsers.NoSuccess(_, _) => None
		}

	def rule(lhs: Term, rhs: Term) : Rule = {
		val target = new TermList
		new Rule(target, target insert lhs, target insert rhs)
	}

	def trs(str: String) : Option[TRS] =
		TermParsers.parseAll(TermParsers.trs, str) match {
			case TermParsers.Success(rs, _) => Some(rs)
			case TermParsers.NoSuccess(_, _) => None
		}
}