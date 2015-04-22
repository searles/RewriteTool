package at.searles.kart.terms

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable

/**
 * File contains classes and elements for basic term rewriting
 */
class TRS(val rules : List[RWRule]) extends (Term => Term) {

	override def toString() : String = rules.mkString("; ")

	def apply(t: Term): Term = tailrecapply(t, rules)

	@tailrec private def tailrecapply(t: Term, rs: List[RWRule]): Term = {
		if(rs.isEmpty) null
		else if(rs.head.applicable(t, this)) rs.head.rhs(t.parent)
		else tailrecapply(t, rs.tail)
	}

	def defined(): Set[String] = rules.map {
		case rule: Rule => rule.lhs match {
			case Fun(f, _, _) => f
			case _ => sys.error("bad format")
		}
		case _ => sys.error("bad format")
	}.toSet
}

trait RWRule {
	def applicable(t: Term, mapping: TRS): Boolean
	def rhs(target: TermList): Term
}

class Rule(val list: TermList, val lhs: Term, val rhs: Term) extends RWRule {
	override def toString: String = lhs + " -> " + rhs

	def applicable(t: Term, mapping: TRS): Boolean = lhs matching t

	def rhs(target: TermList): Term = {
		val ret = target insert rhs
		lhs unmatch()
		ret
	}

	def renaming(blacklist: mutable.Set[String]): Rule = {
		// first, rename other
		def getFreshVariable(id: String, blacklist: mutable.Set[String]): String = {
			// split oldId into prefix and postfix (trailing number)
			var prefix : String = null

			(id.length - 1 to(0, -1)).find(!id.charAt(_).isDigit) match {
				case Some(i) => prefix = id.substring(0, i + 1)
				case None => prefix = ""
			}

			val suffix = Stream.from(0).find(i => !blacklist.contains(prefix + i)).get // None is not an option
			val newId = prefix + suffix // found a new variable
			blacklist.add(newId) // add it to blacklist
			newId
		}

		val renaming = list.vars.foldLeft(new TreeMap[String, String])((m, e) => {
			if(blacklist.contains(e._1)) {
				m + (e._1 -> getFreshVariable(e._1, blacklist))
			} else {
				m
			}
		}) // fixme: is it a problem that I don't check against variables in this?

		if(renaming.isEmpty) this
		else {
			val newrulelist = new TermList
			renaming.foreach(vs => list.vars(vs._1).link = newrulelist.createVar(vs._2))
			val renamedrule = new Rule(newrulelist, newrulelist.insert(lhs), newrulelist.insert(rhs))
			renaming.keySet.foreach(v => list.vars(v).link = null)
			renamedrule
		}
	}


}

class ConditionalRule(val list: TermList, val lhs: Term, val rhs: Term, val cs: List[Condition]) extends RWRule {

	override def toString : String = lhs + " -> " + rhs + " <= " + cs.mkString(", ")

	def applicable(t: Term, mapping: TRS): Boolean =
		if(lhs matching t) {
			if(cs.forall(_.satisfied(t.parent, mapping))) {
				true
			} else {
				lhs unmatch()
				cs.foreach(_.t.unmatch()) // also call unmatch on all rhs's of conditions
				false
			}
		} else false

	def rhs(target: TermList): Term = {
		val ret = target insert rhs
		lhs unmatch()
		cs.foreach(_.t.unmatch()) // also call unmatch on all rhs's of conditions
		ret
	}
}

class Condition(val list: TermList, val s: Term, val t: Term) {
	override def toString : String = s + " ->* " + t

	def satisfied(target: TermList, mapping: TRS): Boolean = {
		// it is assumed that there is a matcher used already
		val sPrime = target insert s

		// store links in termlist and clear them

		val backup = list.backup

		val u = sPrime applym mapping

		list.restore(backup)

		t.matching(u)
	}
}

object Parsing {
	def rule(str: String): Option[RWRule] =
		TermParsers.parseAll(TermParsers.rule, str) match {
			case TermParsers.Success(r, _) => Some(r)
			case TermParsers.NoSuccess(_, _) => None
		}

	/*def rule(lhs: Term, rhs: Term) : Rule = {
		val target = new TermList
		new Rule(target, target insert lhs, target insert rhs)
	}*/

	def trs(str: String): Option[TRS] =
		TermParsers.parseAll(TermParsers.trs, str) match {
			case TermParsers.Success(rs, _) => Some(rs)
			case TermParsers.NoSuccess(_, _) => None
		}
}
