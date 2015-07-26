package at.searles.scart.terms.rewriting

import at.searles.scart.terms._

import scala.annotation.tailrec

object CTRSParser extends RuleParsers {
	def condrule : Parser[ConditionalRule] =
		rule ~ conditions ^^ { case ur ~ cs => ConditionalRule.make(ur, cs)}


	def conditions : Parser[List[Condition]] =
		opt("<=" ~> condition ~ rep("," ~> condition)) ^^ {
			case None => List.empty[Condition]
			case Some(c ~ cs) => c :: cs
		}

	def condition : Parser[Condition] = {
		term ~ ("->" | "-><-") ~ term ^^ {
			case s ~ "->" ~ t => new Reducibility(s, t)
			case s ~ "-><-" ~ t => new Joinability(s, t)
		}
	}

	def ctrs : Parser[CTRS] =
		rep(condrule) ^^ { case rs => new CTRS(rs) }

	def parse(str: String): Option[CTRS] =
		parseAll(ctrs, str) match {
			case CTRSParser.Success(rs, _) => Some(rs)
			case CTRSParser.NoSuccess(_, _) => None
		}
}

trait Condition {
	def satisfied(target: TermList, trs: CTRS) : Boolean
	def copy(target: TermList): Condition
}

case class Reducibility(s: Term, t: Term) extends Condition {
	override def toString : String = s + " ->* " + t

	override def satisfied(target: TermList, trs: CTRS): Boolean = {
		// s might have "link" set already
		val sPrime = target insert s

		// store links in termlist and clear them
		// FIXME: Find another way.
		// thoughts:
		val backup = s.parent.backup

		val u = sPrime normalize trs

		s.parent.restore(backup)

		if(t.matching(u)) {
			true
		} else {
			// FIXME find another way
			s.parent.clear() // clear links
			false
		}
	}

	override def copy(target: TermList): Reducibility = {
		Reducibility(target.insert(s), target.insert(t))
	}
}

case class Joinability(s: Term, t: Term) extends Condition {
	override def toString : String = s + " -><- " + t

	def satisfied(target: TermList, trs: CTRS): Boolean = {
		// s might have "link" set already
		val sPrime = target insert s
		val tPrime = target insert t

		// store links in termlist and clear them
		val backup = s.parent.backup

		val u = sPrime normalize trs
		val v = tPrime normalize trs

		if(u eq v) {
			s.parent.restore(backup)
			true
		} else
			false

	}

	override def copy(target: TermList): Joinability = {
		Joinability(target.insert(s), target.insert(t))
	}
}

case class SemiEq(s: Term, t: Term) extends Condition {
	override def toString : String = s + " <-> " + t

	def satisfied(target: TermList, trs: CTRS): Boolean = false

	override def copy(target: TermList): SemiEq = {
		SemiEq(target.insert(s), target.insert(t))
	}
}

// FIXME: Find a way to obtain a type that is either l or r

// (Rule + condition) = conditional rule

// a -> b <= c -> d, e -> f can be either

// (a -> b <= c -> d) <= e -> f; or
// a -> b <= (e -> f <= c ->d)
// rule.lhs


object ConditionalRule {
	// cs will be reversed because for verification I use the following strategy:
	// l matches t, then recursively satisfy conditions in cs
	// until finally no condition is left.
	def make(mantissa: Rule, cs: List[Condition]): ConditionalRule = make(mantissa.lhs, mantissa.rhs, cs)


	def make(lhs: Term, rhs: Term, cs: List[Condition]) = {
		val ur = Rule.make(lhs, rhs)
		ConditionalRule(ur, cs.map(_.copy(ur.list)))
	}
}

// t0 -> sn+1 <= s1 ->* t1... na, weird.

case class ConditionalRule private(u: Rule, cs: List[Condition]) {
	def renaming(blacklist: Set[String]) =
		u.list.renaming(blacklist, this,
			(list: TermList) => ConditionalRule.make(list.insert(u.lhs), list.insert(u.rhs), cs.map(_.copy(list))))
	/*{
		// FIXME Bug in here!
		// Very much copy/paste from Rule
		val sigma = u.list.renaming(blacklist)

		if (sigma.nonEmpty) {
			// create TermList, add variables and link them
			val tl = new TermList
			sigma.foreach(entry => entry._1.link = tl.createVar(entry._2))

			// now create rule
			// FIXME: Generic version of this: renaming[A](blacklist: Set[String], list: TermList, fn: () => A)
			val ret = ConditionalRule.make(tl.insert(u.lhs), tl.insert(u.rhs), cs.map(_.copy(tl)))

			// and clean up
			sigma.foreach(entry => entry._1.link = null)
			ret
		} else {
			// no renaming necessary
			this
		}
	}*/

	override def toString: String = {
		val cString = if(cs.nonEmpty) " <= " + cs.mkString(", ") else ""
		u.toString + cString
	}

	def apply(t: Term, ctrs: CTRS, target: TermList): Term = {
		if(u.lhs.matching(t)) {
			def check(cs: List[Condition]): Boolean = cs match {
				case c :: ccs => if(c.satisfied(target, ctrs)) check(ccs) else false
				case _ => true
			}

			val ret = if(check(cs)) target.insert(u.rhs) else null

			u.list.foreach(_.link = null) // clear

			ret
		} else null
	}

	def isOriented: Boolean = cs.forall {
		case _: Reducibility => true
		case _ => false
	}

	def isJoin: Boolean = cs.forall {
		case _: Joinability => true
		case _ => false
	}

	def isDeterministic: Boolean = cs.foldLeft((u.lhs.varIds, true))((vss, c) =>
		if(vss._2) c match {
			case Reducibility(s, t) => (vss._1 ++ t.varIds, s.varIds.subsetOf(vss._1))
			case _ => (vss._1, false) // FIXME could stop right here...
		} else (vss._1, false)
	)._2

	def getType: Int = {
		val lVars = u.lhs.varIds
		val rVars = u.rhs.varIds
		val cVars = cs.flatMap{
			case Reducibility(s, t) => s.varIds ++ t.varIds
			case Joinability(s, t) => s.varIds ++ t.varIds
			case SemiEq(s, t) => s.varIds ++ t.varIds
			case _ => sys.error("not supported")
		}.toSet

		if(((cVars ++ rVars) -- lVars).isEmpty) 1
		else if((rVars -- lVars).isEmpty) 2
		else if((rVars -- (lVars ++ cVars)).isEmpty) 3
		else 4
	}

	// FIXME: Difference to DCTRSs?
	def isProperlyOriented: Boolean = {
		getType match {
			case 4 => false
			case 3 =>
				def aux(varSet: Set[String], cs: List[Condition]): Boolean = cs match {
					case Reducibility(s, t) :: rest =>
						if((s.varIds -- varSet).isEmpty)
							aux(varSet ++ t.varIds, rest)
						else
							false
					case _ if cs.isEmpty => true
					case _ => sys.error("not supported")
				}

				aux(u.lhs.varIds, cs)

			case _ => true
		}
	}

	// right stable: all variables in the rhs of conditions
	// are fresh.
	// TODO: Interesting for OpConf!
	def isRightStable(utrs: TRS): Boolean = {
		def aux(varSet: Set[String], cs: List[Condition]): Boolean = cs match {
			case Reducibility(s, t) :: rest =>
				val tVars = t.varIds

				val varSet2 = varSet ++ s.varIds

				if(varSet2.intersect(tVars).isEmpty) {
					// FIXME: Keep underlying TRS somewhere.
					// TODO: Constructor check necessary?
					utrs.isNF(t) && aux(varSet2 ++ tVars, rest)
				} else false
			case _ if cs.isEmpty => true
			case _ => sys.error("not supported")
		}

		aux(u.lhs.varIds, cs)
	}

	def isWLL: Boolean = {
		// all variables occurring more than once in l, t1, ..., tn are erased
		val lVars = cs.foldLeft(u.lhs.vars)((vars, c) => c.asInstanceOf[Reducibility].t.vars ++ vars)
		val rVars = cs.foldRight(u.rhs.varIds)((c, vars) => vars ++ c.asInstanceOf[Reducibility].s.varIds)

		// count variables
		// FIXME: might be useful in term for flat/shallow-criteria
		val varMap = lVars.foldLeft(Map.empty[String, Int])((m, v) => {
			// FIXME: Compare to RLE-compression :)
			val count = if (m.contains(v.id)) m(v.id) + 1 else 1
			m + (v.id -> count)
		})

		val nonlinearVars = varMap.filter(entry => entry._2 > 1).keySet

		val commons = rVars.intersect(nonlinearVars)

		commons.isEmpty
	}

	def isWRL: Boolean = {
		// all variables occurring more than once in r, s1, ..., sn do not occur in lVars
		// exactly symmetric to WLL
		val rVars = cs.foldLeft(u.rhs.vars)((vars, c) => c.asInstanceOf[Reducibility].s.vars ++ vars)
		val lVars = cs.foldRight(u.lhs.varIds)((c, vars) => vars ++ c.asInstanceOf[Reducibility].t.varIds)

		// count variables
		// FIXME: might be useful in term for flat/shallow-criteria
		val varMap = rVars.foldLeft(Map.empty[String, Int])((m, v) => {
			// FIXME: Compare to RLE-compression :)
			val count = if (m.contains(v.id)) m(v.id) + 1 else 1
			m + (v.id -> count)
		})

		val nonlinearVars = varMap.filter(entry => entry._2 > 1).keySet

		val commons = lVars.intersect(nonlinearVars)

		commons.isEmpty
	}

}

class CTRS(val rules : List[ConditionalRule]) extends (Term => Term) {
	// underlying trs
	val utrs = new TRS(rules.map(_.u))

	def defined(): Set[String] = rules.foldLeft(Set.empty[String])(_ + _.u.lhs.f)

	def apply(t: Term): Term = apply(t, t.parent)

	def apply(t: Term, target: TermList): Term = recapply(t, target, rules)

	@tailrec private def recapply(t: Term, target: TermList, rules: List[ConditionalRule]): Term = rules match {
		case rule :: rest =>
			val u = rule.apply(t, this, target)
			if(u ne null) u
			else recapply(t, target, rest)
		case _ => null
	}

	def isOriented: Boolean = rules.forall(_.isOriented)

	def isDeterministic: Boolean = rules.forall(_.isDeterministic)

	def isRightStable: Boolean = rules.forall(_.isRightStable(utrs))

	def isProperlyOriented: Boolean = rules.forall(_.isProperlyOriented)

	// the following two are important for soundness
	def isWLL: Boolean = rules.forall(_.isWLL) // FIXME

	def isWRL: Boolean = false // FIXME
}

