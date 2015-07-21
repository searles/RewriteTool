package at.searles.scart.terms.rewriting

import at.searles.scart.terms._

import scala.annotation.tailrec
import scala.collection.immutable.TreeMap
import scala.collection.mutable



/*abstract class GenericTRS(val rules : List[RWRule]) extends (Term => Term) {



	@tailrec private def recapply(t: Term, rules: List[RWRule]): Term = rules match {
		case Nil => null
		case rule :: tail => rule.apply(t, this) match {
			case null => recapply(t, tail)
			case u => u
		}
	}

	def apply(t: Term): Term = {
		recapply(t, rules)
	}

	def applyAll(t: Term): Set[Term] =
		rules.foldLeft(Set.empty[Term])((reducts, rule) => rule.apply(t, this) match {
			case null => println(t + " -> null"); reducts
			case u => println(t + " -> " + u); reducts + u
		})

	def defined(): Set[String] = rules.map(rule => rule.lhs() match {
		case Fun(f, _, _) => f
		case _ => sys.error("bad format: " + rule)
	}).toSet


	def isConstructorSystem: Boolean = {
		// fixme: case that root is not defined is not considered because
		// it is an invalid TRS in that case.
		val defs = defined()
		rules.forall(rule => rule.lhs().findFirst(rule.lhs().noRoot {
			case t@(fun@Fun(f, _, _)) => defs.contains(f)
			case _ => false
		}).isEmpty)
	}

	def isColl: Boolean = rules.exists(_.isColl)
	def isLL: Boolean = rules.forall(_.isLL)
	def isRL: Boolean = rules.forall(_.isRL)

}
*/