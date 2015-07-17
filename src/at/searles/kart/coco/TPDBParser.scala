package at.searles.kart.coco

import at.searles.kart.coco.ConditionType.ConditionType
import at.searles.kart.terms._
import at.searles.kart.terms.rewriting._

import scala.util.parsing.combinator.RegexParsers

/**
  * Created by searles on 22.04.15.
  */
object ConditionType extends Enumeration {
	type ConditionType = Value
	val oriented, join, semieq = Value
}

object TPDBParser extends RegexParsers {

	def NUM: Parser[String] = """\d+""".r

	def ID: Parser[String] = """[a-zA-Z]\w*'*""".r

	def SYM: Parser[String] = """[+\-*/^<>=:.]+""".r

	def ctrsspec: Parser[CTRS] =  conditiontype >>
		(ctype => varspec >> {
			condrulespec(ctype, _)
		} | condrulespec(ctype, Set.empty[String]))

	def conditiontype: Parser[ConditionType] =
		(("(" ~ "CONDITIONTYPE" ) ~>
			("ORIENTED" | "JOIN" | "SEMI-EQUATIONAL")
			) <~ ")" ^^ {
				case "ORIENTED" => ConditionType.oriented
				case "JOIN" => ConditionType.join
				case "SEMI-EQUATIONAL" => ConditionType.semieq}

	def condrulespec(ctype: ConditionType, vars: Set[String]): Parser[CTRS] = ("(" ~ "RULES") ~> ctrs(ctype, vars) <~ ")"

	def trsspec: Parser[TRS] =
		varspec >> { rulespec } | rulespec(Set.empty[String])

	def varspec: Parser[Set[String]] = ("(" ~ "VAR") ~> rep(ID) <~ ")" ^^ {
		_.toSet
	}

	def rulespec(vars: Set[String]): Parser[TRS] = ("(" ~ "RULES") ~> trs(vars) <~ ")"


	def term(vars: Set[String]): Parser[Term] = term(new TermList, vars)

	// num, f(args)
	def term(parent: TermList, vars: Set[String]): Parser[Term] =
		NUM ^^ {
			parent.createFun(_, new Array[Term](0))
		} |
			ID ~ opt("(" ~> arglist(parent, vars) <~ ")") ^^ {
				case id ~ Some(args) => parent.createFun(id, args.toArray)
				case id ~ None => if(vars.contains(id)) parent.createVar(id) else  parent.createFun(id, Array.empty[Term])
			} |
			SYM ~ opt("(" ~> arglist(parent, vars) <~ ")") ^^ {
				case sym ~ Some(args) => parent.createFun(sym, args.toArray)
				case sym ~ None => parent.createFun(sym, new Array[Term](0))
			}


	// (term (, term)*)?
	def arglist(parent: TermList, vars: Set[String]): Parser[List[Term]] =
		opt(term(parent, vars) ~ rep("," ~> term(parent, vars))) ^^ {
			case Some(head ~ tail) => head :: tail
			case None => Nil
		}

	def rule(vars: Set[String]): Parser[Rule] = {
		term(vars) ~ ("->" ~> term(vars)) ^^ {
			case lhs ~ rhs => Rule.make(lhs, rhs)
		}
	}

	def condrule(condtype: ConditionType, vars: Set[String]): Parser[ConditionalRule] = {
		rule(vars) ~ conditions(condtype, vars) ^^ { case r ~ cs => ConditionalRule.make(r, cs) }
	}

	def conditions(condtype: ConditionType, vars: Set[String]) : Parser[List[Condition]] =
		opt("|" ~> condition(condtype, vars) ~ rep("," ~> condition(condtype, vars))) ^^ {
			case None => List.empty[Condition]
			case Some(c ~ cs) => c :: cs
		}

	def condition(condtype: ConditionType, vars: Set[String]) : Parser[Condition] = {
		term(vars) ~ ("==" ~> term(vars)) ^^ {
			case s ~ t =>
				if(condtype == ConditionType.join) new Joinability(s, t)
				else if(condtype == ConditionType.oriented) new Reducibility(s, t)
				else if(condtype == ConditionType.semieq) new SemiEq(s, t)
				else sys.error("unknown condition type")
		}
	}

	def trs(vars: Set[String]): Parser[TRS] = rep(rule(vars)) ^^ {
		new TRS(_)
	}

	def ctrs(ctype: ConditionType, vars: Set[String]): Parser[CTRS] = rep(condrule(ctype, vars)) ^^ {
		new CTRS(_)
	}

}