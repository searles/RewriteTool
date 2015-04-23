package at.searles.kart.coco

import at.searles.kart.terms.TermParsers._
import at.searles.kart.terms._

import scala.util.parsing.combinator.RegexParsers

/**
  * Created by searles on 22.04.15.
  */
object TPDBParser extends RegexParsers {

	def NUM: Parser[String] = """\d+""".r

	def ID: Parser[String] = """[a-zA-Z]\w*'*""".r

	def SYM: Parser[String] = """[+\-*/^<>=:.]+""".r

	def spec: Parser[TRS] =
		varspec >> { rulespec(_) } | rulespec(Set.empty[String])

	def varspec: Parser[Set[String]] = ("(" ~ "VAR") ~> rep(ID) <~ ")" ^^ {
		_.toSet
	}

	def rulespec(vars: Set[String]): Parser[TRS] = ("(" ~ "RULES") ~> trs(vars) <~ ")"

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
		val list = new TermList
		term(list, vars) ~ ("->" ~> term(list, vars)) ^^ {
			case lhs ~ rhs => new Rule(list, lhs, rhs)
		}
	}

	/*def rule(vars: Set[String]) : Parser[RWRule] = {
		val list = new TermList
		term(list, vars) ~ ("->" ~> term(list, vars) ~ opt("<=" ~> conditions(list, vars))) ^^ {
			case lhs ~ (rhs ~ Some(cs)) => new ConditionalRule(list, lhs, rhs, cs)
		}
	}

	def conditions(list: TermList, vars: Set[String]) : Parser[List[Condition]] =
		(condition(list, vars) ~ rep("," ~> condition(list, vars))) ^^ mkList

	def condition(list: TermList, vars: Set[String]) : Parser[Condition] = {
		term(list, vars) ~ ("->" ~> term(list, vars)) ^^ {
			case s ~ t => new Condition(list, s, t)
		}
	}*/

	def rulelist(vars: Set[String]): Parser[List[RWRule]] = rep(rule(vars))

	/*def trs : Parser[TRS] =
		rep(rule) ^^ { case rs => new TRS(rs) }*/
	def trs(vars: Set[String]): Parser[TRS] = rulelist(vars) ^^ {
		new TRS(_)
	}
}