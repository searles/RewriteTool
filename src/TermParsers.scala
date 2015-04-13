import javax.swing.table.TableRowSorter

import scala.util.parsing.combinator.RegexParsers

/**
 * Created by searles on 09.04.15.
 */
object TermParsers extends RegexParsers {
	def NUM: Parser[String] = """\d+""".r
	def ID: Parser[String] = """[a-zA-Z]\w*""".r
	def SYM: Parser[String] = """[+\-*/^<>=:]+""".r



	/*
	 * expr = NUM
	 *      | ID ( '(' arglist ')' )?
	 *      | SYM ( '(' arglist ')' )?
	 */

	def expr(parent: TermList): Parser[Term] =
			NUM ^^ { parent.createFun(_, new Array[Term](0))} |
			ID ~ opt( "(" ~> arglist(parent) <~ ")") ^^ {
				case id ~ Some(args) => parent.createFun(id, args.toArray)
				case id ~ None => parent.createVar(id)
			} |
			SYM ~ opt( "(" ~> arglist(parent) <~ ")") ^^ {
				case sym ~ Some(args) => parent.createFun(sym, args.toArray)
				case sym ~ None => parent.createFun(sym, new Array[Term](0))
			}


	def arglist(parent: TermList): Parser[List[Term]] =
		opt(expr(parent) ~ rep("," ~> expr(parent))) ^^ {
			case Some(head ~ tail) => head :: tail
			case None => Nil
		}

	def rule : Parser[RWRule] = {
		val list = new TermList;
		expr(list) ~ ("->" ~> expr(list) ~ opt("<=" ~> conditions(list))) ^^ {
			case lhs ~ (rhs ~ Some(cs)) => new ConditionalRule(list, lhs, rhs, cs)
			case lhs ~ (rhs ~ None) => new Rule(list, lhs, rhs)
		}
	}

	def conditions(list: TermList) : Parser[List[Condition]] = {
		condition(list) ~ rep("," ~> condition(list)) ^^ {
			case c0 ~ ctail => c0 :: ctail
		}
	}

	def condition(list: TermList) : Parser[Condition] = {
		expr(list) ~ ("->" ~> expr(list)) ^^ {
			case s ~ t => new Condition(list, s, t)
		}
	}

	def ruleList : Parser[List[RWRule]] =
		opt(rule ~ ruleList) ^^ {
			case Some(r ~ rs) => r :: rs
			case None => Nil
		}

	/*def trs : Parser[TRS] =
		rep(rule) ^^ { case rs => new TRS(rs) }*/
	def trs : Parser[TRS] = // rep does not work because we need to create a new TermList for every rule
	    // If I use rep, a new one is only created for the first, while one is reused for every other one
		// fixme (is this a bug?)
		ruleList ^^ { case rs => new TRS(rs) }

}
