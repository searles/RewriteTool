package at.searles.scart.terms

import at.searles.scart.terms.rewriting._

import scala.util.parsing.combinator.RegexParsers

/**
 * Parser for all kinds of terms and TRSs. I am using my own format here.
 */
object TermParsers extends TermParsers

class TermParsers extends RegexParsers {

	def NUM: Parser[String] = """\d+""".r
	def ID: Parser[String] = """[a-zA-Z]\w*""".r
	def SYM: Parser[String] = """[+\-*/^<>=:]+""".r

	/*
	 * expr = NUM
	 *      | ID ( '(' arglist ')' )?
	 *      | SYM ( '(' arglist ')' )?
	 */

	/* Grammar:
	term
		: lambda
		| app
		| ( fun | var )
		| '(' term ')'
	 */

	/*
	expr: argexpr+

	argexpr
		: \(var)*.expr
		| ( expr )
		| term

	term:
		ID/SYM/NUM
	 */

	def expr(parent: TermList, bindings: List[String]): Parser[Term] = rep1(appargs(parent, bindings)) ^^ {
		case head :: tail => tail.foldLeft(head)(parent.createApp)
		case _ => sys.error("rep1 does not return Nil")
	}

	def appargs(parent: TermList, bindings: List[String]): Parser[Term] =
		lambda(parent, bindings) |
		("(" ~> expr(parent, bindings) <~ ")") |
		symbol(parent, bindings)

	def lambda(parent: TermList, bindings: List[String]):Parser[Term] = {
		// >> resemles ~ but additionally reuses the argument of the previous one.
		("\\" ~> rep(ID) <~ ".") >> {newids => expr(parent, newids.reverse ++ bindings) ^^ {
			newids.foldLeft(_)((u, id) => parent.createLambda(u))
		}}
	}

	// bindings is in wrong direction, ie innermost bound vars are deeper
	def symbol(parent: TermList, bindings: List[String]): Parser[Term] = {
		NUM ^^ { parent.createFun(_, new Array[Term](0))} |
		SYM ^^ { parent.createFun(_, new Array[Term](0))} |
		ID ^^ { case id =>
			// multiple cases. Case 1: Lambda-Var
			val index = bindings.indexOf(id)
			if(index >= 0) parent.createLambdaVar(index)
			else if(id.charAt(0).isUpper) parent.createVar(id)
			else parent.createFun(id, new Array[Term](0))
		}
	}
		
	def term: Parser[Term] = term(new TermList)

	// num, f(args)
	def term(parent: TermList): Parser[Term] =
			NUM ^^ { parent.createFun(_, new Array[Term](0))} |
			ID ~ opt( "(" ~> arglist(parent) <~ ")") ^^ {
				case id ~ Some(args) => parent.createFun(id, args.toArray)
				case id ~ None => parent.createVar(id)
			} |
			SYM ~ opt( "(" ~> arglist(parent) <~ ")") ^^ {
				case sym ~ Some(args) => parent.createFun(sym, args.toArray)
				case sym ~ None => parent.createFun(sym, new Array[Term](0))
			}


	// (term (, term)*)?
	def arglist(parent: TermList): Parser[List[Term]] =
		opt(term(parent) ~ rep("," ~> term(parent))) ^^ {
			case Some(head ~ tail) => head :: tail
			case None => Nil
		}


	/*def ruleList : Parser[List[RWRule]] =
		opt(rule ~ ruleList) ^^ {
			case Some(r ~ rs) => r :: rs
			case None => Nil
		}

	def trs : Parser[GenericTRS] = // rep does not work because we need to create a new TermList for every rule
	    // If I use rep, a new one is only created for the first, while one is reused for every other one
		// fixme (is this a bug?)
		ruleList ^^ { case rs => new GenericTRS(rs) }
*/
}
