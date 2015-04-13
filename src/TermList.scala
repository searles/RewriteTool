/**
 * Created by searles on 09.04.15.
 */
class TermList {
	var terms: List[Term] = Nil

	override def toString() = terms.toString()

	def term(str: String) : Option[Term] = {
		TermParsers.parseAll(TermParsers.expr(this), str) match {
			case TermParsers.Success(t, _) => Some(t)
			case TermParsers.NoSuccess(_, _) => None
		}
	}

	def insert(t: Term) : Term = {
		val u = t merge(this);
		t unsetIs;
		u
	}

	def createLambdaVar(index: Int) = {
		def findOrCreate(ts : List[Term]): LambdaVar = ts match {
			case (lv @ LambdaVar(index2, _)) :: _ if index == index2 => lv ; // found it
			case head :: tail => findOrCreate(tail) ; // nope, but we still might find it
			case _ => { // definitely not found - create it.
			val ret = LambdaVar(index, this);
				terms = ret :: terms;
				ret
			}
		}

		findOrCreate(terms)
	}

	def createVar(id: String) = {
		def findOrCreate(ts : List[Term]): Var = ts match {
			case (v @ Var(id2, _)) :: _ if id == id2 => v ; // found it
			case head :: tail => findOrCreate(tail) ; // nope, but we still might find it
			case _ => { // definitely not found - create it.
				val ret = Var(id, this);
				terms = ret :: terms;
				ret;
			}
		}

		findOrCreate(terms)
	}

	def createFun(f: String, args: List[Term]) = {
		val max = args.foldLeft(-1)((m, t) => m max t.pos);

		def findOrCreate(ts : List[Term]): Fun = ts match {
			case (fun @ Fun(f2, args2, _)) :: _ if f == f2 && args == args2 => fun ; // found it
			case head :: tail if head.pos > max => findOrCreate(tail) ; // nope, but we still might find it
			case _ => { // definitely not found - create it.
				val ret = Fun(f, args, this);
				terms = ret :: terms;
				ret;
			}
		}

		findOrCreate(terms)
	}

	def createApp(l: Term, r: Term) = {
		val max = l.pos max r.pos

		def findOrCreate(ts : List[Term]): App =
			ts match {
			case (app @ App(l2, r2, _)) :: _ if l == l2 && r == r2 => app ; // found it
			case head :: tail if head.pos > max => findOrCreate(tail) ; // nope, but we still might find it
			case _ => { // definitely not found - create it.
			val ret = App(l, r, this);
				terms = ret :: terms;
				ret;
			}
		}

		findOrCreate(terms)
	}

	def createLambda(t: Term): Lambda = {
		def findOrCreate(ts : List[Term]): Lambda = ts match {
			case (lambda @ Lambda(t2, _)) :: _ if t == t2 => lambda ; // found it
			case head :: tail if head.pos > t.pos => findOrCreate(tail) ; // nope, but we still might find it
			case _ => { // definitely not found - create it.
				val ret = Lambda(t, this);
				terms = ret :: terms;
				ret;
			}
		}

		findOrCreate(terms)
	}
}
