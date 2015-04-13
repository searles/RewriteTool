/**
 * Created by searles on 09.04.15.
 */
sealed abstract class Term(val parent: TermList) {
	val pos: Int = parent.terms match {
		case head :: _ => head.pos + 1
		case _ => 0
	}

	// some fields for algorithms
	var is: Term = null;
	var link: Term = null;


	def merge(target: TermList): Term = {
		if (is != null) is
		else if (link != null && link != this) link merge (target)
		else {
			val u = this match {
				case Var(id, _) => target.createVar(id)
				case LambdaVar(index, _) => target.createLambdaVar(index)
				case App(l, r, _) => target.createApp(l merge (target), r merge (target))
				case Fun(f, args, _) => target.createFun(f, args.map(_ merge (target)))
				case Lambda(t, _) => target.createLambda(t merge (target))
			};
			is = u;
			u
		}
	}

	def unsetIs: Unit = {
		if (is != null) {
			is = null;
			if (link != null && link != this) link unsetIs
			else {
				val u = this match {
					case App(l, r, _) => {
						l unsetIs; r unsetIs
					}
					case Fun(f, args, _) => args.foreach(_ unsetIs)
					case Lambda(t, _) => t unsetIs
					case _ =>
				}
			}
		}
	}

	def unmatch: Unit = {
		if (link != null) {
			link = null;
			this match {
				case Fun(_, args, _) => args map {
					_.unmatch
				}
				case App(l, r, _) => {
					l.unmatch; r.unmatch
				}
				case Lambda(t, _) => {
					t.unmatch
				}
				case _ => // nothing
			}
		}
	}

	def matchArgs(argList1: List[Term], argList2: List[Term]): Boolean = (argList1, argList2) match {
		case (Nil, Nil) => true // first go inside to make sure the arity is ok
		case (Nil, _) | (_, Nil) => false
		case (t :: ts, u :: us) => if (matchArgs(ts, us)) {
			if (t matching u) {
				true
			} else {
				ts.map {
					_.unmatch
				}
				false
			}
		} else {
			false
		}
	}

	/*def unify(that: Term): Boolean = {
		if(this.link )
	}

	def auxunify(that: Term): Boolean = this match {
		case fun @ Fun(f, args) => that match {
			case v2 @ Var(id) => v2.link = fun ;
			case fun2 @ Fun(f2, args2) if fun == fun2 => {
				if((args, args2).zipped.forall(_.unify(_))) {
					true
				} else {
					args.foreach(_.ununify())
				}
			}
		}
	} */



	def matching(that: Term): Boolean = {
		if (auxMatching(that)) {
			this.link = that;
			true
		} else {
			false
		}
	}

	def auxMatching(that: Term): Boolean = {
		if (link != null) link == that
		else this match {
			case Var(_, _) => {
				link = that; true
			}
			case Fun(f, args, _) => that match {
				case Fun(f2, args2, _) if f == f2 => matchArgs(args, args2)
				case _ => false
			}
			case App(l, r, _) => that match {
				case App(l2, r2, _) => {
					if (l matching l2) {
						if (r matching r2) {
							true
						} else {
							l unmatch;
							false
						}
					} else {
						false
					}
				}
				case _ => false
			}
			case LambdaVar(_, _) => {
				true
			} // FIXME
			case Lambda(t, _) => that match {
				case Lambda(t2, _) => t matching t2
				case _ => false
			}
		}
	}

	def auxmap(trs: TRS): Term = this match {
		case Fun(f, args, _) => {
			args.foreach(_.map(trs))

			if (args.forall(t => t.eq(t.link))) {
				// it is actually the same
				this
			} else {
				// this -> u ->* ret
				// must set this.link in this case
				parent.createFun(f, args.map(_.link)).map(trs)
			}
		}
		case App(l, r, _) => {
			l.map(trs) ; r.map(trs) ;
			if(l.link.eq(l) && r.link.eq(r)) {
				this
			} else {
				parent.createApp(l, r).map(trs)
			}
		} // FIXME
		case Lambda(t, _) => this // FIXME
		case _ => this // it is a leaf node
	}


	// tail recursive so that it will use a loop
	def map(trs: TRS): Term = {
		//Counter.count = Counter.count + 1; // fixme remove
		if (link != null)
			link
		else {
			val u = trs.apply(this) ;
			if(u == null) {
				this.link = auxmap(trs)
			}  else {
				this.link = u map trs
			}

			this.link
		}
	}
}

case class Fun(val f: String, val args: List[Term], p: TermList) extends Term(p) {
	//override def toString() : String = pos + ":" + f + " " + args.map(_.pos)
	override def toString() : String = f + "(" + args.mkString(", ") + ")"
}

case class Var(val id: String, p: TermList) extends Term(p) {
	override def toString() : String = id
}

case class App(val l: Term, val r: Term, p: TermList) extends Term(p) {
	override def toString() : String = l + " " + r
}

case class Const(val id: String, p: TermList) extends Term(p) {
	override def toString() : String = id
}

case class Lambda(val t: Term, p: TermList) extends Term(p) {

}

// deBruijn-Index
case class LambdaVar(val index: Int, p: TermList) extends Term(p) {

}

