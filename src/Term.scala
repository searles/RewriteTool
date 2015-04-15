import scala.annotation.tailrec


/**
 * Created by searles on 09.04.15.
 * Term class.
 */
sealed abstract class Term(val parent: TermList) {
	var next: Term = null

	// append to parent
	val pos: Int = if (parent.last != null) {
			val u = parent.last
			u.next = this
			parent.last = this
			u.pos + 1
		} else {
			parent.head = this
			parent.last = this
			0
		}

	// some fields for algorithms
	var is: Term = null
	var link: Term = null
	var mark: Boolean = false

	// ----------- traversal -------------------------------------------

	// f(a, g(b)).replace(c, 0 :: 1 :: Nil)
	    // f(a, g(b)).replace(c, 1 :: Nil)
			// f(a,g(b)).replace(c, Nil)
			// f(a,g(b))
		// g(b)
	// b

	def at(p: Int): Term = this match {
		case Fun(f, args, _) => if(p < args.length) args(p) else null
		case App(l, r, _) => if(p == 0) l else if(p == 1) r else null
		case Lambda(t, _) => if(p == 0) t else null
		case _ => null
	}

	def arity(): Int = this match {
		case Fun(f, args, _) => args.length
		case App(l, r, _) => 2
		case Lambda(t, _) => 1
		case _ => 0
	}

	def replace(replacement: Term, p: Int): Term = this match {
		case Fun(f, args, _) => if(p >= 0 && p < args.length) {
			// create array with new argument
			val newargs = new Array[Term](args.length)
			(0 until args.length).foreach(i => newargs(i) = if(i == p) replacement else args(i))
			parent.createFun(f, newargs)
		} else throw new IllegalArgumentException("no such position")
		case App(l, r, _) =>
			if(p == 0) parent.createApp(replacement, r) else
			if(p == 1) parent.createApp(l, replacement)
			else throw new IllegalArgumentException("no such position")
		case Lambda(t, _) =>
			if(p == 0) parent.createLambda(replacement)
			else throw new IllegalArgumentException("no such position")
		case _ => throw new IllegalArgumentException("no such position")
	}

	def replace(replacement: Term, pos: List[Int]): Term = revreplace(replacement, pos.reverse)

	private def revreplace(replacement: Term, revpos: List[Int]): Term = revpos match {
			// fixme (what?)
		case i :: tail =>
			val u = at(i).revreplace(replacement, tail)
			replace(u, i)
		case _ => replacement
	}

	private def auxtraverse[B](f: ((Term, List[Int]) => B), pos: List[Int]) : List[B] = {
		val list = this match {
			case Fun(_, args, _) => args.indices.foldLeft(List[B]())((l, i) => l ++ args(i).auxtraverse(f, i :: pos))
			case App(l, r, _) => l.auxtraverse(f, 0 :: pos) ++ r.auxtraverse(f, 1 :: pos)
			case Lambda(t, _) => t.auxtraverse(f, 0 :: pos)
			case _ => Nil
		}

		f(this, pos) :: list
	}

	def traverse[B](f: ((Term, List[Int]) => B)): List[B] = auxtraverse(f, Nil)

	// ----------- inserting a term into a TermList -----------------------

	def merge(target: TermList): Term = {
		if(mark) throw new OccurCheck(this)
		else mark = true

		try { // because of occurcheck we use try here
			if (is == null) {
				is = if (link != null && link != this) link merge target
					else this match {
						case Var(id, _) => target.createVar(id)
						case LambdaVar(index, _) => target.createLambdaVar(index)
						case Lambda(t, _) => target.createLambda(t merge target)
						case App(l, r, _) =>  // must unsetIs in case of an occurcheck
							l merge target // will use is-field
							try {
								r merge target
								target.createApp(l.is, r.is) // return the new app
							} finally {
								if(r.is == null) // i.e. there was an error in r.merge(target)
									l.unsetIs()
							}
						case Fun(f, args, _) =>
							try {
								args.foreach(_ merge target) // call merge on all subterms
								val newargs = new Array[Term](args.length)
								(0 until args.length).foreach(i => newargs(i) = args(i).is)
								target.createFun(f, newargs)
							} finally {
								if(args.nonEmpty && (args.last.is == null)) {
									// there was an error, hence unsetIs for all args
									(0 until args.length).foreach(i => args(i).unsetIs())
								}
							}
					}
			}

			is
		} finally { // fixme maybe if is == null unset is in subterms?
			mark = false
		}
	}

	def unsetIs(): Unit = {
		if (is != null) {
			is = null
			if (link != null && link != this) link unsetIs()
			else (0 until arity()).foreach(at(_).unsetIs())
		}
	}

	// --------------- unification  ------------------

	def unification(that: Term): Boolean = {
		if(this == that) true
		else if(this.link != null) {
			this.link.unification(that)
		} else if(that.link != null) {
			this.unification(that.link)
		} else {
			if(auxunification(that)) { this.link = that ; true }
			else false
		}
	}

	@tailrec private def argunification(i: Int, args0 : Array[Term], args1 : Array[Term]) : Boolean = {
		if(i >= args0.length) true
		else if(!args0(i).unification(args1(i))) {
			(0 until i).foreach(j => args0(j).ununify(args1(j))) ;	false
		} else argunification(i + 1, args0, args1)
	}


	private def auxunification(that: Term): Boolean = this match {
		case fun @ Fun(f, args, _) => that match {
			case v2 @ Var(id, _) => v2.link = fun ; true
			case fun2 @ Fun(f2, args2, _) if (f == f2) && (args.length == args2.length) &&
				argunification(0, args, args2) => true
			case _ => false
		} case Var(_, _) => this.link = that ; true
		case _ => throw new IllegalArgumentException
	}

	def ununify(that: Term): Unit = {
		// assert: !(this.link != null & that.link != null)
		if(this.link != null) {
			this.link.ununify(that)
			this.link = null
			// call ununify on subterms
			// assert: if 'this' has a subterm at pos i, then so does that.
			(0 until arity()).foreach(i => this.at(i).ununify(that at i))
		} else if(that.link != null) {
			that.ununify(this)
		}
	}

	// --------------- matching  ------------------

	def matching(that: Term): Boolean = {
		if (auxmatching(that)) { this.link = that; true }
		else false
	}

	@tailrec private def argsmatching(i: Int, args0 : Array[Term], args1 : Array[Term]) : Boolean = {
		if(i >= args0.length) true
		else if(!args0(i).matching(args1(i))) {
			(0 until i).foreach(args0(_).unmatch()) ;	false
		} else argsmatching(i + 1, args0, args1)
	}

	private def auxmatching(that: Term): Boolean = {
		if (link != null) link == that
		else this match {
			case Var(_, _) => link = that; true
			case Fun(f, args, _) => that match {
				case Fun(f2, args2, _) if f == f2 && args.length == args2.length && argsmatching(0, args, args2) => true
				case _ => false
			}
			case App(l, r, _) => that match {
				case App(l2, r2, _) => if (l matching l2) {
						if (r matching r2) { true }
						else { l.unmatch(); false }
					} else false
				case _ => false
			}
			case LambdaVar(_, _) => true // FIXME
			case Lambda(t, _) => that match {
				case Lambda(t2, _) => t matching t2
				case _ => false
			}
		}
	}

	def unmatch(): Unit = {
		if (link != null) {
			link = null
			this match {
				case Fun(_, args, _) => args foreach {_.unmatch()}
				case App(l, r, _) => l.unmatch(); r.unmatch()
				case Lambda(t, _) => t.unmatch()
				case _ => // nothing
			}
		}
	}

	def map(mapping: Term => Term): Term = {
		//Counter.count = Counter.count + 1; // fixme remove
		if (link != null)
			link
		else {
			val u = mapping(this) ;
			this.link = if(u == null) auxmap(mapping) else u map mapping
			this.link
		}
	}

	private def auxmap(mapping: Term => Term): Term = this match {
		case Fun(f, args, _) =>
			args.foreach(_.map(mapping))
			if (args.forall(t => t.eq(t.link))) this
			else parent.createFun(f, args.map(_.link)).map(mapping)
		case App(l, r, _) =>
			l.map(mapping); r.map(mapping)
			if(l.link.eq(l) && r.link.eq(r)) this
			else parent.createApp(l, r).map(mapping)
		case Lambda(t, _) => this // FIXME
		case _ => this // it is a leaf node
	}
}

case class Fun(f: String, args: Array[Term], p: TermList) extends Term(p) {
	//override def toString() : String = pos + ":" + f + " " + args.map(_.pos)
	override def toString() : String = f + "(" + args.mkString(", ") + ")"
}

case class Var(id: String, p: TermList) extends Term(p) {
	override def toString() : String = id
}

case class App(l: Term, r: Term, p: TermList) extends Term(p) {
	override def toString() : String = l + " " + r
}

/*case class Const(val id: String, p: TermList) extends Term(p) {
	override def toString() : String = id
}*/

case class Lambda(t: Term, p: TermList) extends Term(p) {

}

// deBruijn-Index
case class LambdaVar(index: Int, p: TermList) extends Term(p) {

}

class OccurCheck(val t: Term) extends RuntimeException

