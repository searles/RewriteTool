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
			parent.first = this
			parent.last = this
			0
		}

	// some fields for algorithms
	var is: Term = null
	var link: Term = null
	var mark: Boolean = false

	def merge(target: TermList): Term = {
		if(mark) throw new OccurCheck(this)
		else mark = true

		try { // because of occurcheck we use try here
			if (is != null) is
			else if (link != null && link != this) link merge target
			else {
				is = this match {
					case Var(id, _) => target.createVar(id)
					case LambdaVar(index, _) => target.createLambdaVar(index)
					case App(l, r, _) => target.createApp(l merge target, r merge target)
					case Fun(f, args, _) => target.createFun(f, args.map(_ merge target))
					case Lambda(t, _) => target.createLambda(t merge target)
				}
				is
			}
		} finally {
			mark = false
		}
	}

	def unsetIs(): Unit = {
		if (is != null) {
			is = null
			if (link != null && link != this) link unsetIs()
			else {
				val u = this match {
					case App(l, r, _) => l unsetIs(); r unsetIs()
					case Fun(f, args, _) => args.foreach(_ unsetIs())
					case Lambda(t, _) => t unsetIs()
					case _ =>
				}
			}
		}
	}

	// --------------- unification  ------------------

	def unification(that: Term): Boolean = {
		if(this.link != null) {
			this.link.unification(that)
		} else if(that.link != null) {
			this.unification(that.link)
		} else {
			auxunification(that)
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
		if(that.link != null) that.link = null
		else if(link != null) {
			link = null
			this match {
				case Fun(_, args, _) => args foreach { _.unmatch() }
				case App(l, r, _) => l.unmatch(); r.unmatch()
				case Lambda(t, _) => t.unmatch()
				case _ => // nothing
			}
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

