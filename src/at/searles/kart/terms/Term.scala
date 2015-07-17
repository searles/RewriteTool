package at.searles.kart.terms

import at.searles.kart.provers.Logging

import scala.annotation.tailrec
/**
 * Term class.
 */
/*class Direct(t: Term) /*extends Iterator[A]*/ {
	var i = 0
	val ar = t.length

	def incr(): Unit = i = i + 1

	def end: Boolean = i >= ar

	def get() = t.apply(i)
	def index(): Int = i

	def replace(replacement: Term): Term = t.replace(replacement, i)

	/*override def next() = {
		val ret = get()
		incr()
		ret
	}

	override def hasNext = !end*/
}


class Traverser(t: Term) {

	var root: Boolean = true
	var done = false

	var subtermTraverser: Direct = null
	var subtermTreeTraverser: Traverser = null

	var is: Term = null

	def isRoot: Boolean = root

	def skip(): Unit = // the current root will not be traversed
		if(root) done = true
		else {
			subtermTreeTraverser.skip()
			incr()
		}

	private def nextParallelSubterm(): Unit = {
		done = subtermTraverser.end
		if(!done) subtermTreeTraverser = subtermTraverser.get().traverser
	}

	def incr(): Unit =
		if(root) {
			root = false
			subtermTraverser = t.direct
			nextParallelSubterm()
		} else {
			subtermTreeTraverser.incr()
			if(subtermTreeTraverser.end) {
				subtermTraverser.incr()
				nextParallelSubterm()
			}
		}

	def get(): Term = if(root) t else subtermTreeTraverser.get() // FIXME

	def replace(replacement: Term): Term =
		if(root)
			replacement
		else
			subtermTraverser.replace(subtermTreeTraverser.replace(replacement))

	private def auxpos(p: List[Int]): List[Int] = if(root) p else subtermTreeTraverser.auxpos(subtermTraverser.index :: p)
	def pos(): List[Int] = auxpos(List.empty[Int])

	def end: Boolean = done
}*/


sealed abstract class Term(val parent: TermList, val debruijn: Int) extends Ordered[Term] with IndexedSeq[Term] {
	var next: Term = null

	// append to parent
	val pos: Int = if (parent.lastNode != null) {
			val u = parent.lastNode
			u.next = this
			parent.lastNode = this
			u.pos + 1
		} else {
			parent.headNode = this
			parent.lastNode = this
			0
		}

	// some fields for algorithms
	var is: Term = null

	var link: Term = null
	var mark: Boolean = false

	var isDebruijn: Term = null

	// ----------- traversal -------------------------------------------

	// f(a, g(b)).replace(c, 0 :: 1 :: Nil)
	    // f(a, g(b)).replace(c, 1 :: Nil)
			// f(a,g(b)).replace(c, Nil)
			// f(a,g(b))
		// g(b)
	// b

	/*override def ==(that: AnyRef) = sys.error("not allowed");
	override def !=(that: AnyRef) = sys.error("not allowed");*/

	// Members of Any
	override def equals(o: Any): Boolean = o match {
		case t: Term => this.compare(t) == 0
		case _ => false
	}

	override def compare(t: Term): Int = {
		assert(parent eq t.parent)
		pos - t.pos // FIXME subterms are smaller
	}

	// Abstract members  for IndexedSeq
	def length: Int = this match {
		case Fun(f, args, _) => args.length
		case App(l, r, _) => 2
		case Lambda(t, _) => 1
		case _ => 0
	}

	def apply(p: Int): Term = this match {
		case Fun(f, args, _) => if(0 <= p && p < args.length) args(p) else sys.error("no such position: " + p + " of " + length)
		case App(l, r, _) => if(p == 0) l else if(p == 1) r else sys.error("no such position")
		case Lambda(t, _) => if(p == 0) t else sys.error("no such position")
		case _ => sys.error("no such position: " + this + ", " + p + " where " + length)
	}

	// ---------------------------

	// positions are reverse lists. The position i.p corresponds to p ++ i.
	def apply(ps: List[Int]): Term = ps.foldRight(this)((p, t) => t.apply(p))

	// create a new term in replacement, in which the term at p is inserted
	def replace(replacement: Term, p: Int): Term = this match {
		case Fun(f, args, _) => if(p >= 0 && p < args.length) {
			// create array with new argument
			val newargs = new Array[Term](args.length)
			args.indices.foreach(i => newargs(i) = if(i == p) replacement else replacement.parent insert args(i))
			replacement.parent.createFun(f, newargs)
		} else sys.error("no such position")
		case App(l, r, _) =>
			if(p == 0) parent.createApp(replacement, replacement.parent insert r) else
			if(p == 1) parent.createApp(replacement.parent insert l, replacement)
			else sys.error("no such position")
		case Lambda(t, _) =>
			if(p == 0) parent.createLambda(replacement)
			else sys.error("no such position")
		case _ => sys.error("no such position")
	}

	private def revreplace(replacement: Term, revpos: List[Int]): Term = revpos match {
		case i :: tail =>
			val u = apply(i).revreplace(replacement, tail)
			replace(u, i)
		case _ => replacement
	}

	def replace(replacement: Term, pos: List[Int]): Term = revreplace(replacement, pos.reverse)

	private def auxtraverse[A](fn: (Term, List[Int]) => A, filter: (Term, List[Int]) => Boolean, p: List[Int]): List[A] = {
		// traverse subterms
		val tl = (0 until length).toList.flatMap(i => {
			val subterm = apply(i)
			subterm.auxtraverse(fn, filter, i :: p)
		})

		if(filter(this, p)) fn(this, p) :: tl else tl
	}

	def traverse[A](fn: (Term, List[Int]) => A) = auxtraverse[A](fn, (t: Term, p: List[Int]) => true, List.empty[Int])

	def filteredTraverse[A](fn: (Term, List[Int]) => A, filter: (Term, List[Int]) => Boolean) = auxtraverse[A](fn, filter, List.empty[Int])

	/*def filteredTraverse[A](fn: (Term, List[Int]) => A, filter: (Term, List[Int]) => Boolean) = {

	}/*

	/*def direct = new Direct(this)
	def traverser = new Traverser(this)*/

	/*private def auxtraverse[B](f: ((Term, List[Int]) => B), pos: List[Int]) : List[B] = {
		val list = this match {
			case Fun(_, args, _) => args.indices.foldRight(List[B]())((i, l) => l ++ args(i).auxtraverse(f, i :: pos))
			case App(l, r, _) => r.auxtraverse(f, 1 :: pos) ++ l.auxtraverse(f, 0 :: pos)
			case Lambda(t, _) => t.auxtraverse(f, 0 :: pos)
			case _ => Nil
		}

		f(this, pos) :: list
	}

	def traverse[B](f: ((Term, List[Int]) => B)): List[B] = auxtraverse(f, Nil)*/*/*/


	private def unmark(): Unit = {
		if(mark) {
			mark = false
			this.foreach(_.unmark())
		}
	}

	// there are two ways to do dfs:
	// one: first mark all subterms and then unmark them afterwards
	// two: mark subterms while iterating, then then unmark them
	private def auxfind(fn: Term => Boolean): Option[Term] = {
		if(!mark) {
			mark = true
			if(fn(this)) Some(this)
			else {
				@tailrec def aux(i: Iterator[Term]): Option[Term] = {
					if(i.hasNext) {
						i.next().auxfind(fn) match {
							case s@Some(_) => s
							case None => aux(i)
						}
					} else {
						None
					}
				}

				aux(iterator)
			}
		} else None
	}

	def findFirst(fn: Term => Boolean): Option[Term] = {
		val ret = auxfind(fn)
		unmark()
		ret
	}

	// sorted by outer first
	private def auxfindAll(fn: Term => Boolean, l: List[Term]): List[Term] = {
		if(!mark) {
			mark = true
			val ll = this.foldRight(l)((t, ll) => t.auxfindAll(fn, ll))
			if(fn(this)) this :: ll else ll
		} else l
	}

	def findAll(fn: Term => Boolean): List[Term] = {
		val ret = auxfindAll(fn, Nil)
		unmark()
		ret
	}

	private def auxfindOutermost(fn: Term => Boolean, l: List[Term]): List[Term] = {
		if(!mark) {
			mark = true
			if(fn(this)) this :: l else this.foldRight(l)((t, ll) => t.auxfindOutermost(fn, ll))
		} else l
	}
	
	def findOutermost(fn: Term => Boolean): List[Term] = {
		val ret = auxfindOutermost(fn, Nil)
		unmark()
		ret
	}

	def noRoot(fn: Term => Boolean) = (t: Term) => (t ne this) && fn(t)
	
	/*def findOutermostNoRoot(fn: Term => Boolean): List[Term] = {
		val ret = this.foldRight(List.empty[Term])((t, l) => auxfindOutermost(fn, l))
		unmark()
		ret
	}*/

	def isLinear: Boolean = {
		def aux(t: Term): Boolean = t match {
			case v: Var => if(v.mark) false else { v.mark = true ; true }
			case _ => t.mark = true ; t.forall(aux)
		}

		val ret = aux(this)
		unmark()

		ret
	}


	
	// in con we mark terms when we look for them
	def hasSubterm(t: Term): Boolean = if(this eq t) false else findFirst(u => t eq u).isDefined

	def vars: List[Var] = {
		def aux(t: Term, l: List[Var]): List[Var] = {
			if(t.mark) l
			else {
				t.mark = true
				t match {
					case v: Var => v :: l
					case w => w.foldLeft(l)((ll, u) => aux(u, ll))
				}
			}
		}

		val ret = aux(this, List.empty[Var])
		unmark()
		ret
	}

	def varIds: Set[String] = {
		def aux(t: Term, set: Set[String]): Set[String] = {
			if(t.mark) set
			else {
				t.mark = true
				t match {
					case v: Var => set + v.id
					case w => w.foldLeft(set)((sset, u) => aux(u, sset))
				}
			}
		}

		val ret = aux(this, Set.empty[String])
		unmark()
		ret
	}

	// get outermost subterms that are rooted by one symbol in funs
	/*private def outermostDefinedSubterms(defs: Set[String], roots: List[Fun]): List[Fun] =
		// set link to new variable if its root is a fun.
		if(!mark) {
			mark = true
			this match {
				case fun@Fun(f, _, _) if defs contains f => fun :: roots
				case _ => this.foldRight(roots)((term, list) => term.outermostDefinedSubterms(defs, list))
			}
		} else roots*/


	// replaces all outermost subterms that are rooted by a
	// function symbol in defs by a new variable
	def con(defs: Set[String], varId: String): Term = {
		def subterms = findOutermost(noRoot { case fun@Fun(f, _, _) if defs contains f => true; case _ => false })
		
		// subterms is a list of all defined outermost subterms
		if(subterms.nonEmpty) {
			val v = parent.createVar(varId)
			subterms.foreach(_.link = v)
			val ret = parent insert this
			subterms.foreach(_.link = null) // unlink
			ret
		} else this
	}

	/*def varpos(): Map[String, List[List[Int]]] = {
		var vps = Map.empty[String, List[List[Int]]]
		traverse(
			(term, pos) => term match {
				case Var(id, _) => vps += (id -> (pos :: (if (vps contains id) vps(id) else Nil)))
				case _ =>
			}
		)
		vps
	}*/


	def lin(prefix: String): Term = {
		val usedVars = collection.mutable.Set.empty[String]
		val index = Stream.from(1).iterator

		def aux(t: Term): Option[Term] = {
			t match {
				case v: Var if usedVars contains v.id => Some(parent.createVar(prefix + index.next())) // new term
				case v: Var => usedVars.add(v.id) ; None // nothing replaced
				case t: Term =>
					val replacements = t.map(aux) // get list [ None, Some(t), Some(u), None ] of terms that were replaced
					val v = replacements.indices.foldLeft(t)((u, i) => replacements.apply(i) match {
						case Some(v) => u.replace(v, i)
						case None => u
					})

					if(v eq t) None else Some(v)
			}
		}

		aux(this) match {
			case Some(t) => t
			case None => this // already linear
		}
	}


	// ----------- inserting a term into a TermList -----------------------

	def merge(target: TermList): Term = {
		if(mark) throw new OccurCheck(this)
		else mark = true

		try { // because of occurcheck we use try here
			if (is eq null) {
				is = if (link.ne(null) && link.ne(this)) link merge target
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
								if(r.is eq null) // i.e. there was an error in r.merge(target)
									l.unsetIs()
							}
						case Fun(f, args, _) =>
							try {
								args.foreach(_ merge target) // call merge on all subterms
								val newargs = new Array[Term](args.length)
								args.indices.foreach(i => newargs(i) = args(i).is)
								target.createFun(f, newargs)
							} finally {
								if(args.nonEmpty && (args.last.is eq null)) {
									// there was an error, hence unsetIs for all args
									args.indices.foreach(i => args(i).unsetIs())
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
		if (is ne null) {
			is = null
			if (link.ne(null) && link.ne(this)) link unsetIs()
			else this.foreach(_.unsetIs())
		}
	}

	private def auxDebruijn(max: Int, low: Int): Term = {
		if(isDebruijn ne null) isDebruijn
		else {
			isDebruijn =
				if(link.ne(null) && link.ne(this)) link.auxDebruijn(max, low)
				else this match {
					case App(l, r, _) =>
						val lPrime = l.auxDebruijn(max, low)
						val rPrime = r.auxDebruijn(max, low)

						if (lPrime.eq(l) && rPrime.eq(r)) this
						else parent.createApp(lPrime, rPrime)
					case Lambda(t, _) =>
						val tPrime = t.auxDebruijn(max, low)

						if (tPrime eq t) this
						else parent.createLambda(tPrime)
					case Fun(f, args, _) =>
						val argsPrime = args.map (_.auxDebruijn (max, low))

						if(args.indices.forall(i => argsPrime(i).eq(args(i)))) this
						else parent.createFun(f, args)
					case LambdaVar(index, _) =>
						if(index < low) this
						else parent.createLambdaVar(index + (max - low))
					case other => other
				}

			isDebruijn
		}
	}

	private def unsetDebruijn(): Unit = {
		if(isDebruijn.ne(null)) {
			isDebruijn = null
			this.foreach(_.unsetDebruijn())
		}
	}

	def updateDebruijn(max: Int): Term = {
		val ret = auxDebruijn(max, debruijn)
		unsetDebruijn()
		ret
	}

	// --------------- unification  ------------------

	def assertLinkIsNull(): Unit = {
		if(link ne null) sys.error("link is not null: " + this + " -> " + this.link)
		this.foreach(_.assertLinkIsNull())
	}

	def unification(that: Term): Boolean = {
		//println("unify\t" + this + "\t" + that)
		if(this eq that) true
		else if(this.link.ne(null)) {
			this.link.unification(that)
		} else if(that.link.ne(null)) {
			this.unification(that.link)
		} else {
			this match {
				case fun@Fun(f, args, _) => that match {
					case v2@Var(id, _) =>
						v2.link = fun
						true
					case fun2@Fun(f2, args2, _) if (f == f2) && (args.length == args2.length) && argunification(0, args, args2) =>
						fun.link = fun2
						true
					case _ => false
				}
				case Var(_, _) =>
					this.link = that
					true
				case _ => sys.error("not implemented")
			}
		}
	}

	@tailrec private def argunification(i: Int, args0 : Array[Term], args1 : Array[Term]) : Boolean = {
		if(i >= args0.length) true
		else if(!args0(i).unification(args1(i))) {
			(0 until i).foreach(j => args0(j).ununify(args1(j))) ;	false
		} else argunification(i + 1, args0, args1)
	}


	def ununify(that: Term): Unit = {
		// fixme this is a bad way of writing this.

		// assert: !(this.link != null & that.link != null)
		//println("!!ify\t" + this + "\t" + that)
		if(this.link.ne(null)) {
			this.link.ununify(that)
			this.link = null
			// call ununify on subterms
			// assert: if 'this' has a subterm at pos i, then so does that.
			(0 until length).foreach(i => this.apply(i).ununify(if(that eq null) null else if(that.length < i) that apply i else null))
		} else if(that.ne(null) && that.link.ne(null)) {
			that.ununify(this)
		}
	}

	// --------------- matching  ------------------

	def matching(that: Term): Boolean = {
		if (auxmatching(that)) { this.link = that; true }
		else false
	}

	// This private thing is here mainly to call unmatch after this one failed and
	// to only match those for which it passed.
	@tailrec private def argsmatching(i: Int, args0 : Array[Term], args1 : Array[Term]) : Boolean = {
		if(i >= args0.length) true
		else if(!args0(i).matching(args1(i))) {
			(0 until i).foreach(args0(_).unmatch())
			false
		} else argsmatching(i + 1, args0, args1)
	}

	private def auxmatching(that: Term): Boolean = {
		if (link ne null) link eq that
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
		if (link ne null) {
			link = null
			this match {
				case Fun(_, args, _) => args foreach {_.unmatch()}
				case App(l, r, _) => l.unmatch(); r.unmatch()
				case Lambda(t, _) => t.unmatch()
				case _ => // nothing
			}
		}
	}

	// normalizing (careful, might not terminate!)
	def normalize(mapping: Term => Term): Term = { // returns true it the term is rewritten
		//Counter.count = Counter.count + 1; // fixme remove
		//Logging.d("normalize", "normalizing " + this)

		if (link eq null) {
			val reduct = mapping(this)
			this.link = reduct match {
				case null => // no reduct, hence
					this.foreach(s => s.normalize(mapping)) // rewrite all subterms

					if (this.forall(s => s eq s.link)) this // if none of them can be rewritten, don't.
					else {
						// otherwise, create new term
						val u = this match {
							case Fun(f, args, _) => parent.createFun(f, args.map(_.link))
							case App(l, r, _) => parent.createApp(l.link, r.link)
							case Lambda(t, _) => parent.createLambda(t.link)
							case _ => sys.error("this one does not have a subterm")
						}

						u.normalize(mapping) // and normalize  this one
						// FIXME: Potential infinite loop
					}
				case t => t.normalize(mapping) // otherwise rewrite
			}
		}

		assert(link != null)

		this.link
	}

	// single step rewriting
	def rewrite(mapping: Term => Set[Term], cache: scala.collection.mutable.Map[Term, Set[Term]]): Set[Term] = {
		if(cache contains this) cache.apply(this)
		else {
			val rootReducts = mapping(this)

			val argsReducts = this.map(t => t.rewrite(mapping, cache)) // IndexedSeq of Set[Term]

			// next, generate all possible reducts
			val reducts = argsReducts.indices.foldLeft(rootReducts)((reducts, idx) => {
				val argReducts = argsReducts(idx)
				argReducts.foldLeft(reducts)((reducts, argReduct) => reducts + this.replace(argReduct, idx))
			})

			cache += (this -> reducts)

			reducts
		}
	}
}

case class Fun(f: String, args: Array[Term], p: TermList) extends Term(p, args.foldLeft(0)(_ max _.debruijn)) {
	//override def toString() : String = pos + ":" + f + " " + args.map(_.pos)
	override def toString(): String = f + "(" + args.mkString(", ") + ")" + (if(mark) "*" else "")
}

case class Var(id: String, p: TermList) extends Term(p, 0) {
	override def toString(): String = id + (if(mark) "*" else "")
}

case class App(l: Term, r: Term, p: TermList) extends Term(p, l.debruijn max r.debruijn) {
	override def toString() : String = (l match {
			case _: Lambda => "(" + l + ")"
			case _ => l.toString()
		}) + " " + (r match {
			case _: App | _: Lambda => "(" + r + ")"
			case _ => r.toString()
		}
	)
}

/*case class Const(val id: String, p: TermList) extends Term(p) {
	override def toString() : String = id
}*/

case class Lambda(t: Term, p: TermList) extends Term(p, t.debruijn + 1) {
	// careful: debruijn = lambda index + 1
	override def toString(): String = "\\" + (debruijn - 1) + "." + t
}

// deBruijn-Index
case class LambdaVar(index: Int, p: TermList) extends Term(p, 0) {
	override def toString(): String = "%" + index
}

class OccurCheck(val t: Term) extends RuntimeException {
	override def toString: String = "occur check in " + t
}

