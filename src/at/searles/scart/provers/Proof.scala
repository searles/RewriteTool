package at.searles.scart.provers

class Proof {
	var proof = List.empty[String]
	var status: Option[Boolean] = None

	def append(line: String): Unit = proof = line :: proof
	def nl(): Unit = proof = "" :: proof

	def subproof(sub: Proof): Unit = {
		proof = sub.proof.foldRight(proof)((line, list) => ("\t" + line) :: list)
	}

	def setStatus(status: Option[Boolean]) = this.status = status

	def show() = {
		status match {
			case None => println("MAYBE")
			case Some(true) => println("YES")
			case Some(false) => println("NO")
		}

		proof.reverse.foreach(println)
	}

	override def toString = {
		proof.foldRight("")(_ + _ + "\n")
	}
}