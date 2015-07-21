package at.searles.scart.provers

object Logging {
	var level = 2

	private def show(tag: String, msg: String): Unit = {
		println(tag + "\t" + msg)
	}

	def i(tag: String, msg: String): Unit = {
		if(level == 0) show(tag, msg)
	}

	def d(tag: String, msg: String): Unit = {
		if(level <= 1) show(tag, msg)
	}
}
