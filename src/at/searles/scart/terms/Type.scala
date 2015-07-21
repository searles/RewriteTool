package at.searles.scart.terms

/**
 * Types for higher order
 */
trait Type {}

class BaseType(val name: String) extends Type
class FunType(val l: Type, val r: Type) extends Type


/*
On Higher order:
We have 5 kinds of terms: Funs, Apps, Lambdas, LambdaVars and Vars.
Funs and Vars have certain types.
(What about lambda vars of different type and debruijn?)

I think that for each type of a var we need one unique lambda var.
Because in the current system, it is replaced by types. But is this true?
Wouldn't it be better to keep lambda vars like it is? Actually yes, because
I mainly need it for beta reduction. And think of the following:

\x:int. x + (\y:int.y) 3

Hence, lambda vars do not have types in a higher order setting, only lambda terms do.


 */