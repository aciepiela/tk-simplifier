package simplifier

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  def apply(node: Node) = simplify(node)

  def simplify(node: Node): Node = node match {
    case node: Assignment => AssignmentSimplifier(node)
    case node: NodeList => NodeListSimplifier(node)
    case node: Unary => UnarySimplifier(node)
    case node: KeyDatumList => KeyDatumListSimplifier(node)
    case node: BinExpr => BinExprSimplifier(node)
    case node: Tuple => TupleSimplifier(node)
    case node: WhileInstr => WhileInstrSimplifier(node)
    case node: IfElseExpr => IfElseExprSimplifier(node)
    case node: IfElseInstr => IfElseInstrSimplifier(node)
    case other => node
  }
}

object UnarySimplifier {

  def apply(node: Unary) = {
    val expr = Simplifier(node.expr)

    Unary(node.op, expr) match {
      case Unary("not", BinExpr("==", x, y)) => BinExpr("!=", x, y)
      case Unary("not", BinExpr("!=", x, y)) => BinExpr("==", x, y)
      case Unary("not", BinExpr(">", x, y)) => BinExpr("<=", x, y)
      case Unary("not", BinExpr("<", x, y)) => BinExpr(">=", x, y)
      case Unary("not", BinExpr(">=", x, y)) => BinExpr("<", x, y)
      case Unary("not", BinExpr("<=", x, y)) => BinExpr(">", x, y)
      case Unary("not", Unary("not", x)) => x
      case Unary("-", Unary("-", x)) => x
      case Unary("not", TrueConst()) => FalseConst()
      case Unary("not", FalseConst()) => TrueConst()

      case other => other
    }
  }
}

object NodeListSimplifier {
  def apply(node: NodeList) = {
    var nodes = node.list.map(n => Simplifier(n)).filter(n => !n.isInstanceOf[Empty])
    val uniqueAssignments = nodes.filter(n => n.isInstanceOf[Assignment]).map(n => n.asInstanceOf[Assignment])
      .groupBy(a => a.left).mapValues(list => list.last).values.toList
    nodes = nodes.filter(n => !n.isInstanceOf[Assignment] || uniqueAssignments.contains(n))
    nodes match {
      case Nil => Empty()
      case x :: Nil => x
      case list => NodeList(list)
    }
  }
}

object AssignmentSimplifier {
  def apply(node: Assignment) = {
    val l = Simplifier(node.left)
    val r = Simplifier(node.right)
    if (l == r) {
      Empty()
    } else {
      Assignment(l, r)
    }
  }
}

object KeyDatumListSimplifier {
  def apply(node: KeyDatumList) = {
    val unique = node.list.groupBy(kd => kd.key).mapValues(list => list.last).values.toList
    KeyDatumList(unique)
  }
}

object BinExprSimplifier {
  def apply(node: BinExpr) = {
    val simplified = BinExpr(node.op, Simplifier(node.left), Simplifier(node.right))
    simplified match {
      case BinExpr("+", x, IntNum(0)) => x
      case BinExpr("+", IntNum(0), x) => x
      case BinExpr("-", x, y) if x == y => IntNum(0)
      case BinExpr("*", x, IntNum(1)) => x
      case BinExpr("*", IntNum(1), x) => x
      case BinExpr("*", x, IntNum(0)) => IntNum(0)
      case BinExpr("*", IntNum(0), x) => IntNum(0)
      case BinExpr("or", x, y) if x == y => x
      case BinExpr("and", x, y) if x == y => x
      case BinExpr("and", x, TrueConst()) => x
      case BinExpr("and", TrueConst(), x) => x
      case BinExpr("or", x, TrueConst()) => TrueConst()
      case BinExpr("or", TrueConst(), x) => TrueConst()
      case BinExpr("and", x, FalseConst()) => FalseConst()
      case BinExpr("and", FalseConst(), x) => FalseConst()
      case BinExpr("or", x, FalseConst()) => x
      case BinExpr("or", FalseConst(), x) => x
      case BinExpr("==", x, y) if x == y => TrueConst()
      case BinExpr(">=", x, y) if x == y => TrueConst()
      case BinExpr("<=", x, y) if x == y => TrueConst()
      case BinExpr("!=", x, y) if x == y => FalseConst()
      case BinExpr(">", x, y) if x == y => FalseConst()
      case BinExpr("<", x, y) if x == y => FalseConst()
      case BinExpr("+", Unary("-", x), y) if x == y => IntNum(0)
      case BinExpr("/", x, y) if x == y => IntNum(1)
      case BinExpr("+", IntNum(x), IntNum(y)) => IntNum(x + y)
      case BinExpr("-", IntNum(x), IntNum(y)) => IntNum(x - y)
      case BinExpr("*", IntNum(x), IntNum(y)) => IntNum(x * y)
      case BinExpr("+", ElemList(x), ElemList(y)) => ElemList(x ++ y)
      case BinExpr("+", Tuple(elems1), Tuple(elems2)) => Tuple(elems1 ++ elems2)
      case other => other
    }
  }
}

object TupleSimplifier {
  def apply(node: Tuple) = Tuple(node.list map Simplifier.apply)
}

object WhileInstrSimplifier {
  def apply(node: WhileInstr) = {
    val simplifiedCondition = Simplifier(node.cond)
    if (simplifiedCondition == FalseConst()) {
      Empty()
    } else {
      WhileInstr(simplifiedCondition, node.body)
    }
  }
}

object IfElseExprSimplifier {
  def apply(node: IfElseExpr) = {
    Simplifier(node.cond) match {
      case TrueConst() => Simplifier(node.left)
      case FalseConst() => Simplifier(node.right)
      case other => node
    }
  }
}

object IfElseInstrSimplifier {
  def apply(node: IfElseInstr) = {
    Simplifier(node.cond) match {
      case TrueConst() => Simplifier(node.left)
      case FalseConst() => Simplifier(node.right)
      case other => node
    }
  }
}