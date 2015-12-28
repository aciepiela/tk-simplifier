package simplifier

import java.lang.Math

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
    case node: Subscription => SubscriptionSimplifier(node)
    case node: GetAttr => GetAttrSimplifier(node)
    case node: IfInstr => IfInstrSimplifier(node)
    case node: ReturnInstr => ReturnInstrSimplifier(node)
    case node: PrintInstr => PrintInstrSimplifier(node)
    case node: FunCall => FunCallSimplifier(node)
    case node: FunDef => FunDefSimplifier(node)
    case node: LambdaDef => LambdaDefSimplifier(node)
    case node: ClassDef => ClassDefSimplifier(node)
    case node: ElemList => ElemListSimplifier(node)
    case node: KeyDatum => KeyDatumSimplifier(node)
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

  def nonCommutativeEquals(b1: BinExpr, b2: BinExpr) = b1.left == b2.left && b1.right == b2.right

  def commutativeEquals(b1: BinExpr, b2: BinExpr) = nonCommutativeEquals(b1, b2) || (b1.left == b2.right && b1.right == b2.left)

  def equals(left: BinExpr, right: BinExpr) = {
    if (left.op == right.op && (left.op == "+" || left.op == "*" || left.op == "and" || left.op == "or")) {
      commutativeEquals(left, right)
    } else {
      nonCommutativeEquals(left, right)
    }
  }

  def apply(node: BinExpr) = {
    val simplified = if (node.op == "**") node else BinExpr(node.op, Simplifier(node.left), Simplifier(node.right))
    simplified match {
      case BinExpr("+", x, IntNum(0)) => x
      case BinExpr("+", IntNum(0), x) => x
      case BinExpr("-", x, y) if x == y => IntNum(0)
      case BinExpr("-", BinExpr("+", x, y), z) if x == z => y
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
      case BinExpr("/", x, BinExpr("/", y, z)) if x == y => z
      case BinExpr("*", x, BinExpr("/", IntNum(1), y)) => BinExpr("/", x, y)
      case BinExpr("+", IntNum(x), IntNum(y)) => IntNum(x + y)
      case BinExpr("-", IntNum(x), IntNum(y)) => IntNum(x - y)
      case BinExpr("*", IntNum(x), IntNum(y)) => IntNum(x * y)
      case BinExpr("**", BinExpr("**", x, IntNum(y)), IntNum(z)) => Simplifier(BinExpr("**", x, IntNum(Math.pow(y, z).toInt)))
      case BinExpr("**", BinExpr("**", x, Variable(y)), Variable(z)) => Simplifier(BinExpr("**", x, BinExpr("*", Variable(y), Variable(z))))
      case BinExpr("**", IntNum(x), IntNum(y)) => IntNum(Math.pow(x, y).toInt)
      case BinExpr("**", x, IntNum(0)) => IntNum(1)
      case BinExpr("**", x, IntNum(1)) => x
      case BinExpr("+", ElemList(x), ElemList(y)) => ElemList(x ++ y)
      case BinExpr("+", Tuple(elems1), Tuple(elems2)) => Tuple(elems1 ++ elems2)
      case BinExpr("/", b1: BinExpr, b2: BinExpr) if equals(b1, b2) => IntNum(1)
      case BinExpr("/", b1: BinExpr, b2: BinExpr) if equals(b1, b2) => IntNum(1)
      case BinExpr("and", b1: BinExpr, b2: BinExpr) if equals(b1, b2) => b1
      case BinExpr("or", b1: BinExpr, b2: BinExpr) if equals(b1, b2) => b1
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
      case other => Simplifier(node)
    }
  }
}

object IfElseInstrSimplifier {
  def apply(node: IfElseInstr) = {
    Simplifier(node.cond) match {
      case TrueConst() => Simplifier(node.left)
      case FalseConst() => Simplifier(node.right)
      case other => IfElseInstr(node.cond, Simplifier(node.left), Simplifier(node.right))
    }
  }
}

object SubscriptionSimplifier {
  def apply(node: Subscription) = Subscription(Simplifier(node.expr), Simplifier(node.sub))
}

object GetAttrSimplifier {
  def apply(node: GetAttr) = GetAttr(Simplifier(node.expr), node.attr)
}

object IfInstrSimplifier {
  def apply(node: IfInstr) = IfInstr(Simplifier(node.cond), Simplifier(node.left))
}

object ReturnInstrSimplifier {
  def apply(node: ReturnInstr) = ReturnInstr(Simplifier(node.expr))
}

object PrintInstrSimplifier {
  def apply(node: PrintInstr) = PrintInstr(Simplifier(node.expr))
}

object FunCallSimplifier {
  def apply(node: FunCall) = FunCall(Simplifier(node.name), Simplifier(node.args_list))
}

object FunDefSimplifier {
  def apply(node: FunDef) = FunDef(node.name, Simplifier(node.formal_args), Simplifier(node.body))
}

object LambdaDefSimplifier {
  def apply(node: LambdaDef) = LambdaDef(Simplifier(node.formal_args), Simplifier(node.body))
}

object ClassDefSimplifier {
  def apply(node: ClassDef) = ClassDef(node.name, Simplifier(node.inherit_list), Simplifier(node.suite))
}

object ElemListSimplifier {
  def apply(node: ElemList) = ElemList(node.list map Simplifier.simplify)
}

object KeyDatumSimplifier {
  def apply(node: KeyDatum) = KeyDatum(Simplifier(node.key), Simplifier(node.value))
}