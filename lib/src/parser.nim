import ASTNode
import location
from system import substr
import nodeTypes
import ptlsError
import token
import tokenTypes as Tok
import strutils
import sequtils
import tables

let defSkip = @[Tok.Newline, Tok.Whitespace, Tok.Comment]

proc contains(a: seq[Tok.Tok], b: Tok.Tok) : bool =
  for i in a:
    if i.str == b.str: return true
  return false

type
  Parser* = ref object of RootObj
    index: int
    tokens: seq[Token]

proc createParser*(tokens: seq[Token]) : Parser = return Parser(index: 0, tokens: tokens)

proc hasTokens(this: Parser) : bool = this.index < len(this.tokens)

proc advance(this: Parser) =
  this.index += 1

proc currentToken(this: Parser) : Token =
  return if this.hasTokens(): this.tokens[this.index]
          else: nil

proc wrongToken(this: Parser, expected: seq[Tok.Tok], got: Token) : PtlsError =
  let error = returnPtlsError("Parser Error")
  let expStr = expected.map(proc(x: Tok.Tok) : string = x.str).join(" or ").replace("Tok.", "")
  let gotStr = got.typeStr();
  error.msg = "Expected " & "'" & expStr & "', got " & "'" & gotStr & "'"
  error.locs.add(got.loc)
  return error

proc isNext(this: Parser, testTypes : seq[Tok.Tok], skip: seq[Tok] = defSkip) : bool =
  for token in this.tokens[this.index .. len(this.tokens)-1]:
    if testTypes.contains(token.tokType):
      return true
    if not skip.contains(token.tokType):
      return false
  return false

proc isNextMulti(this: Parser, testTypes : seq[Tok.Tok], skip: seq[Tok] = defSkip) : bool =
  var tokenQueue = testTypes

  for token in this.tokens[this.index .. len(this.tokens)-1]:
    if tokenQueue == @[]:
      return true;

    if (tokenQueue[0] == token.tokType):
      tokenQueue.delete(0)
    elif not skip.contains(token.tokType):
      return false
  return false

proc getNext(this: Parser, testTypes : seq[Tok.Tok], skip: seq[Tok] = defSkip) : Token {.discardable.} =
  while (this.hasTokens()):
    let token = this.currentToken();
    if testTypes.contains(token.tokType):
      this.advance()
      return token

    if not skip.contains(token.tokType):
      raise this.wrongToken(testTypes, token)

    this.advance()

  raise this.wrongToken(testTypes, this.currentToken());

proc peek(this: Parser, testTypes : seq[Tok.Tok], skip: seq[Tok] = defSkip) : Token =
  let oldIndex = this.index
  let token = this.getNext(testTypes, skip)
  this.index = oldIndex
  return token

proc peekAny(this: Parser, skip: seq[Tok] = defSkip) : Token =
  var oldIndex = this.index
  while skip.contains(this.currentToken().tokType):
    this.advance()

  var res = this.currentToken()
  this.index = oldIndex
  return res

proc getSeq(this: Parser, starter : Tok.Tok, ender : Tok.Tok, sep : Tok.Tok, handler : proc(this: Parser): ASTNode, allowTrailSep : bool) : seq[ASTNode] =
  this.getNext(@[starter])
  var res : seq[ASTNode] = @[]

  if this.isNext(@[ender]):
    discard this.getNext(@[ender])
    return res

  res.add(this.handler())

  while not this.isNext(@[ender]):
    this.getNext(@[sep])

    if allowTrailSep and this.isNext(@[ender]):
      break

    res.add(this.handler())
  this.getNext(@[ender])
  return res

# Declaration of All functions in the parser
proc getName(this: Parser) : ASTNode
proc getString(this: Parser) : ASTNode
proc getNumber(this: Parser) : ASTNode
proc getBool(this: Parser) : ASTNode
proc getLabel(this: Parser) : ASTNode
proc getList(this: Parser) : ASTNode
proc getArray1D(this: Parser) : ASTNode
proc getArray2D(this: Parser) : ASTNode
proc getParenElements(this: Parser, handler: proc(this: Parser) : ASTNode) : seq[ASTNode]
proc getTuple(this: Parser) : ASTNode
proc getTupleName(this: Parser) : ASTNode
proc getDefLHS(this: Parser) : ASTNode
proc getNameDef(this: Parser) : ASTNode
proc getFuncDef(this: Parser) : ASTNode
proc getDef(this: Parser) : ASTNode
proc getObject(this: Parser) : ASTNode
proc getPair(this: Parser) : ASTNode
proc getDict(this: Parser) : ASTNode
proc getSet(this: Parser) : ASTNode
proc getArrayLiteral(this: Parser) : ASTNode
proc getParenLiteral(this: Parser) : ASTNode
proc getBracketLiteral(this: Parser) : ASTNode
proc getUnitBase(this: Parser) : ASTNode
proc getIndex(this: Parser, lhs: ASTNode) : ASTNode
proc getCall(this: Parser, fun: ASTNode) : ASTNode
proc getBinaryOp(this: Parser, precedence: int) : ASTNode
proc getFieldRef(this: Parser, lhs: ASTNode) : ASTNode
proc getOperation(this: Parser) : ASTNode
proc getConditional(this: Parser) : ASTNode
proc getCases(this: Parser) : ASTNode
proc getCond(this: Parser) : ASTNode
proc getFor(this: Parser) : ASTNode
proc getWhen(this: Parser) : ASTNode
proc getListComp(this: Parser) : ASTNode
proc isLambda(this: Parser) : bool
proc getLambda(this: Parser) : ASTNode
proc getTry(this: Parser) : ASTNode
proc getThrow(this: Parser) : ASTNode
proc getExpression(this: Parser) : ASTNode
proc getClause(this: Parser) : ASTNode

# Parser Shall begin
proc getName(this: Parser) : ASTNode =
  let token = this.getNext(@[Tok.Name]);
  return ASTNode(NodeType: Node.Name, location: token.loc, identifier: token.value)

proc getString(this: Parser) : ASTNode =
  let token = this.getNext(@[Tok.String])
  let str = token.value.unescape().replace("\\n", "\n")
  return ASTNode(NodeType: Node.String, location: token.loc, strValue: str)

proc getNumber(this: Parser) : ASTNode =
  let token = this.getNext(@[Tok.Number])
  let num = token.value.parseFloat()
  return ASTNode(NodeType: Node.Number, location: token.loc, numValue: num)

proc getBool(this: Parser) : ASTNode =
  let token = this.getNext(@[Tok.Bool])
  let boolean = token.value == "true"
  return ASTNode(NodeType: Node.Bool, location: token.loc, boolValue: boolean)


proc getLabel(this: Parser) : ASTNode =
  let token = this.getNext(@[Tok.Label]);
  let label = ASTNode(NodeType: Node.Label, location: token.loc, labelValue: token.value)

  if this.isNext(@[Tok.LParen]):
    let tup = this.getTuple()
    let field = ASTNode(NodeType: Node.Name, location: token.loc, identifier: "!getWrapTuple")
    let reference = ASTNode(NodeType: Node.FieldRef, location: token.loc, label: label, field: field)
    return ASTNode(NodeType: Node.Call, location: token.loc, reference: reference, refered: @[tup])

  if this.isNext(@[Tok.LBracket]):
    let obj = this.getObject()
    let field = ASTNode(NodeType: Node.Name, location: token.loc, identifier: "!getWrapObject")
    let reference = ASTNode(NodeType: Node.FieldRef, location: token.loc, label: label, field: field)
    return ASTNode(NodeType: Node.Call, location: token.loc, reference: reference, refered: @[obj])

  return label

proc getList(this: Parser) : ASTNode =
  let loc = this.peek(@[Tok.LArray]).loc;
  let elems = this.getSeq(Tok.LArray, Tok.RArray, Tok.Comma, getClause, true);
  return ASTNode(NodeType: Node.List, location: loc, list_elems: elems)

proc getArray1D(this: Parser) : ASTNode =
  let loc = this.peek(@[Tok.LArray]).loc;
  let elems = this.getSeq(Tok.LArray, Tok.RArray, Tok.Whitespace, getOperation, true)
  return ASTNode(NodeType: Node.Array, location: loc, array_elems: elems)

proc getArray2D(this: Parser) : ASTNode =
  var elems = @[this.getArray1D()]
  let skip = @[Tok.Whitespace, Tok.Comment];

  while this.isNextMulti(@[Tok.Newline, Tok.LArray], skip):
    elems.add(this.getArray1D())

  if (len(elems) == 1):
    return elems[0]

  return ASTNode(NodeType: Node.Array, location: elems[0].location, array_elems: elems)

proc getParenElements(this: Parser, handler: proc(this: Parser) : ASTNode) : seq[ASTNode] =
  let loc = this.peek(@[Tok.LParen]).loc;
  let elems = this.getSeq(Tok.LParen, Tok.RParen, Tok.Comma, handler, false);

  if elems == @[]:
    var error = returnPtlsError("Parser Error")
    error.msg = "Construct requires 1 or more arguments or elements"
    error.locs.add(loc)
    raise error

  return elems

proc getTuple(this: Parser) : ASTNode =
  let loc = this.peek(@[Tok.LParen]).loc
  let elems = this.getParenElements(getClause)
  return ASTNode(NodeType: Node.Tuple, location: loc, tuple_elems: elems)

proc getTupleName(this: Parser) : ASTNode =
  if this.isNext(@[Tok.Blank]):
    let token = this.getNext(@[Tok.Blank])
    return ASTNode(NodeType: Node.Blank, location: token.loc, blank_nullary: true)

  return this.getName()

proc getDefLHS(this: Parser) : ASTNode =
  if this.isNext(@[Tok.LParen]):
    let loc = this.peek(@[Tok.LParen]).loc
    let elems = this.getParenElements(getTupleName)
    return ASTNode(NodeType: Node.Tuple, location: loc, tuple_elems: elems)

  return this.getName()

proc getNameDef(this: Parser) : ASTNode =
  let lhs = this.getDefLHS();
  discard this.getNext(@[Tok.Assign]);
  let rhs = this.getClause();

  return ASTNode(NodeType: Node.Def, location: lhs.location, lhs: lhs, rhs: rhs)

proc getFuncDef(this: Parser) : ASTNode =
  let name = this.getName()
  let params = this.getParenElements(getName)

  discard this.getNext(@[Tok.Assign])

  let body = this.getClause()

  let function = ASTNode(NodeType: Node.Func, location: name.location, func_params: params, fun_body: body)
  return ASTNode(NodeType: Node.Def, location: name.location, lhs: name, rhs: function)

proc getDef(this: Parser) : ASTNode =
  if this.isNextMulti(@[Tok.Name, Tok.LParen]):
    return this.getFuncDef()

  return this.getNameDef()

proc getObject(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.LBracket]).loc;

  var defs: seq[ASTNode] = @[];
  while not this.isNext(@[Tok.RBracket]):
    defs.add(this.getDef())

    if this.isNext(@[Tok.RBracket]):
      break

    discard this.getNext(@[Tok.Newline, Tok.Semicolon])

  this.getNext(@[Tok.RBracket]);
  return ASTNode(NodeType: Node.Object, location: loc, obj_defs: defs);

proc getPair(this: Parser) : ASTNode =
  let key = this.getClause()
  this.getNext(@[Tok.Colon])
  let val = this.getClause()

  return ASTNode(NodeType: Node.Pair, location: key.location, key: key, val: val);

proc getDict(this: Parser) : ASTNode =
  let loc = this.peek(@[Tok.LBracket]).loc
  let elems = this.getSeq(Tok.LBracket, Tok.RBracket, Tok.Comma, getPair, true)
  return ASTNode(NodeType: Node.Dict, location: loc, dict_elems: elems)

proc getSet(this: Parser) : ASTNode =
  let loc = this.peek(@[Tok.LBracket]).loc
  let elems = this.getSeq(Tok.LBracket, Tok.RBracket, Tok.Comma, getClause, true)
  return ASTNode(NodeType: Node.Set, location: loc, set_elems: elems)

proc getArrayLiteral(this: Parser) : ASTNode =
  if this.isNextMulti(@[Tok.LArray, Tok.RArray]):
    return this.getList()
  let oldIndex = this.index
  discard this.getNext(@[Tok.LArray])
  discard this.getClause()
  if this.isNext(@[Tok.Comma, Tok.RArray]):
    this.index = oldIndex;
    return this.getList();
  this.index = oldIndex
  return this.getArray2D()

proc getParenLiteral(this: Parser) : ASTNode =
  let oldIndex = this.index
  discard this.getNext(@[Tok.LParen])
  let clause = this.getClause()

  if this.isNext(@[Tok.RParen]):
    this.getNext(@[Tok.RParen])
    return clause

  this.index = oldIndex;
  return this.getTuple();

proc getBracketLiteral(this: Parser) : ASTNode =
  if this.isNextMulti(@[Tok.LBracket, Tok.RBracket]):
    return this.getDict()

  let oldIndex = this.index
  discard this.getNext(@[Tok.LBracket]);
  discard this.getClause();

  if this.isNext(@[Tok.Assign]):
    this.index = oldIndex;
    return this.getObject();

  if this.isNext(@[Tok.Colon]):
    this.index = oldIndex
    return this.getDict()

  this.index = oldIndex
  return this.getSet()

proc getUnitBase(this: Parser) : ASTNode =
  let unitTokens = @[
    Tok.Number, Tok.String, Tok.Name, Tok.Label, Tok.Bool,
    Tok.LArray, Tok.LParen, Tok.LBracket
  ]

  let peekTok = this.peek(unitTokens).tokType.str

  if peekTok == Tok.Number.str: return this.getNumber()
  elif peekTok == Tok.String.str: return this.getString()
  elif peekTok == Tok.Name.str: return this.getName()
  elif peekTok == Tok.Label.str: return this.getLabel()
  elif peekTok == Tok.Bool.str: return this.getBool()
  elif peekTok == Tok.LArray.str: return this.getArrayLiteral()
  elif peekTok == Tok.LParen.str: return this.getParenLiteral()
  elif peekTok == Tok.LBracket.str: return this.getBracketLiteral()
  else: raise newException(Exception, "Gods among us must have done something incompetent")

proc getIndex(this: Parser, lhs: ASTNode) : ASTNode =
  let loc = this.getNext(@[Tok.LArray]).loc;
  let rhs = this.getClause()
  this.getNext(@[Tok.RArray])
  return ASTNode(NodeType: Node.Index, location: loc, index_lhs: lhs, index_rhs: rhs);

proc getFieldRef(this: Parser, lhs: ASTNode) : ASTNode =
  let token = this.getNext(@[Tok.Field])
  let nameChars = token.value.substr(1, len(token.value)-1);
  let nameNode = ASTNode(NodeType: Node.Name, location: token.loc, identifier: nameChars);
  return ASTNode(NodeType: Node.FieldRef, location: token.loc, label: lhs, field: nameNode);

proc getCall(this: Parser, fun: ASTNode) : ASTNode =
  let loc = this.peek(@[Tok.LParen]).loc
  let args = this.getParenElements(getClause)
  return ASTNode(NodeType: Node.Call, location: loc, reference: fun, refered: args)

proc getUnit(this: Parser) : ASTNode =
  let extTokens = @[
    Tok.LArray, Tok.LParen, Tok.Field
  ]

  var lhs = this.getUnitBase()

  while (this.isNext(@[Tok.LArray, Tok.LParen], @[]) or this.isNext(@[Tok.Field])):
    let toks = this.peek(extTokens).tokType.str
    if toks == Tok.LArray.str:
        lhs = this.getIndex(lhs)
    elif toks == Tok.Field.str:
      lhs = this.getFieldRef(lhs)
    elif toks == Tok.LParen.str:
      lhs = this.getCall(lhs)
    else:
      raise newException(Exception, "Gods among us must have done something incompetent")

  return lhs

proc getPrefixOp(this: Parser) : ASTNode =
  if this.isNext(@[Tok.Neg, Tok.Not]):
    let token = this.getNext(@[Tok.Neg, Tok.Not]);
    let rhs = this.getPrefixOp();
    return ASTNode(NodeType: Node.UnaryOp, location: token.loc, op: token.tokType, unary_node: rhs);
  return this.getUnit()

proc getBinaryOp(this: Parser, precedence: int) : ASTNode =
  var opEntries = [
    (true,  @[Tok.Pipe]),
    (false, @[Tok.Concat]),
    (true,  @[Tok.Or]),
    (true,  @[Tok.And]),
    (true,  @[Tok.Equals, Tok.NotEq]),
    (true,  @[Tok.In]),
    (true,  @[Tok.LessThan, Tok.LessEq, Tok.GreaterThan, Tok.GreaterEq]),
    (true,  @[Tok.Add, Tok.Sub]),
    (true,  @[Tok.Mul, Tok.Div, Tok.Mod]),
    (false, @[Tok.Pow]),
  ]

  if precedence == len(opEntries):
    return this.getPrefixOp()

  var lhs = this.getBinaryOp(precedence + 1);
  let opEntry = opEntries[precedence];

  while this.isNext(opEntry[1]):
    let increment = if opEntry[0]: 1
                    else: 0

    let token = this.getNext(opEntry[1])
    let rhs = this.getBinaryOp(precedence + increment)
    if token.tokType == Tok.Pipe:
      let args = @[lhs]
      lhs = ASTNode(NodeType: Node.Call, location: token.loc, reference: rhs, refered: args)
    else:
      lhs = ASTNode(NodeType: Node.BinaryOp, location: token.loc, binary_op: token.tokType, bin_rhs: rhs, bin_lhs: lhs)

  return lhs

proc getOperation(this: Parser) : ASTNode =
  return this.getBinaryOp(0)

proc getConditional(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.If]).loc
  let cond = this.getExpression()

  this.getNext(@[Tok.Then])
  let thenClause = this.getClause()

  this.getNext(@[Tok.Else]);
  let elseExpr = this.getExpression();

  return ASTNode(NodeType: Node.Conditional, location: loc, ifClause: cond, thenExpr: thenClause, elseExpr: elseExpr)

proc getCases(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.Case]).loc;
  let cond = this.getExpression();
  let thenClause = this.getClause();

  var elseClause: ASTNode
  if this.isNext(@[Tok.Else]):
    this.getNext(@[Tok.Else]);
    elseClause = this.getClause();
  elif this.isNext(@[Tok.RBracket]):
      elseClause = nil;
  else:
    elseClause = this.getCases();

  return ASTNode(NodeType: Node.Conditional, location: loc, ifClause: cond, thenExpr: thenClause, elseExpr: elseClause)

proc getCond(this: Parser) : ASTNode =
  this.getNext(@[Tok.Cond])
  this.getNext(@[Tok.LBracket])
  let res = this.getCases()
  this.getNext(@[Tok.RBracket])
  return res

proc getFor(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.For]).loc
  let variable = this.getDefLHS()

  this.getNext(@[Tok.In])
  let iterable = this.getExpression()
  let res = this.getListComp()

  let params = @[variable]
  let fun = ASTNode(NodeType: Node.Func, location: loc, func_params: params, fun_body: res);
  let args = @[fun, iterable];

  let concatMap = ASTNode(NodeType: Node.Name, location: loc, identifier: "concatMap")
  return ASTNode(NodeType: Node.Call, location: loc, reference: concatMap, refered: args)

proc getWhen(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.When]).loc;
  let cond = this.getExpression();
  let res = this.getListComp();

  var elems : seq[ASTNode] = @[]
  let empty = ASTNode(NodeType: Node.List, location: loc, list_elems: elems)

  return ASTNode(NodeType: Node.Conditional, location: loc, ifClause: cond, thenExpr: res, elseExpr: empty);

proc getYield(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.Yield]).loc;
  let res = @[this.getExpression()];

  return ASTNode(NodeType: Node.List, location: loc, list_elems: res);

proc getListComp(this: Parser) : ASTNode =
  if this.isNext(@[Tok.For]):
    return this.getFor()
  elif this.isNext(@[Tok.When]):
    return this.getWhen();

  return this.getYield();

proc isLambda(this: Parser) : bool =
  if this.isNextMulti(@[Tok.Name, Tok.Lambda]) or this.isNextMulti(@[Tok.Blank, Tok.Lambda]):
    return true

  if not this.isNextMulti(@[Tok.LParen, Tok.Name]) and not this.isNextMulti(@[Tok.LParen, Tok.Blank]):
      return false

  let oldIndex = this.index
  this.getNext(@[Tok.LParen]);
  this.getNext(@[Tok.Name, Tok.Blank]);

  while this.isNextMulti(@[Tok.Comma, Tok.Name]) or this.isNextMulti(@[Tok.Comma, Tok.Blank]):
    this.getNext(@[Tok.Comma]);
    this.getNext(@[Tok.Name, Tok.Blank]);

  let res = this.isNextMulti(@[Tok.RParen, Tok.Lambda]);

  this.index = oldIndex;
  return res

proc getLambda(this: Parser) : ASTNode =
  var params : seq[ASTNode]

  if this.isNext(@[Tok.LParen]):
    params = this.getParenElements(getName)
  else:
    params = @[this.getName()]

  let loc = this.getNext(@[Tok.Lambda]).loc;
  let body = this.getClause()

  return ASTNode(NodeType: Node.Func, location: loc, func_params: params, fun_body: body)

proc getTry(this: Parser) : ASTNode =
  var loc = this.getNext(@[Tok.Try]).loc
  var body = this.getClause()

  this.getNext(@[Tok.Catch])
  var condition = this.getExpression()
  var handler = this.getExpression()

  return ASTNode(NodeType: Node.Try, location: loc, trial_body: body, catch_condition: condition, handler: handler)

proc getThrow(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.Throw]).loc
  let err = this.getExpression()

  return ASTNode(NodeType: Node.Throw, location: loc, thrown_error: err);

proc getExpression(this: Parser) : ASTNode =
  if this.isNext(@[Tok.If]):
    return this.getConditional()
  elif this.isNext(@[Tok.Throw]):
    return this.getThrow()
  elif this.isNext(@[Tok.Try]):
    return this.getTry()
  elif this.isNext(@[Tok.Cond]):
    return this.getCond()
  elif this.isNext(@[Tok.For]):
    return this.getListComp()
  elif this.isLambda():
    return this.getLambda()

  return this.getOperation();

proc getWhere(this: Parser, body: ASTNode) : ASTNode =
  var loc = this.getNext(@[Tok.Where]).loc

  var obj : ASTNode
  if this.isNext(@[Tok.LBracket]):
    obj = this.getObject()
  else:
    let def = this.getDef()
    obj = ASTNode(NodeType: Node.Object, location: def.location, obj_defs: @[def])

  return ASTNode(NodeType: Node.Where, location: loc, where_body: body, where_clause: obj)

proc checkNotBuiltIn(this: Parser, fieldName: string, loc: Location) =
  if fieldName[0] == '!':
    var error = returnPtlsError("Parser Error")
    error.msg = "Cannot create special field '" & $fieldName & "'";
    error.locs.add(loc)
    raise error

proc getDefinable(this: Parser, lhs: ASTNode) : ASTNode =
  let rhsTokens = @[Tok.Field, Tok.LArray]
  discard this.peek(rhsTokens)
  var new_lhs = lhs

  while (this.isNext(rhsTokens)):
    if (this.isNext(@[Tok.LArray])):
      new_lhs = this.getIndex(new_lhs);
    elif (this.isNext(@[Tok.Field])):
      new_lhs = this.getFieldRef(new_lhs)
      let nameNode = new_lhs.field
      this.checkNotBuiltIn(nameNode.identifier, new_lhs.location)

  return new_lhs

proc getWithDef(this: Parser) : ASTNode =
  let compoundToks = {
    Tok.AddAssign: Tok.Add,
    Tok.SubAssign: Tok.Sub,
    Tok.MulAssign: Tok.Mul,
    Tok.DivAssign: Tok.Div,
    Tok.PowAssign: Tok.Pow,
    Tok.ModAssign: Tok.Mod,
  }.toTable()

  let loc = this.getNext(@[Tok.Dollar]).loc;
  let dollar = ASTNode(NodeType: Node.Name, location: loc, identifier: "$");

  let lhs = this.getDefinable(dollar);
  var assign_toks = @[Tok.Assign]
  for key, _ in compoundToks:
    assign_toks.add(key)
  var opToken = this.getNext(assign_toks)
  var rhs = this.getClause();
  if opToken.tokType != Tok.Assign:
    let opType = compoundToks[opToken.tokType]
    rhs = ASTNode(NodeType: Node.BinaryOp, location: opToken.loc, binary_op: opType, bin_lhs: lhs, bin_rhs: rhs)

  return ASTNode(NodeType: Node.Def, location: lhs.location, lhs: lhs, rhs: rhs)

iterator getWithDefs(this: Parser) : ASTNode =
  this.getNext(@[Tok.LBracket])
  while not this.isNext(@[Tok.RBracket]):
    yield this.getWithDef()

    if this.isNext(@[Tok.RBracket]):
      break

    this.getNext(@[Tok.Newline, Tok.Semicolon])

  this.getNext(@[Tok.RBracket])

proc getWith(this: Parser, lhs: ASTNode) : ASTNode =
  var loc = this.getNext(@[Tok.With]).loc;

  var defs : seq[ASTNode] = @[]
  if this.isNext(@[Tok.LBracket]):
    for def in this.getWithDefs():
      defs.add(def)
  else:
    defs = @[this.getWithDef()]

  return ASTNode(NodeType: Node.With, location: loc, with_body: lhs, with_defs: defs)

proc getRequires(this: Parser, lhs: ASTNode) : ASTNode =
  let loc = this.getNext(@[Tok.Requires]).loc
  let condition = this.getOperation()
  return ASTNode(NodeType: Node.Requires, location: loc, required: lhs, requirement: condition)

proc getClause(this: Parser) : ASTNode =
  var res = this.getExpression();
  let clauseTokens = @[Tok.Where, Tok.Requires, Tok.With];


  while this.isNext(clauseTokens):
    let current_tok = this.peek(clauseTokens).tokType.str
    if current_tok == Tok.Where.str:
        res = this.getWhere(res);
    elif current_tok == Tok.Requires.str:
      res = this.getRequires(res)
    elif current_tok == Tok.With.str:
      res = this.getWith(res)
    else:
      raise newException(Exception, "Gods among us must have done something incompetent")

  return res

proc getExport(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.Export]).loc
  let names = this.getSeq(Tok.LBracket, Tok.RBracket, Tok.Comma, getName, true)
  return ASTNode(NodeType: Node.Export, location: loc, exports: names)

proc getImport(this: Parser) : ASTNode =
  let loc = this.getNext(@[Tok.Import]).loc
  let path = this.getString()

  this.getNext(@[Tok.As]);
  return ASTNode(NodeType: Node.Import, location: loc, path: path, as_node: this.getName());

proc getProgram(this: Parser) : ASTNode =
  let loc = this.currentToken().loc;

  var exprt : ASTNode = nil
  if this.isNext(@[Tok.Export]):
    exprt = this.getExport()

  var imports : seq[ASTNode] = @[]
  while this.isNext(@[Tok.Import]):
    imports.add(this.getImport())

  var defs: seq[ASTNode] = @[]
  while not this.isNext(@[Tok.EOF]):
    defs.add(this.getDef())

    if this.isNext(@[Tok.EOF]):
      break

    this.getNext(@[Tok.Newline, Tok.Semicolon])

  this.getNext(@[Tok.EOF])
  return ASTNode(NodeType: Node.Program, location: loc, export_name: exprt, imports: imports, defs: defs)


proc makeast*(tokens : seq[Token]) : ASTNode =
  var ast : ASTNode
  try:
    ast = createParser(tokens).getProgram()
  except PtlsError as err:
    echo err.locs.deduplicate.join("\n")
    raise
  return ast
