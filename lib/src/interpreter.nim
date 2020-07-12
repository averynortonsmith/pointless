from os import existsFile, commandLineParams
import location
import ASTNode
import tables
import nodeTypes
from tokenTypes as Tok import nil
import ptlsError
import strutils
import sequtils
import hashes
import math
import tokenizer
import parser
from random import nil

random.randomize()

type
  ValueTypes* = enum
    ptlsArray
    ptlsBool
    ptlsBuiltIn
    ptlsDict
    ptlsFunc
    ptlsLabel
    ptlsList
    ptlsNumber
    ptlsObject
    ptlsSet
    ptlsString
    ptlsTuple

type
  Thunk* = ref object of RootObj
    name: string
    fun: proc(): ptlsValue
    value: ptlsValue
    index: int
    lock: bool

  Env* = ref object of RootObj
    parent: Env
    prelude: Env
    globals: Env
    defs: tables.Table[string, Thunk]

  ptlsValue* = ref object of RootObj
    loc*: Location
    case ValueType: ValueTypes
      of ptlsArray: array_elems*: seq[ptlsValue]
      of ptlsBuiltIn:
        signature: string
        fun: proc(x: ptlsValue): ptlsValue
      of ptlsBool: boolValue*: bool
      of ptlsDict: dictValue*: tables.Table[ptlsValue, ptlsValue]
      of ptlsFunc:
        scope*: Env
        params*: seq[string]
        fun_body*: ASTNode
      of ptlsLabel: labelValue*: string
      of ptlsList:
        headThunk*: Thunk
        tailThunk*: Thunk
      of ptlsNumber: numValue*: float
      of ptlsSet: setValue*: tables.Table[ptlsValue, ptlsValue]
      of ptlsString: strValue*: string
      of ptlsObject:
        label*: ptlsValue
        objEnv*: Env
      of ptlsTuple:
        tupleLabel*: ptlsValue
        tupleValue*: seq[ptlsValue]

  ptlsException = ref object of ValueError
    exceptValue*: ptlsValue
    exceptLoc*: Location

  RuntimeValueNode = ref object of ASTNode
    value: ptlsValue

# PtlsValue Constructors
proc `$`*(this: ptlsValue): string
proc createPtlsArray(loc: Location, elems: seq[ptlsValue]) : ptlsValue = ptlsValue(ValueType: ptlsArray, loc: loc, array_elems: elems)
proc createPtlsBuiltIn(loc: Location, signature: string, fun: proc(this: ptlsValue): ptlsValue) : ptlsValue =
  return ptlsValue(ValueType: ptlsBuiltIn, loc: loc, signature: signature, fun: fun)
proc createPtlsBool(loc: Location, value: bool) : ptlsValue = ptlsValue(ValueType: ptlsBool, loc: loc, boolValue: value)
proc createPtlsException(exceptValue: ptlsValue, exceptLoc: Location) : ptlsException =
  let ret_error = ptlsException(exceptValue: exceptValue, exceptLoc: exceptLoc)
  ret_error.msg = "Unhandled Exception: " & $exceptValue
  return ret_error
proc createPtlsDict(loc: Location, value: tables.Table[ptlsValue, ptlsValue]) : ptlsValue = ptlsValue(ValueType: ptlsDict, loc: loc, dictValue: value)
proc createPtlsFunc(loc: Location, scope: Env, params: seq[string], body: ASTNode) : ptlsValue =
  return ptlsValue(ValueType: ptlsFunc, loc: loc, scope: scope, params: params, fun_body: body)
proc createPtlsLabel(loc: Location, value: string) : ptlsValue = ptlsValue(ValueType: ptlsLabel, loc: loc, labelValue: value)
proc createPtlsList(loc: Location, head: Thunk, tail: Thunk) : ptlsValue = ptlsValue(ValueType: ptlsList, loc: loc, headThunk: head, tailThunk: tail)
proc createPtlsNumber(loc: Location, value: float) : ptlsValue = ptlsValue(ValueType: ptlsNumber, loc: loc, numValue: value)
proc createPtlsSet(loc: Location, value: tables.Table[ptlsValue, ptlsValue]) : ptlsValue = ptlsValue(ValueType: ptlsSet, loc: loc, setValue: value)
proc createPtlsString(loc: Location, value: string) : ptlsValue = ptlsValue(ValueType: ptlsString, loc: loc, strValue: value)
proc createPtlsObject(loc: Location, env: Env, label: ptlsValue = nil) : ptlsValue =
  if label == nil:
     return ptlsValue(ValueType: ptlsObject, loc: loc, objEnv: env, label: createPtlsLabel(loc, "PtlsObject"))
  if label.ValueType != ptlsLabel:
    raise newException(ValueError, "This ain't a label")
  return ptlsValue(ValueType: ptlsObject, loc: loc, objEnv: env, label: label)
proc createPtlsTuple(loc: Location, value: seq[ptlsValue], label: ptlsValue = nil) : ptlsValue =
  if isNil(label):
     return ptlsValue(ValueType: ptlsTuple, loc: loc, tupleValue: value, tupleLabel: createPtlsLabel(loc, "PtlsTuple"))
  if label.ValueType != ptlsLabel:
    raise newException(ValueError, "This ain't a label")
  return ptlsValue(ValueType: ptlsTuple, loc: loc, tupleValue: value, tupleLabel: label)


# Forward Declarations
# -----------------------
proc eval(env: Env, node: ASTNode): ptlsValue
proc evalCheck(env: Env, node: ASTNode, types: seq[ValueTypes]): ptlsValue
proc checkLength(this: ptlsValue, length: int): ptlsValue
proc getMember(this: ptlsValue, index: int): ptlsValue
proc checkIsList(this: ptlsValue): ptlsValue
proc checkIndex(this: ptlsValue, index: float): int
proc PtlsListFromValues(values: seq[ptlsValue]): ptlsValue
proc checkType(this: ptlsValue, types: seq[ValueTypes]) : ptlsValue {.discardable.}
proc head(this: ptlsValue): ptlsValue
proc tail(this: ptlsValue): ptlsValue
proc toList(this: ptlsValue) : seq[ptlsValue]
proc concat(this: ptlsValue, env: Env, rhsNode: ASTNode) : ptlsValue
proc dispatch(immut_env: Env, immut_node: ASTNode, immut_traceLocs: seq[Location]) : ptlsValue

# Thunk Methods
# -----------------------
proc createThunk(name: string, fun: proc(): ptlsValue): Thunk = Thunk(name: name, fun: fun, lock: false)

proc thunkFromValue(name: string, value: ptlsValue): Thunk =
  let thunk = createThunk(name, nil)
  thunk.value = value
  return thunk

proc checkLoc(this: Thunk) =
  if this.lock:
    let error = returnPtlsError("Name Error")
    error.msg = "Circular definition for name '" & this.name & "'"
    raise error

proc getValue(this: Thunk): ptlsValue =
  if isNil(this.value):
    this.checkLoc()
    this.lock = true
    this.value = this.fun()
    this.lock = false
  return this.value

proc `$`*(this: Thunk): string =
  if isNil(this.fun):
    echo "WTF"
  else:
    echo this.fun()
  return if isNil(this.value): "?"
         else: $this.value

# Environment Methods
# --------------------------
proc createEnv(parent: Env = nil) : Env =
  var env = Env(parent: parent)
  let prelude = if isNil(parent): env
                elif isNil(parent.prelude): env
                else: parent.prelude
  let globals = if isNil(parent): env
                elif isNil(parent.globals): env
                else: parent.globals
  env.prelude = prelude
  env.globals = globals
  return env

proc spawn(this: Env) : Env = createEnv(this)

proc clone(this: Env) : Env =
  let copyEnv = createEnv(this.parent)
  for key, value in this.defs:
    copyEnv.defs[key] = value
  return copyEnv

proc addDefThunk(this: Env, thunk: Thunk) =
  if this.defs.hasKey(thunk.name):
    let error = returnPtlsError("Name Error");
    error.msg = "Duplicate definition for name '" & thunk.name & "'"
    raise error;

  this.defs[thunk.name] = thunk
  thunk.index = len(this.defs)

proc addDefName(this: Env, name: string, rhs: ASTNode) =
  let thunk = createThunk(name, proc(): ptlsValue = eval(this, rhs))
  this.addDefThunk(thunk)

proc addDefTuple(this: Env, members: seq[ASTNode], rhs: ASTNode) =
  proc fun() : ptlsValue =
    let tup = evalCheck(this, rhs, @[ptlsTuple])
    return tup.checkLength(len(members))

  let tupleThunk = createThunk("", fun);
  var index = 0

  for memberNode in members:
    if (memberNode.NodeType == Node.Blank):
      index += 1
      continue

    let node_name = memberNode.identifier

    let ind = index;
    var new_fun = proc(): ptlsValue = tupleThunk.getValue().getMember(ind)
    var thunk = createThunk(node_name, new_fun)

    this.addDefThunk(thunk)
    index += 1

proc addDef(this: Env, defNode: ASTNode) =
  let lhs = defNode.lhs
  let rhs = defNode.rhs

  if lhs.NodeType == Node.Name:
    this.addDefName(lhs.identifier, rhs)
    return

  if lhs.NodeType == Node.Tuple:
    this.addDefTuple(lhs.tuple_elems, rhs)
    return

  raise newException(ValueError, "Ummm... What?")

proc lookupName(this: Env, name: string) : ptlsValue =
  var searchEnv = this

  while searchEnv != nil:
    if searchEnv.defs.hasKey(name):
      return searchEnv.defs[name].getValue()

    searchEnv = searchEnv.parent

  let error = returnPtlsError("Name Error");
  error.msg = "No definition for name '" & name & "'"
  raise error


iterator eagerList(this: ptlsValue) : ptlsValue =
  var output = this.checkIsList()
  while output.ValueType == ptlsList:
    try:
      yield output.checkIsList().head
      output = output.checkIsList().tail
    except ptlsException as exception:
      let error = returnPtlsError("Exception Error")
      error.msg = "Unhandled exception : " & $exception.exceptValue
      raise error


iterator getOutput(this: Env): ptlsValue =
  if not this.defs.hasKey("output"):
    let error = returnPtlsError("Name Error")
    error.msg = "Source root missing 'output' definition"
    raise error

  var output: ptlsValue
  try:
    output = this.lookupName("output").checkIsList()
  except ptlsException as exception:
    let error = returnPtlsError("Exception Error")
    error.msg = "Unhandled exception : " & $exception.exceptValue
    raise error

  for i in output.eagerList():
    yield i

# Value Methods
# ----------------
proc `$`*(this: ptlsValue): string =
  if this.ValueType == ptlsArray:
    return "[" & this.array_elems.join(" ") & "]"
  elif this.ValueType == ptlsBuiltIn:
    return "PtlsBuiltIn(" & this.signature & ")"
  elif this.ValueType == ptlsBool:
    return $this.boolValue
  elif this.ValueType == ptlsDict:
    return $this.dictValue
  elif this.ValueType == ptlsFunc:
    let partParams = this.params.join(", ")
    let newParams = this.params[len(this.scope.defs) .. len(this.params)-1].join(", ")
    if partParams == @[]:
      return "PtlsFunc(" & $newParams & ")"
    else:
      return "PtlsFunc(" & $partParams & ")(" & $newParams & ")"
  elif this.ValueType == ptlsLabel:
    return $this.labelValue
  elif this.ValueType == ptlsList:
    var list = this
    var memberStrs : seq[string] = @[]
    while (list is ptlsValue) and (list != nil) and (list.ValueType == ptlsList):
      memberStrs.add(if list.headThunk.value == nil: "?"
                     else: $list.headThunk.value)
      list = list.tailThunk.value
    if list == nil:
      memberStrs.add("...")
    return "[" & $memberStrs.join(", ") & "]"
  elif this.ValueType == ptlsNumber:
    return $this.numValue
  elif this.ValueType == ptlsObject:
    if this.label.labelValue == "PtlsObject":
      return $this.objEnv.defs
    return $this.label & " " & $this.objEnv.defs
  elif this.ValueType == ptlsSet:
    var keys : seq[ptlsValue] = @[]
    for key in this.setValue.keys:
      keys.add(key)
    return "{" & keys.join(", ") & "}"
  elif this.ValueType == ptlsString:
    return this.strValue
  elif this.ValueType == ptlsTuple:
    return this.tupleLabel.labelValue & "(" & this.tupleValue.join(", ") & ")"
  return "?"

proc hash*(this: ptlsValue): int =
  if this.ValueType == ptlsNumber:
    return hash(this.numValue)
  elif this.ValueType == ptlsBool:
    return hash(this.boolValue)
  elif this.ValueType == ptlsLabel:
    return hash(this.labelValue)
  elif this.ValueType == ptlsNumber:
    return hash(this.numValue)
  elif this.ValueType == ptlsString:
    return hash(this.strValue)
  elif this.ValueType == ptlsTuple:
    var res = 0
    for value in this.tupleValue:
      res += hash(value)
      res *= 7
    return res
  let error = returnptlsError("Type Error")
  error.msg = "Cannot hash '" & $this.ValueType & "'"
  raise error

proc `==`*(this: ptlsValue, other: ptlsValue): bool

proc `==`*(this: ptlsValue, other: ptlsValue): bool =
  if this.ValueType == ptlsArray and other.ValueType == ptlsArray:
    return this.array_elems == other.array_elems
  if this.ValueType == ptlsBool and other.ValueType == ptlsBool:
    return this.boolValue == other.boolValue
  elif this.ValueType == ptlsDict and other.ValueType == ptlsDict:
    if len(this.dictValue) != len(this.dictValue): return false
    for key, value in this.dictValue:
      if other.dictValue.hasKey(key):
        return value == other.dictValue[key]
      else:
        return false
    return false
  elif this.ValueType == ptlsFunc and other.ValueType == ptlsFunc:
    return this.params == other.params and other.fun_body == this.fun_body
  elif this.ValueType == ptlsLabel and other.ValueType == ptlsLabel:
    return this.labelValue == other.labelValue
  elif this.ValueType == ptlsList and other.ValueType == ptlsList:
    var this_seq : seq[ptlsValue] = @[]
    for i in this.eagerList():
      this_seq.add(i)

    var other_seq : seq[ptlsValue] = @[]
    for i in other.eagerList():
      other_seq.add(i)

    return this_seq == other_seq
  elif this.ValueType == ptlsNumber and other.ValueType == ptlsNumber:
    return this.numValue == other.numValue
  elif this.ValueType == ptlsObject and other.ValueType == ptlsObject:
    if len(this.objEnv.defs) != len(other.objEnv.defs): return false
    for key, _ in this.objEnv.defs:
      if not other.objEnv.defs.hasKey(key): return false
      if other.objEnv.defs[key].getValue() != this.objEnv.defs[key].getValue(): return false
    return true
  elif this.ValueType == ptlsSet and other.ValueType == ptlsSet:
    if len(this.setValue) != len(other.setValue): return false
    for key in this.setValue.keys:
      if not other.setValue.hasKey(key):
        return false
    return true
  elif this.ValueType == ptlsString and other.ValueType == ptlsString:
    return this.strValue == other.strValue
  elif this.ValueType == ptlsTuple:
    if other.ValueType == ptlsTuple:
      if this.tupleLabel != other.tupleLabel:
        return false
      if len(this.tupleValue) != len(this.tupleValue):
        return false
      for i in [0 .. len(this.tupleValue)]:
        if this.tupleValue[i] != other.tupleValue[i]:
          return false
      return true
    else:
      return false
  return false


proc contains(this: ptlsValue, value: ptlsValue): bool =
  this.checkType(@[ptlsDict, ptlsSet])
  if this.ValueType == ptlsDict:
    return this.dictValue.hasKey(value)
  elif this.ValueType == ptlsSet:
    return this.setValue.hasKey(value)
  quit "You shouldn't be here"

proc getMember(this: ptlsValue, index: int) : ptlsValue =
  this.checkType(@[ptlsTuple])
  if this.ValueType == ptlsTuple:
    return this.tupleValue[index]
  quit "You shouldn't be here"

proc getIndex(this: ptlsValue, rhs: ptlsValue) : ptlsValue =
  this.checkType(@[ptlsDict, ptlsArray])
  if this.ValueType == ptlsArray:
    let numVal = rhs.checkType(@[ptlsNumber])
    let index = this.checkIndex(numVal.numValue)
    return this.array_elems[index]
  elif this.ValueType == ptlsDict:
    if this.contains(rhs):
      return this.dictValue[rhs]
    else:
      let error = returnPtlsError("Index Error")
      error.msg = "Given key does not exist in dict"
      raise error
  quit "You shouldn't be here"

proc updateIndex(this: ptlsValue, index: ptlsValue, res: ptlsValue) : ptlsValue =
  this.checkType(@[ptlsDict, ptlsArray])
  if this.ValueType == ptlsArray:
    let numVal = index.checkType(@[ptlsNumber])
    let index = this.checkIndex(numVal.numValue)
    var new_array = this.array_elems
    new_array[index] = res
    return createPtlsArray(nil, new_array)
  elif this.ValueType == ptlsDict:
    var new_dictValue = this.dictValue
    new_dictValue[index] = res
    return createPtlsDict(nil, new_dictValue)
  quit "You shouldn't be here"

proc delKey(this: ptlsValue, key: ptlsValue) : ptlsValue

proc checkLabel(this: ptlsValue, val: string, name: string)
proc getLines() : ptlsValue
proc getDebug(this: ptlsValue, val: ptlsValue) : ptlsValue
proc getDebugLoc(this: ptlsValue, val: ptlsValue) : ptlsValue
proc getZeros(this: ptlsValue, val: ptlsValue) : ptlsValue
proc getWrap(this: ptlsValue, value: ptlsValue) : ptlsValue
proc getWrapTuple(this: ptlsValue, tup: ptlsValue) : ptlsValue
proc getWrapObject(this: ptlsValue, obj: ptlsValue) : ptlsValue
proc addElem(this: ptlsValue, elem: ptlsValue) : ptlsValue
proc delElem(this: ptlsValue, elem: ptlsValue) : ptlsValue

proc getField(this: ptlsValue, name: string) : ptlsValue =
  if this.ValueType == ptlsArray:
    if name == "!getList": return PtlsListFromValues(this.array_elems)
    elif name == "!getTuple": return createPtlsTuple(nil, this.array_elems)
    elif name == "!getType": return createPtlsLabel(nil, "PtlsArray")
    elif name ==  "!getLength": return createPtlsNumber(nil, float(len(this.array_elems)))
  elif this.ValueType == ptlsBuiltIn:
    if name == "!getType": return createPtlsLabel(nil, "PtlsBuiltIn")
  elif this.ValueType == ptlsBool:
    if name == "!getInt": return createPtlsNumber(nil, if this.boolValue: 1.0f
                                                                else: 0.0f)
    elif name == "!getFloat": return createPtlsNumber(nil, if this.boolValue: 1.0f
                                                                else: 0.0f)
    elif name == "!getString": return createPtlsString(nil, $this.boolValue)
    elif name ==  "!getType": return createPtlsLabel(nil, "PtlsBool")
  elif this.ValueType == ptlsDict:
    if name == "!getDelKey": return createPtlsBuiltIn(nil, "!getDelKey(key)", proc (x: ptlsValue) : ptlsValue = this.delKey(x))
    elif name == "!getKeys":
      var keys : seq[ptlsValue] = @[]
      for key, _ in this.dictValue:
        keys.add(key)
      return PtlsListFromValues(keys)
    elif name == "!getType": return createPtlsLabel(nil, "PtlsDict")
    elif name == "!getLength": return createPtlsNumber(nil, float(len(this.dictValue)))
  elif this.ValueType == ptlsFunc:
    if name == "!getType": return createPtlsLabel(nil, "PtlsFunc")
  elif this.ValueType == ptlsLabel:
    if name == "!getType": return createPtlsLabel(nil, "PtlsLabel")
    elif name == "!getLines":
      this.checkLabel("IO", "!getLines")
      return getLines()
    elif name == "!getDebug":
      this.checkLabel("IO", "!getDebug")
      return createPtlsBuiltIn(nil, "!getDebug(value)", proc (x: ptlsValue) : ptlsValue = this.getDebug(x))
    elif name == "!getDebugLoc":
      this.checkLabel("IO", "!getDebugLoc")
      return createPtlsBuiltIn(nil, "!getDebugLoc(value)", proc (x: ptlsValue) : ptlsValue = this.getDebugLoc(x))
    elif name == "!getDebugLoc":
      this.checkLabel("IO", "!getDebugLoc")
      return createPtlsBuiltIn(nil, "!getDebugLoc(value)", proc (x: ptlsValue) : ptlsValue = this.getDebugLoc(x))
    elif name == "!getRand":
      this.checkLabel("IO", "!getRand")
      return createPtlsNumber(nil, random.rand(100f))
    elif name == "!getSet":
      this.checkLabel("Empty", "!getSet")
      let ex_map = initTable[ptlsValue, ptlsValue]()
      return createPtlsSet(nil, ex_map)
    elif name == "!getZeros":
      this.checkLabel("PtlsArray", "!getZeros")
      return createPtlsBuiltIn(nil, "!getZeros(n)", proc (x: ptlsValue) : ptlsValue = this.getZeros(x))
    elif name == "!getString":
      return createPtlsString(nil, this.labelValue)
    elif name == "!getType":
      return createPtlsLabel(nil, "PtlsLabel")
    elif name == "!getWrap":
      return createPtlsBuiltIn(nil, "!getWrap(value)", proc (x: ptlsValue) : ptlsValue = this.getWrap(x))
    elif name == "!getWrapTuple":
      return createPtlsBuiltIn(nil, "!getWrapTuple(value)", proc (x: ptlsValue) : ptlsValue = this.getWrapTuple(x))
    elif name == "!getWrapObject":
      return createPtlsBuiltIn(nil, "!getWrapObject(value)", proc (x: ptlsValue) : ptlsValue = this.getWrapObject(x))
  elif this.ValueType == ptlsList:
    if name == "!getHead": return this.head()
    elif name == "!getTail": return this.tail()
    elif name == "!getList": return this
    elif name == "!getType": return createPtlsLabel(nil, "PtlsList")
  elif this.ValueType == ptlsNumber:
    if name == "!getInt": return createPtlsNumber(nil, float(int(this.numValue)))
    elif name == "!getFloat": return createPtlsNumber(nil, float(this.numValue))
    elif name == "!getAsin": return createPtlsNumber(nil, arcsin(this.numValue))
    elif name == "!getAcos": return createPtlsNumber(nil, arccos(this.numValue))
    elif name == "!getAtan": return createPtlsNumber(nil, arctan(this.numValue))
    elif name == "!getSin": return createPtlsNumber(nil, sin(this.numValue))
    elif name == "!getTan": return createPtlsNumber(nil, tan(this.numValue))
    elif name == "!getLn": return createPtlsNumber(nil, ln(this.numValue))
    elif name == "!getString": return createPtlsString(nil, $this.numValue)
    elif name == "!getType": return createPtlsLabel(nil, "PtlsList")
  elif this.ValueType == ptlsObject:
    if this.objEnv.defs.hasKey(name): return this.objEnv.lookupName(name)
    elif name == "!getLabel": return this.label
    elif name == "!getType": return createPtlsLabel(nil, "PtlsObject")
    elif name == "!getDict":
      var map = initTable[ptlsValue, ptlsValue]()
      for key in this.objEnv.defs.keys:
        map[createPtlsString(this.loc, name)] = this.objEnv.lookupName(name)
      return createPtlsDict(nil, map)
    let error = returnPtlsError("Type Error")
    var fields : seq[string] = @[]
    for key in this.objEnv.defs.keys:
      fields.add(key)
    let fieldStr = fields.join(", ")
    error.msg = "Invalid field '" & $name & "' for Object with fields " & $fieldStr
    raise error
  elif this.ValueType == ptlsSet:
    if name == "!getAddElem": return createPtlsBuiltIn(nil, "!getAddElem(elem)", proc (x: ptlsValue) : ptlsValue = this.addElem(x))
    elif name == "!getDelElem": return createPtlsBuiltIn(nil, "!getDelElem(elem)", proc (x: ptlsValue) : ptlsValue = this.delElem(x))
    elif name == "!getType": return createPtlsLabel(nil, "PtlsSet")
    elif name == "!getLength": return createPtlsNumber(nil, float(len(this.setValue)))
    elif name == "!getList":
        var keys : seq[ptlsValue] = @[]
        for key in this.setValue.keys:
          keys.add(key)
          return PtlsListFromValues(keys)
  elif this.ValueType == ptlsString:
    if name == "!getInt": return createPtlsNumber(nil, float(int(this.strValue.parseFloat())))
    elif name == "!getFloat": return createPtlsNumber(nil, this.strValue.parseFloat())
    elif name == "!getString": return this
    elif name == "!getList":
      let new_lisValue = @(this.strValue).map(proc(x: char): ptlsValue = createPtlsString(nil, $x))
      return PtlsListFromValues(new_lisValue)
    elif name == "!getType": return createPtlsLabel(nil, "PtlsString")
    elif name == "!getLength": return createPtlsNumber(nil, float(len(this.strValue)))
  elif this.ValueType == ptlsTuple:
    if name == "!getLabel": return this.tupleLabel
    elif name == "!getType": return createPtlsLabel(nil, "PtlsTuple")
    elif name == "!getLength": return createPtlsNumber(nil, float(len(this.tupleValue)))
    elif name == "!getList": return PtlsListFromValues(this.tupleValue)
  if name[0] == '!' and this.ValueType != ptlsObject:
    let error = returnPtlsError("Type Error")
    error.msg = "No built-in field '" & name & "' for type '" & $this.ValueType & "'"
    error.locs.add(this.loc)
    raise error
  quit "You shouldn't be here"

proc updateField(this: ptlsValue, name: string, res: ptlsValue): ptlsValue =
  this.checkType(@[ptlsObject])
  if this.ValueType == ptlsObject:
    let newEnv = this.objEnv.clone()
    if newEnv.defs.hasKey(name):
      newEnv.defs.del(name)
    let thunk = thunkFromValue(name, res)
    newEnv.addDefThunk(thunk)
    return createPtlsObject(nil, newEnv, this.label)
  quit "You shouldn't be here"

proc update(env: Env, accessor: ASTNode, res: var ptlsValue): ptlsValue =
  if accessor.NodeType == Node.Name:
    return res

  let lhs = eval(env, accessor[0])

  if accessor.NodeType == Node.Index:
    let index = eval(env, accessor[1])
    res = lhs.updateIndex(index, res)
  else:
    let name = $accessor.field.identifier
    res = lhs.updateField(name, res)
  return update(env, accessor[0], res)

proc checkType(this: ptlsValue, types: seq[ValueTypes]) : ptlsValue {.discardable.} =
  if not types.contains(this.ValueType):
    let typesStr = types.join(" or ");
    var error = returnPtlsError("Type Error");
    error.msg = "Expected type '" & $typesStr & "', got '" & $this.ValueType & "'";
    error.locs.add(this.loc);
    raise error

  return this

proc isEmpty(this: ptlsValue) : bool =
  if this.ValueType == ptlsLabel: return this.labelValue == "Empty"
  return false

proc checkIsList(this: ptlsValue): ptlsValue =
  if this.ValueType == ptlsList:
    return this
  elif this.ValueType == ptlsLabel:
    return this
  let error = returnptlsError("Type Error")
  error.msg = "Expected type 'PtlsList or Empty', got '" & $this.ValueType & "'"
  raise error

# Array specific methods
# ---------------------------
proc elemsList(this: ptlsValue) : seq[ptlsValue] =
  if this.ValueType == ptlsArray:
    return this.array_elems
  quit "You tried to access array elements of a non-array type so... Yeah, I am going"

proc checkIndex(this: ptlsValue, index: float) : int =
  if this.ValueType == ptlsArray:
    if int(index) != int(index.round()):
      let error = returnPtlsError("Index Error");
      error.msg = "Expected integer index value, got " & $index;
      raise error;

    if index < 0 or int(index) >= len(this.array_elems):
      let error = returnPtlsError("Index Error")
      let length = len(this.array_elems)
      error.msg = "Invalid index " & $index & ", for array with length " & $length
      raise error

    return int(index)

# Dict specific operations
# ----------------------------
proc delKey(this: ptlsValue, key: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsDict: quit "You called a dict method on something that's not a dict"
  var new_table = this.checkType(@[ptlsDict]).dictValue
  new_table.del(key)
  return createPtlsDict(nil, new_table)

# Label specific methods
# ----------------------------
proc getZeros(this: ptlsValue, val: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  let n = val.checkType(@[ptlsNumber]).numValue
  var zeros : seq[ptlsValue] = @[]
  var x = 0f
  while x<n:
    zeros.add(createptlsNumber(nil, 0f))
    x+=1f
  return createPtlsArray(nil, zeros)

proc debugHandler(this: ptlsValue, str: string) =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"

proc getDebug(this: ptlsValue, val: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  this.debugHandler($val)
  return val

proc getDebugLoc(this: ptlsValue, val: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  this.debugHandler($val.loc)
  return val

proc getLines() : ptlsValue =
  let line = $readLine(stdin)
  if line == "":
    return createPtlsLabel(nil, "Empty")
  let headThunk = thunkFromValue("", createPtlsString(nil, line))
  let tailThunk = createThunk("", getLines)
  return createPtlsList(nil, headThunk, tailThunk)

proc getWrap(this: ptlsValue, value: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  return createPtlsTuple(nil, @[value], this);

proc getWrapTuple(this: ptlsValue, tup: ptlsValue) : ptlsValue =
  tup.checkType(@[ptlsTuple])
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  let new_tup = tup.tuple_value
  return createPtlsTuple(nil, new_tup, this);

proc getWrapObject(this: ptlsValue, obj: ptlsValue) : ptlsValue =
  obj.checkType(@[ptlsObject])
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  return createPtlsObject(nil, obj.objEnv, this);

proc checkLabel(this: ptlsValue, val: string, name: string) =
  if this.ValueType != ptlsLabel: quit "You called a label method on something that's not a label"
  if this.labelValue != val:
    let error = returnPtlsError("Type Error")
    error.msg = "No built-in field '" & $name & "' for label '" & $this.labelValue & "'"
    raise error

# List specific operations
# ---------------------------
proc reverse[T](xs: openarray[T]): seq[T] =
  result = newSeq[T](xs.len)
  for i, x in xs:
    result[xs.high-i] = x

proc PtlsListFromValues(values: seq[ptlsValue]) : ptlsValue =
  var res = createPtlsLabel(nil, "Empty")
  for value in values.reverse():
    let headThunk = thunkFromValue("", value)
    let tailThunk = thunkFromValue("", res)
    res = createPtlsList(nil, headThunk, tailThunk)
  return res

proc head(this: ptlsValue) : ptlsValue = this.headThunk.getValue()
proc tail(this: ptlsValue) : ptlsValue = this.tailThunk.getValue()

proc toList(this: ptlsValue) : seq[ptlsValue] =
  if this.ValueType != ptlsList: quit "You called a list method on something that's not a list"
  var tailIter = this.tail
  var res = @[this.head]
  while tailIter.isEmpty():
    res.add(tailIter.head())
    tailIter = tailIter.tail()
  return res

proc concat(this: ptlsValue, env: Env, rhsNode: ASTNode) : ptlsValue =
  if this.ValueType != ptlsList: quit "You called a list method on something that's not a list"
  proc fun() : ptlsValue =
    return eval(env, rhsNode).checkIsList()
  if this.tail().isEmpty():
    let thunk = createThunk("", fun)
    return createPtlsList(nil, this.headThunk, thunk)
  let thunk = createThunk("", proc () : ptlsValue = this.tail.concat(env, rhsNode))
  return createPtlsList(nil, this.headThunk, thunk)

# Set specific methods
# ----------------------

proc addElem(this: ptlsValue, elem: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsSet: quit "You called a set method on something that's not a set"
  var new_map = this.setValue
  new_map[elem] = elem
  return createPtlsSet(nil, new_map)

proc delElem(this: ptlsValue, elem: ptlsValue) : ptlsValue =
  if this.ValueType != ptlsSet: quit "You called a set method on something that's not a set"
  var new_set = this.setValue
  new_set.del(elem)
  return createPtlsSet(nil, new_set)

# Tuple specific operations
# ---------------------------
proc checkLength(this: ptlsValue, length: int) : ptlsValue =
  if length != len(this.tupleValue):
    var error = returnPtlsError("Type Error")
    error.msg = "Cannot destructure length " & $length & " tuple to " & $len(this.tupleValue) & " names"
    raise error

  return this

# Binary Operation handler
proc handleUnaryOp(env: Env, op: Tok.Tok, operandNode: ASTNode) : ptlsValue =
  if op.str == Tok.Neg.str:
    let operand = evalCheck(env, operandNode, @[ptlsNumber])
    return createPtlsNumber(operand.loc, -operand.numValue)
  elif op.str == Tok.Not.str:
    let operand = evalCheck(env, operandNode, @[ptlsBool])
    return createPtlsBool(operand.loc, not operand.boolValue)

  quit op.str & "isn't quite an operator that I am familiar with"

proc handleBinaryOp(env: Env, op: Tok.Tok, lhsNode: ASTNode, rhsNode: ASTNode) : ptlsValue =
  if op.str == Tok.Concat.str:
    let lhs = eval(env, lhsNode).checkIsList()
    if (lhs.isEmpty):
      return eval(env, rhsNode).checkIsList()
    return lhs.concat(env, rhsNode);

  elif op.str == Tok.Or.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsBool]);
    if lhs.boolValue:
      return createPtlsBool(nil, true)
    var res = evalCheck(env, rhsNode, @[ptlsBool]);
    return res

  elif op.str == Tok.And.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsBool]);
    if not lhs.boolValue:
      return createPtlsBool(nil, false)

    var res = evalCheck(env, rhsNode, @[ptlsBool]);
    return res

  elif op.str == Tok.Equals.str:
    let lhs = eval(env, lhsNode)
    let rhs = eval(env, rhsNode)
    return createPtlsBool(nil, lhs == rhs)

  elif op.str == Tok.NotEq.str:
    let lhs = eval(env, lhsNode);
    let rhs = eval(env, rhsNode);
    return createPtlsBool(nil, lhs != rhs);


  elif op.str == Tok.In.str:
    let lhs = eval(env, lhsNode);
    let rhs = evalCheck(env, rhsNode, @[ptlsSet, ptlsDict]);
    return createPtlsBool(nil, rhs.contains(lhs));

  elif op.str == Tok.LessThan.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    return createPtlsBool(nil, lhs.numValue < rhs.numValue);

  elif op.str == Tok.LessEq.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    return createPtlsBool(nil, lhs.numValue <= rhs.numValue);

  elif op.str == Tok.GreaterThan.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber])
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber])
    return createPtlsBool(nil, lhs.numValue > rhs.numValue)

  elif op.str == Tok.GreaterEq.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    return createPtlsBool(nil, lhs.numValue >= rhs.numValue);

  elif op.str == Tok.Add.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber, ptlsString]);

    if lhs.ValueType == ptlsNumber:
      let rhs = evalCheck(env, rhsNode, @[ptlsNumber])
      return createPtlsNumber(nil, lhs.numValue + rhs.numValue)

    let rhs = evalCheck(env, rhsNode, @[ptlsString])
    return createPtlsString(nil, lhs.strvalue & rhs.strvalue)

  elif op.str == Tok.Sub.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber])
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber])
    return createPtlsNumber(nil, lhs.numValue - rhs.numValue)

  elif op.str == Tok.Mul.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    return createPtlsNumber(nil, lhs.numValue * rhs.numValue);

  elif op.str == Tok.Div.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    if rhs.numValue == 0:
      var error = returnPtlsError("Arithmetic Error");
      error.msg = "Division by zero";
      error.locs.add(rhs.loc);
      raise error
    return createPtlsNumber(nil, lhs.numValue / rhs.numValue);

  elif op.str == Tok.Mod.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber]);
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber]);
    return createPtlsNumber(nil, lhs.numValue mod rhs.numValue);

  elif op.str == Tok.Pow.str:
    let lhs = evalCheck(env, lhsNode, @[ptlsNumber])
    let rhs = evalCheck(env, rhsNode, @[ptlsNumber])
    return createPtlsNumber(nil, pow(lhs.numValue, rhs.numValue))

  quit op.str & "isn't quite an operator that I am familiar with"

# The actual interpreter
# -----------------------
var depth = 0
var lastLoc : Location

proc eval(env: Env, node: ASTNode) : ptlsValue =
  let maxDepth = 1000
  if depth > maxDepth:
    let error = returnPtlsError("Recursion Error")
    error.msg = "Max call depth " & $maxDepth & " exceeded"
    raise error
  var res : ptlsValue
  var oldLastLoc = lastLoc
  var traceLocs : seq[Location] = @[]
  try:
    depth += 1
    res = dispatch(env, node, traceLocs)
    depth -= 1
  except PtlsError as err:
    err.locs.add(traceLocs)
    err.locs.add(lastLoc)
    depth = 0
    raise
  if isNil(res.loc): res.loc = lastLoc
  lastLoc = oldLastLoc
  return res

proc evalCheck(env: Env, node: ASTNode, types: seq[ValueTypes]): ptlsValue =
  return eval(env, node).checkType(types)

proc dispatch(immut_env: Env, immut_node: ASTNode, immut_traceLocs: seq[Location]) : ptlsValue =
  var env = immut_env
  var node = immut_node
  var traceLocs = immut_traceLocs
  while true:
    lastLoc = node.location
    case node.NodeType:
      of Node.Array:
        var ptls_array_seq : seq[ptlsValue] = node.array_elems.map(proc(n: ASTNode) : ptlsValue = eval(env, n))
        return createPtlsArray(nil, ptls_array_seq)

      of Node.BinaryOp:
        return handleBinaryOp(env, node.binary_op, node.bin_lhs, node.bin_rhs)

      of Node.Bool:
        return createPtlsBool(nil, node.boolValue)

      of Node.Call:
        let fun = evalCheck(env, node.reference, @[ptlsBuiltIn, ptlsFunc])
        let args = node.refered.map(proc(n: ASTNode) : ptlsValue = eval(env, n))
        if fun.ValueType == ptlsFunc:
          if (len(args) + len(fun.scope.defs) > len(fun.params)):
            let error = returnPtlsError("Type Error");
            error.msg = "Too many args (" & $len(args) & ") for '" & $fun & "'";
            raise error
          let newEnv = fun.scope.clone()
          for arg in args:
            let name = fun.params[len(newEnv.defs)]
            let thunk = thunkFromValue(name, arg)
            newEnv.addDefThunk(thunk)
          if len(newEnv.defs) < len(fun.params):
            return createPtlsFunc(nil, newEnv, fun.params, fun.fun_body)
          traceLocs.add(node.location)
          env = newEnv
          node = fun.fun_body
          continue
        if fun.ValueType == ptlsBuiltIn:
          if len(args) != 1:
            let error = returnPtlsError("Type Error");
            error.msg = "Invalid arg count for " & fun.signature
            raise error
          return fun.fun(args[0])
        quit "How tf did you get here?"

      of Node.Conditional:
        let pred = evalCheck(env, node.ifClause, @[ptlsBool])
        if pred.boolValue:
          node = node.thenExpr
          continue
        if node.elseExpr == nil:
          let error = returnPtlsError("Condition Error")
          error.msg = "No matching case"
          raise error
        node = node.elseExpr
        continue

      of Node.Dict:
        var map = initTable[ptlsValue, ptlsValue]()
        for pair in node.dict_elems:
          map[eval(env, pair.key)] = eval(env, pair.val)
        return createPtlsDict(nil, map)

      of Node.FieldRef:
        let lhs = eval(env, node.label)
        let name = node.field.identifier
        return lhs.getField(name)

      of Node.Func:
        let params = node.func_params.map(proc(x: ASTNode) : string = x.identifier)
        return createPtlsFunc(nil, env.spawn(), params, node.fun_body)

      of Node.Index:
        let lhs = eval(env, node.index_lhs)
        let rhs = eval(env, node.index_rhs)
        return lhs.getIndex(rhs)

      of Node.Label:
        return createPtlsLabel(nil, node.labelValue)

      of Node.List:
        var res = createPtlsLabel(nil, "Empty");
        for elemNode in node.list_elems.reverse():
          let el = elemNode
          let new_res = res
          var headThunk = createThunk("", proc () : ptlsValue = eval(env, el))
          var tailThunk = createThunk("", proc () : ptlsValue = new_res)
          discard tailThunk.getValue()
          discard headThunk.getValue()
          res = createPtlsList(nil, headThunk, tailThunk)

        return res

      of Node.Name:
        return env.lookupName(node.identifier)

      of Node.Number:
        return createPtlsNumber(nil, node.numValue)

      of Node.Object:
        let newEnv = env.spawn()
        for defNode in node.obj_defs:
          newEnv.addDef(defNode)
        return createPtlsObject(nil, newEnv)

      of Node.Program:
        let exports = node.export_name
        let imports = node.imports
        let defs = node.defs

        for importNode in imports:
          let name = importNode.as_node.identifier
          let thunk = createThunk(name, proc() : ptlsValue = eval(env, importNode))
          env.addDefThunk(thunk)

        for defNode in defs:
          env.addDef(defNode)

        if exports != nil:
          let newEnv = createEnv(nil)
          for nameNode in exports.exports:
            let name = nameNode.identifier
            let thunk = createThunk(name, proc () : ptlsValue = env.lookupName(name))
            newEnv.addDefThunk(thunk)
          return createPtlsObject(nil, newEnv)

        return createPtlsObject(nil, env)

      of Node.Requires:
        let condition = evalCheck(env, node.requirement, @[ptlsBool])
        if not condition.boolValue:
          let error = returnPtlsError("Runtime Error")
          error.msg = "Unmet condition"
          raise error
        node = node.required

      of Node.Set:
        var map = initTable[ptlsValue, ptlsValue]()
        for elemNode in node.set_elems:
          let elem = eval(env, elemNode)
          map[elem] = elem
        return createPtlsSet(nil, map)

      of Node.String:
        return createPtlsString(nil, node.strValue)

      of Node.Throw:
        let value = eval(env, node.thrown_error)
        raise createPtlsException(value, node.location)

      of Node.Try:
        try:
          return eval(env, node.trial_body)
        except ptlsException as exception:
          let valNode : ASTNode = RuntimeValueNode(NodeType: Node.RuntimeValue, location: nil, value: exception.exceptValue)
          let callCond = ASTNode(NodeType: Node.Call, location: node.location, reference: node.catch_condition, refered: @[valNode])
          let cond = evalCheck(env, callCond, @[ptlsBool])
          if not cond.boolValue:
            raise
          let funcNode = node.handler
          let callHandler = ASTNode(NodeType: Node.Call, location: node.location, reference: funcNode, refered: @[valNode])
          node = callHandler
          continue
        quit "You still here... Go down!"

      of Node.Tuple:
        let elems = node.tuple_elems.map(proc(n: ASTNode) : ptlsValue = eval(env, n))
        return createPtlsTuple(nil, elems)

      of Node.UnaryOp:
        return handleUnaryOp(env, node.op, node.unary_node)

      of Node.Where:
        let obj = eval(env, node.where_clause)
        env = obj.objEnv
        node = node.where_body
        continue

      of Node.With:
        let lhs = evalCheck(env, node.with_body, @[ptlsDict, ptlsObject, ptlsArray])
        let newEnv = env.clone()
        let thunk = thunkFromValue("$", lhs)
        newEnv.addDefThunk(thunk)
        let values = node.with_defs.map(proc(n: ASTNode) : ptlsValue = eval(newEnv, n.rhs))
        var index = 0
        for def in node.with_defs:
          var variable_current_def = values[index]
          thunk.value = update(newEnv, def.lhs, variable_current_def)
          index += 1
        return thunk.value

      of Node.RuntimeValue:
        return (cast[RuntimeValueNode](node)).value

      of Node.Import:
        let importValue = evalCheck(env, node.path, @[ptlsString])
        if not existsFile(importValue.strValue):
          let error = returnPtlsError("IO Error")
          error.msg = "The file " & importValue.strValue & " doesn't exist"
          raise error
        let source = eval(createEnv(), makeAST(getToks(@(readFile(importValue.strValue)).filter(proc(x: char) : bool = x!='\r').join(""), importValue.strValue)))
        return createPtlsObject(nil, source.objEnv)

      of Node.Pair: quit "We hate pairs"
      of Node.Blank: quit "We hate blanks"
      of Node.Def: quit "We hate defs"
      of Node.Export: quit "We hate exports"

let commands = commandLineParams().map(proc(x: TaintedString) : string = $x)
if len(commands) != 1:
  quit "Wrong amount of parameters, the correct format is, [interpreter-name] [file-name]"

if not existsFile(commands[0]):
  let error = returnPtlsError("IO Error")
  error.msg = "The file " & commands[0] & " doesn't exist"
  raise error

let program = @(readFile(commands[0])).filter(proc(x: char) : bool = x!='\r').join("")

let toks = getToks(program, commands[0])
let ast = makeast(toks)
let env = eval(createEnv(), ast).objEnv
var sequence : seq[ptlsValue] = @[]
try:
  for element in getOutput(env):
    sequence.add(element)
except PtlsError as err:
  echo err.locs.deduplicate.join("\n")
  raise

echo "[" & sequence.join(", ") & "]"
