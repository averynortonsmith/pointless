import nodeTypes
import location
from tokenTypes as Tok import nil
import strutils
import sequtils

type
  ASTNode* = ref object of RootObj
    location*: Location
    case NodeType*: Node
      of Array: array_elems*: seq[AstNode]
      of BinaryOp:
        binary_op*: Tok.Tok
        bin_lhs*: AstNode
        bin_rhs*: AstNode
      of Blank: blank_nullary*: bool
      of Bool: boolValue*: bool
      of Call:
        refered*: seq[ASTNode]
        reference*: AstNode
      of Conditional: ifClause*, thenExpr*, elseExpr*: AstNode
      of Def: lhs*, rhs*: AstNode
      of Dict: dict_elems*: seq[AstNode]
      of Export: exports*: seq[AstNode]
      of FieldRef: label*, field*: AstNode
      of Func:
        func_params*: seq[ASTNode]
        fun_body*: AstNode
      of Import: path*, as_node*: AstNode
      of Index: index_lhs*, index_rhs*: AstNode
      of Label: labelValue*: string
      of List: list_elems*: seq[AstNode]
      of Name: identifier*: string
      of Number: numValue*: float
      of Object: obj_defs*: seq[AstNode]
      of Pair: key*, val*: AstNode
      of Program:
        export_name*: ASTNode
        imports*: seq[ASTNode]
        defs*: seq[AstNode]
      of Requires: required*, requirement*: AstNode
      of RuntimeValue: unused*: bool
      of Set: set_elems*: seq[AstNode]
      of String: strValue*: string
      of Throw: thrown_error*: AstNode
      of Try: trial_body*, catch_condition*, handler*: AstNode
      of Tuple: tuple_elems*: seq[AstNode]
      of UnaryOp:
        op*: Tok.Tok
        unary_node*: AstNode
      of Where: where_body*, where_clause*: AstNode
      of With:
        with_defs*: seq[ASTNode]
        with_body*: AstNode


proc toString*(this: ASTNode) : string
proc toString*(this: ASTNode) : string =
  case this.NodeType:
    of Array: return "[" & this.array_elems.map(proc(x: ASTNode) : string = x.toString()).join(" ") & "]"
    of BinaryOp: return this.bin_lhs.toString() & this.binary_op.str & this.bin_rhs.toString()
    of Blank: return "_"
    of Bool: return $this.boolValue
    of Call: return this.reference.toString() & "(" & this.refered.map(proc(x: ASTNode) : string = x.toString()).join(", ") & ")"
    of Conditional: return "if (" & this.ifClause.toString() & ") " & this.thenExpr.toString() & " else " & this.elseExpr.toString()
    of Def: return this.lhs.toString() & " = " & this.rhs.toString()
    of Dict: return "{" & this.dict_elems.map(proc(x: ASTNode) : string = x.toString()).join(",\n") & "}"
    of Export: return "export (" & this.exports.map(proc(x: ASTNode) : string = x.toString()).join("\n") & "\n)"
    of FieldRef: return this.label.toString() & "." & this.field.toString()
    of Func: return "fun " & "(" & this.func_params.map(proc(x: ASTNode) : string = x.toString()).join(", ") & ") -> " & this.fun_body.toString()
    of Import: return "import " & this.path.toString() & " as " & this.as_node.toString()
    of Index: return this.index_lhs.toString() & "[" & this.index_rhs.toString() & "]"
    of Label: return "Label" & this.labelValue
    of List: return "[" & this.list_elems.map(proc(x: ASTNode) : string = x.toString()).join(", ") & "]"
    of Name: return this.identifier
    of Number: return $this.numValue
    of Object: return this.obj_defs.map(proc(x: ASTNode) : string = x.toString()).join("\n")
    of Pair: return "(" & this.key.toString() & ", " & this.val.toString() & ")"
    of Program:
      let imports = if this.imports == @[]: ""
                    else: this.imports.map(proc(x: ASTNode) : string = x.toString()).join("\n")
      let defs = if this.defs == @[]: ""
                    else: this.defs.map(proc(x: ASTNode) : string = x.toString()).join("\n")
      let export_name = if this.export_name == nil: ""
                    else: this.export_name.toString()
      return ("-- Imports\n" & imports & "\n" &
      "-- Definitions" & "\n" & defs & "\n" &
      "-- Exports" & "\n" & export_name
      )
    of Requires: return this.requirement.toString() & " requires " & this.required.toString()
    of RuntimeValue: return "RuntimeValue"
    of Set: return "[" & this.set_elems.map(proc(x: ASTNode) : string = x.toString()).join(" ") & "]"
    of String: return "\"" & this.strValue & "\""
    of Throw: return "throw " & this.thrown_error.toString()
    of Try: return "try " & this.trial_body.toString() & " catch " & this.catch_condition.toString() & " -> " & this.handler.toString()
    of Tuple: return "(" & this.tuple_elems.map(proc(x: ASTNode) : string = x.toString()).join(" ") & ")"
    of UnaryOp: return this.op.str & this.unary_node.toString()
    of Where: return this.where_body.toString() & " where " & this.where_clause.toString()
    of With: return this.with_body.toString() & " with " & "(" & this.with_defs.map(proc(x: ASTNode) : string = x.toString()).join(", ") & ")"

proc `$`*(this: ASTNode) : string = this.toString()

proc `[]`*(this: ASTNode, index : int) : ASTNode =
  case index:
    of 0:
      case this.NodeType:
        of Index: return this.index_lhs
        of FieldRef: return this.label
        else: quit "0 case for " & $this.NodeType & "... I don't know what to do"
    of 1:
      case this.NodeType:
        of Index: return this.index_rhs
        of FieldRef: return this.field
        else: quit "1 case for " & $this.NodeType & "... I don't know what to do"
    else: quit "Humanity has to end..."
