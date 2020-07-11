import location
import tokenTypes
import strutils

type
  Token* = ref object of RootObj
    tokType* : Tok
    value* : string
    loc* : Location

proc createToken*(tokType : Tok, value : string, loc : Location) : Token = Token(tokType : tokType, value : value, loc : loc)

proc typeStr*(this: Token) : string = this.tokType.str

proc trim(this: string) : string =
  var new_str = this
  for i, c in this:
    if [' ', '\t', '\v', '\c', '\n', '\f'].contains(c):
      new_str.delete(i, i+1)
  return new_str

proc toString*(this: Token) : string =
  let lineStr = alignLeft($(this.loc.lineNum), 3)
  let colStr = align($(this.loc.colNum), 2)
  let tokStr = align(this.typeStr(), 12)
  return lineStr & ":" & colStr & " [ " & tokStr & " ] " & this.value.trim()
