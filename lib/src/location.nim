import strutils

type
  Location* = ref object of RootObj
    lineNum* : int
    colNum* : int
    path*: string
    line*: string

proc createLocation*(lineNum : int, colNum : int, path: string, line: string) : Location =
  return Location(lineNum : lineNum, colNum : colNum, path: path, line: line)

proc `==`*(this: Location, other: Location) : bool {.inline.} =
  return this.lineNum == other.lineNum and this.colNum == other.colNum and this.path == other.path

proc hashCode*(this: Location) : int {.inline.} = this.lineNum + 17 * this.colNum

proc toString*(this: Location) : string =
  let lineColStr = "(line " & $this.lineNum & " column " & $this.colNum & ")";
  var res = "\nAt " & lineColStr & " in " & "'" & $this.path & "'\n";
  res &= $this.line & "\n" & " ".repeat(this.colNum - 1) & "^";
  return res;

proc `$`*(this: Location) : string = this.toString()
