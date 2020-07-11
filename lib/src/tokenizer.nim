import system
import location
import ptlsError
import sets
import tables
import symbols
import token
import tokenTypes as Tok
import strutils
import sequtils

let digits = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "0"]
let lowers = [
                "a", "b", "c", "d", "e", "f", "g", "h",
                "i", "j", "k", "l", "m", "n", "o", "p", "_",
                "q", "r", "s", "t", "u", "v", "w", "x", "y",
                "z"
                ]

let uppers = [
              "A", "B", "C", "D", "E", "F", "G", "H",
              "I", "J", "K", "L", "M", "N", "O", "P", "Q",
              "R", "S", "T", "U", "V", "W", "X", "Y", "Z"
              ]

let alnums = [
                "1", "2", "3", "4", "5", "6", "7", "8", "9",
                "a", "b", "c", "d", "e", "f", "g", "h", "0",
                "i", "j", "k", "l", "m", "n", "o", "p", "_",
                "q", "r", "s", "t", "u", "v", "w", "x", "y",
                "z", "A", "B", "C", "D", "E", "F", "G", "H",
                "I", "J", "K", "L", "M", "N", "O", "P", "Q",
                "R", "S", "T", "U", "V", "W", "X", "Y", "Z"
                ]

type
  Tokenizer = ref object of RootObj
    index : int
    tokIndex : int
    chars : string
    path : string
    locs : seq[Location]

proc getLocs(this: Tokenizer) =
  var lineNum = 1;
  var colNum = 1;

  var lines = this.chars.split("\n");

  for c in this.chars:
    this.locs.add(createLocation(lineNum, colNum, this.path, lines[lineNum - 1]))

    if c == '\n':
      colNum = 1
      lineNum += 1
    else:
      colNum += 1

  this.locs.add(createLocation(lineNum, colNum, this.path, this.chars))

proc createTokenizer(chars : string, path : string) : Tokenizer =
  let this = Tokenizer(index: 0, path: path, tokIndex: 0, chars : chars.replace("\r", "\n"))
  this.getLocs()
  return this

proc advance(this: Tokenizer) : string {.discardable.} =
  var value : string
  if this.index < len(this.chars):
    value = $this.chars[this.index]
  else:
    value = ""
  this.index += 1
  return value

proc hasChars(this: Tokenizer, offset : int) : bool = return this.index + offset < len(this.chars)

proc getChar(this: Tokenizer, offset: int) : string = return if (this.hasChars(offset)): $this.chars[this.index + offset]
                                                      else: ""

proc getTokValue(this: Tokenizer) : string = return this.chars.substr(this.tokIndex, this.index-1)

proc makeToken(this: Tokenizer, tokType : Tok) : Token =
  var value = this.getTokValue()
  var token = createToken(tokType, value, this.locs[this.tokIndex])
  this.tokIndex = this.index
  return token

proc isBlank(this: Tokenizer) : bool = return this.getChar(0) == "_"
proc isComment(this: Tokenizer) : bool = return this.getChar(0) == "-" and this.getChar(1) == "-"

proc isNumber(this: Tokenizer) : bool =
  let isInt = digits.contains(this.getChar(0))
  let isFloat = this.getChar(0) == "." and digits.contains(this.getChar(1))
  return isInt or isFloat

proc isName(this: Tokenizer) : bool = return lowers.contains(this.getChar(0))
proc isLabel(this: Tokenizer) : bool = return uppers.contains(this.getChar(0))
proc isField(this: Tokenizer) : bool =
  let isCustom = this.getChar(0) == "." and lowers.contains(this.getChar(1));

  let isLangField =
    this.getChar(0) == "." and
    this.getChar(1) == "!" and
    lowers.contains(this.getChar(2));

  return isCustom or isLangField;
proc isOpSym(this: Tokenizer) : bool = return opSymChars.contains(this.getChar(0))
proc isWhiteSpace(this: Tokenizer) : bool = return this.getChar(0) == " "
proc isNewline(this: Tokenizer) : bool = return this.getChar(0) == "\n"
proc isSeparator(this: Tokenizer) : bool = return separators.hasKey(this.getChar(0))
proc isLeftSym(this: Tokenizer) : bool = return leftSyms.hasKey(this.getChar(0))
proc isRightSym(this: Tokenizer) : bool = return rightSyms.hasKey(this.getChar(0))
proc isString(this: Tokenizer) : bool = return this.getChar(0) == "\""

proc handleBlank(this: Tokenizer) : Token =
  this.advance()
  return this.makeToken(Tok.Blank)

proc handleComment(this: Tokenizer) : Token =
  while (this.getChar(0) == "-"):
    this.advance()

  while this.hasChars(0) and this.getChar(0) != "\n":
    this.advance()

  return this.makeToken(Tok.Comment);

proc handleWhitespace(this: Tokenizer) : Token =
  while this.getChar(0) == " ":
    this.advance();

  return this.makeToken(Tok.Whitespace)

proc handleNewline(this: Tokenizer) : Token =
  while this.getChar(0) == "\n":
    this.advance()

  return this.makeToken(Tok.Newline)

proc handleSeparator(this: Tokenizer) : Token =
  let sym = this.advance()
  return this.makeToken(separators[sym])

proc handleName(this: Tokenizer) : Token =
  while alnums.contains(this.getChar(0)):
    this.advance()

  let value = this.getTokValue();
  if keywords.hasKey(value):
    return this.makeToken(keywords[value])

  return this.makeToken(Tok.Name);

proc handleField(this: Tokenizer) : Token =
  this.advance()
  this.advance()

  while alnums.contains(this.getChar(0)):
    this.advance()

  return this.makeToken(Tok.Field);

proc handleLabel(this: Tokenizer) : Token =
  while alnums.contains(this.getChar(0)):
    this.advance()

  return this.makeToken(Tok.Label);

proc handleString(this: Tokenizer) : Token =
    this.advance()
    while this.hasChars(0) and this.getChar(0) != "\"":
      if (this.getChar(0) == "\\" and this.getChar(1) != ""):
        this.advance()
        this.advance()
        continue

      this.advance()

      if this.getChar(0) == "\n":
        let error = returnPtlsError("Tokenizer Error");
        error.msg = "Unmatched quote (must escape line breaks in string)"
        error.locs.add(this.locs[this.tokIndex])
        raise error

    if not this.hasChars(0):
      let error = returnPtlsError("Tokenizer Error");
      error.msg = "Unmatched quote"
      error.locs.add(this.locs[this.tokIndex])
      raise error

    this.advance()
    return this.makeToken(Tok.String)

proc handleNumber(this: Tokenizer) : Token =
  this.advance()
  while digits.contains(this.getChar(0)):
    this.advance()

  if this.getChar(0) == "." and digits.contains(this.getChar(1)):
    this.advance()
    while (digits.contains(this.getChar(0))):
      this.advance()

  return this.makeToken(Tok.Number);

proc handleOpSym(this: Tokenizer) : Token =
  while opSymChars.contains(this.getChar(0)):
    this.advance()
  let value = this.getTokValue()
  if (not opSyms.hasKey(value)):
    var error = returnPtlsError("Tokenizer Error");
    error.msg = "Invalid operator " & value
    error.locs.add(this.locs[this.tokIndex])
    raise error

  return this.makeToken(opSyms[value])

proc handleLeftSym(this: Tokenizer) : Token =
  let value = this.advance()
  return this.makeToken(leftSyms[value])

proc handleRightSym(this: Tokenizer) : Token =
  let value = this.advance()
  return this.makeToken(rightSyms[value])

proc getToken(this: Tokenizer) : Token =
  if this.isBlank(): return this.handleBlank()
  if this.isComment(): return this.handleComment()
  if this.isWhitespace(): return this.handleWhitespace()
  if this.isNewline(): return this.handleNewline()
  if this.isSeparator(): return this.handleSeparator()
  if (this.isName()): return this.handleName()
  if (this.isField()): return this.handleField()
  if (this.isLabel()): return this.handleLabel()
  if (this.isString()): return this.handleString()
  if (this.isNumber()): return this.handleNumber()
  if (this.isOpSym()): return this.handleOpSym()
  if (this.isLeftSym()): return this.handleLeftSym()
  if (this.isRightSym()): return this.handleRightSym()

  var error = returnPtlsError("Tokenizer Error");
  error.msg = "Unexpected symbol '" & this.chars[this.index] & "'";
  error.locs.add(this.locs[this.index]);
  raise error;

var startToks : seq[Tok.Tok] = @[]
for value in opSyms.values:
  startToks.add(value)
for value in separators.values:
  startToks.add(value)
for value in leftSyms.values:
  startToks.add(value)
for value in keywords.values:
  startToks.add(value)

var endSyms : seq[Tok.Tok] = @[Tok.Name, Tok.Field, Tok.String, Tok.Number]
for value in keywords.values:
  endSyms.add(value)

iterator getInitialTokens(this: Tokenizer) : Token =
  while this.hasChars(0):
    yield this.getToken()
  yield this.makeToken(Tok.EOF)

iterator getTokens(this: Tokenizer) : Token =
  var isStartExpr = true
  var tokens : seq[Token] = @[]
  for token in this.getInitialTokens():
    tokens.add(token)
  var index = 0
  while index<len(tokens):
    let token = tokens[index]
    let lastToken = if (index == 0 or index-1>=len(tokens)): nil
                    else: tokens[index - 1]
    let nextToken = if (index == 0 or index+1>=len(tokens)): nil
                    else: tokens[index + 1]
    if token.tokType == Tok.Sub and isStartExpr:
      token.tokType = Tok.Neg;
    let lastTokenIsWhiteSpace = if isNil(lastToken): false
                                else: lastToken.tokType == Tok.Whitespace
    let nextTokIsNumNameOrLParen = if isNil(nextToken): false
                                else: [Tok.Number, Tok.Name, Tok.LParen].contains(nextToken.tokType)
    let tokenIsSub = token.tokType == Tok.Sub
    if tokenIsSub and lastTokenIsWhiteSpace and nextTokIsNumNameOrLParen:
        yield createToken(Tok.Neg, token.value, token.loc)
    else:
        yield token
    index += 1
    if startToks.contains(token.tokType):
      isStartExpr = true
    elif endSyms.contains(token.tokType):
      isStartExpr = false;

proc getToks*(str: string, path: string) : seq[Token] =
  let tokenizing = createTokenizer(str, path)
  var toks : seq[Token] = @[]
  try:
    for t in tokenizing.getTokens():
      toks.add(t)
  except PtlsError as err:
    echo err.locs.deduplicate.join("\n")
    raise

  return toks
