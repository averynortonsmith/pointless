import tables
import tokenTypes as Tok
import sets

let keywords* = {
  "if": Tok.If,
  "then": Tok.Then,
  "else": Tok.Else,
  "where": Tok.Where,
  "with": Tok.With,
  "cond": Tok.Cond,
  "case": Tok.Case,
  "and": Tok.And,
  "or": Tok.Or,
  "not": Tok.Not,
  "in": Tok.In,
  "as": Tok.As,
  "true": Tok.Bool,
  "false": Tok.Bool,
  "for": Tok.For,
  "when": Tok.When,
  "yield": Tok.Yield,
  "import": Tok.Import,
  "export": Tok.Export,
  "requires": Tok.Requires,
  "throw": Tok.Throw,
  "try": Tok.Try,
  "catch": Tok.Catch,
}.toTable()

let opSyms* = {
  "+": Tok.Add,
  "-": Tok.Sub,
  "*": Tok.Mul,
  "/": Tok.Div,
  "**": Tok.Pow,
  "%": Tok.Mod,
  "+=": Tok.AddAssign,
  "-=": Tok.SubAssign,
  "*=": Tok.MulAssign,
  "/=": Tok.DivAssign,
  "**=": Tok.PowAssign,
  "%=": Tok.ModAssign,
  "|>": Tok.Pipe,
  "=": Tok.Assign,
  "==": Tok.Equals,
  "!=": Tok.NotEq,
  "<": Tok.LessThan,
  ">": Tok.GreaterThan,
  "<=": Tok.LessEq,
  ">=": Tok.GreaterEq,
  "=>": Tok.Lambda,
  "$": Tok.Dollar,
  "++": Tok.Concat,
}.toTable()

let opSymChars* = ["+", "-", "*", "/", "%", "|", "=", "!", "<", ">", "$"].toHashSet()


let leftSyms* = {
  "(": Tok.LParen,
  "{": Tok.LBracket,
  "[": Tok.LArray,
}.toTable()

let rightSyms* = {
  ")": Tok.RParen,
  "}": Tok.RBracket,
  "]": Tok.RArray,
}.toTable()

let separators* = {
  ";": Tok.Semicolon,
  ":": Tok.Colon,
  ",": Tok.Comma,
}.toTable()
