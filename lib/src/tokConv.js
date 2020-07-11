const x = `
Array,
BinaryOp,
Blank,
Bool,
Call,
Conditional,
Def,
Dict,
Export,
FieldRef,
Func,
Import,
Index,
Label,
List,
Name,
Number,
Object,
Pair,
Program,
Requires,
RuntimeValue,
Set,
String,
Throw,
Try,
Tuple,
UnaryOp,
Where,
With,
}`
var count = 0
const in_array = x.split(",\n")
const out_array = in_array.map((x) => `of ${x}: return "${x}"`)

const out_x = out_array.join("\n")
console.log(out_x);
