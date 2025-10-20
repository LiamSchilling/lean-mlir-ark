import LeanMLIR.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Field Dialect

Defines a dialect `Fld` for algebra over a field.

This dialect will be the basis for a number of extension dialects
for objects that contain field elements:
- Vectors: `FieldStructs\Vector\Basic.lean`
- Univariate polynomials: `FieldStructs\UniPoly\Basic.lean`
- Multilinear polynomials: `FieldStructs\MLPoly\Basic.lean`

Instances of `Fld` with specialized fields should be lowered to an integer dialect.
This will allow the extension dialects to generically lower to a tensor dialect
given any specific lowering from `Fld` to the integer dialect.
-/

namespace Fld

open LeanMLIR

variable {F : Type} [Field F]

/-- The types in the dialect:
- `int`: integers
- `f`: field members -/
inductive Ty (F : Type) where
| int
| f

instance : DecidableEq (Ty F)
| .int, .int => isTrue rfl
| .int, .f => isFalse (by intro; contradiction)
| .f, .int => isFalse (by intro; contradiction)
| .f, .f => isTrue rfl

instance : ToString (Ty F) where
toString
| .int => "int"
| .f => "f"

/-- A map from types in the dialect to the Lean types of their semantic interpretations. -/
instance : TyDenote (Ty F) where
toType
| .int => ℤ
| .f => F

/-- The operations in the dialect:
- `zero`: the additive identity
- `one`: the multiplicative identity
- `add`: field addition
- `sub`: addition with the inverse
- `neg`: the additive inverse
- `mul`: field multiplication
- `div`: multiplication by the inverse
- `inv`: the multiplicative inverse
- `zmul`: repeated addition (of the inverse for negative integers)
- `pow`: repeated multiplication (of the inverse for negative integers)
- `ofint`: repeated addition of `1` (of `-1` for negative integers)
- `const`: an integer value -/
inductive Op (F : Type) where
| zero | one
| add | sub | neg
| mul | div | inv
| zmul | pow | ofint
| const (_ : ℤ)

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.sig : Op F → List (Ty F)
| .zero => []
| .one => []
| .add => [.f, .f]
| .sub => [.f, .f]
| .neg => [.f]
| .mul => [.f, .f]
| .div => [.f, .f]
| .inv => [.f]
| .zmul => [.int, .f]
| .pow => [.f, .int]
| .ofint => [.int]
| const _ => []

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.returnTypes : Op F → List (Ty F)
| .zero => [.f]
| .one => [.f]
| .add => [.f]
| .sub => [.f]
| .neg => [.f]
| .mul => [.f]
| .div => [.f]
| .inv => [.f]
| .zmul => [.f]
| .pow => [.f]
| .ofint => [.f]
| .const _ => [.int]

/-- A map from operations to their full type signatures. -/
@[simp, reducible]
def Op.signature : Op F → Signature (Ty F)
| o => { sig := o.sig, returnTypes := o.returnTypes, regSig := [] }

/-- The dialect. -/
abbrev Fld (F : Type) : Dialect where
Op := Op F
Ty := Ty F

instance : DialectSignature (Fld F) where
signature := Op.signature

instance : DialectPrint (Fld F) where
printTy := toString
printOpName
| .zero => "zero"
| .one => "one"
| .add => "add"
| .sub => "sub"
| .neg => "neg"
| .mul => "mul"
| .div => "div"
| .inv => "inv"
| .zmul => "zmul"
| .pow => "pow"
| .ofint => "ofint"
| .const _ => "const"
printAttributes
| .const v => s!"\{value = {v} : int}"
| _ => ""
dialectName := "Fld"
printReturn _ := "return"

/-- The semantics for the dialect. -/
instance : DialectDenote (Fld F) where
denote
| .zero, _, _ => [0]ₕ
| .one, _, _ => [1]ₕ
| .add, arg, _ => [(fun args => args.1 + args.2) arg.toPair]ₕ
| .sub, arg, _ => [(fun args => args.1 - args.2) arg.toPair]ₕ
| .neg, arg, _ => [-arg.toSingle]ₕ
| .mul, arg, _ => [(fun args => args.1 * args.2) arg.toPair]ₕ
| .div, arg, _ => [(fun args => args.1 * args.2⁻¹) arg.toPair]ₕ
| .inv, arg, _ => [arg.toSingle⁻¹]ₕ
| .zmul, arg, _ => [(fun args => (args.1 : ℤ) • args.2) arg.toPair]ₕ
| .pow, arg, _ => [(fun args => args.1 ^ (args.2 : ℤ)) arg.toPair]ₕ
| .ofint, arg, _ => [arg.toSingle]ₕ
| .const v, _, _ => [v]ₕ

/-- The parser for the dialect from an MLIR AST. -/
instance : DialectParse (Fld F) 0 where
mkTy
| .int .Signless 32 => return .int -- TODO: this should be `.Signed` but it breaks parsing
| .undefined "f" => return .f
| .int _ g => throw <| .undeclaredName (toString g)
| _ => throw .unsupportedType
mkExpr Γ opStx := do opStx.mkExprOf Γ <|← match opStx.name with
| "zero" => return .zero
| "one" => return .one
| "add" => return .add
| "sub" => return .sub
| "neg" => return .neg
| "mul" => return .mul
| "div" => return .div
| "inv" => return .inv
| "zmul" => return .zmul
| "pow" => return .pow
| "ofint" => return .ofint
| "const" => return .const (←opStx.getIntAttr "value").1
| opName => throw <| .unsupportedOp opName
isValidReturn _ opStx := return opStx.name == "return"

open Qq in
elab "[fld" Fi:term "," hfield:term " | " reg:mlir_region "]" : term => do
  let F : Q(Type) ← elabTermEnsuringTypeQ Fi q(Type)
  let _ ← elabTermEnsuringTypeQ hfield q(Field $F)
  SSA.elabIntoCom reg q(Fld $F)

/-- An example program in the dialect that adds `1` and `2` in the field `ℤ/5ℤ`. -/
def program :=
  [fld ZMod 5, sorry | {
    %c1 = "const"() {value = 2} : () -> i32
    %c2 = "one"() : () -> ! "f"
    %c3 = "ofint"(%c1) : (i32) -> ! "f"
    %c4 = "add"(%c2, %c3) : (! "f", ! "f") -> ! "f"
    "return"(%c4) : (! "f") -> ()
  }]

end Fld
