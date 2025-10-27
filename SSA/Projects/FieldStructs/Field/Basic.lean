import LeanMLIR.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Field Dialect

Defines a wrapper dialect `Flop` for algebra over a field.
`Flop` requires that the underlying dialect contains an integer type.
It is up to the underlying dialect to implement integer operations.

This dialect will be the basis for a number of extension dialects
for objects that contain field elements:
- Vectors: `FieldStructs\Vector\Basic.lean`
- Univariate polynomials: `FieldStructs\UniPoly\Basic.lean`
- Multilinear polynomials: `FieldStructs\MLPoly\Basic.lean`

Instances of `Flop` with specialized fields should be lowered to an integer dialect.
This will allow the extension dialects to generically lower to a tensor dialect
given any specific lowering from `Flop` to the integer dialect.
-/

open LeanMLIR

variable {F : Type} [Field F]

variable {Ty' Op' : Type} {int' : Ty'}
variable [DecidableEq Ty'] [TyDenote Ty']

variable {D : Dialect} {int : D.Ty}
variable [DecidableEq D.Ty] [TyDenote D.Ty]
variable [DialectSignature D] [DialectDenote D] [DialectPrint D] [P : DialectParse D 0]

namespace Flop

/-- The types in the dialect:
- `coe`: a type in the underlying dialect
- `coe int'`: the integer type in the underlying dialect
- `f`: field members -/
inductive Ty (F Ty' : Type) (int' : Ty') where
| coe (_ : Ty')
| f

/-- Lowers a type to the underlying dialect,
with `none` when the type is not from the underlying dialect. -/
def Ty.lower : Ty F Ty' int' → Option Ty'
| .coe ty' => some ty'
| _ => none

/-- Lowers a context to the underlying dialect,
filtering types that are not from the underlying dialect. -/
def lowerCtxt (Γ : Ctxt (Ty F Ty' int')) : Ctxt Ty' :=
  .ofList <| Γ.toList.filterMap Ty.lower

instance : DecidableEq (Ty F Ty' int')
| .coe a, .coe b => decidable_of_iff (a = b) (by simp)
| .coe _, .f => isFalse (by intro; contradiction)
| .f, .coe _ => isFalse (by intro; contradiction)
| .f, .f => isTrue rfl

/-- A map from types in the dialect to the Lean types of their semantic interpretations.
The semantic interpretations of types from the underlying dialect are preserved,
except for `coe int'` which is interpreted as `ℤ`. -/
instance : TyDenote (Ty F Ty' int') where
toType
| .coe ty' => if ty' = int' then ℤ else ⟦ty'⟧
| .f => F

omit [Field F] in
lemma denote_int (Ty' : Type) {int' : Ty'} [DecidableEq Ty'] [TyDenote Ty'] :
    TyDenote.toType (Ty.coe int' : Ty F Ty' int') = ℤ := by
  simp [TyDenote.toType]

/-- The operations in the dialect:
- `coe`: an operation in the underlying dialect
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
- `ofint`: repeated addition of `1` (of `-1` for negative integers) -/
inductive Op (F : Type) (Op' : Type) where
| coe (_ : Op')
| zero | one
| add | sub | neg
| mul | div | inv
| zmul | pow | ofint

/-- Lowers an operation to the underlying dialect,
with `none` when the operation is not from the underlying dialect. -/
def Op.unwrapCoe : Op F Op' → Option Op'
| .coe ty' => some ty'
| _ => none

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.sig (sig₀ : Op' → List Ty') : Op F Op' → List (Ty F Ty' int')
| .coe Op' => sig₀ Op' |>.map .coe
| .zero => []
| .one => []
| .add => [.f, .f]
| .sub => [.f, .f]
| .neg => [.f]
| .mul => [.f, .f]
| .div => [.f, .f]
| .inv => [.f]
| .zmul => [.coe int', .f]
| .pow => [.f, .coe int']
| .ofint => [.coe int']

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.returnTypes (returnTypes₀ : Op' → List Ty') : Op F Op' → List (Ty F Ty' int')
| .coe Op' => returnTypes₀ Op' |>.map .coe
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

/-- A map from operations to the kinds of their effects.
Native operations are pure, but this cannot be assumed of operations in the underlying dialect. -/
@[simp, reducible]
def Op.effectKind (effectKind₀ : Op' → EffectKind) : Op F Op' → EffectKind
| .coe op' => effectKind₀ op'
| _ => .pure

/-- A map from operations to their full type signatures. -/
@[simp, reducible]
def Op.signature (signature₀ : Op' → Signature Ty') : Op F Op' → Signature (Ty F Ty' int')
| op => {
  sig := op.sig (Signature.sig <| signature₀ .),
  returnTypes := op.returnTypes (Signature.returnTypes <| signature₀ .),
  regSig := []
  effectKind := op.effectKind (Signature.effectKind <| signature₀ .) }

end Flop

/-- The dialect, which wraps the underlying dialect `D`. -/
@[reducible]
def Flop (F : Type) (D : Dialect) (int : D.Ty) : Dialect where
Op := Flop.Op F D.Op
Ty := Flop.Ty F D.Ty int
m := D.m

namespace Flop

/-- The type signatures for the dialect. -/
instance : DialectSignature (Flop F D int) where
signature := Op.signature <| DialectSignature.signature

/-- Coerces an expression from the underlying dialect. -/
def coeExpr (e : Expr D (lowerCtxt Γ) eff' tys') : Expr (Flop F D int) Γ eff' (tys'.map .coe) :=
  Expr.mk
    (.coe e.op)
    (by simp[DialectSignature.returnTypes, signature, e.ty_eq])
    (by simp[DialectSignature.effectKind, signature]; exact e.eff_le)
    sorry
    sorry

/-- Coerces an expression bundled with its type and effects from the underlying dialect. -/
def coeSumExpr : (Σ eff ty, Expr D (lowerCtxt Γ) eff ty) → (Σ eff ty, Expr (Flop F D int) Γ eff ty)
| ⟨eff', tys', e⟩ => ⟨eff', tys'.map .coe, coeExpr e⟩

/-- The semantics for the dialect. -/
instance : DialectDenote (Flop F D int) where
denote
| .coe op', arg, _ => sorry
| .zero, _, _ => [0]ₕ
| .one, _, _ => [1]ₕ
| .add, arg, _ => [(fun args => args.1 + args.2) arg.toPair]ₕ
| .sub, arg, _ => [(fun args => args.1 - args.2) arg.toPair]ₕ
| .neg, arg, _ => [-arg.toSingle]ₕ
| .mul, arg, _ => [(fun args => args.1 * args.2) arg.toPair]ₕ
| .div, arg, _ => [(fun args => args.1 * args.2⁻¹) arg.toPair]ₕ
| .inv, arg, _ => [arg.toSingle⁻¹]ₕ
| .zmul, arg, _ => [(fun args => (denote_int D.Ty ▸ args.1 : ℤ) • args.2) arg.toPair]ₕ
| .pow, arg, _ => [(fun args => args.1 ^ (denote_int D.Ty ▸ args.2 : ℤ)) arg.toPair]ₕ
| .ofint, arg, _ => [(denote_int D.Ty ▸ arg.toSingle : ℤ)]ₕ

/-- The pretty printer for the dialect. -/
instance : DialectPrint (Flop F D int) where
printTy
| .coe ty' => DialectPrint.printTy ty'
| .f => "field.elem"
printOpName
| .coe op' => DialectPrint.printOpName op'
| .zero => "field.zero"
| .one => "field.one"
| .add => "field.add"
| .sub => "field.sub"
| .neg => "field.neg"
| .mul => "field.mul"
| .div => "field.div"
| .inv => "field.inv"
| .zmul => "field.zmul"
| .pow => "field.pow"
| .ofint => "field.ofint"
printAttributes
| .coe op' => DialectPrint.printAttributes op'
| _ => ""
printReturn _ := "return"--DialectPrint.printReturn <| tys.filterMap Ty.lower
dialectName := s!"Flop({DialectPrint.dialectName D})"

local instance : ToString (Flop F D int).Ty :=
  DialectPrint.instToStringTy

/-- The parser for the dialect from an MLIR AST. -/
instance : DialectParse (Flop F D int) 0 where
mkTy
| .undefined "field.elem" => return .f
| tyName => return .coe <| ←P.mkTy tyName
mkExpr Γ opStx := match opStx.name with
| "field.zero" => opStx.mkExprOf Γ .zero
| "field.one" => opStx.mkExprOf Γ .one
| "field.add" => opStx.mkExprOf Γ .add
| "field.sub" => opStx.mkExprOf Γ .sub
| "field.neg" => opStx.mkExprOf Γ .neg
| "field.mul" => opStx.mkExprOf Γ .mul
| "field.div" => opStx.mkExprOf Γ .div
| "field.inv" => opStx.mkExprOf Γ .inv
| "field.zmul" => opStx.mkExprOf Γ .zmul
| "field.pow" => opStx.mkExprOf Γ .pow
| "field.ofint" => opStx.mkExprOf Γ .ofint
| _ => do return coeSumExpr <| ←P.mkExpr (lowerCtxt Γ) opStx
isValidReturn _ opStx := return opStx.name = "return"--P.isValidReturn (lowerCtxt Γ) opStx

/-- An identifier for a `Flop` dialect.
Enforces that the underlying dialect has instances for parsing and denotational semantics. -/
structure FlopIdent where
F : Type
instField : Field F
D : Dialect
instDialectMonad : Monad D.m
instTyDecidableEq : DecidableEq D.Ty
instTyDenote : TyDenote D.Ty
instDialectSignature : DialectSignature D
instDialectDenote : DialectDenote D
instDialectPrint : DialectPrint D
instDialectParse : DialectParse D 0
int : D.Ty

abbrev FlopIdent.MkFlop (flop : FlopIdent) : Dialect :=
  Flop flop.F flop.D flop.int

instance (flop : FlopIdent) : Field flop.F :=
  flop.instField

instance (flop : FlopIdent) : Monad flop.D.m :=
  flop.instDialectMonad

instance (flop : FlopIdent) : DecidableEq flop.D.Ty :=
  flop.instTyDecidableEq

instance (flop : FlopIdent) : TyDenote flop.D.Ty :=
  flop.instTyDenote

instance (flop : FlopIdent) : DialectSignature flop.D :=
  flop.instDialectSignature

instance (flop : FlopIdent) : DialectDenote flop.D :=
  flop.instDialectDenote

instance (flop : FlopIdent) : DialectPrint flop.D :=
  flop.instDialectPrint

instance (flop : FlopIdent) : DialectParse flop.D 0 :=
  flop.instDialectParse

open Qq in
elab "[field_ops" flopi:term " | " reg:mlir_region "]" : term => do
  let flop : Q(FlopIdent) ← elabTermEnsuringTypeQ flopi q(FlopIdent)
  SSA.elabIntoCom reg q($flop |>.MkFlop)

/- An example program in the dialect that adds `1` to itself in the field `ℤ/5ℤ`. -/

def flop : FlopIdent where
F := ZMod 5
instField := sorry
D := sorry
instDialectMonad := sorry
instTyDecidableEq := sorry
instTyDenote := sorry
instDialectSignature := sorry
instDialectDenote := sorry
instDialectPrint := sorry
instDialectParse := sorry
int := sorry

def program :=
  [field_ops flop | {
    %c1 = "field.one"() : () -> ! "field.elem"
    %c2 = "field.add"(%c1, %c1) : (! "field.elem", ! "field.elem") -> ! "field.elem"
    "return"(%c2) : (! "field.elem") -> ()
  }]

--#eval program

lemma denote_program : program.denote .nil = by exact [(2 : ZMod 5)]ₕ := by
  sorry

end Flop
