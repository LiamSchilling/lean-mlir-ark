import SSA.Projects.Field.Util
import Mathlib.Data.ZMod.Basic

/-!
# Field Dialect

Defines a wrapper dialect `Flop` for algebra over a field.
`Flop` requires that the underlying dialect contains an integer type.
It is up to the underlying dialect to implement integer operations.

Wrapper dialects are not an unusual way to design dialects
that are amenable to composition.
Another important wrapper dialect is `SSA\Scf`,
which attaches structured control flow mechanisms to an underlying dialect.

This dialect will be the basis for a number of extension dialects
for objects that contain field elements:
- Vectors: `Field\Vector\Basic.lean`
- Univariate polynomials: `Field\UniPoly\Basic.lean`
- Multilinear polynomials: `Field\MLPoly\Basic.lean`

Instances of `Flop` with specialized fields should be lowered to an integer dialect.
This will allow the extension dialects to generically lower to a tensor dialect
given any specific lowering from `Flop` to the integer dialect.
-/

open LeanMLIR MLIR.AST

variable {F : Type} [Field F]

variable {Ty' Op' : Type} [DecidableEq Ty'] [TyDenote Ty']
variable {int' : Ty'}

variable {D : Dialect} [Monad D.m] [DecidableEq D.Ty] [TyDenote D.Ty]
variable {int : D.Ty} {raiseInt : ⟦int⟧ → ℤ}
variable [DialectSignature D] [DialectDenote D] [DialectPrint D]
variable [T : TransformTy D 0] [E : TransformExpr D 0] [R : TransformReturn D 0]

namespace Flop

/-- The types in the dialect:
- `raise`: a type in the underlying dialect
- `raise int'`: the integer type in the underlying dialect
- `f`: field members -/
inductive Ty (F Ty' : Type) (int' : Ty') where
| raise : Ty' → Ty F Ty' int'
| f

/-- Lowers a type to the underlying dialect,
with `none` when the type is not from the underlying dialect. -/
def Ty.lower : Ty F Ty' int' → Option Ty'
| .raise ty' => some ty'
| _ => none

omit [Field F] [DecidableEq Ty'] [TyDenote Ty'] in
@[simp]
lemma ty_lower_raise_eq : ∀ {ty'}, Ty.lower (.raise ty' : Ty F Ty' int') = some ty' := by
  simp [Ty.lower]

omit [Field F] [DecidableEq Ty'] [TyDenote Ty'] in
@[simp]
lemma ty_lower_raise_some : (Ty.lower : Ty F Ty' int' → Option Ty') ∘ .raise = some := by
  ext; simp

instance : DecidableEq (Ty F Ty' int')
| .raise a, .raise b => decidable_of_iff (a = b) <| by simp
| .raise _, .f => isFalse <| by intro; contradiction
| .f, .raise _ => isFalse <| by intro; contradiction
| .f, .f => isTrue rfl

/-- A map from types in the dialect to the Lean types of their semantic interpretations.
The semantic interpretations of types from the underlying dialect are preserved. -/
@[simp, reducible]
instance : TyDenote (Ty F Ty' int') where
toType
| .raise ty' => ⟦ty'⟧
| .f => F

/-- The operations in the dialect:
- `raise`: an operation in the underlying dialect
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
| raise : Op' → Op F Op'
| zero | one
| add | sub | neg
| mul | div | inv
| zmul | pow | ofint

/-- Lowers an operation to the underlying dialect,
with `none` when the operation is not from the underlying dialect. -/
def Op.lower : Op F Op' → Option Op'
| .raise ty' => some ty'
| _ => none

omit [Field F] in
@[simp]
lemma op_lower_raise_eq : ∀ {op'}, Op.lower (.raise op' : Op F Op') = some op' := by
  simp [Op.lower]

omit [Field F] in
@[simp]
lemma op_lower_raise_some : (Op.lower : Op F Op' → Option Op') ∘ .raise = some := by
  ext; simp

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.sig (sig' : Op' → List Ty') : Op F Op' → List (Ty F Ty' int')
| .raise op' => sig' op' |>.map .raise
| .zero => []
| .one => []
| .add => [.f, .f]
| .sub => [.f, .f]
| .neg => [.f]
| .mul => [.f, .f]
| .div => [.f, .f]
| .inv => [.f]
| .zmul => [.raise int', .f]
| .pow => [.f, .raise int']
| .ofint => [.raise int']

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.returnTypes (returnTypes' : Op' → List Ty') : Op F Op' → List (Ty F Ty' int')
| .raise op' => returnTypes' op' |>.map .raise
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

/-- A map from operations to the signatures of their attached regions.
Native operations have no regions. -/
@[simp, reducible]
def Op.regSig (regSig' : Op' → RegionSignature Ty') : Op F Op' → RegionSignature (Ty F Ty' int')
| .raise op' => regSig' op' |>.map .raise
| _ => []

/-- A map from operations to the kinds of their effects.
Native operations are pure. -/
@[simp, reducible]
def Op.effectKind (effectKind' : Op' → EffectKind) : Op F Op' → EffectKind
| .raise op' => effectKind' op'
| _ => .pure

/-- A map from operations to their full type signatures. -/
@[simp, reducible]
def Op.signature (signature' : Op' → Signature Ty') : Op F Op' → Signature (Ty F Ty' int')
| op => {
  sig := op.sig (Signature.sig <| signature' .),
  returnTypes := op.returnTypes (Signature.returnTypes <| signature' .),
  regSig := op.regSig (Signature.regSig <| signature' .),
  effectKind := op.effectKind (Signature.effectKind <| signature' .) }

end Flop

/-- The dialect, which wraps the underlying dialect `D`. -/
@[reducible]
def Flop (F : Type) (D : Dialect) [TyDenote D.Ty] (int : D.Ty) (_ : ⟦int⟧ → ℤ) : Dialect where
Ty := Flop.Ty F D.Ty int
Op := Flop.Op F D.Op
m := D.m

namespace Flop

/-- The type signatures for the dialect. -/
@[simp, reducible]
instance : DialectSignature (Flop F D int raiseInt) where
signature := Op.signature DialectSignature.signature

section Maps

mutual

/-- Transform an expression to any
mapped context `Γ.map f` and mapped type universe `tys.map f`. -/
def raiseExprToMap
    (expr : Expr D Γ' eff tys') :
    Expr (Flop F D int raiseInt) (Γ'.map .raise) eff (tys'.map .raise) :=
  Expr.mk
    (.raise expr.op)
    (by simp_rw [expr.ty_eq]; rfl)
    expr.eff_le
    (expr.args.map' Ty.raise fun _ => .toMap)
    (expr.regArgs.map'
      (fun (Γ', tys') => (Γ'.map Ty.raise, tys'.map Ty.raise))
      (fun _ => raiseComToMap) )
decreasing_by sorry

/-- Transform a computation to any
mapped context `Γ.map f` and mapped type universe `tys.map f`. -/
def raiseComToMap
    (com : Com D Γ' eff tys') :
    Com (Flop F D int raiseInt) (Γ'.map .raise) eff (tys'.map .raise) :=
  match com with
  | Com.rets vars => Com.rets <| vars.map' Ty.raise fun _ => .toMap
  | Com.var expr body => Com.var
    (raiseExprToMap expr)
    (Ctxt.map_append _ _ _ ▸ raiseComToMap
      body )

end

/-- Transform an expression from any
filter-mapped context `Γ.filterMap f` and filter-mapped type universe `tys.filterMap f`. -/
def raiseExprFromFilterMap
    (expr : Expr D (Γ.filterMap Ty.lower) eff tys') :
    Expr (Flop F D int raiseInt) Γ eff (tys'.map .raise) :=
  Expr.mk
    (.raise expr.op)
    (by simp_rw [expr.ty_eq]; rfl)
    expr.eff_le
    (expr.args.map' Ty.raise fun _ => .fromFilterMap ty_lower_raise_eq)
    (expr.regArgs.map'
      (fun (Γ', tys') => (Γ'.map Ty.raise, tys'.map Ty.raise))
      (fun _ => raiseComToMap) )

/-- Transform a computation from any
filter-mapped context `Γ.filterMap f` and filter-mapped type universe `tys.filterMap f`. -/
def raiseComFromFilterMap
    (com : Com D (Γ.filterMap Ty.lower) eff tys') :
    Com (Flop F D int raiseInt) Γ eff (tys'.map .raise) :=
  match com with
  | Com.rets vars => Com.rets <| vars.map' Ty.raise fun _ => .fromFilterMap ty_lower_raise_eq
  | Com.var expr body => Com.var
    (raiseExprFromFilterMap expr)
    (raiseComFromFilterMap <| Ctxt.filterMap_append _ _ _ ▸
      Ctxt.filterMap_map ▸ ty_lower_raise_some ▸ Ctxt.filterMap_some ▸ body )
decreasing_by sorry

/-- Transform an expression bundled with its types and effect kind to any
mapped context `Γ.map f` and mapped type universe `tys.map f`. -/
def raiseSumExprToMap :
    (Σ eff tys', Expr D Γ' eff tys') →
    (Σ eff tys', Expr (Flop F D int raiseInt) (Γ'.map .raise) eff tys')
| ⟨eff, tys', expr⟩ => ⟨eff, tys'.map .raise, raiseExprToMap expr⟩

/-- Transform a computation bundled with its types and effect kind to any
mapped context `Γ.map f` and mapped type universe `tys.map f`. -/
def raiseSumComToMap :
    (Σ eff tys', Com D Γ' eff tys') →
    (Σ eff tys', Com (Flop F D int raiseInt) (Γ'.map .raise) eff tys')
| ⟨eff, tys', com⟩ => ⟨eff, tys'.map .raise, raiseComToMap com⟩

/-- Transform an expression bundled with its types and effect kind from any
filter-mapped context `Γ.filterMap f` and filter-mapped type universe `tys.filterMap f`. -/
def raiseSumExprFromFilterMap :
    (Σ eff tys', Expr D (Γ.filterMap Ty.lower) eff tys') →
    (Σ eff tys', Expr (Flop F D int raiseInt) Γ eff tys')
| ⟨eff, tys', expr⟩ => ⟨eff, tys'.map .raise, raiseExprFromFilterMap expr⟩

/-- Transform a computation bundled with its types and effect kind from any
filter-mapped context `Γ.filterMap f` and filter-mapped type universe `tys.filterMap f`. -/
def raiseSumComFromFilterMap :
    (Σ eff tys', Com D (Γ.filterMap Ty.lower) eff tys') →
    (Σ eff tys', Com (Flop F D int raiseInt) Γ eff tys')
| ⟨eff, tys', com⟩ => ⟨eff, tys'.map .raise, raiseComFromFilterMap com⟩

end Maps

/-- The semantics for the dialect. -/
instance : DialectDenote (Flop F D int raiseInt) where
denote
| .raise op', arg, _ => do
  let res ← DialectDenote.denote op' sorry sorry
  return res.map' Ty.raise fun _ => id
| .zero, _, _ => [0]ₕ
| .one, _, _ => [1]ₕ
| .add, arg, _ => [(fun args => args.1 + args.2) arg.toPair]ₕ
| .sub, arg, _ => [(fun args => args.1 - args.2) arg.toPair]ₕ
| .neg, arg, _ => [-arg.toSingle]ₕ
| .mul, arg, _ => [(fun args => args.1 * args.2) arg.toPair]ₕ
| .div, arg, _ => [(fun args => args.1 * args.2⁻¹) arg.toPair]ₕ
| .inv, arg, _ => [arg.toSingle⁻¹]ₕ
| .zmul, arg, _ => [(fun args => raiseInt args.1 • args.2) arg.toPair]ₕ
| .pow, arg, _ => [(fun args => args.1 ^ raiseInt args.2) arg.toPair]ₕ
| .ofint, arg, _ => [raiseInt arg.toSingle]ₕ

/-- The pretty printer for the dialect. -/
instance : DialectPrint (Flop F D int raiseInt) where
printTy
| .raise ty' => DialectPrint.printTy ty'
| .f => "field.elem"
printOpName
| .raise op' => DialectPrint.printOpName op'
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
| .raise op' => DialectPrint.printAttributes op'
| _ => ""
printReturn tys := DialectPrint.printReturn <| tys.filterMap Ty.lower
printFunc tys := DialectPrint.printFunc <| tys.filterMap Ty.lower
dialectName := s!"Flop({DialectPrint.dialectName D})"

local instance : ToString (Flop F D int raiseInt).Ty :=
  DialectPrint.instToStringTy

/-- Part of the parser for the dialect from an MLIR AST. -/
instance : TransformTy (Flop F D int raiseInt) 0 where
mkTy
| .undefined "field.elem" => return .f
| tyName => return .raise <| ←T.mkTy tyName

/-- Part of the parser for the dialect from an MLIR AST. -/
instance : TransformExpr (Flop F D int raiseInt) 0 where
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
| _ => do return raiseSumExprFromFilterMap <| ←E.mkExpr (Γ.filterMap Ty.lower) opStx

/-- Part of the parser for the dialect from an MLIR AST. -/
instance : TransformReturn (Flop F D int raiseInt) 0 where
mkReturn Γ opStx := do return raiseSumComFromFilterMap <| ←R.mkReturn (Γ.filterMap Ty.lower) opStx

/-- An identifier for a `Flop` dialect.
Enforces that the underlying dialect has instances for parsing and denotational semantics. -/
structure FlopIdent where
F : Type
instField : Field F := by infer_instance
D : Dialect
instDialectMonad : Monad D.m := by infer_instance
instTyDecidableEq : DecidableEq D.Ty := by infer_instance
instTyDenote : TyDenote D.Ty := by infer_instance
instDialectSignature : DialectSignature D := by infer_instance
instDialectDenote : DialectDenote D := by infer_instance
instDialectPrint : DialectPrint D := by infer_instance
instTransformTy : TransformTy D 0 := by infer_instance
instTransformExpr : TransformExpr D 0 := by infer_instance
instTransformReturn : TransformReturn D 0 := by infer_instance
int : D.Ty
raiseInt : ⟦int⟧ → ℤ

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

instance (flop : FlopIdent) : TransformTy flop.D 0 :=
  flop.instTransformTy

instance (flop : FlopIdent) : TransformExpr flop.D 0 :=
  flop.instTransformExpr

instance (flop : FlopIdent) : TransformReturn flop.D 0 :=
  flop.instTransformReturn

abbrev FlopIdent.MkFlop (flop : FlopIdent) : Dialect :=
  Flop flop.F flop.D flop.int flop.raiseInt

open Qq in
elab "[field_ops" flopi:term " | " reg:mlir_region "]" : term => do
  let flop : Q(FlopIdent) ← elabTermEnsuringTypeQ flopi q(FlopIdent)
  SSA.elabIntoCom reg q($flop |>.MkFlop)

end Flop
