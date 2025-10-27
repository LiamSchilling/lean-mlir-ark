import SSA.Projects.Field.Flop.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Univariate Polynomial Dialect

Defines a dialect `UniPoly` for univariate polynomials over a field.
The type system enforces two distinct representations whose members are semantically polynomials:
- coefficients: a map from monomials
  to their coefficients.
- evaluations: a map from a finite set of points
  (specified at the global level in the dialect)
  to their evaluations.
-/

namespace UniPoly

open LeanMLIR Polynomial

variable {F : Type} [Field F] {nodes : Finset F} [Nonempty nodes]

/-- The types of representations of less-than-`#nodes`-degree polynomials in the dialect:
- `coeffs`: the `#nodes`-many coefficients representation
- `evals`: the evaluation for each point in `nodes` representation -/
inductive PolyTy [Field F] (nodes : Finset F) [Nonempty nodes] where
| coeffs
| evals

instance : DecidableEq (PolyTy nodes)
| .coeffs, .coeffs => isTrue rfl
| .coeffs, .evals => isFalse (by intro; contradiction)
| .evals, .coeffs => isFalse (by intro; contradiction)
| .evals, .evals => isTrue rfl

instance : ToString (PolyTy nodes) where
toString
| .coeffs => "coeffs"
| .evals => "evals"

/-- The types in the dialect:
- `scalar`: a member of the field `F`
- `poly t`: a less-than-`#nodes`-degree polynomial using the `t` representation -/
inductive Ty (nodes : Finset F) [Nonempty nodes] where
| scalar : Ty nodes
| poly : PolyTy nodes → Ty nodes

instance : DecidableEq (Ty nodes)
| .scalar, .scalar => isTrue rfl
| .scalar, .poly _ => isFalse (by intro; contradiction)
| .poly _, .scalar => isFalse (by intro; contradiction)
| .poly t₁, .poly t₂ => @decidable_of_decidable_of_iff (t₁ = t₂) _ _ (by simp)

instance : ToString (Ty nodes) where
toString
| .scalar => "scalar"
| .poly t => s!"{t}"

/-- A map from types in the dialect to the Lean types of their semantic interpretations.
All members of `.poly t` are semantically polynomials regardless of `t`. -/
instance : TyDenote (Ty nodes) where
toType
| .scalar => F
| .poly _ => F[X]

/-- The operations in the dialect:
- `add t`: adds members of the type `t`
- `sub t`: subtracts members of the type `t`
- `smul t`: multiplication by a scalar for a member of the type `t`
- `sdiv t`: division by a scalar for a member of the type `t`
- `eval t`: evaluation of a polynomial using the `t` representation
- `const t v`: a constant of type `t` whose value is `v` -/
inductive Op (nodes : Finset F) [Nonempty nodes] where
| add : Ty nodes → Op nodes
| sub : Ty nodes → Op nodes
| smul : Ty nodes → Op nodes
| sdiv : Ty nodes → Op nodes
| eval : PolyTy nodes → Op nodes
| tocoeffs : Op nodes
| toevals : Op nodes
| const : F → Op nodes

/-- A map from operations to the types of their inputs. -/
@[simp, reducible]
def Op.sig : Op nodes → List (Ty nodes)
| .add t => [t, t]
| .sub t => [t, t]
| .smul t => [.scalar, t]
| .sdiv t => [t, .scalar]
| .eval t => [.poly t, .scalar]
| .tocoeffs => [.poly .evals]
| .toevals => [.poly .coeffs]
| .const _ => []

/-- A map from operations to the types of their outputs. -/
@[simp, reducible]
def Op.returnTypes : Op nodes → List (Ty nodes)
| .add t => [t]
| .sub t => [t]
| .smul t => [t]
| .sdiv t => [t]
| .eval _ => [.scalar]
| .tocoeffs => [.poly .coeffs]
| .toevals => [.poly .evals]
| .const _ => [.scalar]

/-- A map from operations to their full type signatures. -/
@[simp, reducible]
def Op.signature : Op nodes → Signature (Ty nodes)
| o => { sig := o.sig, returnTypes := o.returnTypes, regSig := [] }

/-- The dialect. -/
abbrev Ark (nodes : Finset F) [Nonempty nodes] : Dialect where
Op := Op nodes
Ty := Ty nodes

instance : DialectSignature (Ark nodes) where
signature := Op.signature

instance [ToString F] : DialectPrint (Ark nodes) where
printTy := toString
printOpName
| .add t => s!"add<{t}>"
| .sub t => s!"sub<{t}>"
| .smul t => s!"smul<{t}>"
| .sdiv t => s!"sdiv<{t}>"
| .eval t => s!"eval<{t}>"
| .tocoeffs => "tocoeffs"
| .toevals => "toevals"
| .const _ => "const"
printAttributes
| .const v => s!"\{value = {v} : scalar}"
| _ => ""
dialectName := "Ark"
printReturn _ := "return"

/-- The semantics for the dialect.
For polynomials from `.poly t`, the representation `t` is semantically irrelevant. -/
noncomputable instance : DialectDenote (Ark nodes) where
denote
| .add .scalar, arg, _ => [(fun args => args.1 + args.2) arg.toPair]ₕ
| .add <| .poly _, arg, _ => [(fun args => args.1 + (args.2 : F[X])) arg.toPair]ₕ
| .sub .scalar, arg, _ => [(fun args => args.1 - args.2) arg.toPair]ₕ
| .sub <| .poly _, arg, _ => [(fun args => args.1 - (args.2 : F[X])) arg.toPair]ₕ
| .smul .scalar, arg, _ => [(fun args => args.1 • args.2) arg.toPair]ₕ
| .smul <| .poly _, arg, _ => [(fun args => args.1 • (args.2 : F[X])) arg.toPair]ₕ
| .sdiv .scalar, arg, _ => [(fun args => args.1 • args.2⁻¹) arg.toPair]ₕ
| .sdiv <| .poly _, arg, _ => [(fun args => args.2⁻¹ • (args.1 : F[X])) arg.toPair]ₕ
| .eval _, arg, _ => [(fun args => args.1.eval args.2) arg.toPair]ₕ
| .tocoeffs, arg, _ => [arg.toSingle]ₕ
| .toevals, arg, _ => [arg.toSingle]ₕ
| .const v, _, _ => [v]ₕ

instance [Coe ℕ F] : DialectParse (Ark nodes) 0 where
mkTy
| .int .Signless 32 => return .scalar
| .undefined "coeffs" => return .poly .coeffs
| .undefined "evals" => return .poly .evals
| _ => throw .unsupportedType
mkExpr Γ opStx := do opStx.mkExprOf Γ <|← match opStx.name with
| "add<scalar>" => return .add .scalar
| "add<coeffs>" => return .add <| .poly .coeffs
| "add<evals>" => return .add <| .poly .evals
| "sub<scalar>" => return .sub .scalar
| "sub<coeffs>" => return .sub <| .poly .coeffs
| "sub<evals>" => return .sub <| .poly .evals
| "smul<scalar>" => return .smul .scalar
| "smul<coeffs>" => return .smul <| .poly .coeffs
| "smul<evals>" => return .smul <| .poly .evals
| "sdiv<scalar>" => return .sdiv .scalar
| "sdiv<coeffs>" => return .sdiv <| .poly .coeffs
| "sdiv<evals>" => return .sdiv <| .poly .evals
| "eval<coeffs>" => return .eval .coeffs
| "eval<evals>" => return .eval .evals
| "tocoeffs" => return .tocoeffs
| "toevals" => return .toevals
| "const" => return .const <| Coe.coe <| (←opStx.getIntAttr "value").1.toNat
| opName => throw <| .unsupportedOp opName
isValidReturn _ opStx := return opStx.name == "return"

open Qq in
elab "[unipoly"
    Fi:term ","
    hfield:term ","
    nodesi:term ","
    hnonempty:term ","
    natintoF:term " | " reg:mlir_region "]" : term => do
  let F : Q(Type) ← elabTermEnsuringTypeQ Fi q(Type)
  let _ ← elabTermEnsuringTypeQ hfield q(Field $F)
  let nodes : Q(Finset $F) ← elabTermEnsuringTypeQ nodesi q(Finset $F)
  let _ ← elabTermEnsuringTypeQ hnonempty q(Nonempty $nodes)
  let _ ← elabTermEnsuringTypeQ natintoF q(Coe ℕ $F)
  SSA.elabIntoCom reg q(Ark $nodes)

/-- An example program in the dialect that adds `1` and `2` in the field `ℤ/5ℤ` -/
def programnodes : Finset (ZMod 5) := {-1, 2}
instance : Field (ZMod 5) := sorry
instance : Nonempty programnodes := by simp [programnodes]
def program :=
  [unipoly ZMod 5, inferInstance, programnodes, inferInstance, { coe x := x } | {
    %c1 = "const"() {value = 1} : () -> i32
    %c2 = "const"() {value = 2} : () -> i32
    %c3 = "add<scalar>"(%c1, %c2) : (i32, i32) -> i32
    "return"(%c3) : (i32) -> ()
  }]

end UniPoly
