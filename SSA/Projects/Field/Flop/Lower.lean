import SSA.Projects.Field.Flop.Basic
import LeanMLIR.Dialects.LLVM.Syntax
import Mathlib.Algebra.Field.ZMod

/-!
# Lowering Finite-Field Dialects to an Integer Dialect

Lowers `Flop` to `LLVM` in the special case that the field is `ℤ/pℤ`.

Extension dialects based on `Flop` will use this lowering
to scaffold their lowering to a tensor dialect.
-/

open LeanMLIR InstCombine

variable {p w : ℕ} [Fact p.Prime]

namespace Flop

/-- Identifies a `Flop` dialect that attaches the field `ℤ/pℤ` to `LLVM`.
`LLVM` bitvectors of width `w` are taken to be the integer type in the new dialect. -/
def flopZModOnLLVM (p w : ℕ) [Fact p.Prime] : FlopIdent where
F := ZMod p
D := LLVM
int := .bitvec w
raiseInt := by
  dsimp only [TyDenote.toType]
  exact fun X => match X with
  | .poison => 0 --this may become problematic
  | .value x => x.toInt

/- Getting an ERROR I don't understand

The source where it is thrown can apparently can be found in `LeanMLIR\MLIRSyntax\EDSL.lean`.

instance : Fact (5).Prime := by decide
def program :=
  [field_ops flopZModOnLLVM 5 9 | {
    %c2 = "llvm.mlir.constant"(){value = 8} : () -> i64
    "llvm.return"(%c2) : (i64) -> ()
  }]
-/

/- In this lowering, it will turn out to be bad that the lowered context is filtered.
Instead, data from `Flop` must itself be lowered to a representative type `f` in `LLVM`.
The way to design this is unclear, since it will be impossible to disambiguate
variables of type `f` that were lowered from a `Flop` field element
from variables of type `f` that are true `LLVM` values of type `f`. -/

def lower_flopZModOnLLVM :
    Com (flopZModOnLLVM p w).MkFlop Γ eff ty → Com LLVM (Γ.filterMap Ty.lower) eff ty'
| .var (Expr.mk (.raise op') ty_eq eff_le _ _) body => sorry
| .var (Expr.mk .zero _ _ _ _) body => sorry
| .var (Expr.mk .one _ _ _ _) body => sorry
| .var (Expr.mk .add _ _ _ _) body => sorry
| .var (Expr.mk .sub _ _ _ _) body => sorry
| .var (Expr.mk .neg _ _ _ _) body => sorry
| .var (Expr.mk .mul _ _ _ _) body => sorry
| .var (Expr.mk .div _ _ _ _) body => sorry
| .var (Expr.mk .inv _ _ _ _) body => sorry
| .var (Expr.mk .zmul _ _ _ _) body => sorry
| .var (Expr.mk .pow _ _ _ _) body => sorry
| .var (Expr.mk .ofint _ _ _ _) body => sorry
| .rets _ => sorry

def llvm_program :=
  [llvm()| {
    ^bb0(%c1 : i64):
    %c2 = "llvm.mlir.constant"(){value = 8} : () -> i64
    "llvm.return"(%c1) : (i64) -> ()
  }]

def my_denote : llvm_program.denote (.cons (PoisonOr.value 8) .nil) = [.value 8]ₕ :=
  rfl

#eval llvm_program

end Flop
