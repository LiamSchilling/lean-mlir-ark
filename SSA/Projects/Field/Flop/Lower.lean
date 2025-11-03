import SSA.Projects.Field.Flop.Basic
import LeanMLIR.Dialects.LLVM.Syntax

/-!
# Lowering Finite-Field Dialects to an Integer Dialect

Lowers `Flop` to `LLVM` in the special case that the field is `ℤ/pℤ`.

Extension dialects based on `Flop` will use this lowering
to scaffold their lowering to a tensor dialect.
-/

open LeanMLIR InstCombine

variable {p w : ℕ} [Fact (Prime p)]

namespace Flop

/-- Identifies a `Flop` dialect that attaches the field `ℤ/pℤ` to `LLVM`.
`LLVM` bitvectors of width `w` are taken to be the integer type in the new dialect. -/
def flop_zmod_on_llvm (p w : ℕ) [Fact (Prime p)] : FlopIdent where
F := ZMod p
instField := sorry
D := LLVM
int := .bitvec w
raiseInt := by
  dsimp only [TyDenote.toType]
  exact fun X => match X with
  | .poison => 0 --this may become problematic
  | .value x => x.toInt

/- Getting an ERROR I don't understand

The source where it is thrown
can apparently can be found in `LeanMLIR\MLIRSyntax\EDSL.lean`.

instance : Fact (Prime 5) := by decide
def program :=
  [field_ops flop_zmod_on_llvm 5 9 | {
    %c2 = "llvm.mlir.constant"() {value = 8} : () -> i64
    "llvm.return"(%c2) : (i64) -> ()
  }]
-/

end Flop
