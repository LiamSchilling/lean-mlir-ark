import SSA.Projects.Field.Flop.Basic

/-!
# Lowering Finite-Field Dialects to an Integer Dialect

Lowers `Flop` to an integer dialect in the special case that the field is `GF(p ^ n)`.

Extension dialects based on `Flop` will use this lowering
to scaffold their lowering to a tensor dialect.
-/

namespace Flop

open LeanMLIR

variable {F : Type} [Field F]

end Flop
