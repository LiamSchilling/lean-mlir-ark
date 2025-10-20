import SSA.Projects.FieldStructs.Field.Basic

/-!
# Lowering Finite-Field Dialects to an Integer Dialect

Lowers `Fld` to an integer dialect in the special case that the field is `GF(p ^ n)`.

Extension dialects based on `Fld` will use this lowering
to scaffold their lowering to a tensor dialect.
-/

namespace Fld

open LeanMLIR

variable {F : Type} [Field F]

end Fld
