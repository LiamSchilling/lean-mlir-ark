import SSA.Projects.FieldStructs.Vector.Basic
import SSA.Projects.FieldStructs.Field.Basic

/-!
# Lowering Vector Dialect to a Tensor Dialect

Since `Vec` depends on the underlying dialect `Fld` for algebra over a field,
the lowering from `Vec` to a tensor dialect will depend
on a lowering from `Fld` to an underlying integer dialect.
In this way, `Vec` may be lowered generically,
with the underlying field logic specified by the `Fld` lowering.
-/

namespace Vec

open LeanMLIR

variable {F : Type} [Field F]

end Vec
