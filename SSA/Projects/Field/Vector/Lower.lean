import SSA.Projects.Field.Flop.Basic

/-!
# Lowering Vector Dialect to a Tensor Dialect

Since `Vec` depends on the underlying dialect `Flop` for algebra over a field,
the lowering from `Vec` to a tensor dialect will depend
on a lowering from `Flop` to an underlying integer dialect.
In this way, `Vec` may be lowered generically,
with the underlying field logic specified by the `Flop` lowering.
-/

namespace Vec

open LeanMLIR

variable {F : Type} [Field F]

end Vec
