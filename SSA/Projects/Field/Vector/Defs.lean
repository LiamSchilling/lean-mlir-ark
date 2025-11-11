import SSA.Projects.Field.Flop.Defs

/-!
# Vector Dialect

Defines a dialect `Vec` for coordinate-representation vectors with components from a field.

Dialects for polynomials will lower to `Vec`:
- Univariate polynomials: `Field\UniPoly\Basic.lean`
- Multilinear polynomials: `Field\MLPoly\Basic.lean`
-/

open LeanMLIR

variable {F : Type} [Field F]

namespace Vec

end Vec
