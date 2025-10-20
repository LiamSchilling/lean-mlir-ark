import SSA.Projects.FieldStructs.Field.Basic

/-!
# Vector Dialect

Defines a dialect `Vec` for coordinate-representation vectors with components from a field.

Dialects for polynomials will lower to `Vec`:
- Univariate polynomials: `FieldStructs\UniPoly\Basic.lean`
- Multilinear polynomials: `FieldStructs\MLPoly\Basic.lean`
-/

namespace Vec

open LeanMLIR

variable {F : Type} [Field F]

end Vec
