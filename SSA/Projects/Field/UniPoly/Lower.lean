import SSA.Projects.Field.UniPoly.Basic
import SSA.Projects.Field.Vector.Basic

/-!
# Lowering Univariate Polynomial Dialect to a Vector Dialect
-/

namespace UniPoly

open LeanMLIR

variable {F : Type} [Field F]

namespace UniPoly
