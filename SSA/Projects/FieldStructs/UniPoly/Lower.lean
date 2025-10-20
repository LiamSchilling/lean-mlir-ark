import SSA.Projects.FieldStructs.UniPoly.Basic
import SSA.Projects.FieldStructs.Vector.Basic

/-!
# Lowering Univariate Polynomial Dialect to a Vector Dialect
-/

namespace UniPoly

open LeanMLIR

variable {F : Type} [Field F]

namespace UniPoly
