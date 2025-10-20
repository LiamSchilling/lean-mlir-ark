import SSA.Projects.FieldStructs.Field.Basic

/-!
# Multilinear Polynomial Dialect

Defines a dialect `MLPoly` for multilinear polynomials over a field.
The type system enforces two distinct representations whose members are semantically polynomials:
- coefficients: a map from monomials
  to their coefficients.
- evaluations: a map from a finite set of points
  (specified at the global level in the dialect)
  to their evaluations.
-/

namespace MLPoly

open LeanMLIR

variable {F : Type} [Field F]

end MLPoly
