import LeanMLIR.Basic

/-!
# Algebraic Structures for Types in Dialects

This file is from an old design and will likely be removed.
-/

/-- A dialect with a type `t` of members from the monoid `M`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class AddCommMonoidDialect
    (M : Type) [AddCommMonoid M]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] where
  t : d.Ty
  nat : d.Ty
  zero : d.Op
  add : d.Op
  natmul : d.Op
  t_denote : (⟦t⟧ : Type) = M := by trivial
  nat_denote : (⟦nat⟧ : Type) = ℕ := by trivial
  zero_sig : S.sig zero = [] := by trivial
  zero_returnTypes : S.returnTypes zero = [t] := by trivial
  zero_pure : S.effectKind zero = .pure := by trivial
  add_sig : S.sig add = [t, t] := by trivial
  add_returnTypes : S.returnTypes add = [t] := by trivial
  add_pure : S.effectKind add = .pure := by trivial
  natmul_sig : S.sig natmul = [nat, t] := by trivial
  natmul_returnTypes : S.returnTypes natmul = [t] := by trivial
  natmul_pure : S.effectKind natmul = .pure := by trivial
  zero_denote :
    D.denote zero (zero_sig ▸ []ₕ) reg =
    zero_returnTypes ▸ zero_pure ▸ [t_denote ▸ 0]ₕ
  add_denote (a b : M) :
    D.denote add (add_sig ▸ [t_denote ▸ a, t_denote ▸ b]ₕ) reg =
    add_returnTypes ▸ add_pure ▸ [t_denote ▸ (a + b)]ₕ
  natmul_denote (n : ℕ) (a : M) :
    D.denote natmul (natmul_sig ▸ [nat_denote ▸ n, t_denote ▸ a]ₕ) reg =
    natmul_returnTypes ▸ natmul_pure ▸ [t_denote ▸ (n • a)]ₕ

/-- A dialect with a type `t` of members from the group `G`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class AddCommGroupDialect
    (G : Type) [AddCommGroup G]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] extends
    AddCommMonoidDialect G d where
  int : d.Ty
  sub : d.Op
  neg : d.Op
  intmul : d.Op
  int_denote : (⟦int⟧ : Type) = ℤ := by trivial
  sub_sig : S.sig sub = [t, t] := by trivial
  sub_returnTypes : S.returnTypes sub = [t] := by trivial
  sub_pure : S.effectKind sub = .pure := by trivial
  neg_sig : S.sig neg = [t] := by trivial
  neg_returnTypes : S.returnTypes neg = [t] := by trivial
  neg_pure : S.effectKind neg = .pure := by trivial
  intmul_sig : S.sig intmul = [int, t] := by trivial
  intmul_returnTypes : S.returnTypes intmul = [t] := by trivial
  intmul_pure : S.effectKind intmul = .pure := by trivial
  sub_denote (a b : G) :
    D.denote sub (sub_sig ▸ [t_denote ▸ a, t_denote ▸ b]ₕ) reg =
    sub_returnTypes ▸ sub_pure ▸ [t_denote ▸ (a - b)]ₕ
  neg_denote (a : G) :
    D.denote neg (neg_sig ▸ [t_denote ▸ a]ₕ) reg =
    neg_returnTypes ▸ neg_pure ▸ [t_denote ▸ -a]ₕ
  intmul_denote (n : ℤ) (a : G) :
    D.denote intmul (intmul_sig ▸ [int_denote ▸ n, t_denote ▸ a]ₕ) reg =
    intmul_returnTypes ▸ intmul_pure ▸ [t_denote ▸ (n • a)]ₕ

/-- A dialect with a type `t` of members from the monoid `M`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class CommMonoidDialect
    (M : Type) [CommMonoid M]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] where
  t : d.Ty
  nat : d.Ty
  one : d.Op
  mul : d.Op
  natpow : d.Op
  t_denote : (⟦t⟧ : Type) = M := by trivial
  nat_denote : (⟦nat⟧ : Type) = ℕ := by trivial
  one_sig : S.sig one = [] := by trivial
  one_returnTypes : S.returnTypes one = [t] := by trivial
  one_pure : S.effectKind one = .pure := by trivial
  mul_sig : S.sig mul = [t, t] := by trivial
  mul_returnTypes : S.returnTypes mul = [t] := by trivial
  mul_pure : S.effectKind mul = .pure := by trivial
  natpow_sig : S.sig natpow = [t, nat] := by trivial
  natpow_returnTypes : S.returnTypes natpow = [t] := by trivial
  natpow_pure : S.effectKind natpow = .pure := by trivial
  one_denote :
    D.denote one (one_sig ▸ []ₕ) reg =
    one_returnTypes ▸ one_pure ▸ [t_denote ▸ 1]ₕ
  mul_denote (a b : M) :
    D.denote mul (mul_sig ▸ [t_denote ▸ a, t_denote ▸ b]ₕ) reg =
    mul_returnTypes ▸ mul_pure ▸ [t_denote ▸ (a * b)]ₕ
  natpow_denote (a : M) (n : ℕ) :
    D.denote natpow (natpow_sig ▸ [t_denote ▸ a, nat_denote ▸ n]ₕ) reg =
    natpow_returnTypes ▸ natpow_pure ▸ [t_denote ▸ (a ^ n)]ₕ

/-- A dialect with a type `t` of members from the group `G`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class CommGroupDialect
    (G : Type) [CommGroup G]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] extends
    CommMonoidDialect G d where
  int : d.Ty
  div : d.Op
  inv : d.Op
  intpow : d.Op
  int_denote : (⟦int⟧ : Type) = ℤ := by trivial
  div_sig : S.sig div = [t, t] := by trivial
  div_returnTypes : S.returnTypes div = [t] := by trivial
  div_pure : S.effectKind div = .pure := by trivial
  inv_sig : S.sig inv = [t] := by trivial
  inv_returnTypes : S.returnTypes inv = [t] := by trivial
  inv_pure : S.effectKind inv = .pure := by trivial
  intpow_sig : S.sig intpow = [t, int] := by trivial
  intpow_returnTypes : S.returnTypes intmul = [t] := by trivial
  intpow_pure : S.effectKind intmul = .pure := by trivial
  div_denote (a b : G) :
    D.denote div (div_sig ▸ [t_denote ▸ a, t_denote ▸ b]ₕ) reg =
    div_returnTypes ▸ div_pure ▸ [t_denote ▸ (a * b⁻¹)]ₕ
  inv_denote (a : G) :
    D.denote inv (inv_sig ▸ [t_denote ▸ a]ₕ) reg =
    inv_returnTypes ▸ inv_pure ▸ [t_denote ▸ a⁻¹]ₕ
  intpow_denote (a : G) (n : ℤ) :
    D.denote intpow (intpow_sig ▸ [t_denote ▸ a, int_denote ▸ n]ₕ) reg =
    intpow_returnTypes ▸ intpow_pure ▸ [t_denote ▸ (a ^ n)]ₕ

/-- A dialect with a type `t` of members from the ring `R`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class RingDialect
    (R : Type) [CommRing R]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] extends
    AddCommGroupDialect R d,
    CommMonoidDialect R d

/-- A dialect with a type `t` of members from the field `F`.
Type signature correctness, semantic correctness, and purity are enforced for field operations. -/
class FieldDialect
    (F : Type) [Field F]
    (d : Dialect) [TyDenote d.Ty] [S : DialectSignature d] [D : DialectDenote d] extends
    AddCommGroupDialect F d,
    letI : CommGroup F := by sorry -- this is actually not possible to inhabit because of `0`
    CommGroupDialect F d
