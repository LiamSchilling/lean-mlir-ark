import LeanMLIR.Basic

/-!
# Context Mapping

Extends previously defined `Ctxt.map` and `Ctxt.Var.toMap`
which are for mapping a context according to a total type mapping.
This functionality captures simple raising and lowering
between dialects with types that correspond.

## Main definitions
- `Ctxt.Var.fromMap`: transport a variable from a mapped context
  (the missing inverse of `Ctxt.Var.toMap`)
- `Ctxt.filterMap`: map a context according to a partial type mapping
- `Ctxt.Var.toFilterMap`: transport a variable to a filter-mapped context
- `Ctxt.Var.fromFilterMap`: transport a variable from a filter-mapped context
-/

namespace HVector

variable {α β : Type*} {A : α → Type*} {B : β → Type*}

/-- An alternative to `map'` which eliminates a mapped type instead of introducing one. -/
def fromMap' (f' : β → α) (f : ∀ (b : β), A (f' b) → B b) :
    ∀ {l : List β}, HVector A (l.map f') → HVector B l
  | [], .nil => .nil
  | t :: _, .cons a as  => .cons (f t a) (fromMap' f' f as)

end HVector

namespace Ctxt

variable {Ty₁ Ty₂ : Type} {f : Ty₁ → Ty₂} {g : Ty₂ → Option Ty₁}

/-- Map a partial function from one type universe to another over a context,
filtering types that map to `none`. -/
def filterMap (g : Ty₂ → Option Ty₁) : Ctxt Ty₂ → Ctxt Ty₁ :=
  ofList ∘ (List.filterMap g) ∘ toList

namespace Var

/-- Transport a variable from any mapped context `Γ.map f` to `Γ`. -/
def fromMap (inj : ∀ {ty₁ ty₂}, f ty₁ = f ty₂ → ty₁ = ty₂) : Var (Γ₁.map f) (f ty₁) → Var Γ₁ ty₁
| ⟨i, h⟩ => ⟨i, by
  simp only [getElem?_map, Option.map_eq_some_iff] at h
  have ⟨_, h₁, h₂⟩ := h
  simp only [h₁, Option.some.injEq]
  exact inj h₂ ⟩

/-- Transport a variable from `Γ` to any mapped context `Γ.filterMap f`. -/
def toFilterMap (inv : ∀ {ty}, g (f ty) = some ty) : Var Γ₂ (f ty₁) → Var (Γ₂.filterMap g) ty₁
| ⟨i, h⟩ => ⟨
  Γ₂.toList.take i |>.countP <| Option.isSome ∘ g, by
  sorry ⟩

/-- Transport a variable from any mapped context `Γ.filterMap f` to `Γ`. -/
def fromFilterMap (inv : ∀ {ty}, g (f ty) = some ty) : Var (Γ₂.filterMap g) ty₁ → Var Γ₂ (f ty₁)
| ⟨i, h⟩ => ⟨
  let countAndDrop acc tys₂ :=
    (acc + (tys₂.takeWhile <| Option.isNone ∘ g).length, tys₂.dropWhile <| Option.isNone ∘ g)
  i.repeat (fun (j, tys₂) => countAndDrop (j + 1) <| tys₂.drop 1) (countAndDrop 0 Γ₂.toList) |>.1, by
  sorry ⟩

end Var

namespace Valuation

variable [TyDenote Ty₁] [TyDenote Ty₂]

/-- Transport a valuation from `Γ` to any mapped context `Γ.map f`. -/
def toMap (inj : ∀ {ty₁ ty₂}, f ty₁ = f ty₂ → ty₁ = ty₂) (t : ∀ ty₁, ⟦ty₁⟧ → ⟦f ty₁⟧) :
    Valuation Γ₁ → Valuation (Γ₁.map f)
| val, ty₂, ⟨i, h⟩ =>
  let var := Var.mk i h
  have : i < Γ₁.length := by rw [←length_map]; exact var.lt_length
  have heq : ty₂ = f Γ₁[i] := by
    simp only [getElem?_map, Option.map_eq_some_iff] at h
    match h with | ⟨_, h₁, h₂⟩ => rw [getElem?_eq_some_iff.mp h₁ |>.2, h₂]
  heq ▸ t Γ₁[i] <| val <| heq ▸ var |>.fromMap inj

end Valuation

@[simp]
theorem filterMap_some {Γ₂ : Ctxt Ty₂} :
    Γ₂.filterMap some = Γ₂ := by
  simp [filterMap]

@[simp]
theorem filterMap_append (g : Ty₂ → Option Ty₁) (Γ₂ Δ₂ : Ctxt Ty₂) :
    (Γ₂ ++ Δ₂).filterMap g = Γ₂.filterMap g ++ Δ₂.filterMap g := by
  simp [filterMap]

@[simp]
theorem filterMap_map {Γ₁ : Ctxt Ty₁} :
    (Γ₁.map f).filterMap g = Γ₁.filterMap (g ∘ f) := by
  simp [filterMap, map]

end Ctxt

namespace RegionSignature

variable {Ty₁ Ty₂ : Type}

/-- Performs the mapping of a single entry of a regional signature,
that is, a signature corresponding to one region. -/
def mapElem (f : Ty₁ → Ty₂) : Ctxt Ty₁ × List Ty₁ → Ctxt Ty₂ × List Ty₂
| (ctxt, tys) => (ctxt.map f, tys.map f)

end RegionSignature

namespace EffectKind

variable {m m' : Type → Type} [Monad m] [Monad m'] {α : Type}

/-- Transforms a lift between monads into a lift between those monads mapped by any effect kind. -/
@[always_inline, inline, expose]
protected def lift (f : m α → m' α) : ∀ {eff : EffectKind}, (eff.toMonad m) α → (eff.toMonad m') α
| .pure, t => t
| .impure, t => f t

instance {eff : EffectKind} [MonadLift m m'] : MonadLift (eff.toMonad m) (eff.toMonad m') where
monadLift := EffectKind.lift MonadLift.monadLift

end EffectKind
