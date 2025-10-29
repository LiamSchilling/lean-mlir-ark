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

variable {Ty₁ Ty₂ : Type} {f : Ty₁ → Ty₂} {g : Ty₂ → Option Ty₁}
variable {Γ₁ : Ctxt Ty₁} {Γ₂ : Ctxt Ty₂} {ty₁ : Ty₁} {ty₂ : Ty₂}

namespace Ctxt

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
  let countAndDrop acc L :=
    (acc + (L.takeWhile <| Option.isNone ∘ g).length, L.dropWhile <| Option.isNone ∘ g)
  i.repeat (fun (j, L) => countAndDrop (j + 1) <| L.drop 1) (countAndDrop 0 Γ₂.toList) |>.1, by
  sorry ⟩

end Var

end Ctxt
