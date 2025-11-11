import LeanMLIR.Basic

namespace RegionSignature

variable {Ty₁ Ty₂ : Type} (D : Dialect) [DialectSignature D]

/-- Performs the mapping of a single entry of a regional signature,
that is, a signature corresponding to one region. -/
def mapElem (f : Ty₁ → Ty₂) : Ctxt Ty₁ × List Ty₁ → Ctxt Ty₂ × List Ty₂
| (ctxt, tys) => (ctxt.map f, tys.map f)

/-- Denotes a single entry of a regional signature to the type of such a region. -/
def denoteSigElem : Ctxt D.Ty × List D.Ty → Type
| (ctxt, tys) => Com D ctxt .impure tys

end RegionSignature

namespace Expr

variable {D : Dialect} [DialectSignature D] {Γ : Ctxt D.Ty} {eff : EffectKind} {tys : List D.Ty}

lemma outContext_eq : ∀ expr : Expr D Γ eff tys, expr.outContext = tys ++ Γ := by
  simp

end Expr
