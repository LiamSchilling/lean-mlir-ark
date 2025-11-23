import LeanMLIR.Framework.Basic
import LeanMLIR.Framework.Refinement

/--
`DialectLowerSpecification` specifies how types in two dialects correspond,
and how to compare members of corresponding types for semantic equivalence.

Semantic equivalence is defined via a refinement relation.
In this way, `DialectLowerSpecification` is similar to `DialectHRefinement`.
The difference is that instead of specifying refinements between any two types in the dialects,
we only specify refinements between two types the correspond.

First, a correspondence between types is accessible via a representative from `Ty`.
- `mapTy` produces the corresponding member of `d.Ty` from the representative member of `Ty`
- `mapTy'` produces the corresponding member of `d'.Ty` from the representative member of `Ty`

Then, semantic equivalence is defined via a refinement relation.
- `IsRefinedBy`: a refinement between types that correspond
- `MonadIsRefinedBy`: lifts a refinement between types to a refinement between monadic types
-/
structure DialectLowerSpecification (d d' : Dialect) [TyDenote d.Ty] [TyDenote d'.Ty] where
  Ty : Type
  mapTy : Ty → d.Ty
  mapTy' : Ty → d'.Ty
  MonadIsRefinedBy {α β} [HRefinement α β] : HRefinement (d.m α) (d'.m β) := by
    solve
    | exact @Id.instRefinement
  IsRefinedBy : ∀ {t : Ty}, HRefinement ⟦mapTy t⟧ ⟦mapTy' t⟧

attribute [instance, simp, simp_denote] DialectLowerSpecification.IsRefinedBy
attribute [instance, simp, simp_denote] DialectLowerSpecification.MonadIsRefinedBy

/--
A version of `DialectLowerSpecification` that bundles the dialects with the specification.

This is necessary for sane `HRefinement` synthesis.
Otherwise, the conclusion of the `MonadIsRefinedBy` instance
would not refer the desired `DialectLowerSpecification`,
so this premise could not be inferred.
-/
structure SumDialectLowerSpecification where
  d : Dialect
  d' : Dialect
  tyDenote_d : TyDenote d.Ty
  tyDenote_d' : TyDenote d'.Ty
  spec : DialectLowerSpecification d d'

attribute [instance] SumDialectLowerSpecification.tyDenote_d
attribute [instance] SumDialectLowerSpecification.tyDenote_d'

variable (L : SumDialectLowerSpecification)
variable [Monad L.d.m] [Monad L.d'.m]
variable [DialectSignature L.d] [DialectSignature L.d']
variable [DialectDenote L.d] [DialectDenote L.d']

@[reducible]
def SumDialectLowerSpecification.Ty :=
  L.spec.Ty

@[reducible]
def SumDialectLowerSpecification.mapTy :=
  L.spec.mapTy

@[reducible]
def SumDialectLowerSpecification.mapTy' :=
  L.spec.mapTy'

instance [HRefinement α β] : HRefinement (L.d.m α) (L.d'.m β) :=
  L.spec.MonadIsRefinedBy

/--
A refinement between valuations of corresponding contexts.
Corresponding contexts are accessible via map from a representative context.
Valuations refine each other when the values of respective variables refine each other.
-/
instance {Γ : Ctxt L.Ty} :
    HRefinement ((Γ.map L.mapTy).Valuation) ((Γ.map L.mapTy').Valuation) where
  IsRefinedBy V₁ V₂ := ∀ t (v : Γ.Var t), V₁ v.toMap ⊑ V₂ v.toMap

/--
A refinement between expressions of corresponding signatures.
Expressions refine each other when their output valuations refine each other
for all input valuations that refine each other.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} :
    HRefinement
      (Expr L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Expr L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')) where
  IsRefinedBy e₁ e₂ :=
    ∀ V₁ V₂, V₁ ⊑ V₂ →
      Ctxt.map_append _ _ _ ▸ e₁.outContext_eq ▸ e₁.denote V₁ ⊑
      Ctxt.map_append _ _ _ ▸ e₂.outContext_eq ▸ e₂.denote V₂

/--
A refinement between computations of corresponding signatures.
Computations refine each other when their output valuations refine each other
for all input valuations that refine each other.
-/
instance {Γ : Ctxt L.Ty} {t : List L.Ty} :
    HRefinement
      (Com L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy))
      (Com L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')) where
  IsRefinedBy c₁ c₂ :=
    ∀ V₁ V₂, V₁ ⊑ V₂ →
      HVector.castFromMap L.mapTy rfl <$> c₁.denote V₁ ⊑
      HVector.castFromMap L.mapTy' rfl <$> c₂.denote V₂

/--
A lowering between two dialects
that preserves semantics according to a `SumDialectLowerSpecification`.
-/
class DialectLower where
  lowerCom (Γ : Ctxt L.Ty) (eff₁ eff₂ : EffectKind) (t : List L.Ty) :
    Com L.d (Γ.map L.mapTy) eff₁ (t.map L.mapTy) → Com L.d' (Γ.map L.mapTy') eff₂ (t.map L.mapTy')
  lowerCom_refined :
    ∀ c, c ⊑ lowerCom Γ eff₁ eff₂ t c
