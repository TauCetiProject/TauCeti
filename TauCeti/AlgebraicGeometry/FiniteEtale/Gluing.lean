/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
import TauCeti.AlgebraicGeometry.Gluing.Over
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Gluing finite étale covers along two opens

Let `S` be covered by the images of two open immersions `j₁ : W₁ ⟶ S` and `j₂ : W₂ ⟶ S`, with
overlap `W₁₂ = W₁ ×_S W₂` and inclusions `i₁ : W₁₂ ⟶ W₁`, `i₂ : W₁₂ ⟶ W₂`. Finite étale covers
`Y₁` of `W₁` and `Y₂` of `W₂` together with an isomorphism `e` between their restrictions to
`W₁₂` glue to a finite étale cover `Y` of `S` whose restrictions to `W₁` and `W₂` are `Y₁` and `Y₂`,
compatibly with `e` (`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback`).

The glued scheme is `TauCeti.AlgebraicGeometry.glueOver`, the pushout of `Y₁` and `Y₂` along
`Y₁ ×_{W₁} W₁₂`, which `e` identifies with the open `Y₂ ×_{W₂} W₁₂` of `Y₂`. Its inverse images of
`W₁` and `W₂` are `Y₁` and `Y₂`, so it is finite and étale over `S`, these properties being local on
the target (`AlgebraicGeometry.IsZariskiLocalAtTarget.of_glueOver`).

This is how a finite étale cover of an open `U` is extended across an open `W`: a cover of `W`
which agrees with the given one over `U ∩ W` glues with it to a cover of `U ∪ W`. Extensions of
covers obtained locally, for instance by spreading out a cover of the spectrum of a local ring to
a neighbourhood of the point, are assembled in this way.

## References

* [The Stacks Project, Section 26.14, Gluing schemes](https://stacks.math.columbia.edu/tag/01JA)
* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5), the gluing step
  in spreading out from a local scheme.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S W₁ W₂ W₁₂ : Scheme.{u}} {i₁ : W₁₂ ⟶ W₁} {i₂ : W₁₂ ⟶ W₂} {j₁ : W₁ ⟶ S}
  {j₂ : W₂ ⟶ S} [IsOpenImmersion j₁] [IsOpenImmersion j₂]
  {Y₁ : FiniteEtaleScheme W₁} {Y₂ : FiniteEtaleScheme W₂}

/-- **Gluing finite étale covers along two opens.** Let `j₁ : W₁ ⟶ S` and `j₂ : W₂ ⟶ S` be open
immersions covering `S`, with overlap `W₁₂` given by a cartesian square `i₁ ≫ j₁ = i₂ ≫ j₂`. Let
`Y₁` and `Y₂` be finite étale covers of `W₁` and `W₂`, and `e` an isomorphism between their
restrictions to `W₁₂`. Then there is a finite étale cover `Y` of `S` whose restrictions to `W₁` and
`W₂` are isomorphic to `Y₁` and `Y₂`, such that the two resulting embeddings of the overlap
`Y₁ ×_{W₁} W₁₂` into `Y`, directly and through `e`, agree. -/
theorem exists_pullback_iso_of_isPullback (h : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    (e : (pullback i₁).obj Y₁ ≅ (pullback i₂).obj Y₂) :
    ∃ (Y : FiniteEtaleScheme S) (e₁ : (pullback j₁).obj Y ≅ Y₁)
      (e₂ : (pullback j₂).obj Y ≅ Y₂),
      Limits.pullback.fst Y₁.obj.hom i₁ ≫ e₁.inv.hom.left ≫ Limits.pullback.fst Y.obj.hom j₁ =
        e.hom.hom.left ≫ Limits.pullback.fst Y₂.obj.hom i₂ ≫ e₂.inv.hom.left ≫
          Limits.pullback.fst Y.obj.hom j₂ := by
  let e' : (Over.pullback i₁).obj Y₁.obj ≅ (Over.pullback i₂).obj Y₂.obj :=
    (finiteEtaleSchemeProperty _).ι.mapIso e
  let Y_over : Over S := TauCeti.AlgebraicGeometry.glueOver h Y₁.obj Y₂.obj e'
  have hfin : IsFinite Y_over.hom :=
    IsZariskiLocalAtTarget.of_glueOver (P := @IsFinite.{u}) h hcover Y₁.obj Y₂.obj e'
      inferInstance inferInstance
  have het : Etale Y_over.hom :=
    IsZariskiLocalAtTarget.of_glueOver (P := @Etale.{u}) h hcover Y₁.obj Y₂.obj e'
      inferInstance inferInstance
  let Y : FiniteEtaleScheme S :=
    ⟨Y_over, (finiteEtaleSchemeProperty_iff Y_over).mpr ⟨hfin, het⟩⟩
  let e₁ : (pullback j₁).obj Y ≅ Y₁ :=
    ObjectProperty.isoMk _ (TauCeti.AlgebraicGeometry.glueOverPullbackLeftIso h Y₁.obj Y₂.obj e')
  let e₂ : (pullback j₂).obj Y ≅ Y₂ :=
    ObjectProperty.isoMk _ (TauCeti.AlgebraicGeometry.glueOverPullbackRightIso h Y₁.obj Y₂.obj e')
  refine ⟨Y, e₁, e₂, ?_⟩
  have hcompat := TauCeti.AlgebraicGeometry.glueOverPullback_compat h Y₁.obj Y₂.obj e'
  rw [← Category.assoc, ← Functor.mapIso_hom, ← Iso.eq_comp_inv, Functor.mapIso_inv] at hcompat
  have hcompat' := congrArg (fun k ↦ k.left ≫
    Limits.pullback.fst (Limits.pullback.snd Y_over.hom j₂) i₂ ≫
      Limits.pullback.fst Y_over.hom j₂) hcompat
  change Limits.pullback.fst Y₁.obj.hom i₁ ≫
      (TauCeti.AlgebraicGeometry.glueOverPullbackLeftIso h Y₁.obj Y₂.obj e').inv.left ≫
        Limits.pullback.fst (TauCeti.AlgebraicGeometry.glueOver h Y₁.obj Y₂.obj e').hom j₁ =
    e'.hom.left ≫ Limits.pullback.fst Y₂.obj.hom i₂ ≫
      (TauCeti.AlgebraicGeometry.glueOverPullbackRightIso h Y₁.obj Y₂.obj e').inv.left ≫
        Limits.pullback.fst (TauCeti.AlgebraicGeometry.glueOver h Y₁.obj Y₂.obj e').hom j₂
  rw [TauCeti.AlgebraicGeometry.glueOverPullbackLeftIso_inv_left_fst,
    TauCeti.AlgebraicGeometry.glueOverPullbackRightIso_inv_left_fst]
  simpa [Y_over, Over.comp_left, Over.pullback_map_left] using hcompat'

end TauCeti.FiniteEtaleScheme
