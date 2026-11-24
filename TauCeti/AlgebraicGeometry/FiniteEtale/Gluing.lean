/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Gluing finite étale covers along two opens

Let `S` be covered by the images of two open immersions `j₁ : W₁ ⟶ S` and `j₂ : W₂ ⟶ S`, with
overlap `W₁₂ = W₁ ×_S W₂` and inclusions `i₁ : W₁₂ ⟶ W₁`, `i₂ : W₁₂ ⟶ W₂`. Finite étale covers
`Y₁` of `W₁` and `Y₂` of `W₂` together with an isomorphism `e` between their restrictions to
`W₁₂` glue to a finite étale cover `Y` of `S` whose restrictions to `W₁` and `W₂` are `Y₁` and `Y₂`,
compatibly with `e` (`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback`).

The glued scheme is the pushout of `Y₁` and `Y₂` along `Y₁ ×_{W₁} W₁₂`, which `e` identifies with
the open `Y₂ ×_{W₂} W₁₂` of `Y₂`. Its inverse images of `W₁` and `W₂` are `Y₁` and `Y₂`
(`AlgebraicGeometry.Scheme.isPullback_pushout_desc_comp_inl`), so it is finite and étale over `S`,
these properties being local on the target.

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
  {j₂ : W₂ ⟶ S} [IsOpenImmersion i₁] [IsOpenImmersion i₂] [IsOpenImmersion j₁]
  [IsOpenImmersion j₂] {Y₁ : FiniteEtaleScheme W₁} {Y₂ : FiniteEtaleScheme W₂}

/-- The isomorphism of underlying schemes of `e`, with source and target written as the
pullbacks they are by definition. -/
private def overlapIso (e : (pullback i₁).obj Y₁ ≅ (pullback i₂).obj Y₂) :
    Limits.pullback Y₁.obj.hom i₁ ≅ Limits.pullback Y₂.obj.hom i₂ :=
  (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso e)

omit [IsOpenImmersion i₁] [IsOpenImmersion i₂] in
private lemma overlapIso_hom (e : (pullback i₁).obj Y₁ ≅ (pullback i₂).obj Y₂) :
    (overlapIso e).hom = e.hom.hom.left :=
  rfl

omit [IsOpenImmersion i₁] [IsOpenImmersion i₂] in
private lemma overlapIso_hom_snd (e : (pullback i₁).obj Y₁ ≅ (pullback i₂).obj Y₂) :
    (overlapIso e).hom ≫ Limits.pullback.snd Y₂.obj.hom i₂ = Limits.pullback.snd Y₁.obj.hom i₁ :=
  Over.w e.hom.hom

omit [IsOpenImmersion i₁] [IsOpenImmersion i₂] in
/-- The restriction `Y₁ ×_{W₁} W₁₂` of `Y₁`, mapped into `Y₂` through `e`, is the restriction of
`Y₂` to `W₁₂`. -/
private lemma isPullback_overlap (e : (pullback i₁).obj Y₁ ≅ (pullback i₂).obj Y₂) :
    IsPullback ((overlapIso e).hom ≫ Limits.pullback.fst Y₂.obj.hom i₂)
      (Limits.pullback.snd Y₁.obj.hom i₁) Y₂.obj.hom i₂ :=
  IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Limits.pullback.condition,
    reassoc_of% overlapIso_hom_snd e]⟩ (overlapIso e) rfl (overlapIso_hom_snd e)

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
  have h₁ := IsPullback.of_hasPullback Y₁.obj.hom i₁
  have h₂ := isPullback_overlap e
  have : IsOpenImmersion (Limits.pullback.fst Y₁.obj.hom i₁) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion ((overlapIso e).hom ≫ Limits.pullback.fst Y₂.obj.hom i₂) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have w : Limits.pullback.fst Y₁.obj.hom i₁ ≫ Y₁.obj.hom ≫ j₁ =
      ((overlapIso e).hom ≫ Limits.pullback.fst Y₂.obj.hom i₂) ≫ Y₂.obj.hom ≫ j₂ := by
    rw [h₁.w_assoc, h.w, ← h₂.w_assoc]
  have : IsFinite (pushout.desc (Y₁.obj.hom ≫ j₁) (Y₂.obj.hom ≫ j₂) w) :=
    (IsZariskiLocalAtTarget.pushout_desc_comp_iff h h₁ h₂ w hcover).mpr
      ⟨inferInstance, inferInstance⟩
  have : Etale (pushout.desc (Y₁.obj.hom ≫ j₁) (Y₂.obj.hom ≫ j₂) w) :=
    (IsZariskiLocalAtTarget.pushout_desc_comp_iff h h₁ h₂ w hcover).mpr
      ⟨inferInstance, inferInstance⟩
  have chart₁ := (Scheme.isPullback_pushout_desc_comp_inl h h₁.toCommSq h₂ w).flip
  have chart₂ := (Scheme.isPullback_pushout_desc_comp_inr h h₁ h₂.toCommSq w).flip
  -- Build `Y` with `ofHom`, then use `ofHom_obj` to see its structure morphism as `pushout.desc`.
  obtain ⟨⟨Y, hY⟩, hYobj⟩ : ∃ Y : FiniteEtaleScheme S,
      Y.obj = Over.mk (pushout.desc (Y₁.obj.hom ≫ j₁) (Y₂.obj.hom ≫ j₂) w) :=
    ⟨ofHom _, ofHom_obj _⟩
  subst hYobj
  let Y : FiniteEtaleScheme S := ⟨_, hY⟩
  let e₁ : (pullback j₁).obj Y ≅ Y₁ :=
    ObjectProperty.isoMk _ (Over.isoMk chart₁.isoPullback.symm chart₁.isoPullback_inv_snd)
  let e₂ : (pullback j₂).obj Y ≅ Y₂ :=
    ObjectProperty.isoMk _ (Over.isoMk chart₂.isoPullback.symm chart₂.isoPullback_inv_snd)
  -- Through `e₁` and `e₂`, the embeddings of `Y₁` and `Y₂` into `Y` are the pushout inclusions.
  have c₁ : e₁.inv.hom.left ≫ Limits.pullback.fst Y.obj.hom j₁ = pushout.inl _ _ :=
    chart₁.isoPullback_hom_fst
  have c₂ : e₂.inv.hom.left ≫ Limits.pullback.fst Y.obj.hom j₂ = pushout.inr _ _ :=
    chart₂.isoPullback_hom_fst
  refine ⟨Y, e₁, e₂, ?_⟩
  rw [c₁, c₂, ← overlapIso_hom]
  exact pushout.condition.trans (Category.assoc _ _ _)

end TauCeti.FiniteEtaleScheme
