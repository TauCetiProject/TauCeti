/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Smooth.NoetherianDescent
import TauCeti.CategoryTheory.MorphismProperty.Ind

/-!
# Étale ring maps out of filtered colimits

Let `A = colim Aᵢ` be a small filtered colimit of commutative rings and `A → B` an étale ring map.
This file shows that `A → B` is the pushout of an étale ring map `Aⱼ → Bⱼ` out of some stage, i.e.
`B ≅ A ⊗[Aⱼ] Bⱼ`. In the language of Mathlib's `MorphismProperty.PreIndSpreads`, étale ring maps
spread out of filtered colimits.

No finiteness or noetherian hypothesis is imposed on the stages.

Together with the stability of étale ring maps under composition and cobase change and their
finite presentability, this makes filtered colimits of étale ring maps stable under composition
(`CategoryTheory.MorphismProperty.isStableUnderComposition_ind`).

## Main results

* `RingHom.Etale.preIndSpreads`: étale ring maps out of a small filtered colimit of commutative
  rings are pushouts of étale ring maps out of a stage.
* `RingHom.Etale.isStableUnderComposition_ind`: filtered colimits of étale ring maps, in the
  sense of `CategoryTheory.MorphismProperty.ind`, are stable under composition.

## References

* [Stacks Project, Lemma 10.143.3 (8) (00U2)](https://stacks.math.columbia.edu/tag/00U2), for
  the noetherian models of étale algebras.
* [Stacks Project, Tag 0BSI](https://stacks.math.columbia.edu/tag/0BSI), for the
  composition of ind-étale ring maps.
-/

public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace RingHom

/-- Étale ring maps, as morphisms of commutative rings, are stable under composition. -/
instance Etale.isStableUnderComposition_toMorphismProperty :
    (toMorphismProperty Etale).IsStableUnderComposition where
  comp_mem f g hf hg := Etale.stableUnderComposition f.hom g.hom hf hg

/-- Étale ring maps, as morphisms of commutative rings, are stable under cobase change. -/
instance Etale.isStableUnderCobaseChange_toMorphismProperty :
    (toMorphismProperty Etale).IsStableUnderCobaseChange :=
  isStableUnderCobaseChange_toMorphismProperty_iff.mpr Etale.isStableUnderBaseChange

/-- Étale ring maps are finitely presentable as objects of the under category of their source. -/
theorem Etale.toMorphismProperty_le_isFinitelyPresentable :
    toMorphismProperty Etale ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} :=
  fun _ _ f hf ↦
    let := f.hom.toAlgebra
    have : Algebra.Etale _ _ := hf
    CommRingCat.isFinitelyPresentable_hom f (inferInstanceAs (Algebra.FinitePresentation _ _))

-- By `Algebra.Etale.exists_subalgebra_fg`, `B` is the base change `A ⊗[A₀] B₀` of an étale
-- algebra `B₀` over a subring `A₀ ⊆ A` of finite type over `ℤ`. Such a subring is finitely
-- presented over `ℤ`, so its inclusion into `A` factors through some stage `Aⱼ`
-- (`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`), and `Bⱼ = Aⱼ ⊗[A₀] B₀` works by
-- pasting the two pushout squares `A₀ → Aⱼ → A` and `B₀ → Bⱼ → B`. This follows the plan of
-- `Ring.DirectLimit.exists_etale_finite_algEquiv_tensorProduct` for finite étale algebras over a
-- directed colimit of rings.
/-- Étale ring maps spread out of small filtered colimits of commutative rings: an étale ring map
out of the colimit is the pushout of an étale ring map out of some stage. -/
instance Etale.preIndSpreads :
    MorphismProperty.PreIndSpreads.{u}
      (toMorphismProperty Etale : MorphismProperty CommRingCat.{u}) where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    let := f.hom.toAlgebra
    have : Algebra.Etale c.pt T := hf
    obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ c.pt T
    have : Algebra.FinitePresentation ℤ A₀ :=
      Algebra.FinitePresentation.of_finiteType.mp ((Subalgebra.fg_iff_finiteType A₀).mp hA₀)
    let α : (Functor.const J).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ D :=
      { app _ := CommRingCat.isInitial.to _
        naturality _ _ _ := CommRingCat.isInitial.hom_ext _ _ }
    -- The map out of the initial object `ULift ℤ` is the cast `ULift ℤ ≃+* ℤ → A₀`.
    have hfp : (CommRingCat.isInitial.to (CommRingCat.of A₀)).hom.FinitePresentation :=
      (finitePresentation_algebraMap.mpr this).comp
        (FinitePresentation.of_bijective ULift.ringEquiv.bijective)
    -- The inclusion `A₀ → A` factors through a stage `Aᵢ`.
    obtain ⟨i, a, -, ha⟩ := EssFiniteType.exists_eq_comp_ι_app_of_isColimit _ D α _ c hc hfp
      (CommRingCat.ofHom (algebraMap A₀ c.pt)) fun _ ↦ CommRingCat.isInitial.hom_ext _ _
    let : Algebra A₀ (D.obj i) := a.hom.toAlgebra
    -- The outer square `A₀ → A → B`, `A₀ → B₀ → B` is a pushout, through `e`.
    have s : IsPushout (CommRingCat.ofHom (algebraMap A₀ (D.obj i)) ≫ c.ι.app i)
        (CommRingCat.ofHom (algebraMap A₀ B₀)) f
        (CommRingCat.ofHom ((e.symm : c.pt ⊗[A₀] B₀ ≃+* T).toRingHom.comp
          Algebra.TensorProduct.includeRight.toRingHom)) := by
      refine (CommRingCat.isPushout_tensorProduct A₀ c.pt B₀).of_iso (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (e.symm : c.pt ⊗[A₀] B₀ ≃+* T).toCommRingCatIso ?_ ?_ ?_ ?_
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        -- `algebraMap A₀ (D.obj i)` is `a` by the choice of the algebra structure.
        exact ha
      · simp
      · -- `algebraMap c.pt T` is `f` by the choice of the algebra structure.
        ext x
        exact (by simpa using e.symm.commutes x : e.symm (x ⊗ₜ[A₀] 1) = algebraMap c.pt T x)
      · simp
    have t := CommRingCat.isPushout_tensorProduct A₀ (D.obj i) B₀
    refine ⟨i, _, _, _, s.of_left' t, ?_⟩
    -- The new leg `Dᵢ → Dᵢ ⊗[A₀] B₀` of the pushout square is the structure map of the
    -- tensor product, up to unfolding `Algebra.TensorProduct.includeLeftRingHom`.
    change Etale (algebraMap (D.obj i) (D.obj i ⊗[A₀] B₀))
    rw [etale_algebraMap]
    infer_instance

/-- Filtered colimits of étale ring maps are stable under composition (Stacks, Tag 0BSI). -/
instance Etale.isStableUnderComposition_ind :
    (MorphismProperty.ind.{u}
      (toMorphismProperty Etale : MorphismProperty CommRingCat.{u})).IsStableUnderComposition :=
  MorphismProperty.isStableUnderComposition_ind Etale.toMorphismProperty_le_isFinitelyPresentable

end RingHom
