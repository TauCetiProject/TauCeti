/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Lifting valuative squares over an affine target

Let `f : X ⟶ Spec B` be a morphism to an affine scheme and let `R` be a valuation ring with
fraction field `K`. To verify the existence part of the valuative criterion for `f`, one extends
`K`-points of `X` to `R`-points. When the `K`-point comes from a ring map `φ : A → K` through some
morphism `Spec A ⟶ X`, for instance an affine chart of `X`, it extends as soon as `φ` takes values
in `R`: compose `Spec R ⟶ Spec A` with the chart. The resulting `R`-point lies over the given
`R`-point of `Spec B` automatically, because morphisms into an affine scheme are ring maps and
`R → K` is injective.

This reduces the valuative criterion for a scheme covered by affine charts to a statement about
ring maps out of the chart rings, as in the proof that the projective line is universally closed.

## Main results

* `AlgebraicGeometry.ValuativeCommSq.hasLift_of_specMap_comp`: a valuative square over a morphism
  to an affine scheme has a lift as soon as its `K`-point factors through some `Spec A` by a ring
  map `A → K` with image in `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.4.7.
* The Stacks Project, Tag 01KF, the valuative criterion for universal closedness.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.ValuativeCommSq

universe u

/-- **A valuative square over a morphism to an affine scheme lifts once its `K`-point factors
through `R`**: if the `K`-point `S.i₁` of `X` is `Spec φ` followed by a morphism `Spec A ⟶ X`, and
`φ : A ⟶ K` takes values in the valuation ring `R`, then the square has a lift. -/
theorem hasLift_of_specMap_comp {X : Scheme.{u}} {B : CommRingCat.{u}} {f : X ⟶ Spec B}
    (S : ValuativeCommSq f) {A : CommRingCat.{u}} (c : Spec A ⟶ X) (φ : A ⟶ .of S.K)
    (hφ : Spec.map φ ≫ c = S.i₁) (hR : ∀ a, IsLocalization.IsInteger S.R (φ a)) :
    S.commSq.HasLift := by
  have hinj := IsFractionRing.injective S.R S.K
  -- `φ` factors through `R`, as `σ : A ⟶ R`.
  let e : S.R ≃+* (algebraMap S.R S.K).rangeS :=
    RingEquiv.ofBijective (algebraMap S.R S.K).rangeSRestrict
      ⟨fun a b h ↦ hinj (congrArg Subtype.val h), (algebraMap S.R S.K).rangeSRestrict_surjective⟩
  let σ : A ⟶ .of S.R := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict _ hR))
  have hσ : σ ≫ CommRingCat.ofHom (algebraMap S.R S.K) = φ := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hR a⟩)
  have hσφ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map σ = Spec.map φ := by
    rw [← Spec.map_comp, hσ]
  refine ⟨⟨⟨Spec.map σ ≫ c, by rw [reassoc_of% hσφ, hφ], ?_⟩⟩⟩
  -- Both morphisms `Spec R ⟶ Spec B` come from ring maps `B ⟶ R`, which agree after composing
  -- with the injection `R → K` since the two morphisms agree on `Spec K`.
  have hK : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ (Spec.map σ ≫ c) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := by
    simpa only [Category.assoc, reassoc_of% hσφ, reassoc_of% hφ] using S.commSq.w
  obtain ⟨g₁, hg₁⟩ := Spec.map_surjective ((Spec.map σ ≫ c) ≫ f)
  obtain ⟨g₂, hg₂⟩ := Spec.map_surjective S.i₂
  rw [← hg₁, ← hg₂, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hK
  rw [← hg₁, ← hg₂, Spec.map_inj]
  ext b
  exact hinj congr($hK b)

end AlgebraicGeometry.ValuativeCommSq
