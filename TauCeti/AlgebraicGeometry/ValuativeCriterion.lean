/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Lifting valuative squares over a separated target

Let `f : X ⟶ Y` be a morphism to a separated scheme, for instance an affine one, and let `R` be a
valuation ring with fraction field `K`. To verify the existence part of the valuative criterion
for `f`, one extends `K`-points of `X` to `R`-points. When the `K`-point comes from a ring map
`φ : A → K` through some morphism `Spec A ⟶ X`, for instance an affine chart of `X`, it extends as
soon as `φ` takes values in `R`: compose `Spec R ⟶ Spec A` with the chart. The resulting `R`-point
lies over the given `R`-point of `Y` automatically, because both are morphisms `Spec R ⟶ Y` that
agree on `Spec K`, and such morphisms are equal when `Y` is separated (the uniqueness part of the
valuative criterion).

This reduces the valuative criterion for a scheme covered by affine charts to a statement about
ring maps out of the chart rings, as in the proof that the projective line is universally closed.

## Main results

* `AlgebraicGeometry.ValuativeCommSq.hasLift_of_specMap_comp`: a valuative square over a morphism
  to a separated scheme has a lift as soon as its `K`-point factors through some `Spec A` by a
  ring map `A → K` with image in `R`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.4.7.
* The Stacks Project, Tag 01KF, the valuative criterion for universal closedness.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.ValuativeCommSq

universe u

/-- **A valuative square over a morphism to a separated scheme lifts once its `K`-point factors
through `R`**: if the `K`-point `S.i₁` of `X` is `Spec φ` followed by a morphism `Spec A ⟶ X`, and
`φ : A ⟶ K` takes values in the valuation ring `R`, then the square has a lift. -/
theorem hasLift_of_specMap_comp {X Y : Scheme.{u}} [Y.IsSeparated] {f : X ⟶ Y}
    (S : ValuativeCommSq f) {A : CommRingCat.{u}} (c : Spec A ⟶ X) (φ : A ⟶ .of S.K)
    (hφ : Spec.map φ ≫ c = S.i₁) (hR : ∀ a, IsLocalization.IsInteger S.R (φ a)) :
    S.commSq.HasLift := by
  -- `φ` factors through `R`, as `σ : A ⟶ R`.
  let e := AlgEquiv.ofInjective (Algebra.ofId S.R S.K) (IsFractionRing.injective S.R S.K)
  let σ : A ⟶ .of S.R := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.hom.codRestrict _ hR))
  have h₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ Spec.map σ ≫ c = S.i₁ := by
    rw [← Spec.map_comp_assoc, ← hφ]
    congr 2
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hR a⟩)
  refine ⟨⟨⟨Spec.map σ ≫ c, h₁, ?_⟩⟩⟩
  -- Both morphisms `Spec R ⟶ Y` lift the same valuative square over `Y ⟶ ⊤_`, and such lifts
  -- are unique because `Y` is separated.
  let S' : ValuativeCommSq (terminal.from Y) :=
    ⟨S.R, S.K, S.i₁ ≫ f, terminal.from _, ⟨terminal.hom_ext _ _⟩⟩
  have := IsSeparated.valuativeCriterion (terminal.from Y) S'
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim (α := S'.commSq.LiftStruct)
    ⟨(Spec.map σ ≫ c) ≫ f, by simpa using h₁ =≫ f, terminal.hom_ext _ _⟩
    ⟨S.i₂, S.commSq.w.symm, terminal.hom_ext _ _⟩)

end AlgebraicGeometry.ValuativeCommSq
