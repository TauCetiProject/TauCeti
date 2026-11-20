/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Transport of the orthogonal Lie algebra along an isometry

The orthogonal Lie algebra of a quadratic form `Q` is Mathlib's Lie subalgebra
`skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)` of the endomorphisms that are skew-adjoint
for the polar form. An isometric equivalence `e : Q₁.IsometryEquiv Q₂` preserves the polar form,
so conjugation `f ↦ e ∘ f ∘ e⁻¹` identifies the two orthogonal Lie algebras. This is the
infinitesimal counterpart of `QuadraticMap.IsometryEquiv.orthogonalGroupCongr`.

The equivalence is assembled from Mathlib's `skewAdjointLieSubalgebraEquiv`, which transports the
skew-adjoint endomorphisms of a bilinear form `B` along a linear equivalence `e` from those of
`B.compl₁₂ e e`.

## Main definitions

* `QuadraticMap.IsometryEquiv.skewAdjointLieSubalgebraCongr`: the Lie algebra equivalence of
  orthogonal Lie algebras induced by an isometric equivalence.

## Main results

* `QuadraticMap.IsometryEquiv.coe_skewAdjointLieSubalgebraCongr_apply`: it acts by conjugation.
* `QuadraticMap.IsometryEquiv.skewAdjointLieSubalgebraCongr_refl`,
  `QuadraticMap.IsometryEquiv.skewAdjointLieSubalgebraCongr_symm` and
  `QuadraticMap.IsometryEquiv.skewAdjointLieSubalgebraCongr_trans`: it is functorial.
-/

public section

universe u

namespace QuadraticMap.IsometryEquiv

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} {M₁ M₂ M₃ : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- **The orthogonal Lie algebras of isometric quadratic forms are isomorphic.** Conjugation by an
isometric equivalence `e : Q₁.IsometryEquiv Q₂` carries the endomorphisms skew-adjoint for the
polar form of `Q₁` onto those skew-adjoint for the polar form of `Q₂`. -/
def skewAdjointLieSubalgebraCongr (e : Q₁.IsometryEquiv Q₂) :
    skewAdjointLieSubalgebra (polarBilin Q₁) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra (polarBilin Q₂) :=
  (LieEquiv.ofEq _ _ (by rw [e.polarBilin_compl₁₂])).trans
    (skewAdjointLieSubalgebraEquiv (polarBilin Q₂) e.toLinearEquiv)

/-- The transported endomorphism is the conjugate `e ∘ f ∘ e⁻¹`. -/
@[simp]
theorem coe_skewAdjointLieSubalgebraCongr_apply (e : Q₁.IsometryEquiv Q₂)
    (f : skewAdjointLieSubalgebra (polarBilin Q₁)) (m : M₂) :
    (e.skewAdjointLieSubalgebraCongr f : Module.End R M₂) m =
      e ((f : Module.End R M₁) (e.symm m)) := by
  simp [skewAdjointLieSubalgebraCongr, LinearEquiv.conj_apply_apply]

/-- The identity isometry induces the identity of the orthogonal Lie algebra. -/
@[simp]
theorem skewAdjointLieSubalgebraCongr_refl :
    (IsometryEquiv.refl Q₁).skewAdjointLieSubalgebraCongr = LieEquiv.refl := by
  ext f m
  rw [coe_skewAdjointLieSubalgebraCongr_apply]
  -- Mathlib has no evaluation lemma for the inverse of `IsometryEquiv.refl`; it is the identity
  -- by definition.
  rfl

/-- The inverse isometry induces the inverse equivalence. -/
@[simp]
theorem skewAdjointLieSubalgebraCongr_symm (e : Q₁.IsometryEquiv Q₂) :
    e.skewAdjointLieSubalgebraCongr.symm = e.symm.skewAdjointLieSubalgebraCongr := by
  refine LieEquiv.ext fun f => ?_
  rw [LieEquiv.symm_apply_eq]
  ext m
  simp

/-- A composite isometry induces the composite equivalence. -/
@[simp]
theorem skewAdjointLieSubalgebraCongr_trans (e₁ : Q₁.IsometryEquiv Q₂)
    (e₂ : Q₂.IsometryEquiv Q₃) :
    e₁.skewAdjointLieSubalgebraCongr.trans e₂.skewAdjointLieSubalgebraCongr =
      (e₁.trans e₂).skewAdjointLieSubalgebraCongr := by
  ext f m
  rw [LieEquiv.trans_apply, coe_skewAdjointLieSubalgebraCongr_apply,
    coe_skewAdjointLieSubalgebraCongr_apply, coe_skewAdjointLieSubalgebraCongr_apply]
  -- Mathlib has no evaluation lemma for the inverse of `IsometryEquiv.trans`; it is the composite
  -- of the inverses by definition.
  rfl

end QuadraticMap.IsometryEquiv
