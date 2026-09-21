/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Base change of the tangent Lie algebra

For a commutative bialgebra `H` over `R` and a commutative `R`-algebra `K`, restriction
along `h ↦ 1 ⊗ h` identifies the tangent Lie algebra of `K ⊗[R] H` over `K` with the
`K`-valued tangent derivations of `H`. The inverse sends `d` to `a ⊗ h ↦ a * d h`.
This comparison requires neither flatness nor finiteness. It connects geometric base
change to the coefficient-valued tangent space and its convolution bracket. For an extension
of fields, `finrank_lie_baseChange` deduces invariance of Lie dimension when the original
augmentation cotangent space is finite-dimensional.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.

The tensor calculation for compatibility with convolution follows the point comparison in
`TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic`.
-/

public section

namespace TauCeti

open TensorProduct

noncomputable section

variable {R K H : Type*} [CommRing R] [CommRing K] [CommRing H]
  [Algebra R K] [Bialgebra R H]

/-- The `K`-linear extension of a tangent vector, with its coefficient type transported. -/
private def extendTangentLinear (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    K ⊗[R] H →ₗ[K] Bialgebra.CounitAlgebra K (K ⊗[R] H) K :=
  (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).symm.toLinearMap.comp
    (AlgebraTensorModule.lift (LinearMap.toSpanSingleton K (H →ₗ[R] K)
      ((Bialgebra.CounitAlgebra.algEquivSelf R H K).toLinearMap.comp d.toLinearMap)))

private theorem extendTangentLinear_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
      (extendTangentLinear d (a ⊗ₜ[R] h)) =
      a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h) := by
  simp only [extendTangentLinear, LinearMap.comp_apply, AlgebraTensorModule.lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply, smul_eq_mul, Derivation.coeFn_coe]

/-- Extend a counit-valued derivation to the base-changed coordinate algebra. -/
private def extendTangent (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) :=
  Derivation.mk' (extendTangentLinear d) fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp [add_mul, map_add, hx, hz, add_smul, smul_add]; abel
    | tmul a h =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp [mul_add, map_add, hy, hz, add_smul, smul_add]; abel
      | tmul b j =>
        apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
        simp only [Algebra.TensorProduct.tmul_mul_tmul, map_add,
          Bialgebra.CounitAlgebra.algEquivSelf_smul, extendTangentLinear_tmul,
          TensorProduct.counit_tmul, CommSemiring.counit_apply, d.leibniz]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def]
        ring

private theorem extendTangent_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
      (extendTangent d (a ⊗ₜ[R] h)) = a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h) := by
  rw [extendTangent, Derivation.coe_mk']
  exact extendTangentLinear_tmul d a h

/-- Restrict a tangent vector along the inclusion of the original coordinate algebra. -/
private def restrictTangent
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    Derivation R H (Bialgebra.CounitAlgebra R H K) :=
  Derivation.mk'
    ((Bialgebra.CounitAlgebra.algEquivSelf R H K).symm.toLinearMap.comp
      (((Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).toLinearMap.comp
        d.toLinearMap).restrictScalars R |>.comp
          Algebra.TensorProduct.includeRight.toLinearMap)) fun h j ↦ by
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
      AlgHom.toLinearMap_apply, Derivation.coeFn_coe, map_add,
      Bialgebra.CounitAlgebra.algEquivSelf_smul,
      Algebra.TensorProduct.includeRight_apply]
    have ht : (1 : K) ⊗ₜ[R] (h * j) =
        (1 ⊗ₜ[R] h) * (1 ⊗ₜ[R] j) := by simp
    rw [ht, d.leibniz, map_add]
    simp only [Bialgebra.CounitAlgebra.algEquivSelf_smul]
    simp only [TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, mul_one, Algebra.algebraMap_self, RingHom.id_apply]

private theorem restrictTangent_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R H K (restrictTangent d h) =
      Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K (d (1 ⊗ₜ[R] h)) := by
  simp only [restrictTangent, Derivation.coe_mk', LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeRight_apply, Derivation.coeFn_coe]

private theorem restrictTangent_extendTangent
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    restrictTangent (extendTangent d) = d := by
  ext h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [restrictTangent_apply, extendTangent_tmul, one_mul]

private theorem extendTangent_restrictTangent
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    extendTangent (restrictTangent d) = d := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h =>
    apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
    rw [extendTangent_tmul, restrictTangent_apply]
    have ht : a ⊗ₜ[R] h = a • ((1 : K) ⊗ₜ[R] h) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, d.map_smul, map_smul, smul_eq_mul]

/-- Restriction and extension identify coefficient-valued tangent vectors with tangent vectors
of the base-changed coordinate algebra. -/
private def tangentBaseChangeLinearEquiv :
    Derivation R H (Bialgebra.CounitAlgebra R H K) ≃ₗ[K]
      Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) where
  toFun := extendTangent
  invFun := restrictTangent
  left_inv := restrictTangent_extendTangent
  right_inv := extendTangent_restrictTangent
  map_add' d e := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a h =>
      apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
      simp only [Derivation.add_apply, map_add, extendTangent_tmul, mul_add]
  map_smul' a d := by
    ext x
    apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
    simp only [RingHom.id_apply, algEquivSelf_derivation_smul_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b h =>
      simp only [extendTangent_tmul, algEquivSelf_derivation_smul_apply]
      ring

/-- The linear comparison applies by extending the tangent vector. -/
private theorem tangentBaseChangeLinearEquiv_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) :
    tangentBaseChangeLinearEquiv d = extendTangent d := rfl

/-- The inverse linear comparison applies by restricting the tangent vector. -/
private theorem tangentBaseChangeLinearEquiv_symm_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    tangentBaseChangeLinearEquiv.symm d = restrictTangent d := rfl

private theorem restrictTangent_lie
    (d e : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) :
    restrictTangent ⁅d, e⁆ = ⁅restrictTangent d, restrictTangent e⁆ := by
  ext h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [restrictTangent_apply, Derivation.bracket_apply, Derivation.bracket_apply]
  simp only [map_sub, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero, sub_zero]
  | add x y hx hy =>
    simpa only [tmul_add, map_add, add_sub_add_comm] using congrArg₂ (· + ·) hx hy
  | tmul x y =>
    simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
      LinearMap.mul'_apply, Derivation.coeFn_coe, map_mul, restrictTangent_apply]

/-- The Lie algebra of a base-changed affine monoid is its coefficient-valued tangent Lie
algebra. The comparison preserves the convolution bracket and needs no flatness assumption. -/
def tangentBaseChangeLieEquiv :
    Derivation R H (Bialgebra.CounitAlgebra R H K) ≃ₗ⁅K⁆
      Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K) :=
  { tangentBaseChangeLinearEquiv with
    map_lie' := fun {d e} ↦ by
      apply tangentBaseChangeLinearEquiv.symm.injective
      exact (restrictTangent_extendTangent ⁅d, e⁆).trans
        ((congrArg₂ (fun x y ↦ ⁅x, y⁆)
          (restrictTangent_extendTangent d) (restrictTangent_extendTangent e)).symm.trans
            (restrictTangent_lie (extendTangent d) (extendTangent e)).symm) }

/-- Base change extends a tangent vector by `K`-linearity. -/
@[simp]
theorem tangentBaseChangeLieEquiv_tmul
    (d : Derivation R H (Bialgebra.CounitAlgebra R H K)) (a : K) (h : H) :
    tangentBaseChangeLieEquiv d (a ⊗ₜ[R] h) =
      (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).symm
        (a * Bialgebra.CounitAlgebra.algEquivSelf R H K (d h)) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K).injective
  rw [AlgEquiv.apply_symm_apply]
  -- The Lie comparison retains the underlying linear equivalence.
  change Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K
    (tangentBaseChangeLinearEquiv d (a ⊗ₜ[R] h)) = _
  rw [tangentBaseChangeLinearEquiv_apply]
  exact extendTangent_tmul d a h

/-- The inverse Lie comparison restricts along `h ↦ 1 ⊗ h`. -/
@[simp]
theorem tangentBaseChangeLieEquiv_symm_apply
    (d : Derivation K (K ⊗[R] H) (Bialgebra.CounitAlgebra K (K ⊗[R] H) K)) (h : H) :
    tangentBaseChangeLieEquiv.symm d h =
      (Bialgebra.CounitAlgebra.algEquivSelf R H K).symm
        (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[R] H) K (d (1 ⊗ₜ[R] h))) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H K).injective
  rw [AlgEquiv.apply_symm_apply]
  -- The inverse Lie comparison retains the inverse linear equivalence.
  change Bialgebra.CounitAlgebra.algEquivSelf R H K
    (tangentBaseChangeLinearEquiv.symm d h) = _
  rw [tangentBaseChangeLinearEquiv_symm_apply]
  exact restrictTangent_apply d h

end

/-- Extension of the ground field preserves the dimension of the Lie algebra of an affine
monoid whose augmentation cotangent space is finite-dimensional. This compares the Lie algebras
of the original and base-changed coordinate rings, not merely their coefficient spaces. -/
theorem finrank_lie_baseChange {k K H : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing H] [Bialgebra k H] [Module.Finite k (Bialgebra.CotangentSpace k H)] :
    Module.finrank K
        (Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) =
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) :=
  (tangentBaseChangeLieEquiv (R := k) (K := K) (H := H)).toLinearEquiv.finrank_eq.symm.trans
    Derivation.finrank_tangent_baseChange

end TauCeti
