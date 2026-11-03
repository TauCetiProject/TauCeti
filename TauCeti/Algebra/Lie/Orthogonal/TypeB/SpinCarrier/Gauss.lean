/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
public import TauCeti.Algebra.Lie.Sl2.Gauss
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Tactic.NoncommRing

/-!
# Opposite-root Gauss factorization in the type-B spin carrier

The positive and negative simple-root points admit rank-one Gauss factorization over every
commutative ring when `1 + a * b` is a unit. The middle factor is the corresponding coordinate
of the existing spin weight torus, not an independently chosen diagonal element.

The calculation includes the short terminal root and uses integral root-string identities
before changing coefficients; in particular no invertibility of two is needed. It supplies
opposite-root collection for the numbered root parametrizations, without identifying the
carrier with an independently pinned group scheme.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The formal construction uses `TypeBSpinCarrier.rootIntMatrix` and its integral weight support,
and the square-zero root-string identities of `TauCeti.Sl2`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

private theorem rootIntMatrix_mul_self (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootIntMatrix n j * rootIntMatrix n j = 0 := by
  have h := congrArg (fun g : points n ℤ ↦
    ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) ℤ) :
      Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ))
    ((rootSubgroupPoints n j ℤ).map_mul (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1))
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_eq_one_add_smul,
    toAdd_mul, toAdd_ofAdd, one_smul] at h
  have hm : (rootIntMatrix n j).map (Int.cast : ℤ → ℤ) = rootIntMatrix n j :=
    Matrix.ext fun _ _ ↦ Int.cast_id
  rw [hm] at h
  simp only [add_smul, one_smul] at h
  linear_combination (norm := noncomm_ring) -h

private theorem cartan_mul_rootIntMatrix_sub (j : Fin (n + 1) ⊕ Fin (n + 1))
    (i : Fin (n + 1)) :
    Matrix.diagonal (fun a ↦ basisWeight n a i) * rootIntMatrix n j -
        rootIntMatrix n j * Matrix.diagonal (fun a ↦ basisWeight n a i) =
      rootGeneratorWeight n j i • rootIntMatrix n j := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, zsmul_eq_mul]
  by_cases h : basisWeight n a - basisWeight n b = rootGeneratorWeight n j
  · have hi := congrFun h i
    simp only [Pi.sub_apply] at hi
    rw [← hi]
    simp only [Int.cast_id]
    ring
  · rw [rootIntMatrix_eq_zero_of_weight_ne n j h]
    simp

private theorem rootIntMatrix_pair (i : Fin (n + 1)) :
    rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i) =
        rootIntMatrix n (.inl i) ∧
      rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i) =
        rootIntMatrix n (.inr i) := by
  have hEF := lie_rootIntMatrix_inl_inr n i
  rw [Ring.lie_def] at hEF
  have hHE := cartan_mul_rootIntMatrix_sub n (.inl i) i
  have hHF := cartan_mul_rootIntMatrix_sub n (.inr i) i
  simp only [rootGeneratorWeight_inl, rootGeneratorWeight_inr, Pi.neg_apply,
    CartanMatrix.B_diag, neg_smul, ofNat_zsmul] at hHE hHF
  have htwo : IsSMulRegular (Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) (2 : ℕ) := by
    intro X Y h
    ext a b
    have he := congrFun (congrFun h a) b
    simp only [Matrix.smul_apply, nsmul_eq_mul] at he
    omega
  exact ⟨Sl2.e_mul_f_mul_e_of_mul_self_eq_zero htwo
      (rootIntMatrix_mul_self n (.inl i)) hEF hHE,
    Sl2.f_mul_e_mul_f_of_mul_self_eq_zero htwo
      (rootIntMatrix_mul_self n (.inr i)) hEF hHF⟩

private theorem coroot_matrix (i : Fin (n + 1)) (A : Type*) [CommRing A] (u : Aˣ) :
    ((weightTorusPoints n A (Pi.mulSingle i u) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + ((u : A) - 1) •
          ((rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i)).map (Int.cast : ℤ → A)) +
        ((↑(u⁻¹) : A) - 1) •
          ((rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i)).map (Int.cast : ℤ → A)) := by
  -- Split each integral weight vector into its two root-string endpoint projections.
  let f := (Matrix.toLinAlgEquiv' :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ ≃ₐ[ℤ]
      Module.End ℤ (Fin (dimension n) → ℤ))
  have hEE := congrArg f (rootIntMatrix_mul_self n (.inl i))
  have hFF := congrArg f (rootIntMatrix_mul_self n (.inr i))
  have hEFE := congrArg f (rootIntMatrix_pair n i).1
  have hFEF := congrArg f (rootIntMatrix_pair n i).2
  have hEF := congrArg f (lie_rootIntMatrix_inl_inr n i)
  simp only [Ring.lie_def, map_sub, map_mul, map_zero] at hEE hFF hEFE hFEF hEF
  rw [coe_weightTorusPoints, kostantTorusMatrix_apply, diagGL_coe]
  ext a b
  have hv : f (Matrix.diagonal (fun a ↦ basisWeight n a i)) (Pi.single b 1) =
      basisWeight n b i • (Pi.single b 1) := by
    simp only [f, Matrix.toLinAlgEquiv'_apply, Matrix.diagonal_mulVec_single, mul_one]
    ext c
    by_cases hc : c = b <;> simp [hc]
  have hv0 : (Pi.single b 1 : Fin (dimension n) → ℤ) ≠ 0 := by
    intro h
    have := congrFun h b
    simp at this
  have hcases := Sl2.mul_apply_of_eq_zsmul hEE hFF hEFE hFEF hEF hv hv0
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, torusCharacter_mulSingle]
  rcases hcases with ⟨hm, hp, hq⟩ | ⟨hm, hp, hq⟩ | ⟨hm, hp, hq⟩
  all_goals
    rw [← map_mul] at hp hq
    simp only [f, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_single_one] at hp hq
    have hp' := congrFun hp a
    have hq' := congrFun hq a
    simp only [Matrix.col_apply, Pi.single_apply, Pi.zero_apply] at hp' hq'
    simp only [hp', hq']
    rcases eq_or_ne a b with rfl | hab
    · simp only [hm]
      simp
    · simp only [hab, ite_false, Int.cast_zero, mul_zero, add_zero]

/-- Opposite simple-root points factor through the numbered coroot of the spin weight torus
on the rank-one open cell. This includes the short terminal root over rings of characteristic
two, and requires neither root parameter to be a unit. -/
theorem rootSubgroupPoints_inl_mul_inr_gauss (i : Fin (n + 1))
    (A : Type*) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (b * (↑(u⁻¹) : A))) *
        weightTorusPoints n A (Pi.mulSingle i u) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (a * (↑(u⁻¹) : A))) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_eq_one_add_smul,
    toAdd_ofAdd, coroot_matrix]
  -- Establish the root-string identities over ℤ before specializing the coefficient ring.
  let f : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ →+*
      Matrix (Fin (dimension n)) (Fin (dimension n)) A := (Int.castRingHom A).mapMatrix
  have hEE := congrArg f (rootIntMatrix_mul_self n (.inl i))
  have hFF := congrArg f (rootIntMatrix_mul_self n (.inr i))
  have hEFE := congrArg f (rootIntMatrix_pair n i).1
  have hFEF := congrArg f (rootIntMatrix_pair n i).2
  simp only [map_mul, map_zero, f, RingHom.mapMatrix_apply,
    Int.coe_castRingHom] at hEE hFF hEFE hFEF
  rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast]
  exact Sl2.gauss_of_mul_self_eq_zero hEE hFF hEFE hFEF a b u hu

/-- The reverse-order opposite-root factorization has the inverse coroot in its middle
factor. It holds under the same unit condition as the positive-first formula. -/
theorem rootSubgroupPoints_inr_mul_inl_gauss (i : Fin (n + 1))
    (A : Type*) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (a * (↑(u⁻¹) : A))) *
        weightTorusPoints n A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (b * (↑(u⁻¹) : A))) := by
  have h := rootSubgroupPoints_inl_mul_inr_gauss n i A (-a) (-b) u (by simpa using hu)
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev, neg_mul, ofAdd_neg, map_inv, inv_inv,
    ← map_inv (weightTorusPoints n A), ← Pi.mulSingle_inv, mul_assoc] using hi

end TauCeti.TypeBSpinCarrier
