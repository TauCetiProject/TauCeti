/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FittingIdeal.Determinant
import Mathlib.Tactic.LinearCombination

/-!
# Codimension-one minors of a matrix with left and right null vectors

For a square matrix of size `n + 1`, left and right null vectors whose last coordinates
are units allow its `n`-minors ideal to be computed from its last principal minor.
The right null vector removes the last relation generator, and the left null vector
expresses the last ambient coordinate in terms of the others. No rank or domain
assumption is needed, so the formula also applies when every codimension-one minor vanishes.

This is the algebraic calculation relating a Burau corner determinant to the
presentation ideal of an Alexander module.

Reference: J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 3.
-/

public section

noncomputable section

namespace Matrix

open LinearMap Finset

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The right null vector eliminates the last generator of the image: the principal minor `B` of `A`
sends the reduced coordinates of `x` to the first `n` coordinates of `A *ᵥ x`. -/
private theorem submatrix_castSucc_mulVec_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u : Fin (n + 1) → R} (hu : A *ᵥ u = 0) (huunit : IsUnit (u (Fin.last n)))
    (x : Fin (n + 1) → R) :
    (A.submatrix Fin.castSucc Fin.castSucc) *ᵥ (fun i => x i.castSucc -
      u i.castSucc * ((huunit.unit⁻¹ : Rˣ) : R) * x (Fin.last n)) =
        LinearMap.funLeft R R Fin.castSucc (A *ᵥ x) := by
  have huinv : ((huunit.unit⁻¹ : Rˣ) : R) * u (Fin.last n) = 1 := by
    simpa only [huunit.unit_spec] using Units.inv_mul huunit.unit
  have hcol (i : Fin (n + 1)) :
      A i (Fin.last n) =
        -((huunit.unit⁻¹ : Rˣ) : R) * ∑ j : Fin n, A i j.castSucc * u j.castSucc := by
    have h := congrFun hu i
    simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.zero_apply] at h
    calc A i (Fin.last n) =
        ((huunit.unit⁻¹ : Rˣ) : R) * (A i (Fin.last n) * u (Fin.last n)) := by
          rw [mul_left_comm, huinv, mul_one]
      _ = _ := by linear_combination ((huunit.unit⁻¹ : Rˣ) : R) * h
  ext i
  simp only [LinearMap.funLeft_apply, mulVec, dotProduct, submatrix_apply,
    Fin.sum_univ_castSucc, hcol, mul_sub, Finset.sum_sub_distrib]
  simp only [sub_eq_add_neg, neg_mul, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The left null vector recovers the last coordinate of every image vector from the others. -/
private theorem mulVec_last_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {w : Fin (n + 1) → R} (hw : w ᵥ* A = 0) (hwunit : IsUnit (w (Fin.last n)))
    (x : Fin (n + 1) → R) :
    (A *ᵥ x) (Fin.last n) =
      -((hwunit.unit⁻¹ : Rˣ) : R) *
        ∑ i : Fin n, w i.castSucc * (A *ᵥ x) i.castSucc := by
  have hwinv : ((hwunit.unit⁻¹ : Rˣ) : R) * w (Fin.last n) = 1 := by
    simpa only [hwunit.unit_spec] using Units.inv_mul hwunit.unit
  have h : w ⬝ᵥ (A *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, hw, zero_dotProduct]
  simp only [dotProduct, Fin.sum_univ_castSucc] at h
  calc (A *ᵥ x) (Fin.last n) =
      ((hwunit.unit⁻¹ : Rˣ) : R) * (w (Fin.last n) * (A *ᵥ x) (Fin.last n)) := by
        rw [← mul_assoc, hwinv, one_mul]
    _ = _ := by linear_combination ((hwunit.unit⁻¹ : Rˣ) : R) * h

/-- The `n`-minors ideal of an `(n + 1)`-square matrix with left and right null vectors equals
that of its last principal minor, provided the last coordinates of both null vectors are units. -/
private theorem minorsIdeal_range_eq_minorsIdeal_range_submatrix_castSucc
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u w : Fin (n + 1) → R} (hu : A *ᵥ u = 0) (hw : w ᵥ* A = 0)
    (huunit : IsUnit (u (Fin.last n))) (hwunit : IsUnit (w (Fin.last n))) :
    (range A.mulVecLin).minorsIdeal n =
      (range (A.submatrix Fin.castSucc Fin.castSucc).mulVecLin).minorsIdeal n := by
  classical
  let B := A.submatrix Fin.castSucc Fin.castSucc
  let π : (Fin (n + 1) → R) →ₗ[R] (Fin n → R) :=
    LinearMap.funLeft R R Fin.castSucc
  let P : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
    LinearMap.pi (Fin.lastCases
      (-((hwunit.unit⁻¹ : Rˣ) : R) •
        ∑ i : Fin n, w i.castSucc • LinearMap.proj i)
      (fun i => LinearMap.proj i))
  have hupper : range A.mulVecLin ≤ (range B.mulVecLin).map P := by
    rintro _ ⟨x, rfl⟩
    refine ⟨π (A *ᵥ x), ?_, ?_⟩
    · exact ⟨_, submatrix_castSucc_mulVec_eq A hu huunit x⟩
    · ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [P, π, LinearMap.pi_apply, Fin.lastCases_last, LinearMap.neg_apply,
          LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply,
          LinearMap.funLeft_apply, smul_eq_mul, Matrix.mulVecLin_apply] using
            (mulVec_last_eq A hw hwunit x).symm
      · simp [P, π]
  have hlower : range B.mulVecLin ≤ (range A.mulVecLin).map π := by
    rintro _ ⟨x, rfl⟩
    refine ⟨A *ᵥ Fin.lastCases 0 x, ⟨_, rfl⟩, ?_⟩
    ext i
    simp [π, B, mulVec, dotProduct, Fin.sum_univ_castSucc]
  exact le_antisymm
    ((Submodule.minorsIdeal_mono hupper n).trans (Submodule.minorsIdeal_map_le P _ n))
    ((Submodule.minorsIdeal_mono hlower n).trans (Submodule.minorsIdeal_map_le π _ n))

/-- The `n`-minors ideal of an `(n + 1)`-square matrix with left and right null vectors
is generated by its last principal minor, provided the last coordinates of both
null vectors are units. This includes matrices of rank smaller than `n`. -/
theorem minorsIdeal_range_eq_span_det_submatrix_castSucc
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    {u w : Fin (n + 1) → R} (hu : A *ᵥ u = 0) (hw : w ᵥ* A = 0)
    (huunit : IsUnit (u (Fin.last n))) (hwunit : IsUnit (w (Fin.last n))) :
    (range A.mulVecLin).minorsIdeal n =
      Ideal.span {(A.submatrix Fin.castSucc Fin.castSucc).det} := by
  classical
  nontriviality R
  rw [minorsIdeal_range_eq_minorsIdeal_range_submatrix_castSucc A hu hw huunit hwunit]
  have hdet :=
    (Matrix.toLin' (A.submatrix Fin.castSucc Fin.castSucc)).minorsIdeal_range_finrank_eq_span_det
  rw [LinearMap.det_toLin'] at hdet
  simpa only [Module.finrank_fin_fun, Matrix.toLin'_apply'] using hdet

end Matrix
