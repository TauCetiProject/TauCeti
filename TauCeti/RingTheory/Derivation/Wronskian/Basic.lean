/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.RingTheory.Derivation.Basic

/-!
# Wronskians and linear independence

The Wronskian of a finite family is the determinant whose rows are its successive
derivatives. In a differential field, it is nonzero exactly when the family is linearly independent
over the constant field of the derivation when the scalars act faithfully. The constant-field
hypothesis is explicit: every element killed by the derivation must come from the scalars.
No characteristic assumption is needed with this hypothesis.

Scalar changes of generators multiply the Wronskian by the determinant of the coefficient
matrix, so an invertible change of basis preserves its nonvanishing. This law holds over
commutative rings. A Wronskian that is a non-zero-divisor implies linear independence over any
faithfully acting scalar semiring. In an integral domain, nonvanishing suffices; the converse
requires an ambient differential field.

This criterion supplies the nonvanishing required to define ramification divisors of linear
series by Wronskians. The differential-field argument follows the Wronskian method in
D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003.
-/

public section

noncomputable section

namespace Derivation

open Matrix

variable {k F : Type*}

section

variable [CommSemiring k] [CommRing F] [Algebra k F]

/-- The Wronskian of `f`: row `i` consists of its `i`-th derivatives. The empty
family has Wronskian `1`. -/
def wronskian (D : Derivation k F F) {n : ℕ} (f : Fin n → F) : F :=
  Matrix.det (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (f j))

/-- The determinant characterizing the Wronskian. -/
theorem wronskian_def (D : Derivation k F F) {n : ℕ} (f : Fin n → F) :
    D.wronskian f = Matrix.det (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (f j)) :=
  (rfl)

@[simp]
theorem wronskian_empty (D : Derivation k F F) (f : Fin 0 → F) : D.wronskian f = 1 := by
  rw [wronskian_def]
  exact Matrix.det_fin_zero

@[simp]
theorem wronskian_singleton (D : Derivation k F F) (f : Fin 1 → F) :
    D.wronskian f = f 0 := by
  rw [wronskian_def, Matrix.det_fin_one]
  simp

end

section

variable [CommRing k] [CommRing F] [Algebra k F]

/-- A scalar change of generators multiplies the Wronskian by the determinant of its
coefficient matrix. The columns of `A` give the coefficients of the new family. -/
theorem wronskian_sum_smul (D : Derivation k F F) {n : ℕ} (f : Fin n → F)
    (A : Matrix (Fin n) (Fin n) k) :
    D.wronskian (fun j ↦ ∑ i, A i j • f i) =
      D.wronskian f * algebraMap k F A.det := by
  classical
  have hmatrix :
      (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (∑ l, A l j • f l)) =
        (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (f j)) *
          (algebraMap k F).mapMatrix A := by
    ext i j
    simp only [Matrix.of_apply]
    rw [D.iterate_sum_smul]
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  rw [wronskian_def, hmatrix, Matrix.det_mul, ← RingHom.map_det, ← wronskian_def]

/-- An invertible scalar change of generators preserves nonvanishing of the Wronskian.
This does not require the scalars to contain every constant of the derivation. -/
theorem wronskian_sum_smul_ne_zero_iff (D : Derivation k F F) {n : ℕ} (f : Fin n → F)
    (A : Matrix (Fin n) (Fin n) k) (hA : IsUnit A.det) :
    D.wronskian (fun j ↦ ∑ i, A i j • f i) ≠ 0 ↔ D.wronskian f ≠ 0 := by
  rw [D.wronskian_sum_smul]
  simpa using ((hA.map (algebraMap k F)).mul_left_inj (b := D.wronskian f) (c := 0)).not

end

/-- A Wronskian that is a non-zero-divisor implies linear independence over any faithfully
acting scalar semiring, even if the derivation has additional constants. -/
theorem linearIndependent_of_wronskian_mem_nonZeroDivisors [CommSemiring k] [CommRing F]
    [Algebra k F] [FaithfulSMul k F] (D : Derivation k F F)
    {n : ℕ} {f : Fin n → F} (hw : D.wronskian f ∈ nonZeroDivisors F) :
    LinearIndependent k f := by
  classical
  rw [wronskian_def] at hw
  apply Fintype.linearIndependent_iffₛ.mpr
  intro a b hab j
  apply FaithfulSMul.algebraMap_injective k F
  have hjets :
      (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (f j)) *ᵥ
          (fun j ↦ algebraMap k F (a j)) =
        (Matrix.of fun i j : Fin n ↦ (D : F → F)^[i.val] (f j)) *ᵥ
          (fun j ↦ algebraMap k F (b j)) := by
    ext i
    have h := congrArg (D : F → F)^[i.val] hab
    simp only [D.iterate_sum_smul] at h
    simpa [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm] using h
  exact congrFun (Matrix.mulVec_injective_of_det_mem_nonZeroDivisors hw hjets) j

/-- Nonzero Wronskian implies linear independence over any faithfully acting scalar
semiring, even if the derivation has additional constants. -/
theorem linearIndependent_of_wronskian_ne_zero [CommSemiring k] [CommRing F]
    [NoZeroDivisors F] [Algebra k F] [FaithfulSMul k F] (D : Derivation k F F)
    {n : ℕ} {f : Fin n → F} (hw : D.wronskian f ≠ 0) : LinearIndependent k f :=
  D.linearIndependent_of_wronskian_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hw)

/-- A linearly independent family has nonzero Wronskian if every constant of the
derivation comes from the scalars. -/
theorem wronskian_ne_zero_of_linearIndependent [CommSemiring k] [Field F] [Algebra k F]
    (D : Derivation k F F)
    (hconst : ∀ y : F, D y = 0 → ∃ a : k, algebraMap k F a = y)
    {n : ℕ} {f : Fin n → F} (hf : LinearIndependent k f) : D.wronskian f ≠ 0 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
      Matrix.of fun i j ↦ (D : F → F)^[i.val] (f j)
    let N : Matrix (Fin n) (Fin n) F :=
      Matrix.of fun i j ↦ (D : F → F)^[i.val] (f j.castSucc)
    have hN : N.det ≠ 0 := by
      simpa only [wronskian_def, Function.comp_def] using
        ih (hf.comp Fin.castSucc (Fin.castSucc_injective n))
    intro hdet
    rw [wronskian_def] at hdet
    obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hrow (i : Fin (n + 1)) : ∑ j, M i j * c j = 0 :=
      congrFun hMc i
    -- The independent initial family makes the last kernel coefficient nonzero.
    have hlast : c (Fin.last n) ≠ 0 := by
      intro hz
      have hNc : N *ᵥ (fun j ↦ c j.castSucc) = 0 := by
        ext i
        have h := hrow i.castSucc
        simpa [Fin.sum_univ_castSucc, hz, M, N, Matrix.mulVec, dotProduct] using h
      have hzero := Matrix.eq_zero_of_mulVec_eq_zero hN hNc
      apply hc
      ext j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · exact hz
      · exact congrFun hzero i
    let b : Fin (n + 1) → F := fun j ↦ c j / c (Fin.last n)
    have hb : b (Fin.last n) = 1 := div_self hlast
    have hMb (i : Fin (n + 1)) : ∑ j, M i j * b j = 0 := by
      simp only [b, ← mul_div_assoc, ← Finset.sum_div, hrow, zero_div]
    -- Normalize that coefficient to one, then differentiate and subtract the next row.
    have hDb : N *ᵥ (fun j ↦ D (b j.castSucc)) = 0 := by
      ext i
      have hd := congrArg D (hMb i.castSucc)
      have hnext := hMb i.succ
      have hshift (j : Fin (n + 1)) : D (M i.castSucc j) = M i.succ j := by
        simp [M, Function.iterate_succ_apply']
      have hsum : ∑ j, M i.castSucc j * D (b j) = 0 := by
        simpa only [map_sum, D.leibniz, smul_eq_mul, hshift, mul_comm (b _),
          Finset.sum_add_distrib, hnext, zero_add, add_zero, D.map_zero] using hd
      simpa [Fin.sum_univ_castSucc, hb, M, N, Matrix.mulVec, dotProduct] using hsum
    have hDbzero := Matrix.eq_zero_of_mulVec_eq_zero hN hDb
    -- The resulting kernel vector vanishes, so the original relation has constant coefficients.
    have hkill (j : Fin (n + 1)) : D (b j) = 0 := by
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · simp [hb]
      · exact congrFun hDbzero i
    choose a ha using fun j ↦ hconst (b j) (hkill j)
    have hrel : ∑ j, a j • f j = 0 := by
      simpa [M, ← ha, Algebra.smul_def, mul_comm] using hMb 0
    have hazero := Fintype.linearIndependent_iffₛ.mp hf a 0 (by simpa using hrel) (Fin.last n)
    have := ha (Fin.last n)
    simp [hazero, hb] at this

/-- The Wronskian detects linear independence when the scalars embed faithfully and
contain every constant of the derivation. -/
theorem wronskian_ne_zero_iff [CommSemiring k] [Field F] [Algebra k F]
    [FaithfulSMul k F] (D : Derivation k F F)
    (hconst : ∀ y : F, D y = 0 → ∃ a : k, algebraMap k F a = y)
    {n : ℕ} (f : Fin n → F) : D.wronskian f ≠ 0 ↔ LinearIndependent k f :=
  ⟨D.linearIndependent_of_wronskian_ne_zero,
    D.wronskian_ne_zero_of_linearIndependent hconst⟩

end Derivation
