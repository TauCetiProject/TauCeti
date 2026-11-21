/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Probability.StrongLaw
import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Matrix.Normed

/-!
# Strong law for upper-triangular corners

In column order, the strictly upper entries of an `n × n` corner form an initial segment of
length `n.choose 2`. The strong law then controls empirical averages over the corner, including
the entrywise squared errors that give the Frobenius distance of two Wigner matrices.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix.Norms.Frobenius

namespace TauCeti

private theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

private theorem strictUpperIndex_lt_choose_iff (ij : StrictUpper) (n : ℕ) :
    ij.val.2.choose 2 + ij.val.1 < n.choose 2 ↔ ij.val.2 < n := by
  constructor
  · contrapose!
    intro h
    exact (Nat.choose_mono 2 h).trans (Nat.le_add_right _ _)
  · intro h
    calc
      _ < (ij.val.2 + 1).choose 2 := by rw [choose_two_succ]; exact Nat.add_lt_add_left ij.prop _
      _ ≤ _ := Nat.choose_mono 2 h

/-- The column-by-column enumeration of strictly upper-triangular indices. -/
def strictUpperEquivNat : StrictUpper ≃ ℕ := by
  refine Equiv.ofBijective (fun ij ↦ ij.val.2.choose 2 + ij.val.1) ⟨?_, ?_⟩
  · intro x y h
    dsimp only at h
    have hx := (strictUpperIndex_lt_choose_iff x (y.val.2 + 1)).mp (h.symm ▸
      (strictUpperIndex_lt_choose_iff y (y.val.2 + 1)).mpr (Nat.lt_succ_self _))
    have hy := (strictUpperIndex_lt_choose_iff y (x.val.2 + 1)).mp (h ▸
      (strictUpperIndex_lt_choose_iff x (x.val.2 + 1)).mpr (Nat.lt_succ_self _))
    have hs : x.val.2 = y.val.2 := by omega
    exact Subtype.ext (Prod.ext (by rw [hs, Nat.add_right_inj] at h; exact h) hs)
  · intro k
    induction k with
    | zero => exact ⟨⟨(0, 1), by decide⟩, by simp⟩
    | succ k ih =>
      obtain ⟨⟨⟨i, j⟩, hij⟩, hk⟩ := ih
      dsimp only at hk
      by_cases h : i + 1 < j
      · refine ⟨⟨(i + 1, j), h⟩, ?_⟩
        dsimp only
        omega
      · refine ⟨⟨(0, j + 1), Nat.zero_lt_succ _⟩, ?_⟩
        dsimp only
        rw [choose_two_succ, add_zero]
        omega

/-- The index of a strictly upper entry is the size of the preceding columns plus its row. -/
@[simp]
theorem strictUpperEquivNat_apply (ij : StrictUpper) :
    strictUpperEquivNat ij = ij.val.2.choose 2 + ij.val.1 :=
  (rfl)

/-- The upper entries of the corner of size `n` are the initial segment of length `n.choose 2`. -/
theorem strictUpperEquivNat_lt_choose_iff (ij : StrictUpper) (n : ℕ) :
    strictUpperEquivNat ij < n.choose 2 ↔ ij.val.2 < n :=
  strictUpperIndex_lt_choose_iff ij n

private def strictUpperFinOfIndex {n : ℕ} (ij : StrictUpper) (hj : ij.val.2 < n) :
    StrictUpperFin n :=
  ⟨(⟨ij.val.1, ij.prop.trans hj⟩, ⟨ij.val.2, hj⟩), ij.prop⟩

private theorem wignerUpperIndex_strictUpperFinOfIndex {n : ℕ} (ij : StrictUpper)
    (hj : ij.val.2 < n) : wignerUpperIndex (strictUpperFinOfIndex ij hj) = ij := by
  exact Subtype.ext (wignerUpperIndex_val _)

private def strictUpperFinEquiv (n : ℕ) : StrictUpperFin n ≃ Fin (n.choose 2) where
  toFun ij := ⟨strictUpperEquivNat (wignerUpperIndex ij),
    (strictUpperEquivNat_lt_choose_iff _ _).2 (by simp)⟩
  invFun k := strictUpperFinOfIndex (strictUpperEquivNat.symm k)
    ((strictUpperEquivNat_lt_choose_iff _ _).1
      (by simpa only [Equiv.apply_symm_apply] using k.isLt))
  left_inv ij := by
    have h := strictUpperEquivNat.symm_apply_apply (wignerUpperIndex ij)
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact (congrArg (fun x : StrictUpper ↦ x.val.1) h).trans (by simp)
    · exact (congrArg (fun x : StrictUpper ↦ x.val.2) h).trans (by simp)
  right_inv k := by
    apply Fin.ext
    exact (congrArg strictUpperEquivNat (wignerUpperIndex_strictUpperFinOfIndex _ _)).trans
      (strictUpperEquivNat.apply_symm_apply k)

/-- A sum over a finite strictly upper corner is the sum over the corresponding prefix
of the column-order enumeration. -/
theorem sum_strictUpperFin_eq_sum_range {E : Type*} [AddCommMonoid E]
    (n : ℕ) (f : StrictUpper → E) :
    ∑ ij : StrictUpperFin n, f (wignerUpperIndex ij) =
      ∑ k ∈ Finset.range (n.choose 2), f (strictUpperEquivNat.symm k) := by
  calc
    _ = ∑ k : Fin (n.choose 2), f (strictUpperEquivNat.symm k) :=
      Fintype.sum_equiv (strictUpperFinEquiv n) _ _
        fun ij ↦ congrArg f (strictUpperEquivNat.symm_apply_apply _).symm
    _ = _ := by
      rw [Finset.sum_fin_eq_sum_range]
      exact Finset.sum_congr rfl fun k hk ↦ dite_eq_left (Finset.mem_range.mp hk)

namespace Probability

/-- Squared Frobenius error between Wigner matrices with a common diagonal, in terms of
the squared errors on the strictly upper corner. -/
theorem norm_wignerMatrix_sub_sq_eq_sum_strictUpperFin
    {Ω : Type*} {ξ : StrictUpper → Ω → ℂ} (ζ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ η n ω - wignerMatrix ζ η n ω‖ ^ 2 =
      (2 / (n : ℝ)) * ∑ i : StrictUpperFin n,
        ‖ξ (wignerUpperIndex i) ω - ζ (wignerUpperIndex i) ω‖ ^ 2 := by
  let D := wignerMatrix ξ η n ω - wignerMatrix ζ η n ω
  have hD : D.IsHermitian :=
    (wignerMatrix_isHermitian ξ η ω n).sub (wignerMatrix_isHermitian ζ η ω n)
  have hsymm (i j : Fin n) : ‖D i j‖ ^ 2 = ‖D j i‖ ^ 2 := by
    rw [← hD.apply i j, norm_star]
  have hdiag (i : Fin n) : ‖D i i‖ ^ 2 = 0 := by
    simp [D]
  have hn : ‖(Real.sqrt n : ℂ)⁻¹‖ ^ 2 = (n : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hupper (p : StrictUpperFin n) : ‖D p.val.1 p.val.2‖ ^ 2 =
      (n : ℝ)⁻¹ * ‖ξ (wignerUpperIndex p) ω - ζ (wignerUpperIndex p) ω‖ ^ 2 := by
    have hp : wignerUpperIndex p = ⟨(p.val.1.val, p.val.2.val), p.prop⟩ :=
      Subtype.ext (wignerUpperIndex_val _)
    simp only [D, Matrix.sub_apply, wignerMatrix_apply_of_lt _ _ _ p.prop,
      hp, ← mul_sub, norm_mul, mul_pow, hn]
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    sum_symmetric_pairs _ hsymm]
  simp only [hdiag, Finset.sum_const_zero, zero_add, hupper, ← Finset.mul_sum, nsmul_eq_mul,
    Nat.cast_ofNat, div_eq_mul_inv, mul_assoc]
  rfl

/-- Strong law for the arithmetic means of the strictly upper triangular corners of an
identically distributed, pairwise independent array. -/
theorem ae_tendsto_sum_strictUpperFin_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : StrictUpper → Ω → ℝ} (hInt : Integrable (X ⟨(0, 1), by decide⟩) P)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hid : ∀ i, IdentDistrib (X i) (X ⟨(0, 1), by decide⟩) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      (∑ ij : StrictUpperFin n, X (wignerUpperIndex ij) ω) / (n.choose 2 : ℝ))
      atTop (𝓝 (∫ ω, X ⟨(0, 1), by decide⟩ ω ∂P)) := by
  let Y (k : ℕ) := X (strictUpperEquivNat.symm k)
  have h0 : strictUpperEquivNat.symm 0 = ⟨(0, 1), by decide⟩ := by
    apply strictUpperEquivNat.injective
    simp
  have hd : Tendsto (fun n : ℕ ↦ n.choose 2) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hs := choose_two_succ (n - 1)
    have hp : 1 ≤ (n - 1).choose 2 := Nat.choose_pos (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
    dsimp only [id_eq]
    omega
  have hY := strong_law_ae_real Y (by simpa only [Y, h0] using hInt)
    (fun i j hij ↦ hind (strictUpperEquivNat.symm.injective.ne hij))
    (fun i ↦ by simpa only [Y, h0] using hid (strictUpperEquivNat.symm i))
  filter_upwards [hY] with ω hω
  simp_rw [sum_strictUpperFin_eq_sum_range _ (fun ij ↦ X ij ω)]
  simpa only [Function.comp_def, Y, h0] using hω.comp hd

/-- The largest absolute entry of the zero-diagonal normalized Wigner corners vanishes
almost surely under a common finite fourth moment. Independence is unnecessary. -/
theorem ae_eventually_norm_wignerMatrix_zero_apply_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : StrictUpper → Ω → ℂ} {X : Ω → ℂ}
    (hid : ∀ ij, IdentDistrib (ξ ij) X P P) (hX : MemLp X 4 P) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin (n + 1), ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖ ≤ ε := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hm : ∀ᶠ n : ℕ in atTop, ((n + 1).choose 2 : ℝ) ≤ Real.sqrt (n + 1 : ℕ) ^ 4 :=
    .of_forall fun n ↦ by
      have hpow : Real.sqrt (n + 1 : ℕ) ^ 4 = ((n + 1 : ℕ) : ℝ) ^ 2 := calc
        _ = (Real.sqrt (n + 1 : ℕ) ^ 2) ^ 2 := by norm_num [← pow_mul]
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [hpow]
      exact_mod_cast Nat.choose_le_pow (n + 1) 2
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib
    (fun k ↦ hid (strictUpperEquivNat.symm k)) hX hs hm] with ω hω
  intro ε hε
  filter_upwards [hω ε hε] with n hn i j
  have hscale (ij : StrictUpper) (hij : ij.val.2 < n + 1) :
      (Real.sqrt (n + 1 : ℕ))⁻¹ * ‖ξ ij ω‖ ≤ ε := by
    have h := hn _ ((strictUpperEquivNat_lt_choose_iff ij _).2 hij)
    rw [Equiv.symm_apply_apply] at h
    rw [inv_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.2 (by positivity)), mul_comm]
    simpa only [mul_comm ε] using h
  by_cases hij : i = j
  · subst j
    simpa using hε.le
  · rw [norm_wignerMatrix_apply_of_ne _ _ _ hij]
    exact hscale _ (max_lt i.isLt j.isLt)

end Probability

end TauCeti
