/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
import Mathlib.Probability.StrongLaw
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
    ((strictUpperEquivNat_lt_choose_iff _ _).1 (by simpa only [Equiv.apply_symm_apply] using k.2))
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
  let g (p : Fin n × Fin n) := if h : p.1 < p.2 then
    ‖ξ ⟨(p.1.val, p.2.val), h⟩ ω - ζ ⟨(p.1.val, p.2.val), h⟩ ω‖ ^ 2 else 0
  have hentry (i j : Fin n) :
      ‖(wignerMatrix ξ η n ω - wignerMatrix ζ η n ω) i j‖ ^ 2 =
        (n : ℝ)⁻¹ * (g (i, j) + g (j, i)) := by
    have hn : ‖(Real.sqrt n : ℂ)⁻¹‖ ^ 2 = (n : ℝ)⁻¹ := by
      simp [norm_inv, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
    rcases lt_trichotomy i.val j.val with h | h | h
    · have hij : i < j := h
      simp only [Matrix.sub_apply, wignerMatrix_apply_of_lt _ _ _ h, g, dite_eq_left hij,
        dite_eq_right hij.not_gt, add_zero, ← mul_sub, norm_mul, mul_pow, hn]
    · obtain rfl := Fin.ext h
      simp [g]
    · have hji : j < i := h
      simp only [Matrix.sub_apply, wignerMatrix_apply_of_gt _ _ _ h, g, dite_eq_left hji,
        dite_eq_right hji.not_gt, zero_add, ← mul_sub, ← star_sub, norm_mul, norm_star, mul_pow, hn]
  have hsum : ∑ p, g p = ∑ i : StrictUpperFin n,
      ‖ξ (wignerUpperIndex i) ω - ζ (wignerUpperIndex i) ω‖ ^ 2 := by
    have hf : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n ↦ p.1 < p.2), g p =
        ∑ p, g p := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun p _ ↦ by by_cases hp : p.1 < p.2 <;> simp [g, hp]
    rw [← hf, Finset.sum_subtype (p := fun p : Fin n × Fin n ↦ p.1.val < p.2.val) _ (by simp)]
    exact Finset.sum_congr rfl fun (i : StrictUpperFin n) _ ↦ by
      have hi : wignerUpperIndex i = ⟨(i.val.1.val, i.val.2.val), i.prop⟩ :=
        Subtype.ext (wignerUpperIndex_val _)
      have hlt : i.val.1 < i.val.2 := i.prop
      simp only [hi, g, dite_eq_left hlt]
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  simp only [hentry, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ g (j, i)), ← Fintype.sum_prod_type, hsum]
  ring

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

end Probability

end TauCeti
