/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Sinkhorn.Basic

/-!
# A posteriori error certificates for Sinkhorn scaling

The usual geometric convergence estimate contains the distance to the unknown optimal scaling
factors. Here that distance is bounded by the Hilbert distance between a positive vector and its
next Sinkhorn iterate. Thus every bound on the right-hand side can be evaluated without knowing
the limiting plan.

For `t = tanh (Δ(K) / 4)`, the full step contracts by `t²`, giving a row-factor error at most
`d(u, F(u)) / (1 - t²)`. One column update gives the bound
`E = t * d(u, F(u)) / (1 - t²)`. The Sinkhorn plan and the exact scaling agree entrywise up to
`exp E`. In particular their entrywise absolute error is bounded by `(exp E - 1)` times the
computed entry. Summing gives an error certificate in the sum of absolute entry differences.

The column residual has the same bound, and the row residual is zero. Equal marginal mass is
needed only for existence of the exact scaling, not for defining the certificate. The computed
plan generally does not have both prescribed marginals, so these are approximation certificates,
not objective-gap bounds for a feasible plan.

Use `TauCeti.sinkhornErrorBound K a b u` to evaluate the certificate. Its characteristic
and error lemmas are also in `TauCeti`. After `open TauCeti`, the certificate can be written
as `sinkhornErrorBound K a b u`; the iteration and plan operations are in `Matrix`.

## References

* J. Franklin and J. Lorenz, *On the scaling of multidimensional matrices*, Linear Algebra Appl.
  114/115 (1989), 717--735, for Hilbert-metric contraction in matrix scaling.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Section 4.2, for Sinkhorn iteration.

The fixed-point estimate is the Hilbert-pseudometric analogue of Mathlib's
`ContractingWith.dist_le_of_fixedPoint`; no metric on scaling factors is assumed.
-/

public section

open Matrix Real
open scoped BigOperators

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A computable-in-real-arithmetic bound on the column-factor Hilbert error, using one full
Sinkhorn step from `u`. Its denominator is positive for every finite real kernel. -/
noncomputable def sinkhornErrorBound (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (u : ι → ℝ) : ℝ :=
  tanh (K.projectiveDiameter / 4) * hilbertProjectiveDist u (K.sinkhornStep a b u) /
    (1 - tanh (K.projectiveDiameter / 4) ^ 2)

/-- The defining formula of the a posteriori certificate. -/
theorem sinkhornErrorBound_def (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) :
    sinkhornErrorBound K a b u =
      tanh (K.projectiveDiameter / 4) * hilbertProjectiveDist u (K.sinkhornStep a b u) /
        (1 - tanh (K.projectiveDiameter / 4) ^ 2) :=
  (rfl)

/-- The a posteriori certificate is nonnegative. -/
theorem sinkhornErrorBound_nonneg (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ) (u : ι → ℝ) :
    0 ≤ sinkhornErrorBound K a b u := by
  rw [sinkhornErrorBound_def]
  exact div_nonneg (mul_nonneg (tanh_projectiveDiameter_div_four_nonneg K)
    (hilbertProjectiveDist_nonneg _ _)) (sub_pos.mpr (Real.tanh_sq_lt_one _)).le

/-- The certificate vanishes at a fixed point of the Sinkhorn step. -/
@[simp]
theorem sinkhornErrorBound_eq_zero_of_sinkhornStep_eq {K : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ}
    {u : ι → ℝ} (h : K.sinkhornStep a b u = u) : sinkhornErrorBound K a b u = 0 := by
  simp [sinkhornErrorBound_def, h]

/-- **A posteriori row-factor error.** The distance to any positive fixed point is controlled by
one observed Sinkhorn step. No normalization of the scaling factors is required. -/
theorem hilbertProjectiveDist_le_hilbertProjectiveDist_sinkhornStep_div_of_sinkhornStep_eq
    {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, a i ≠ 0)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {u uStar : ι → ℝ}
    (hu : ∀ i, 0 < u i) (huStar : ∀ i, 0 < uStar i)
    (hfixed : K.sinkhornStep a b uStar = uStar) :
    hilbertProjectiveDist u uStar ≤ hilbertProjectiveDist u (K.sinkhornStep a b u) /
      (1 - tanh (K.projectiveDiameter / 4) ^ 2) := by
  have hcontract := hilbertProjectiveDist_sinkhornStep_le hK ha hb hu huStar
  rw [hfixed] at hcontract
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have hstep : K.sinkhornStep a b u = K.sinkhornStep a b uStar := by
      simp only [sinkhornStep_def, Subsingleton.elim (Kᵀ.sinkhornUpdate b u)
        (Kᵀ.sinkhornUpdate b uStar)]
    rw [hstep, hfixed]
    exact le_div_iff₀ (sub_pos.mpr (Real.tanh_sq_lt_one _)) |>.mpr (by
      nlinarith [sq_nonneg (tanh (K.projectiveDiameter / 4)),
        hilbertProjectiveDist_nonneg u uStar])
  have hnext : ∀ i, K.sinkhornStep a b u i ≠ 0 := by
    intro i
    have : Nonempty ι := ⟨i⟩
    rw [sinkhornStep_def, sinkhornUpdate_apply]
    exact div_ne_zero (ha i) (by
      rw [mulVec_apply_eq_sum]
      exact (Finset.sum_pos (fun j _ ↦ mul_pos (hK i j)
        (sinkhornUpdate_pos (fun j i ↦ hK i j) hb hu j)) Finset.univ_nonempty).ne')
  have htriangle := hilbertProjectiveDist_triangle u uStar hnext
  rw [le_div_iff₀ (sub_pos.mpr (Real.tanh_sq_lt_one _))]
  nlinarith

/-- **A posteriori column-factor error.** The column update is within the computable
certificate of any positive exact scaling with the prescribed marginals. -/
theorem hilbertProjectiveDist_sinkhornUpdate_le_sinkhornErrorBound {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} {uStar : ι → ℝ}
    {vStar : κ → ℝ} (hP : IsDiagonalScaling P K uStar vStar)
    (hPm : HasMarginals P a b) (huStar : ∀ i, 0 < uStar i) (hvStar : ∀ j, 0 < vStar j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    hilbertProjectiveDist (Kᵀ.sinkhornUpdate b u) vStar ≤ sinkhornErrorBound K a b u := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simpa [hilbertProjectiveDist_def] using sinkhornErrorBound_nonneg K a b u
  have herr := hilbertProjectiveDist_le_hilbertProjectiveDist_sinkhornStep_div_of_sinkhornStep_eq
    hK (fun i ↦ (ha i).ne') hb hu huStar (hP.sinkhornStep_eq hPm hK huStar hvStar)
  have hcol := hP.hilbertProjectiveDist_sinkhornUpdate_iterate_le hPm hK ha hb huStar
    hvStar hu 0
  simp only [Function.iterate_zero, id_eq, Nat.mul_zero, zero_add, pow_one] at hcol
  refine hcol.trans ?_
  rw [sinkhornErrorBound_def, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left herr (tanh_projectiveDiameter_div_four_nonneg K)

/-- Every computed entry is at most `exp E` times the corresponding exact scaling entry. -/
theorem sinkhornPlan_apply_le_exp_sinkhornErrorBound_mul {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} {uStar : ι → ℝ}
    {vStar : κ → ℝ} (hP : IsDiagonalScaling P K uStar vStar)
    (hPm : HasMarginals P a b) (huStar : ∀ i, 0 < uStar i) (hvStar : ∀ j, 0 < vStar j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) (i : ι) (j : κ) :
    K.sinkhornPlan a b u i j ≤ exp (sinkhornErrorBound K a b u) * P i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  refine ((isDiagonalScaling_sinkhornPlan K a b u).apply_le_exp_hilbertProjectiveDist_mul
    hP (hK i) (sinkhornStep_pos hK ha hb hu i).le
    (sinkhornUpdate_pos (fun j i ↦ hK i j) hb hu) hvStar
    ((sum_sinkhornPlan_apply hK a hb hu i).trans (((hasMarginals_def P a b).mp hPm).1 i).symm)
    j).trans ?_
  exact mul_le_mul_of_nonneg_right
    (exp_le_exp.mpr (hilbertProjectiveDist_sinkhornUpdate_le_sinkhornErrorBound hK ha hb hP hPm
      huStar hvStar hu)) (hP.pos hK huStar hvStar i j).le

/-- Every exact scaling entry is at most `exp E` times the corresponding computed entry. -/
theorem le_exp_sinkhornErrorBound_mul_sinkhornPlan_apply {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} {uStar : ι → ℝ}
    {vStar : κ → ℝ} (hP : IsDiagonalScaling P K uStar vStar)
    (hPm : HasMarginals P a b) (huStar : ∀ i, 0 < uStar i) (hvStar : ∀ j, 0 < vStar j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) (i : ι) (j : κ) :
    P i j ≤ exp (sinkhornErrorBound K a b u) * K.sinkhornPlan a b u i j := by
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  have hw := sinkhornUpdate_pos (fun j i ↦ hK i j) hb hu
  refine (hP.apply_le_exp_hilbertProjectiveDist_mul (isDiagonalScaling_sinkhornPlan K a b u)
    (hK i) (huStar i).le hvStar hw ((((hasMarginals_def P a b).mp hPm).1 i).trans
      (sum_sinkhornPlan_apply hK a hb hu i).symm) j).trans ?_
  rw [hilbertProjectiveDist_comm]
  exact mul_le_mul_of_nonneg_right
    (exp_le_exp.mpr (hilbertProjectiveDist_sinkhornUpdate_le_sinkhornErrorBound hK ha hb hP hPm
      huStar hvStar hu))
    ((isDiagonalScaling_sinkhornPlan K a b u).pos hK (sinkhornStep_pos hK ha hb hu) hw i j).le

/-- The certificate itself decreases geometrically along the iteration, starting from the
observed initial step rather than the unknown limiting factors. -/
theorem sinkhornErrorBound_sinkhornStep_iterate_le {K : Matrix ι κ ℝ} (hK : ∀ i j, 0 < K i j)
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) {b : κ → ℝ} (hb : ∀ j, 0 < b j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) (n : ℕ) :
    sinkhornErrorBound K a b ((K.sinkhornStep a b)^[n] u) ≤
      tanh (K.projectiveDiameter / 4) ^ (2 * n) * sinkhornErrorBound K a b u := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · simp [sinkhornErrorBound_def, projectiveDiameter_def]
  have h := hilbertProjectiveDist_sinkhornStep_iterate_le hK ha hb hu
    (sinkhornStep_pos hK ha hb hu) n
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at h
  rw [sinkhornErrorBound_def, sinkhornErrorBound_def]
  calc _ ≤ tanh (K.projectiveDiameter / 4) *
      (tanh (K.projectiveDiameter / 4) ^ (2 * n) *
        hilbertProjectiveDist u (K.sinkhornStep a b u)) /
      (1 - tanh (K.projectiveDiameter / 4) ^ 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h (tanh_projectiveDiameter_div_four_nonneg K))
          (sub_pos.mpr (Real.tanh_sq_lt_one _)).le
    _ = _ := by ring

/-- **Certified entrywise absolute error.** The right-hand side uses only the computed plan
and one additional Sinkhorn step, not the exact scaling factors. -/
theorem abs_sinkhornPlan_apply_sub_le_exp_sinkhornErrorBound_sub_one_mul {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} {uStar : ι → ℝ}
    {vStar : κ → ℝ} (hP : IsDiagonalScaling P K uStar vStar)
    (hPm : HasMarginals P a b) (huStar : ∀ i, 0 < uStar i) (hvStar : ∀ j, 0 < vStar j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) (i : ι) (j : κ) :
    |K.sinkhornPlan a b u i j - P i j| ≤
      (exp (sinkhornErrorBound K a b u) - 1) * K.sinkhornPlan a b u i j := by
  have hup := sinkhornPlan_apply_le_exp_sinkhornErrorBound_mul hK ha hb hP hPm huStar hvStar hu i j
  have hlow := le_exp_sinkhornErrorBound_mul_sinkhornPlan_apply hK ha hb hP hPm huStar hvStar hu i j
  have hexp : 1 ≤ exp (sinkhornErrorBound K a b u) :=
    one_le_exp_iff.mpr (sinkhornErrorBound_nonneg K a b u)
  rw [abs_sub_le_iff]
  constructor
  · by_cases hle : P i j ≤ K.sinkhornPlan a b u i j
    · have hmul := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hexp)
      nlinarith
    · have hnonneg := mul_nonneg (sub_nonneg.mpr hexp) (hP.pos hK huStar hvStar i j).le
      nlinarith
  · nlinarith

/-- **Certified total plan error.** The sum of absolute entry errors is at most the total
marginal mass times `exp E - 1`. -/
theorem sum_sum_abs_sinkhornPlan_apply_sub_le_exp_sinkhornErrorBound_sub_one_mul {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) {P : Matrix ι κ ℝ} {uStar : ι → ℝ}
    {vStar : κ → ℝ} (hP : IsDiagonalScaling P K uStar vStar)
    (hPm : HasMarginals P a b) (huStar : ∀ i, 0 < uStar i) (hvStar : ∀ j, 0 < vStar j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    ∑ i, ∑ j, |K.sinkhornPlan a b u i j - P i j| ≤
      (exp (sinkhornErrorBound K a b u) - 1) * ∑ i, a i := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have ha0 : ∀ i, a i = 0 := fun i ↦ by
      simpa using (((hasMarginals_def P a b).mp hPm).1 i).symm
    simp [ha0]
  calc _ ≤ ∑ i, ∑ j, (exp (sinkhornErrorBound K a b u) - 1) *
      K.sinkhornPlan a b u i j :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          abs_sinkhornPlan_apply_sub_le_exp_sinkhornErrorBound_sub_one_mul
            hK ha hb hP hPm huStar hvStar hu i j
    _ = _ := by simp only [← Finset.mul_sum, sum_sinkhornPlan_apply hK a hb hu]

/-- **Certified column residual.** For positive marginals of equal mass, the sum of absolute
column-marginal errors is bounded by the computable a posteriori certificate. Row marginals
are already exact by `Matrix.sum_sinkhornPlan_apply`. -/
theorem sum_abs_sum_sinkhornPlan_apply_sub_le_exp_sinkhornErrorBound_sub_one_mul {K : Matrix ι κ ℝ}
    (hK : ∀ i j, 0 < K i j) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    {b : κ → ℝ} (hb : ∀ j, 0 < b j) (hmass : ∑ i, a i = ∑ j, b j)
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    ∑ j, |(∑ i, K.sinkhornPlan a b u i j) - b j| ≤
      (exp (sinkhornErrorBound K a b u) - 1) * ∑ i, a i := by
  obtain ⟨uStar, vStar, huStar, hvStar, hrow, hcol⟩ := exists_sinkhorn_scaling hK ha hb hmass
  let P : Matrix ι κ ℝ := fun i j ↦ uStar i * K i j * vStar j
  have hP : IsDiagonalScaling P K uStar vStar :=
    (isDiagonalScaling_def P K uStar vStar).mpr (fun _ _ ↦ rfl)
  have hPm : HasMarginals P a b := (hasMarginals_def P a b).mpr ⟨hrow, hcol⟩
  calc _ = ∑ j, |∑ i, (K.sinkhornPlan a b u i j - P i j)| := by
          simp only [Finset.sum_sub_distrib, ((hasMarginals_def P a b).mp hPm).2]
    _ ≤ ∑ j, ∑ i, |K.sinkhornPlan a b u i j - P i j| :=
          Finset.sum_le_sum fun j _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, |K.sinkhornPlan a b u i j - P i j| := Finset.sum_comm
    _ ≤ _ := sum_sum_abs_sinkhornPlan_apply_sub_le_exp_sinkhornErrorBound_sub_one_mul
      hK ha hb hP hPm huStar hvStar hu

end TauCeti
