/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
public import TauCeti.Analysis.Complex.PowerSeries.TaylorRemainder
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Multi-index Cauchy inequalities and truncated Taylor bounds on polydiscs

On `ι → ℂ` with its sup norm, the open ball of radius `R` is the open polydisc of equal radii `R`.
This file proves **Cauchy's inequality for multi-index coefficients** and the resulting
**truncated Taylor bound** for power series on `ι → ℂ` with values in any complex normed space `V`:

* If the homogeneous polynomial `p (∑ i, α i) (fun _ ↦ z)` is bounded by `M` on the distinguished
  torus `∀ i, ‖z i‖ = ρ` (`0 ≤ ρ`), averaging it against the conjugate character on the finite grid
  `z j i = ρ * ω ^ (j i)` for a primitive `(∑ i, α i + 1)`-th root of unity `ω` extracts
  `p.mvCoeff α` exactly and yields `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M`
  (`FormalMultilinearSeries.norm_mvCoeff_mul_pow_le_of_forall_norm_coord_eq`). Unlike the contour
  identification on `Fin n → ℂ` in `TauCeti.Analysis.Complex.PowerSeries.Identification`, this
  discrete Fourier average applies to any finite index type `ι`, includes `ρ = 0`, and needs no
  completeness of `V`.
* Combining this polynomial extraction with `HasFPowerSeriesOnBall.norm_apply_le` gives Cauchy's
  inequality `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` on a polydisc for `0 ≤ ρ < R`
  (`HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le`).
* Combining `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` with
  `FormalMultilinearSeries.norm_partialSum_le_sum_mvCoeff` bounds `‖f (x + z)‖` on a smaller closed
  polydisc `‖z‖ ≤ r < R` by `(1 + T) * M * (r / R) ^ T` plus
  `∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`
  (`HasFPowerSeriesOnBall.norm_add_le_add_sum_mvCoeff`,
  `HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff`).

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer (2000), §4.5, Lemma 4.13, pp. 134–135.
* Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/Interpolation.lean`, Apache 2.0).
-/

public section

open Finset Metric
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

namespace FormalMultilinearSeries

/-- Character orthogonality on `(ι → Fin m)` for a primitive `m`-th root of unity `ω`: when every
coordinate of `α` and `β` is strictly less than `m`, summing `∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ j i`
over `j : ι → Fin m` isolates `β = α` with weight `m ^ card ι`. -/
private theorem sum_prod_pow_mul_inv_pow_eq [DecidableEq ι] {m : ℕ} (hm0 : m ≠ 0) {ω : ℂ}
    (hprim : IsPrimitiveRoot ω m) {α β : ι → ℕ} (hα : ∀ i, α i < m) (hβ : ∀ i, β i < m) :
    (∑ j : ι → Fin m, ∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) =
      if β = α then (m : ℂ) ^ Fintype.card ι else 0 := by
  have hω_ne : ω ≠ 0 := hprim.ne_zero hm0
  rw [← Fintype.prod_sum (fun i (t : Fin m) ↦ (ω ^ β i * (ω⁻¹) ^ α i) ^ (t : ℕ))]
  split_ifs with hβα
  · subst hβα
    simp [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hω_ne)]
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hβα
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    set ζ : ℂ := ω ^ β i₀ * (ω⁻¹) ^ α i₀
    have hζ1 : ζ ≠ 1 := by
      intro h1
      have hpow : ω ^ β i₀ = ω ^ α i₀ := by
        calc ω ^ β i₀ = ζ * ω ^ α i₀ := by
              simp [ζ, mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hω_ne)]
          _ = ω ^ α i₀ := by rw [h1, one_mul]
      exact hi₀ (hprim.injOn_pow (Finset.mem_range.2 (hβ i₀)) (Finset.mem_range.2 (hα i₀)) hpow)
    have hζm : ζ ^ m = 1 := by
      dsimp only [ζ]
      rw [mul_pow, ← pow_mul, mul_comm (β i₀) m, pow_mul, hprim.pow_eq_one,
        ← pow_mul, mul_comm (α i₀) m, pow_mul, inv_pow, hprim.pow_eq_one]
      simp
    rw [Fin.sum_univ_eq_sum_range (fun t ↦ ζ ^ t) m]
    refine eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hζ1) ?_
    rw [mul_geom_sum, hζm, sub_self]

/-- Discrete Fourier extraction of `p.mvCoeff α` by averaging `p k` over the finite torus grid
`z j i = ρ * ω ^ j i` (`m = k + 1`, `k = ∑ i, α i`). -/
private theorem sum_smul_apply_grid_eq_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries ℂ (ι → ℂ) V) (α : ι → ℕ) (ρ : ℂ) {ω : ℂ}
    (hprim : IsPrimitiveRoot ω (∑ i, α i + 1)) :
    (∑ j : ι → Fin (∑ i, α i + 1),
      (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) •
        p (∑ i, α i) (fun _ i ↦ ρ * ω ^ (j i : ℕ))) =
      (((∑ i, α i + 1 : ℕ) : ℂ) ^ Fintype.card ι) • (ρ ^ (∑ i, α i) • p.mvCoeff α) := by
  set k : ℕ := ∑ i, α i
  set m : ℕ := k + 1
  have hterm (j : ι → Fin m) :
      (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ ρ * ω ^ (j i : ℕ)) =
        ∑ β ∈ univ.piAntidiag k,
          (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) • (ρ ^ k • p.mvCoeff β) := by
    rw [p.apply_eq_sum_mvCoeff k _, smul_sum]
    refine Finset.sum_congr rfl fun β hβ ↦ ?_
    have hcoef : (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) * (∏ i, (ρ * ω ^ (j i : ℕ)) ^ β i) =
        (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) * ρ ^ k := by
      have hρk : (∏ i, ρ ^ β i) = ρ ^ k := by
        rw [Finset.prod_pow_eq_pow_sum, (mem_piAntidiag.1 hβ).1]
      have hfac : (∏ i, (ρ * ω ^ (j i : ℕ)) ^ β i) =
          (∏ i, ρ ^ β i) * ∏ i, (ω ^ β i) ^ (j i : ℕ) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ ↦ by simp only [mul_pow, ← pow_mul, mul_comm (j i : ℕ)]
      have hχ : (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) = ∏ i, ((ω⁻¹) ^ α i) ^ (j i : ℕ) :=
        Finset.prod_congr rfl fun i _ ↦ by rw [← pow_mul, mul_comm]
      rw [hfac, hρk, hχ, mul_left_comm, ← Finset.prod_mul_distrib, mul_comm (ρ ^ k)]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ by rw [mul_comm, mul_pow]
    rw [smul_smul, hcoef, mul_smul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hα_lt (i : ι) : α i < m :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_lt
      (Nat.lt_succ_self k)
  have hα_mem : α ∈ univ.piAntidiag k := mem_piAntidiag.2 ⟨rfl, by simp⟩
  calc ∑ β ∈ univ.piAntidiag k,
        ∑ j : ι → Fin m, (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) • (ρ ^ k • p.mvCoeff β)
      = ∑ β ∈ univ.piAntidiag k,
          (∑ j : ι → Fin m, ∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) • (ρ ^ k • p.mvCoeff β) :=
        Finset.sum_congr rfl fun _ _ ↦ (sum_smul).symm
    _ = ∑ β ∈ univ.piAntidiag k,
          (if β = α then (m : ℂ) ^ Fintype.card ι else 0) • (ρ ^ k • p.mvCoeff β) := by
        refine Finset.sum_congr rfl fun β hβ ↦ ?_
        have hβ_lt (i : ι) : β i < m :=
          (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_lt
            ((mem_piAntidiag.1 hβ).1.trans_lt (Nat.lt_succ_self k))
        rw [sum_prod_pow_mul_inv_pow_eq (Nat.succ_ne_zero k) hprim hα_lt hβ_lt]
    _ = ((m : ℂ) ^ Fintype.card ι) • (ρ ^ k • p.mvCoeff α) := by
        rw [Finset.sum_eq_single α]
        · simp
        · intro β _ hβα; simp [hβα]
        · intro hnot; exact (hnot hα_mem).elim

/-- **Polynomial Cauchy inequality on a torus**: if the homogeneous term `p (∑ i, α i) (fun _ ↦ z)`
has norm at most `M` whenever every coordinate satisfies `‖z i‖ = ρ` (`0 ≤ ρ`), then
`‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M`. -/
theorem norm_mvCoeff_mul_pow_le_of_forall_norm_coord_eq (p : FormalMultilinearSeries ℂ (ι → ℂ) V)
    (α : ι → ℕ) {ρ M : ℝ} (hρ0 : 0 ≤ ρ)
    (hM : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = ρ) → ‖p (∑ i, α i) (fun _ ↦ z)‖ ≤ M) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  classical
  set k : ℕ := ∑ i, α i
  set m : ℕ := k + 1
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (Nat.succ_ne_zero k)
  have hω_norm : ‖ω‖ = 1 := hprim.norm'_eq_one (Nat.succ_ne_zero k)
  have hm_pos : (0 : ℝ) < (m : ℝ) ^ Fintype.card ι := by positivity
  refine le_of_mul_le_mul_left ?_ hm_pos
  have hlhs : (m : ℝ) ^ Fintype.card ι * (‖p.mvCoeff α‖ * ρ ^ k) =
      ‖((m : ℂ) ^ Fintype.card ι) • ((ρ : ℂ) ^ k • p.mvCoeff α)‖ := by
    simp [norm_smul, Complex.norm_real, abs_of_nonneg hρ0, mul_comm (ρ ^ k)]
  rw [hlhs, ← p.sum_smul_apply_grid_eq_mvCoeff α (ρ : ℂ) hprim]
  calc ‖∑ j : ι → Fin m,
        (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ (ρ : ℂ) * ω ^ (j i : ℕ))‖
      ≤ ∑ j : ι → Fin m,
          ‖(∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ (ρ : ℂ) * ω ^ (j i : ℕ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : ι → Fin m, M := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hχ : ‖∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)‖ = 1 := by simp [norm_prod, hω_norm]
        rw [norm_smul, hχ, one_mul]
        exact hM _ fun i ↦ by simp [Complex.norm_real, abs_of_nonneg hρ0, hω_norm]
    _ = (m : ℝ) ^ Fintype.card ι * M := by simp [nsmul_eq_mul]

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries

/-- **Cauchy's inequality on a polydisc** (`Metric.eball` form): if `f` has the power series `p`
on `Metric.eball x r` in `ι → ℂ` and `‖f‖ ≤ M` there, then
`‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` whenever `0 ≤ ρ` and `ENNReal.ofReal ρ < r`. -/
theorem norm_mvCoeff_mul_pow_le_of_forall_mem_eball {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {M : ℝ} (hM : ∀ y ∈ Metric.eball x r, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ < r) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  refine p.norm_mvCoeff_mul_pow_le_of_forall_norm_coord_eq α hρ0 fun z hz ↦ ?_
  refine hf.norm_apply_le_of_forall_mem_eball hM _ ?_
  have hz_le : ‖z‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ0).2 fun i ↦ (hz i).le
  rw [mem_eball_zero_iff, ← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hz_le).trans_lt hρ

/-- **Cauchy's inequality on a polydisc**: if `f` has the power series `p` on `Metric.ball x R`
in `ι → ℂ` and `‖f‖ ≤ M` there, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` for every `α : ι → ℕ`
and every `0 ≤ ρ < R`. -/
theorem norm_mvCoeff_mul_pow_le {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < R) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  rw [← Metric.eball_coe] at hM
  exact hf.norm_mvCoeff_mul_pow_le_of_forall_mem_eball hM α hρ0
    ((ENNReal.ofReal_lt_coe_iff hρ0).2 hρ)

/-- **Truncated Taylor bound on a polydisc** about an arbitrary centre `x`: if `f` has the power
series `p` on `Metric.ball x R` in `ι → ℂ` and `‖f‖ ≤ M` there, then for `‖z‖ ≤ r < R`,
`‖f (x + z)‖` is bounded by `(1 + T) * M * (r / R) ^ T` plus
`∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`. -/
theorem norm_add_le_add_sum_mvCoeff [DecidableEq ι] {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M)
    (T : ℕ) {r : ℝ} {z : ι → ℂ} (hz : ‖z‖ ≤ r) (hr : r < R) :
    ‖f (x + z)‖ ≤ (1 + T) * M * (r / R) ^ T +
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
  have hzR : ‖z‖ < R := hz.trans_lt hr
  have hR0 : 0 < (R : ℝ) := (norm_nonneg z).trans_lt hzR
  have hM0 : 0 ≤ M := (norm_nonneg (f x)).trans (hM x (mem_ball_self hR0))
  calc ‖f (x + z)‖
      ≤ ‖f (x + z) - p.partialSum T z‖ + ‖p.partialSum T z‖ := norm_le_norm_sub_add _ _
    _ ≤ (1 + T) * M * (‖z‖ / R) ^ T +
          ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k :=
        add_le_add (hf.norm_add_sub_partialSum_le hM T hzR) (p.norm_partialSum_le_sum_mvCoeff T hz)
    _ ≤ (1 + T) * M * (r / R) ^ T +
          ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
        gcongr

/-- **Truncated Taylor bound on a polydisc** about the origin: if `f` has the power series `p` on
`Metric.ball 0 R` in `ι → ℂ` and `‖f‖ ≤ M` there, then for `‖z‖ ≤ r < R`, `‖f z‖` is bounded by
`(1 + T) * M * (r / R) ^ T` plus
`∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`. -/
theorem norm_le_add_sum_mvCoeff [DecidableEq ι] {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 R) {M : ℝ} (hM : ∀ y ∈ Metric.ball (0 : ι → ℂ) R, ‖f y‖ ≤ M)
    (T : ℕ) {r : ℝ} {z : ι → ℂ} (hz : ‖z‖ ≤ r) (hr : r < R) :
    ‖f z‖ ≤ (1 + T) * M * (r / R) ^ T +
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
  simpa only [zero_add] using hf.norm_add_le_add_sum_mvCoeff hM T hz hr

end HasFPowerSeriesOnBall
