/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.Analytic.MultiIndex.Coeff
public import TauCeti.Analysis.Complex.PowerSeries.TaylorRemainder
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Multi-index Cauchy inequalities and truncated Taylor bounds on polydiscs

On `ι → ℂ` with its sup norm, the open ball of radius `R` is the open polydisc of equal radii `R`.
This file proves **Cauchy's inequality for multi-index coefficients** and the resulting
**truncated Taylor bound** for power series on `ι → ℂ` with values in any complex normed space `V`:

* If the homogeneous polynomial `p (∑ i, α i) (fun _ ↦ z)` is bounded by `M` on the distinguished
  torus `∀ i, ‖z i‖ = ρ i` (`0 ≤ ρ i`), averaging it against the conjugate character over the
  index grid `j : ι → Fin (∑ i, α i + 1)` (of cardinality `(∑ i, α i + 1) ^ Fintype.card ι`,
  counting repeated points `z j i = ρ i * ω ^ (j i)` with multiplicity when some `ρ i = 0`) for a
  primitive `(∑ i, α i + 1)`-th root of unity `ω` extracts the radius-weighted coefficient
  `(∏ i, (ρ i : ℂ) ^ α i) • p.mvCoeff α`
  (`FormalMultilinearSeries.sum_smul_apply_grid_eq_mvCoeff`) and yields
  `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M`
  (`FormalMultilinearSeries.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_eq`). Unlike the
  contour identification on `Fin n → ℂ` in `TauCeti.Analysis.Complex.PowerSeries.Identification`,
  this discrete Fourier average applies to any finite index type `ι`, includes `ρ i = 0`, and needs
  no completeness of `V`.
* Combining the discrete Fourier extraction with
  `HasFPowerSeriesOnBall.norm_apply_le_of_forall_norm_eq_one` on radially contracted tori gives
  Cauchy's inequality `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M` requiring `‖f (x + z)‖ ≤ M` only on
  the coordinatewise polydisc `‖z‖ₑ < r` and `∀ i, ‖z i‖ ≤ ρ i`
  (`HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le_eball`, and
  finite-ball `HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le`), from
  which the ball-wide bounds
  `HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le_of_forall_mem_eball`,
  `HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le`,
  `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le_of_forall_mem_eball`, and
  `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le` follow by restriction.
* Combining `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` with
  `FormalMultilinearSeries.norm_partialSum_le_sum_mvCoeff` bounds `‖f (x + z)‖` on a smaller closed
  polydisc `‖z‖ ≤ r < R` by `(1 + T) * M * (r / R) ^ T` plus
  `∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`
  (`HasFPowerSeriesOnBall.norm_add_le_add_sum_mvCoeff`,
  `HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff`).

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer (2000), §4.5, Lemma 4.13, pp. 134–135.
* Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/Interpolation.lean`, Apache 2.0).
-/

public section

open Complex Filter Finset Metric
open scoped Real ENNReal NNReal Topology

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

namespace FormalMultilinearSeries

/-- Unnormalized discrete Fourier sum of `p (∑ i, α i)` over the index grid
`ι → Fin (∑ i, α i + 1)`, evaluating at `z j i = ρ i * ω ^ (j i : ℕ)` (counting repeated grid
points with multiplicity when some `ρ i = 0`), equal to `(∑ i, α i + 1) ^ Fintype.card ι`
(the cardinality of `ι → Fin (∑ i, α i + 1)`) times the radius-weighted coefficient
`(∏ i, ρ i ^ α i) • p.mvCoeff α`. -/
theorem sum_smul_apply_grid_eq_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries ℂ (ι → ℂ) V) (α : ι → ℕ) (ρ : ι → ℂ) {ω : ℂ}
    (hprim : IsPrimitiveRoot ω (∑ i, α i + 1)) :
    (∑ j : ι → Fin (∑ i, α i + 1),
      (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) •
        p (∑ i, α i) (fun _ i ↦ ρ i * ω ^ (j i : ℕ))) =
      (((∑ i, α i + 1 : ℕ) : ℂ) ^ Fintype.card ι) • ((∏ i, ρ i ^ α i) • p.mvCoeff α) := by
  set k : ℕ := ∑ i, α i
  set m : ℕ := k + 1
  have hterm (j : ι → Fin m) :
      (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ ρ i * ω ^ (j i : ℕ)) =
        ∑ β ∈ univ.piAntidiag k,
          (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) • ((∏ i, ρ i ^ β i) • p.mvCoeff β) := by
    rw [p.apply_eq_sum_mvCoeff k _, smul_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    have hpt (i : ι) :
        (ω⁻¹) ^ ((j i : ℕ) * α i) * (ρ i * ω ^ (j i : ℕ)) ^ β i =
          (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ) * ρ i ^ β i := by
      simp only [mul_pow, ← pow_mul, mul_comm (j i : ℕ)]
      ring
    have hcoef : (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) * (∏ i, (ρ i * ω ^ (j i : ℕ)) ^ β i) =
        (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) * ∏ i, ρ i ^ β i := by
      simp only [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ hpt i
    rw [smul_smul, hcoef, mul_smul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hmem_lt {γ : ι → ℕ} (hγ : γ ∈ univ.piAntidiag k) (i : ι) : γ i < m :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_lt
      ((mem_piAntidiag.1 hγ).1.trans_lt (Nat.lt_succ_self k))
  have hα_mem : α ∈ univ.piAntidiag k := mem_piAntidiag.2 ⟨rfl, by simp⟩
  calc ∑ β ∈ univ.piAntidiag k,
        ∑ j : ι → Fin m,
          (∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) • ((∏ i, ρ i ^ β i) • p.mvCoeff β)
      = ∑ β ∈ univ.piAntidiag k,
          (∑ j : ι → Fin m, ∏ i, (ω ^ β i * (ω⁻¹) ^ α i) ^ (j i : ℕ)) •
            ((∏ i, ρ i ^ β i) • p.mvCoeff β) :=
        Finset.sum_congr rfl fun _ _ ↦ (sum_smul).symm
    _ = ∑ β ∈ univ.piAntidiag k,
          (if β = α then (m : ℂ) ^ Fintype.card ι else 0) •
            ((∏ i, ρ i ^ β i) • p.mvCoeff β) := by
        refine Finset.sum_congr rfl fun β hβ ↦ ?_
        rw [hprim.sum_prod_pow_mul_inv_pow_eq (hmem_lt hα_mem) (hmem_lt hβ)]
    _ = ((m : ℂ) ^ Fintype.card ι) • ((∏ i, ρ i ^ α i) • p.mvCoeff α) := by
        rw [Finset.sum_eq_single α]
        · simp
        · intro β _ hβα; simp [hβα]
        · intro hnot; exact (hnot hα_mem).elim

/-- **Polynomial Cauchy inequality on a torus (unequal polyradii)**: if the homogeneous term
`p (∑ i, α i) (fun _ ↦ z)` has norm at most `M` whenever every coordinate satisfies `‖z i‖ = ρ i`
(`0 ≤ ρ i`), then `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M`. -/
theorem norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_eq
    (p : FormalMultilinearSeries ℂ (ι → ℂ) V) (α : ι → ℕ) {ρ : ι → ℝ} {M : ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i)
    (hM : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = ρ i) → ‖p (∑ i, α i) (fun _ ↦ z)‖ ≤ M) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M := by
  classical
  set k : ℕ := ∑ i, α i
  set m : ℕ := k + 1
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (Nat.succ_ne_zero k)
  have hω_norm : ‖ω‖ = 1 := hprim.norm'_eq_one (Nat.succ_ne_zero k)
  have hm_pos : (0 : ℝ) < (m : ℝ) ^ Fintype.card ι := by positivity
  refine le_of_mul_le_mul_left ?_ hm_pos
  have hlhs : (m : ℝ) ^ Fintype.card ι * (‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i) =
      ‖((m : ℂ) ^ Fintype.card ι) • ((∏ i, (ρ i : ℂ) ^ α i) • p.mvCoeff α)‖ := by
    simp only [norm_smul, norm_prod, norm_pow, Complex.norm_natCast, Complex.norm_real,
      fun i ↦ Real.norm_of_nonneg (hρ0 i)]
    ring
  rw [hlhs, ← p.sum_smul_apply_grid_eq_mvCoeff α (fun i ↦ (ρ i : ℂ)) hprim]
  calc ‖∑ j : ι → Fin m,
        (∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ (ρ i : ℂ) * ω ^ (j i : ℕ))‖
      ≤ ∑ j : ι → Fin m,
          ‖(∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)) • p k (fun _ i ↦ (ρ i : ℂ) * ω ^ (j i : ℕ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : ι → Fin m, M := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hχ : ‖∏ i, (ω⁻¹) ^ ((j i : ℕ) * α i)‖ = 1 := by simp [norm_prod, hω_norm]
        rw [norm_smul, hχ, one_mul]
        exact hM _ fun i ↦ by simp [Complex.norm_real, abs_of_nonneg (hρ0 i), hω_norm]
    _ = (m : ℝ) ^ Fintype.card ι * M := by simp [nsmul_eq_mul]

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries

/-- **Cauchy's inequality on a coordinatewise polydisc (`Metric.eball` form)**: if `f` has the
power series `p` on `Metric.eball x r` in `ι → ℂ`, `0 ≤ ρ i`, `ENNReal.ofReal (ρ i) ≤ r`, and
`‖f (x + z)‖ ≤ M` whenever `‖z‖ₑ < r` and `∀ i, ‖z i‖ ≤ ρ i`, then
`‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M`. Completeness of `V` is not needed. -/
theorem norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le_eball {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {M : ℝ} (α : ι → ℕ) {ρ : ι → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : ∀ i, ENNReal.ofReal (ρ i) ≤ r)
    (hM : ∀ z : ι → ℂ, ‖z‖ₑ < r → (∀ i, ‖z i‖ ≤ ρ i) → ‖f (x + z)‖ ≤ M) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M := by
  have hcontract {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      t ^ (∑ i, α i) * (‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i) ≤ M := by
    have hprod : ∏ i, (t * ρ i) ^ α i = t ^ (∑ i, α i) * ∏ i, ρ i ^ α i := by
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hnorm_prod : ‖p.mvCoeff α‖ * ∏ i, (t * ρ i) ^ α i =
        t ^ (∑ i, α i) * (‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i) := by
      rw [hprod]
      ring
    rw [← hnorm_prod]
    refine p.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_eq α
      (fun i ↦ mul_nonneg ht0.le (hρ0 i)) fun z hz ↦ ?_
    have hzr : ‖z‖ₑ < r := by
      rcases eq_or_ne r ⊤ with rfl | hr_top
      · exact eNorm_lt_top
      · lift r to ℝ≥0 using hr_top
        have hr_pos : 0 < (r : ℝ) := ENNReal.coe_pos.1 hf.r_pos
        have hz_le : ‖z‖ ≤ t * r := (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦
          (hz i).le.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_coe.1 (hρ i)) ht0.le)
        have hz_lt : ‖z‖ < r := hz_le.trans_lt (mul_lt_of_lt_one_left hr_pos ht1)
        rwa [← ofReal_norm, ENNReal.ofReal_lt_coe_iff (norm_nonneg z)]
    refine hf.norm_apply_le_of_forall_norm_eq_one (∑ i, α i) hzr fun ζ hζ hζz ↦ ?_
    refine hM (ζ • z) hζz fun i ↦ ?_
    have hcoord : ‖(ζ • z) i‖ = t * ρ i := by simp [hζ, hz i]
    rw [hcoord]
    exact mul_le_of_le_one_left (hρ0 i) ht1.le
  have htend : Tendsto (fun t : ℝ ↦ t ^ (∑ i, α i) * (‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i))
      (𝓝[<] (1 : ℝ)) (𝓝 (‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i)) :=
    (((continuous_id.pow (∑ i, α i)).mul continuous_const).tendsto' 1 _ (by simp)).mono_left
      nhdsWithin_le_nhds
  exact le_of_tendsto htend (eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one)
    fun _ ht ↦ hcontract ht.1 ht.2)

/-- **Cauchy's inequality on a coordinatewise polydisc**: if `f` has the power series `p` on
`Metric.ball x R` in `ι → ℂ`, `0 ≤ ρ i ≤ R`, and `‖f (x + z)‖ ≤ M` whenever `‖z‖ < R` and
`∀ i, ‖z i‖ ≤ ρ i`, then `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M`. Completeness of `V` is not
needed. -/
theorem norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (α : ι → ℕ) {ρ : ι → ℝ}
    (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : ∀ i, ρ i ≤ R)
    (hM : ∀ z : ι → ℂ, ‖z‖ < R → (∀ i, ‖z i‖ ≤ ρ i) → ‖f (x + z)‖ ≤ M) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M :=
  hf.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le_eball α hρ0
    (fun i ↦ ENNReal.ofReal_le_coe.2 (hρ i)) fun z hz hzi ↦
      hM z (by rwa [← ofReal_norm, ENNReal.ofReal_lt_coe_iff (norm_nonneg z)] at hz) hzi

/-- **Cauchy's inequality on a polydisc (unequal polyradii, `Metric.eball` form)**: if `f` has
the power series `p` on `Metric.eball x r` in `ι → ℂ` and `‖f‖ ≤ M` there, then
`‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M` for every multi-index `α : ι → ℕ` and every `ρ : ι → ℝ` with
`0 ≤ ρ i` and `ENNReal.ofReal (ρ i) ≤ r`. Completeness of `V` is not needed. -/
theorem norm_mvCoeff_mul_prod_pow_le_of_forall_mem_eball {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {M : ℝ} (hM : ∀ y ∈ Metric.eball x r, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ι → ℝ} (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : ∀ i, ENNReal.ofReal (ρ i) ≤ r) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M :=
  hf.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le_eball α hρ0 hρ fun z hz _ ↦
    hM (x + z) (by rw [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]; exact hz)

/-- **Cauchy's inequality on a polydisc (unequal polyradii)**: if `f` has the power series `p` on
`Metric.ball x R` in `ι → ℂ` and `‖f‖ ≤ M` there, then `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M` for
every multi-index `α : ι → ℕ` and every `ρ : ι → ℝ` with `0 ≤ ρ i ≤ R`. Completeness of `V` is
not needed. -/
theorem norm_mvCoeff_mul_prod_pow_le {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ι → ℝ} (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : ∀ i, ρ i ≤ R) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M :=
  hf.norm_mvCoeff_mul_prod_pow_le_of_forall_norm_coord_le α hρ0 hρ fun z hz _ ↦
    hM (x + z) (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

/-- **Cauchy's inequality on a polydisc** (`Metric.eball` form): if `f` has the power series `p`
on `Metric.eball x r` in `ι → ℂ` and `‖f‖ ≤ M` there, then
`‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` whenever `0 ≤ ρ` and `ENNReal.ofReal ρ ≤ r`. -/
theorem norm_mvCoeff_mul_pow_le_of_forall_mem_eball {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) {M : ℝ} (hM : ∀ y ∈ Metric.eball x r, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ ≤ r) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    hf.norm_mvCoeff_mul_prod_pow_le_of_forall_mem_eball hM α (fun _ ↦ hρ0) (fun _ ↦ hρ)

/-- **Cauchy's inequality on a polydisc**: if `f` has the power series `p` on `Metric.ball x R`
in `ι → ℂ` and `‖f‖ ≤ M` there, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` for every `α : ι → ℕ`
and every `0 ≤ ρ ≤ R`. -/
theorem norm_mvCoeff_mul_pow_le {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {x : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x R) {M : ℝ} (hM : ∀ y ∈ Metric.ball x R, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ R) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    hf.norm_mvCoeff_mul_prod_pow_le hM α (fun _ ↦ hρ0) (fun _ ↦ hρ)

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
