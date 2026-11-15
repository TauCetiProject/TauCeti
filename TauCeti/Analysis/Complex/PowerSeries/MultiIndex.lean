/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.PartialSum
public import TauCeti.MeasureTheory.Integral.Torus.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Complex.PowerSeries.Identification
import TauCeti.Analysis.Complex.PowerSeries.Polydisc
import TauCeti.Analysis.Complex.PowerSeries.Remainder

/-!
# Multi-index Cauchy inequalities and polydisc Taylor bounds

For a function `f : (Fin n → ℂ) → V` with formal multilinear power series `p` on a ball around `c`
in a complex Banach space `V`, `HasFPowerSeriesOnBall.torusIntegral_cauchyCoeff` identifies the
multivariate Cauchy integral of `f` on any interior polytorus `T(c, R)` with the basis-evaluation
sum defining `p.mvCoeff α` (`HasFPowerSeriesOnBall.torusIntegral_cauchyCoeff_eq_mvCoeff`).

Combining this integral formula with the distinguished-boundary estimate
`TauCeti.norm_torusIntegral_cauchyCoeff_le`, reindexing coordinates from `Fin (Fintype.card ι)` to
an arbitrary finite type `ι`, applying Hahn–Banach to drop completeness of `V`, and passing to the
boundary limit along interior polyradii yields Cauchy's inequality on polydiscs: if `‖f y‖ ≤ M` on
`ball c R`, then `‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M` whenever `0 ≤ ρ i ≤ R`, and in particular
`‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` for `0 ≤ ρ ≤ R`
(`HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le`).

Combining `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` with the multi-index partial-sum
majorant `FormalMultilinearSeries.norm_partialSum_le_sum_mvCoeff` bounds `‖f (c + z)‖` on `‖z‖ ≤ r`
(`r < R`) by `(1 + T) * M * (r / R) ^ T` plus the multi-index majorant
`∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k`.

## Main results

* `HasFPowerSeriesOnBall.torusIntegral_cauchyCoeff_eq_mvCoeff`: the torus Cauchy integral of `f`
  equals `p.mvCoeff α`.
* `HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le` and
  `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le`: Cauchy's inequalities for `p.mvCoeff α` with
  polyradii `0 ≤ ρ i ≤ R` and equal radius `0 ≤ ρ ≤ R`.
* `HasFPowerSeriesOnBall.norm_add_le_add_sum_mvCoeff` and
  `HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff`: polydisc upper bounds on `‖f (c + z)‖` and
  `‖f z‖` in terms of `p.mvCoeff` up to degree `T` and the degree-`T` Taylor remainder.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemma 4.13, pp. 134–135.
* Multi-index Cauchy inequalities and truncated Taylor bounds on polydiscs also appear in Michail
  Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit
  `1d51891b5b`, `Interpolation.lean`, Apache 2.0).
-/

public section

open Complex Filter Finset MeasureTheory Metric Topology
open scoped Real ENNReal NNReal

namespace HasFPowerSeriesOnBall

/-- On `Fin n → ℂ` with values in a complete complex normed space `V`, the multivariate Cauchy
integral of `f` on any positive polytorus strictly inside the ball of representation equals
`p.mvCoeff α`. -/
theorem torusIntegral_cauchyCoeff_eq_mvCoeff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {n : ℕ} {f : (Fin n → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (Fin n → ℂ) V} {c : Fin n → ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p c r) {R : Fin n → ℝ} (hR : ∀ i, 0 < R i)
    (hRr : ∀ i, ENNReal.ofReal (R i) < r) (α : Fin n → ℕ) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
        (∯ z in T(c, R), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • f z) = p.mvCoeff α := by
  have hm : p.mvCoeff α =
      ∑ a ∈ univ.filter (fun a : Fin (∑ i, α i) → Fin n ↦
        ∀ i, Fintype.card {j // a j = i} = α i),
        p (∑ i, α i) (fun j ↦ Pi.single (a j) 1) := by
    rw [p.mvCoeff_eq_sum rfl]
    congr!
  rcases n.eq_zero_or_pos with rfl | hn
  · exact (hf.torusIntegral_cauchyCoeff (s := 0) hf.r_pos hR (fun i ↦ Fin.elim0 i) α).trans hm.symm
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let s : ℝ≥0 := univ.sup' univ_nonempty fun i ↦ (R i).toNNReal
    have hs : (s : ℝ≥0∞) < r := by
      have hsup : (s : ℝ≥0∞) = univ.sup' univ_nonempty fun i ↦ ((R i).toNNReal : ℝ≥0∞) :=
        Finset.apply_sup'_eq_sup'_comp univ_nonempty _ fun _ _ ↦ ENNReal.coe_max _ _
      rw [hsup, Finset.sup'_lt_iff]
      intro i _
      simpa [ENNReal.ofReal] using hRr i
    have hRs (i : Fin n) : R i ≤ s := by
      have hi : (R i).toNNReal ≤ s := Finset.le_sup' (fun j ↦ (R j).toNNReal) (mem_univ i)
      exact (Real.coe_toNNReal (R i) (hR i).le).symm.trans_le (NNReal.coe_le_coe.2 hi)
    exact (hf.torusIntegral_cauchyCoeff hs hR hRs α).trans hm.symm

/-- Scalar `Fin n → ℂ` case of `HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le` on strictly
interior positive polyradii `0 < r i < R`. -/
private theorem norm_mvCoeff_mul_prod_pow_le_of_fin {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    {q : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ} {c : Fin n → ℂ} {R : ℝ≥0}
    (hg : HasFPowerSeriesOnBall g q c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖g y‖ ≤ M)
    (α : Fin n → ℕ) {r : Fin n → ℝ} (hr0 : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) :
    ‖q.mvCoeff α‖ * ∏ i, r i ^ α i ≤ M := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hg.r_pos
  have hrR' (i : Fin n) : ENNReal.ofReal (r i) < (R : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_lt_ofReal_iff hR |>.2 (hrR i)
  have hid := hg.torusIntegral_cauchyCoeff_eq_mvCoeff hr0 hrR' α
  rw [← inv_pow] at hid
  have hsph (z : Fin n → ℂ) (hz : z ∈ Set.univ.pi fun i ↦ sphere (c i) (r i)) : ‖g z‖ ≤ M :=
    hM z <| mem_ball.2 <| (dist_pi_lt_iff hR).2 fun i ↦
      (mem_sphere.1 (hz i trivial)).trans_lt (hrR i)
  have hcauchy := TauCeti.norm_torusIntegral_cauchyCoeff_le hr0 hsph α
  rw [hid] at hcauchy
  have hpos : 0 < ∏ i, r i ^ α i := prod_pos fun i _ ↦ pow_pos (hr0 i) _
  calc ‖q.mvCoeff α‖ * ∏ i, r i ^ α i
      ≤ (M * ∏ i, (r i)⁻¹ ^ α i) * ∏ i, r i ^ α i :=
        mul_le_mul_of_nonneg_right hcauchy hpos.le
    _ = M * ∏ i, ((r i)⁻¹ ^ α i * r i ^ α i) := by rw [mul_assoc, prod_mul_distrib]
    _ = M := by simp [inv_mul_cancel₀ (pow_ne_zero _ (hr0 _).ne')]

section MultiIndex

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Strictly interior positive polyradius case of
`HasFPowerSeriesOnBall.norm_mvCoeff_mul_prod_pow_le` on an arbitrary finite index type `ι`. -/
private theorem norm_mvCoeff_mul_prod_pow_le_of_pos_of_lt {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {c : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M)
    (α : ι → ℕ) {r : ι → ℝ} (hr0 : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) :
    ‖p.mvCoeff α‖ * ∏ i, r i ^ α i ≤ M := by
  classical
  obtain ⟨φ, hφ_norm, hφ_val⟩ := exists_dual_vector'' ℂ (p.mvCoeff α)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ι ↦ ℂ) e
  let Lc : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) := L
  have hL_dist (x y : Fin (Fintype.card ι) → ℂ) : dist (L x) (L y) = dist x y :=
    (IsometryEquiv.piCongrLeft (Y := fun _ : ι ↦ ℂ) e).dist_eq x y
  have hL_norm : ‖Lc‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 <| Lc.opNorm_le_bound zero_le_one fun x ↦ by
      simpa [Lc, dist_zero_right] using (hL_dist x 0).le
  have hps_base : HasFPowerSeriesOnBall (φ ∘ f) (φ.compFormalMultilinearSeries p) (Lc (L.symm c))
      R := by simpa [Lc] using φ.comp_hasFPowerSeriesOnBall hf
  have hps := (hps_base.compContinuousLinearMap (u := Lc) (x := L.symm c)).mono hf.r_pos <|
    ENNReal.le_div_iff_mul_le (Or.inr hf.r_pos.ne') (Or.inl ENNReal.coe_ne_top) |>.2
      (mul_le_of_le_one_right zero_le hL_norm)
  have hbound (z : Fin (Fintype.card ι) → ℂ) (hz : z ∈ ball (L.symm c) R) :
      ‖((φ ∘ f) ∘ Lc) z‖ ≤ M :=
    (φ.le_opNorm _).trans <| (mul_le_of_le_one_left (norm_nonneg _) hφ_norm).trans <|
      hM (L z) (by rwa [mem_ball, ← L.apply_symm_apply c, hL_dist])
  have hcoeff : ‖((φ.compFormalMultilinearSeries p).compContinuousLinearMap Lc).mvCoeff (α ∘ e)‖ =
      ‖p.mvCoeff α‖ := by
    rw [(φ.compFormalMultilinearSeries p).mvCoeff_compContinuousLinearMap_piCongrLeft e α,
      (φ.compFormalMultilinearSeries p).mvCoeff_eq_sum rfl]
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ← map_sum,
      ← p.mvCoeff_eq_sum rfl, hφ_val]
    simp
  have hfin := norm_mvCoeff_mul_prod_pow_le_of_fin hps hbound (α ∘ e)
    (fun j ↦ hr0 (e j)) (fun j ↦ hrR (e j))
  rwa [hcoeff, show (∏ j, r (e j) ^ (α ∘ e) j) = ∏ i, r i ^ α i from
    e.prod_comp fun i ↦ r i ^ α i] at hfin

/-- **Cauchy's inequality on a polydisc (unequal polyradii).** If `f : (ι → ℂ) → V` has formal
power series `p` on `ball c R` and satisfies `‖f y‖ ≤ M` there, then
`‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M` for every multi-index `α : ι → ℕ` and every `ρ : ι → ℝ` with
`0 ≤ ρ i` and `ρ i ≤ R`. Completeness of `V` is not needed. -/
theorem norm_mvCoeff_mul_prod_pow_le {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {c : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M)
    (α : ι → ℕ) {ρ : ι → ℝ} (hρ0 : ∀ i, 0 ≤ ρ i) (hρ : ∀ i, ρ i ≤ R) :
    ‖p.mvCoeff α‖ * ∏ i, ρ i ^ α i ≤ M := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  -- Approximate `ρ` from inside `(0, R)` by `(1 - t) * (R / 2) + t * ρ i` and let `t → 1⁻`.
  have hsub (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      ‖p.mvCoeff α‖ * ∏ i, ((1 - t) * ((R : ℝ) / 2) + t * ρ i) ^ α i ≤ M :=
    norm_mvCoeff_mul_prod_pow_le_of_pos_of_lt hf hM α
      (fun i ↦ by nlinarith [ht.1, ht.2, hρ0 i])
      (fun i ↦ by nlinarith [ht.1, ht.2, hρ i])
  have hcont : Continuous fun t : ℝ ↦
      ‖p.mvCoeff α‖ * ∏ i, ((1 - t) * ((R : ℝ) / 2) + t * ρ i) ^ α i := by fun_prop
  have hlim := le_of_tendsto (hcont.continuousWithinAt (s := Set.Iio (1 : ℝ))) <| by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht using hsub t ht
  simpa using hlim

/-- **Cauchy's inequality on a polydisc.** If `f : (ι → ℂ) → V` has formal power series `p` on
`ball c R` and satisfies `‖f y‖ ≤ M` there, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M` for every
multi-index `α : ι → ℕ` and every `ρ : ℝ` with `0 ≤ ρ` and `ρ ≤ R`. -/
theorem norm_mvCoeff_mul_pow_le {f : (ι → ℂ) → V} {p : FormalMultilinearSeries ℂ (ι → ℂ) V}
    {c : ι → ℂ} {R : ℝ≥0} (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ}
    (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M) (α : ι → ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ R) :
    ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤ M := by
  simpa [prod_pow_eq_pow_sum] using
    hf.norm_mvCoeff_mul_prod_pow_le hM α (fun _ ↦ hρ0) (fun _ ↦ hρ)

/-- **Polydisc truncated Taylor bound** around an arbitrary centre `c : ι → ℂ` (Waldschmidt,
Lemma 4.13): if `f : (ι → ℂ) → V` has formal power series `p` on `ball c R` and `‖f y‖ ≤ M` there,
then for `‖z‖ ≤ r` with `r < R`, `‖f (c + z)‖` is bounded by `(1 + T) * M * (r / R) ^ T` plus the
multi-index coefficient majorant below degree `T`. -/
theorem norm_add_le_add_sum_mvCoeff [DecidableEq ι] {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {c : ι → ℂ} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p c R) {M : ℝ} (hM : ∀ y ∈ ball c R, ‖f y‖ ≤ M) (T : ℕ)
    {z : ι → ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < R) :
    ‖f (c + z)‖ ≤ (1 + T) * M * (r / R) ^ T +
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
  have hR : 0 < (R : ℝ) := mod_cast ENNReal.coe_pos.1 hf.r_pos
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  calc ‖f (c + z)‖ ≤ ‖f (c + z) - p.partialSum T z‖ + ‖p.partialSum T z‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ (1 + T) * M * (‖z‖ / R) ^ T +
          ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k :=
        add_le_add (hf.norm_add_sub_partialSum_le hM T (hz.trans_lt hr))
          (p.norm_partialSum_le_sum_mvCoeff T hz)
    _ ≤ (1 + T) * M * (r / R) ^ T +
          ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by gcongr

/-- **Polydisc truncated Taylor bound** around `0 : ι → ℂ` (Waldschmidt, Lemma 4.13): if
`f : (ι → ℂ) → V` has formal power series `p` on `ball 0 R` and `‖f y‖ ≤ M` there, then for
`‖z‖ ≤ r` with `r < R`, `‖f z‖` is bounded by `(1 + T) * M * (r / R) ^ T` plus the multi-index
coefficient majorant below degree `T`. -/
theorem norm_le_add_sum_mvCoeff [DecidableEq ι] {f : (ι → ℂ) → V}
    {p : FormalMultilinearSeries ℂ (ι → ℂ) V} {R : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p 0 R) {M : ℝ} (hM : ∀ y ∈ ball (0 : ι → ℂ) R, ‖f y‖ ≤ M)
    (T : ℕ) {z : ι → ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r < R) :
    ‖f z‖ ≤ (1 + T) * M * (r / R) ^ T +
      ∑ k ∈ range T, ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ k := by
  simpa using hf.norm_add_le_add_sum_mvCoeff hM T hz hr

end MultiIndex

end HasFPowerSeriesOnBall
