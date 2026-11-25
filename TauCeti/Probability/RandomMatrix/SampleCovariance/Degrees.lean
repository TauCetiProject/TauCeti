/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Moments.CenteredTruncation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Moments.Bernstein

/-!
# Uniform row and column norms of truncated sample covariance data

Let `Yₙ` be a `p(n) × n` corner with entries independent within each row and column and a common
law of mean zero and unit second absolute moment, truncated at `n ^ a`, recentered and divided
by `√n`. When `0 < a < 1 / 2` and
`p(n) / n → y`, almost surely the squared row norms converge uniformly to `1` and the squared
column norms converge uniformly to `y`. These sums are the weighted degrees of the Hermitian
dilation of `Yₙ` in Bai and Yin's argument for the lower covariance edge.

The square of a truncated entry is bounded by `4 * n ^ (2 * a)`, and its variance is at most
that bound times its expectation. Bernstein's inequality thus makes the exceptional
probabilities summable even after taking a union over all rows or all columns. The truncated
second moment tends to `1` by mean-square convergence of the centered truncations.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability.SampleCovariance

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω} {ν : Measure E}

/-- Bernstein's bound for one row of centered truncations, normalized by the size index `n`.
The length of the row may differ from `n` by a bounded factor. -/
private theorem measureReal_abs_sum_norm_sq_centeredTruncation_sub_ge_le {n m : ℕ} {a C ε : ℝ}
    (hn : 0 < n) (hm : (m : ℝ) ≤ C * n) (hε : 0 < ε)
    {X : Fin m → Ω → E} (hind : iIndepFun X P) (hX : ∀ j, HasLaw (X j) ν P)
    (hunit : ∫ z, ‖z‖ ^ 2 ∂ν = 1) :
    P.real {ω | ε ≤ |(∑ j, ‖centeredTruncation (X j) P ((n : ℝ≥0) ^ a) ω‖ ^ 2) / n -
      (m : ℝ) / n * ∫ z, ‖centeredTruncation id ν ((n : ℝ≥0) ^ a) z‖ ^ 2 ∂ν|} ≤
      2 * exp (-(ε ^ 2 / (8 * (C + ε / 3))) * (n : ℝ) ^ (1 - 2 * a)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((Nat.cast_nonneg m).trans hm) hn'
  let R : ℝ≥0 := (n : ℝ≥0) ^ a
  let Z (j : Fin m) (ω : Ω) := ‖centeredTruncation (X j) P R ω‖ ^ 2
  let v := ∫ z, ‖centeredTruncation id ν R z‖ ^ 2 ∂ν
  have h2 : MemLp (id : E → E) 2 ν :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (integrable_of_integral_eq_one hunit)
  have hZ j : ∫ ω, Z j ω ∂P = v := by
    have h := ((hX j).identDistrib (HasLaw.id (μ := ν))).prodMk_centeredTruncation R
    exact (h.comp (measurable_snd.norm.pow_const 2)).integral_eq
  have hbound : ∑ j, ∫ ω, Z j ω ∂P ≤ C * n := by
    calc
      _ ≤ ∑ _ : Fin m, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦
        (((hX j).memLp h2).integral_norm_centeredTruncation_sq_le R).trans
          (((hX j).integral_comp (f := fun z : E ↦ ‖z‖ ^ 2) (by fun_prop)).trans hunit).le
      _ ≤ _ := by simpa using hm
  have hindZ : iIndepFun Z P := (hind.centeredTruncation fun _ ↦ R).comp
    (fun _ z ↦ ‖z‖ ^ 2) (fun _ ↦ by fun_prop)
  let b : ℝ≥0 := (2 * R) ^ 2
  have hb : 0 < (b : ℝ) := by dsimp [b, R]; positivity
  have htail := hindZ.measureReal_abs_sum_sub_sum_integral_ge_le_of_nonneg_of_le
    (s := Finset.univ) (b := b) (t := ε * n)
    (fun j _ ↦
      (((hX j).aemeasurable.aestronglyMeasurable.centeredTruncation R).norm.pow 2).aemeasurable)
    (fun _ _ ↦ .of_forall fun _ ↦ sq_nonneg _) (fun j _ ↦ .of_forall fun ω ↦ by
      simpa [Z, b] using pow_le_pow_left₀ (norm_nonneg _) (norm_centeredTruncation_le R ω) 2)
    (by positivity)
  have hnonneg : 0 ≤ ∑ j, ∫ ω, Z j ω ∂P :=
    Finset.sum_nonneg fun j _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hden : 0 < 2 * ((b : ℝ) * (∑ j, ∫ ω, Z j ω ∂P) + b * (ε * n) / 3) := by
    exact mul_pos zero_lt_two (add_pos_of_nonneg_of_pos (by positivity)
      (div_pos (mul_pos hb (mul_pos hε hn')) (by norm_num)))
  refine (measureReal_mono (s₂ := _) (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans
    (htail.trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)))
  · simpa [hZ, Z, R, v, div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos hn',
      le_div_iff₀ hn'] using hω
  · calc
      _ ≤ -(ε * n) ^ 2 / (2 * ((b : ℝ) * (C * n) + b * (ε * n) / 3)) := by
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (sq_nonneg _) hden (by gcongr)
      _ = _ := by
        simp only [b, R, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_rpow,
          NNReal.coe_natCast, mul_pow, ← Real.rpow_mul_natCast hn'.le, Nat.cast_ofNat, mul_comm a 2]
        rw [Real.rpow_sub hn', Real.rpow_one]
        field_simp
        ring

/-- Uniform concentration within rows about the truncated second moment, with the same
normalization `n` for every row. Only a linear upper bound on both dimensions is needed. -/
private theorem ae_eventually_abs_sum_norm_sq_centeredTruncation_sub_le
    {x : ℕ × ℕ → Ω → E} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hind : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) (hunit : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    {p q : ℕ → ℕ} {C a : ℝ} (hC : 0 < C)
    (hdim : ∀ᶠ n in atTop, (p n : ℝ) ≤ C * n ∧ (q n : ℝ) ≤ C * n) (ha : a < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (p n),
      |(∑ j : Fin (q n), ‖centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω‖ ^ 2) / n -
        (q n : ℝ) / n * ∫ z, ‖centeredTruncation id ν ((n : ℝ≥0) ^ a) z‖ ^ 2 ∂ν| ≤ ε := by
  have : IsProbabilityMeasure P := (hind 0).isProbabilityMeasure
  let err (n : ℕ) (i : Fin (p n)) (ω : Ω) :=
    |(∑ j : Fin (q n), ‖centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω‖ ^ 2) / n -
      (q n : ℝ) / n * ∫ z, ‖centeredTruncation id ν ((n : ℝ≥0) ^ a) z‖ ^ 2 ∂ν|
  have hbc (k : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i, err n i ω ≤ (k + 1 : ℝ)⁻¹ := by
    let ε := (k + 1 : ℝ)⁻¹
    have hε : 0 < ε := by dsimp [ε]; positivity
    let c := ε ^ 2 / (8 * (C + ε / 3))
    have hc : 0 < c := by dsimp [c]; positivity
    let S (n : ℕ) := ⋃ i, {ω | ε < err n i ω}
    have hsum : Summable (fun n : ℕ ↦ 2 * C * (n : ℝ) ^ (-2 : ℝ)) :=
      (Real.summable_nat_rpow.2 (by norm_num)).mul_left _
    have hlog := ((isLittleO_log_rpow_atTop (r := 1 - 2 * a) (by linarith)).def
      (div_pos hc (by norm_num : (0 : ℝ) < 3))).natCast_atTop
    have hb : ∀ᶠ n : ℕ in atTop, P.real (S n) ≤ 2 * C * (n : ℝ) ^ (-2 : ℝ) := by
      filter_upwards [hdim, hlog, eventually_gt_atTop 0] with n hdim hnlog hn
      have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hrate : exp (-c * (n : ℝ) ^ (1 - 2 * a)) ≤ (n : ℝ) ^ (-3 : ℝ) := by
        rw [Real.rpow_def_of_pos hn' (-3 : ℝ), exp_le_exp]
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn'.le _)] at hnlog
        linarith [le_abs_self (Real.log n)]
      have hrow (i : Fin (p n)) : P.real {ω | ε < err n i ω} ≤
          2 * exp (-c * (n : ℝ) ^ (1 - 2 * a)) := by
        have hsubset : {ω | ε < err n i ω} ⊆ {ω | ε ≤ err n i ω} := by
          intro ω h
          simp only [Set.mem_ofPred_eq] at h ⊢
          exact h.le
        exact (measureReal_mono hsubset (measure_ne_top _ _)).trans
          (measureReal_abs_sum_norm_sq_centeredTruncation_sub_ge_le
            (X := fun j : Fin (q n) ↦ x (i, j)) hn hdim.2 hε
            ((hind i).precomp (g := Fin.val) Fin.val_injective) (fun j ↦ hx (i, j)) hunit)
      calc
        _ ≤ ∑ i : Fin (p n), P.real {ω | ε < err n i ω} := measureReal_iUnion_fintype_le _
        _ ≤ (p n : ℝ) * (2 * exp (-c * (n : ℝ) ^ (1 - 2 * a))) := by
          simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hrow i
        _ ≤ (C * n) * (2 * (n : ℝ) ^ (-3 : ℝ)) :=
          mul_le_mul hdim.1 (mul_le_mul_of_nonneg_left hrate zero_le_two)
            (by positivity) (by positivity)
        _ = _ := by
          rw [(by norm_num : (-2 : ℝ) = 1 + -3), Real.rpow_add hn', Real.rpow_one]
          ring
    have hb' : ∀ᶠ n in atTop, P (S n) ≤ ENNReal.ofReal (2 * C * (n : ℝ) ^ (-2 : ℝ)) :=
      hb.mono fun n hn ↦ by simpa using ENNReal.ofReal_le_ofReal hn
    simpa [S, ε, Set.mem_iUnion, not_lt] using
      (TauCeti.MeasureTheory.ae_eventually_notMem_of_eventually_measure_le
        hsum.tsum_ofReal_lt_top hb')
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  exact (hω k).mono fun n hn i ↦ (hn i).trans (by simpa [one_div] using hk.le)

/-- In the `p(n) × n` corner of an array with common centered law of unit second absolute moment
and independence within each row and column, truncate at `n ^ a`, recenter, and divide by `√n`.
If `0 < a < 1 / 2` and `p(n) / n → y`, the entries tend uniformly to zero, and almost surely the
squared row norms tend uniformly to `1` and the squared column norms tend uniformly to `y`. -/
theorem ae_eventually_row_col_norm_sq_centeredTruncation
    {x : ℕ × ℕ → Ω → E} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hrow : ∀ i, iIndepFun (fun j ↦ x (i, j)) P) (hcol : ∀ j, iIndepFun (fun i ↦ x (i, j)) P)
    (hmean : ∫ z, z ∂ν = 0) (hunit : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    {p : ℕ → ℕ} {y : ℝ≥0} (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 (y : ℝ)))
    {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    let Y (n : ℕ) (ω : Ω) : Matrix (Fin (p n)) (Fin n) E := (√(n : ℝ))⁻¹ •
      Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop,
      (∀ i j, ‖Y n ω i j‖ ≤ ε) ∧
      (∀ i, |∑ j, ‖Y n ω i j‖ ^ 2 - 1| ≤ ε) ∧
      (∀ j, |∑ i, ‖Y n ω i j‖ ^ 2 - y| ≤ ε) := by
  have : IsProbabilityMeasure P := (hrow 0).isProbabilityMeasure
  have : IsProbabilityMeasure ν := (hx (0, 0)).isProbabilityMeasure_iff.1 ‹IsProbabilityMeasure P›
  have hdim : ∀ᶠ n in atTop, (p n : ℝ) ≤ (y + 1) * n ∧ (n : ℝ) ≤ (y + 1) * n := by
    filter_upwards [hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ))), eventually_gt_atTop 0]
      with n hpn hn
    exact ⟨(div_le_iff₀ (Nat.cast_pos.mpr hn)).mp hpn.le, by nlinarith [y.coe_nonneg]⟩
  have hvar : Tendsto (fun n : ℕ ↦ ∫ z, ‖centeredTruncation id ν ((n : ℝ≥0) ^ a) z‖ ^ 2 ∂ν)
      atTop (𝓝 1) := by
    have h2 : MemLp (id : E → E) 2 ν :=
      (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
        (integrable_of_integral_eq_one hunit)
    have h := h2.tendsto_integral_norm_centeredTruncation_sq.comp
      ((NNReal.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
    simp only [id_eq, hmean, sub_zero, hunit] at h
    exact h.congr fun _ ↦ rfl
  have hcolMean := hp.mul hvar
  have hentry : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) ^ (a - 1 / 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr ha')).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, neg_sub, mul_zero] using h.const_mul 2
  dsimp only
  filter_upwards [ae_eventually_abs_sum_norm_sq_centeredTruncation_sub_le hx hrow hunit
    (p := p) (q := id) (by positivity) hdim ha',
    ae_eventually_abs_sum_norm_sq_centeredTruncation_sub_le (x := fun ij ↦ x ij.swap)
      (fun ij ↦ hx ij.swap) hcol hunit (p := id) (q := p) (by positivity)
      (hdim.mono fun _ hn ↦ hn.symm) ha'] with ω hrows hcols
  intro ε hε
  filter_upwards [hrows (ε / 2) (by positivity), hcols (ε / 2) (by positivity),
    Metric.tendsto_nhds.1 hvar (ε / 2) (by positivity),
    Metric.tendsto_nhds.1 hcolMean (ε / 2) (by positivity),
    hentry.eventually (ge_mem_nhds hε), eventually_gt_atTop 0] with n hr hc hrm hcm he hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [id_eq, div_self hn'.ne', one_mul] at hr
  simp only [Real.dist_eq, mul_one] at hrm hcm
  simp only [Prod.swap_prod_mk] at hc
  simp only [Matrix.smul_apply, Matrix.of_apply, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (sqrt_nonneg _))]
  constructor
  · intro i j
    refine (mul_le_mul_of_nonneg_left (norm_centeredTruncation_le _ _) (by positivity)).trans ?_
    convert he using 1
    rw [Real.rpow_sub hn', Real.sqrt_eq_rpow]
    simp only [NNReal.coe_rpow, NNReal.coe_natCast]
    ring
  simp_rw [mul_pow, inv_pow, Real.sq_sqrt hn'.le, ← Finset.mul_sum, ← div_eq_inv_mul]
  constructor
  · intro i
    exact (abs_sub_le _ _ _).trans ((add_le_add (hr i) hrm.le).trans_eq (add_halves ε))
  · intro j
    exact (abs_sub_le _ _ _).trans ((add_le_add (hc j) hcm.le).trans_eq (add_halves ε))

end TauCeti.Probability.SampleCovariance
