/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.HansonWright
public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.SampleSecondMoment
import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.Probability.Independence.Matrix
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Concentration of independent resolvent quadratic forms

For independent centered directionally sub-Gaussian complex coordinates of unit second moment,
the quadratic form of an independent Hermitian resolvent concentrates about its trace. For a
rectangular matrix with independent entries, zeroing one column makes the sample covariance
independent of the removed column. The resulting leave-one-column-out quadratic form therefore
satisfies the same concentration estimate, with the column normalization kept explicit.

These estimates control the replacement of quadratic forms by normalized traces in resolvent
self-consistency arguments. The spectral parameter can be in either open half-plane; no
independence of real and imaginary parts within a complex coordinate is assumed.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2, proof of Theorem 2.5.
* R. Vershynin, *High-Dimensional Probability* (2018), Theorem 6.2.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Real
open scoped Matrix.Norms.L2Operator NNReal Topology ENNReal
open Filter

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {P : Measure Ω} {Z : ι → Ω → ℂ} {K : ℝ≥0}

/-- A scaled independent Hermitian resolvent quadratic form concentrates about its trace.
The real scale `c` may vanish or be negative. The norm is the complex modulus, and `K` is the
common directional sub-Gaussian variance proxy. At real spectral parameters the bound is trivial. -/
theorem measureReal_norm_star_dotProduct_inv_sub_smul_one_mulVec_sub_trace_gt_le
    (hind : iIndepFun Z P)
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ i, ∫ ω, ‖Z i ω‖ ^ 2 ∂P = 1)
    {A : Ω → Matrix ι ι ℂ} (hA : AEMeasurable A P)
    (hherm : ∀ᵐ ω ∂P, (A ω).IsHermitian) (hAZ : IndepFun A (fun ω i ↦ Z i ω) P)
    (z : ℂ) (c : ℝ) {t : ℝ} :
    P.real {ω | t < ‖(c : ℂ) * (star (fun i ↦ Z i ω) ⬝ᵥ
        (A ω - z • 1)⁻¹ *ᵥ (fun i ↦ Z i ω) - (A ω - z • 1)⁻¹.trace)‖} ≤
      2 * exp (-(1 / 150528) *
        min (t ^ 2 / ((K : ℝ) ^ 2 * (c ^ 2 * Fintype.card ι * |z.im|⁻¹ ^ 2)))
          (t / ((K : ℝ) * (|c| * |z.im|⁻¹)))) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  by_cases hz : z.im = 0
  · simp only [hz, abs_zero, _root_.inv_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, div_zero,
      min_self, exp_zero, mul_one]
    exact (measureReal_mono (Set.subset_univ _)).trans (by simp)
  have hm : Measurable (fun M : Matrix ι ι ℂ ↦ (c : ℂ) • (M - z • 1)⁻¹) := by fun_prop
  have hop : ∀ᵐ ω ∂P, ‖(c : ℂ) • (A ω - z • 1)⁻¹‖ ≤ |c| * |z.im|⁻¹ := by
    filter_upwards [hherm] with ω hω
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, RCLike.im_eq_complex_im] using
      mul_le_mul_of_nonneg_left (hω.l2_opNorm_inv_sub_smul_one_le hz) (abs_nonneg c)
  have hfrob : ∀ᵐ ω ∂P, ∑ i, ∑ j, ‖((c : ℂ) • (A ω - z • 1)⁻¹) i j‖ ^ 2 ≤
      c ^ 2 * Fintype.card ι * |z.im|⁻¹ ^ 2 := by
    filter_upwards [hop] with ω hω
    calc
      _ ≤ (Fintype.card ι : ℝ) * ‖(c : ℂ) • (A ω - z • 1)⁻¹‖ ^ 2 :=
        Matrix.sum_sum_norm_sq_le_card_mul_l2_opNorm_sq _
      _ ≤ (Fintype.card ι : ℝ) * (|c| * |z.im|⁻¹) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, sq_abs]; ring
  have h := hind.measureReal_norm_star_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    hZ (hm.comp_aemeasurable hA) (hAZ.comp hm measurable_id) hfrob hop (t := t)
  have hform (ω : Ω) :
      star (fun i ↦ Z i ω) ⬝ᵥ ((c : ℂ) • (A ω - z • 1)⁻¹) *ᵥ (fun i ↦ Z i ω) -
        ∑ i, ((c : ℂ) • (A ω - z • 1)⁻¹) i i * ((P[fun ω' ↦ ‖Z i ω'‖ ^ 2] : ℝ) : ℂ) =
      (c : ℂ) * (star (fun i ↦ Z i ω) ⬝ᵥ (A ω - z • 1)⁻¹ *ᵥ
        (fun i ↦ Z i ω) - (A ω - z • 1)⁻¹.trace) := by
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hunit, Complex.ofReal_one,
      mul_one, Matrix.smul_apply, ← Finset.mul_sum, Matrix.trace, Matrix.diag]
    rw [mul_sub]
  convert h using 1
  congr 1
  ext ω
  exact iff_of_eq (congrArg (fun w : ℂ ↦ t < ‖w‖) (hform ω).symm)

end ProbabilityTheory.iIndepFun

namespace ProbabilityTheory.iIndepFun

variable {Ω p n : Type*} [MeasurableSpace Ω] [Fintype p] [Fintype n]
  [DecidableEq p] [DecidableEq n] {P : Measure Ω} {X : Ω → Matrix p n ℂ} {K : ℝ≥0}

/-- The column-normalized leave-one-column-out covariance resolvent quadratic form concentrates
about the column-normalized trace. Entries are independent; only the chosen column needs unit
second absolute moments and directional sub-Gaussian bounds. Empty row types are included. -/
theorem measureReal_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace_gt_le
    (hind : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hm : AEMeasurable X P) (k : n)
    (hX : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X ω i k).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ i, ∫ ω, ‖X ω i k‖ ^ 2 ∂P = 1)
    (z : ℂ) {t : ℝ} :
    P.real {ω | t < ‖(Fintype.card n : ℂ)⁻¹ *
        (star (fun i ↦ X ω i k) ⬝ᵥ (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
          (fun i ↦ X ω i k) - (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹.trace)‖} ≤
      2 * exp (-(1 / 150528) *
        min ((Fintype.card n : ℝ) ^ 2 * t ^ 2 * |z.im| ^ 2 /
          ((K : ℝ) ^ 2 * Fintype.card p)) ((Fintype.card n : ℝ) * t * |z.im| / K)) := by
  have hcov : Measurable (sampleCovariance : Matrix p n ℂ → Matrix p p ℂ) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [sampleCovariance_apply]
    fun_prop
  have hup : Measurable (fun M : Matrix p n ℂ ↦ M.updateCol k 0) := by
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.updateCol_apply]
    split_ifs <;> fun_prop
  have hcol := hind.precomp (g := fun i : p ↦ (i, k)) (by intro i j h; exact congrArg Prod.fst h)
  have h := hcol.measureReal_norm_star_dotProduct_inv_sub_smul_one_mulVec_sub_trace_gt_le
    hX hunit ((hcov.comp hup).comp_aemeasurable hm)
    (.of_forall fun ω ↦ isHermitian_sampleCovariance _)
    ((hind.indepFun_updateCol_zero hm k).comp hcov measurable_id) z
    (Fintype.card n : ℝ)⁻¹ (t := t)
  have hrate :
      min (t ^ 2 / ((K : ℝ) ^ 2 *
        ((Fintype.card n : ℝ)⁻¹ ^ 2 * Fintype.card p * |z.im|⁻¹ ^ 2)))
        (t / ((K : ℝ) * (|(Fintype.card n : ℝ)⁻¹| * |z.im|⁻¹))) =
      min ((Fintype.card n : ℝ) ^ 2 * t ^ 2 * |z.im| ^ 2 /
        ((K : ℝ) ^ 2 * Fintype.card p)) ((Fintype.card n : ℝ) * t * |z.im| / K) := by
    congr 1 <;> simp only [abs_inv, Nat.abs_cast, div_eq_mul_inv,
      _root_.mul_inv_rev, inv_pow, inv_inv] <;> ring
  have hcomp : ((sampleCovariance ∘ fun M : Matrix p n ℂ ↦ M.updateCol k 0) ∘ X) =
      (fun ω ↦ sampleCovariance ((X ω).updateCol k 0)) := by funext ω; rfl
  rw [hrate, hcomp] at h
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using h

/-- A simultaneous leave-one-column-out covariance resolvent estimate. The union bound has
one term per column and requires no additional independence between the quadratic forms. -/
theorem measureReal_exists_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace_gt_le
    (hind : iIndepFun (fun ij : p × n ↦ fun ω ↦ X ω ij.1 ij.2) P)
    (hX : ∀ i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ i j, ∫ ω, ‖X ω i j‖ ^ 2 ∂P = 1)
    (z : ℂ) {t : ℝ} :
    P.real {ω | ∃ k, t < ‖(Fintype.card n : ℂ)⁻¹ *
        (star (fun i ↦ X ω i k) ⬝ᵥ (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
          (fun i ↦ X ω i k) - (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹.trace)‖} ≤
      2 * Fintype.card n * exp (-(1 / 150528) *
        min ((Fintype.card n : ℝ) ^ 2 * t ^ 2 * |z.im| ^ 2 /
          ((K : ℝ) ^ 2 * Fintype.card p)) ((Fintype.card n : ℝ) * t * |z.im| / K)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  have hm : AEMeasurable X P := .of_eval fun i ↦ .of_eval fun j ↦
    (integrable_of_hasSubgaussianMGF_re_star_mul (hX i j)).aemeasurable
  calc
    _ = P.real (⋃ k, {ω | t < ‖(Fintype.card n : ℂ)⁻¹ *
        (star (fun i ↦ X ω i k) ⬝ᵥ (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
          (fun i ↦ X ω i k) - (sampleCovariance ((X ω).updateCol k 0) - z • 1)⁻¹.trace)‖}) := by
      congr 1
      ext ω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    _ ≤ _ := (measureReal_iUnion_fintype_le _).trans
      ((Finset.sum_le_sum fun k _ ↦
        hind.measureReal_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace_gt_le
          hm k (fun i ↦ hX i k) (fun i ↦ hunit i k) z (t := t)).trans_eq (by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring))

end ProbabilityTheory.iIndepFun

namespace TauCeti.Probability

private lemma covariance_quadraticForm_rate_le {s d C L t η : ℝ}
    (hs : 0 ≤ s) (hd : 0 < d) (h : d ≤ C * s) :
    s * min (t ^ 2 * η ^ 2 / (L ^ 2 * C)) (t * η / L) ≤
      min (s ^ 2 * t ^ 2 * η ^ 2 / (L ^ 2 * d)) (s * t * η / L) := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp
  by_cases hL : L = 0
  · simp [hL]
  have hC : 0 < C := by nlinarith
  rw [mul_min_of_nonneg _ _ hs.le]
  refine min_le_min ?_ (le_of_eq (by ring))
  calc
    s * (t ^ 2 * η ^ 2 / (L ^ 2 * C)) =
        s ^ 2 * t ^ 2 * η ^ 2 / (L ^ 2 * (C * s)) := by field_simp
    _ ≤ s ^ 2 * t ^ 2 * η ^ 2 / (L ^ 2 * d) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {p : ℕ → ℕ} {X : (m : ℕ) → Ω → Matrix (Fin (p m)) (Fin (m + 1)) ℂ} {K : ℝ≥0}

/-- Leave-one-column-out covariance quadratic-form errors have summable exceptional
probabilities when the aspect ratios are eventually bounded. The matrices at different sizes
may have any coupling, and their entry laws may vary with size and position. -/
theorem summable_measureReal_exists_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ X m ω ij.1 ij.2) P)
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X m ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    (hdim : ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, (p m : ℝ) ≤ C * (m + 1))
    {z : ℂ} (hz : z.im ≠ 0) {t : ℝ} (ht : 0 < t) :
    Summable (fun m ↦ P.real {ω | ∃ k, t < ‖((m + 1 : ℕ) : ℂ)⁻¹ *
      (star (fun i ↦ X m ω i k) ⬝ᵥ (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
        (fun i ↦ X m ω i k) - (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹.trace)‖}) := by
  have : IsProbabilityMeasure P := (hind 0).isProbabilityMeasure
  obtain ⟨C, hC, hdim⟩ := hdim
  let L : ℝ≥0 := max K 1
  have : 0 < (L : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast le_max_right K 1)
  have hXL m i j u := (hX m i j u).mono
    (mul_le_mul_of_nonneg_left (le_max_left K 1) (by positivity))
  let a := (1 / 150528 : ℝ) * min (t ^ 2 * |z.im| ^ 2 / ((L : ℝ) ^ 2 * C)) (t * |z.im| / L)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs : Summable (fun m : ℕ ↦ 2 * (m + 1 : ℝ) * exp (-a * (m + 1))) := by
    simpa only [pow_one, Nat.cast_add, Nat.cast_one, mul_assoc] using
      ((summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul 1 ha)).mul_left 2
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hdim] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  by_cases hp : p m = 0
  · have : IsEmpty (Fin (p m)) := by rw [hp]; infer_instance
    simp only [dotProduct_of_isEmpty, trace_eq_zero_of_isEmpty, sub_self, mul_zero, norm_zero,
      not_lt.2 ht.le, exists_const, Set.ofPred_false, measureReal_empty]
    positivity
  have hp' : 0 < (p m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hrate := covariance_quadraticForm_rate_le (L := (L : ℝ)) (t := t) (η := |z.im|)
    (by positivity : 0 ≤ (m + 1 : ℝ)) hp' hm
  have hi := hind m
  have htail :=
    hi.measureReal_exists_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace_gt_le
      (hXL m) (hunit m) z (t := t)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at htail
  have hexp : exp (-(1 / 150528) * min
      ((m + 1 : ℝ) ^ 2 * t ^ 2 * |z.im| ^ 2 / ((L : ℝ) ^ 2 * p m))
      ((m + 1 : ℝ) * t * |z.im| / L)) ≤ exp (-a * (m + 1)) := by
    apply exp_le_exp.2
    dsimp only [a]
    nlinarith
  simpa only [Nat.cast_add, Nat.cast_one] using
    htail.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- Uniformly over all columns, the column-normalized leave-one-column-out covariance
resolvent quadratic-form errors tend almost surely to zero at each nonreal spectral parameter.
Only an eventual upper bound on the aspect ratios is needed; empty row spaces are allowed.
There is no independence assumption across matrix sizes. -/
theorem ae_tendsto_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace
    (hind : ∀ m, iIndepFun (fun ij : Fin (p m) × Fin (m + 1) ↦
      fun ω ↦ X m ω ij.1 ij.2) P)
    (hX : ∀ m i j (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * X m ω i j).re)
      (‖u‖₊ ^ 2 * K) P)
    (hunit : ∀ m i j, ∫ ω, ‖X m ω i j‖ ^ 2 ∂P = 1)
    (hdim : ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, (p m : ℝ) ≤ C * (m + 1))
    {z : ℂ} (hz : z.im ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun m ↦ ‖fun k ↦ ((m + 1 : ℕ) : ℂ)⁻¹ *
      (star (fun i ↦ X m ω i k) ⬝ᵥ (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
        (fun i ↦ X m ω i k) - (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹.trace)‖)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hind 0).isProbabilityMeasure
  let E (m : ℕ) (ω : Ω) (k : Fin (m + 1)) := ((m + 1 : ℕ) : ℂ)⁻¹ *
    (star (fun i ↦ X m ω i k) ⬝ᵥ (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹ *ᵥ
      (fun i ↦ X m ω i k) - (sampleCovariance ((X m ω).updateCol k 0) - z • 1)⁻¹.trace)
  have hbc (j : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ∀ k, ‖E m ω k‖ ≤ (j + 1 : ℝ)⁻¹ := by
    have hs :=
      summable_measureReal_exists_norm_star_dotProduct_sampleCovariance_resolvent_mulVec_sub_trace
        hind hX hunit hdim hz (by positivity : 0 < (j + 1 : ℝ)⁻¹)
    have hfinite : (∑' m, P {ω | ∃ k, (j + 1 : ℝ)⁻¹ < ‖E m ω k‖}) ≠ ∞ := by
      simpa only [E, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        hs.tsum_ofReal_ne_top
    simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using ae_eventually_notMem hfinite
  filter_upwards [ae_all_iff.2 hbc] with ω hω
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω j] with m hm
  have hnorm : ‖E m ω‖ ≤ (j + 1 : ℝ)⁻¹ := (pi_norm_le_iff_of_nonneg (by positivity)).2 hm
  simpa only [E, Real.dist_eq, sub_zero, Real.norm_eq_abs, abs_norm] using
    hnorm.trans_lt (by simpa only [one_div] using hj)

end TauCeti.Probability
