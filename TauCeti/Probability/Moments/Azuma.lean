/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import TauCeti.MeasureTheory.Measure.Tail

/-!
# Azuma-Hoeffding inequality

This file proves the Azuma-Hoeffding tail bound for a finite sum of bounded martingale
differences, on an arbitrary probability space. A conditional form of Hoeffding's lemma bounds the
conditional exponential moment of each bounded, conditionally centered increment, using a chord
bound and the two-point law rather than regular conditional distributions. Induction on the
partial sums then shows that the sum is sub-Gaussian, and the Chernoff bound gives the tail.
Only `hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`, whose conclusion is Mathlib's kernel
predicate, needs a standard Borel space.

## Main results

* `TauCeti.Probability.hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero` — conditional
  Hoeffding's lemma for an arbitrary interval;
* `TauCeti.Probability.measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences` — the
  one-sided Azuma-Hoeffding inequality with interval bounds;
* `TauCeti.Probability.measureReal_sum_range_ge_le_of_bounded_martingale_differences` — the
  one-sided Azuma-Hoeffding inequality for increments with `|Y i| ≤ b i`;
* `TauCeti.Probability.measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences` — its
  two-sided interval-bounded form;
* `TauCeti.Probability.measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences` — the
  two-sided bounded-increment form.

## References

* K. Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal 19
  (1967), 357-367.
* C. McDiarmid, *On the method of bounded differences*, in *Surveys in Combinatorics*, 1989,
  London Math. Soc. Lecture Note Ser. 141, Cambridge Univ. Press (1989), 148-188.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- A conditionally centered random variable whose values lie in `[a, b]` is conditionally
sub-Gaussian with parameter `((‖b - a‖₊ / 2) ^ 2)`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable[mΩ] X) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  have hX_int : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hbound
  have hmean_trim : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    (stronglyMeasurable_condExp.ae_eq_trim_iff hm stronglyMeasurable_const).2 hmean
  have hzero_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∫ y, X y ∂condExpKernel (mΩ := mΩ) μ m ω = 0 := by
    exact (condExp_ae_eq_trim_integral_condExpKernel (mΩ := mΩ) hm hX_int).symm.trans
      hmean_trim
  have hbound_kernel :
      ∀ᵐ ω ∂μ.trim hm, ∀ᵐ y ∂condExpKernel (mΩ := mΩ) μ m ω,
        X y ∈ Set.Icc a b := by
    have hcomp : condExpKernel (mΩ := mΩ) μ m ∘ₘ μ.trim hm = μ :=
      condExpKernel_comp_trim (mΩ := mΩ) hm
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    exact hbound
  -- The conditional predicate is the kernel-level sub-Gaussian bound.
  change Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2)
    (condExpKernel (mΩ := mΩ) μ m) (μ.trim hm)
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim (mΩ := mΩ) hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hbound
  · intro q
    filter_upwards [hzero_kernel, hbound_kernel] with ω hzero hω
    have : IsProbabilityMeasure (condExpKernel (mΩ := mΩ) μ m ω) :=
      (inferInstance : IsMarkovKernel (condExpKernel (mΩ := mΩ) μ m)).isProbabilityMeasure ω
    have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hX.aemeasurable hω hzero
    exact hsub.mgf_le q

/-- The chord of the exponential lies above it on `[a, b]`. -/
theorem exp_mul_le_add_mul {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) (t : ℝ) :
    exp (t * x) ≤ (b * exp (t * a) - a * exp (t * b)) / (b - a) +
      (exp (t * b) - exp (t * a)) / (b - a) * x := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hconv := convexOn_exp.2 (Set.mem_univ (t * a)) (Set.mem_univ (t * b))
    (div_nonneg (sub_nonneg.2 hx.2) hba.le) (div_nonneg (sub_nonneg.2 hx.1) hba.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at hconv
  have h1 : (b - x) / (b - a) * (t * a) + (x - a) / (b - a) * (t * b) = t * x := by
    field_simp; ring
  rw [h1] at hconv
  refine hconv.trans_eq ?_
  field_simp; ring

/-- The chord value `(b e^{ta} - a e^{tb}) / (b - a)` is at most `exp (((b - a) / 2) ^ 2 t ^ 2 / 2)`
for `a ≤ 0 ≤ b`, by Hoeffding's lemma applied to the mean-zero two-point law on `{a, b}`. -/
theorem chord_le_exp {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a < b) (t : ℝ) :
    (b * exp (t * a) - a * exp (t * b)) / (b - a) ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) := by
  have hba : 0 < b - a := sub_pos.2 hab
  set ν : Measure ℝ := ENNReal.ofReal (b / (b - a)) • Measure.dirac a +
    ENNReal.ofReal (-a / (b - a)) • Measure.dirac b with hν
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp only [hν, add_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (div_nonneg hb hba.le) (div_nonneg (neg_nonneg.2 ha) hba.le)]
    rw [show b / (b - a) + -a / (b - a) = 1 by field_simp; ring]
    simp
  have hint (f : ℝ → ℝ) : ∀ c : ℝ, Integrable f (ENNReal.ofReal c • Measure.dirac a) ∧
      Integrable f (ENNReal.ofReal c • Measure.dirac b) := fun c =>
    ⟨(integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top,
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top⟩
  have hI (f : ℝ → ℝ) : ∫ x, f x ∂ν = b / (b - a) * f a + -a / (b - a) * f b := by
    rw [hν, integral_add_measure (hint f _).1 (hint f _).2, integral_smul_measure,
      integral_smul_measure]
    simp only [integral_dirac, ENNReal.toReal_ofReal (div_nonneg hb hba.le),
      ENNReal.toReal_ofReal (div_nonneg (neg_nonneg.2 ha) hba.le), smul_eq_mul]
  have hae : ∀ᵐ x ∂ν, id x ∈ Set.Icc a b := by
    rw [hν, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).2 ⟨le_rfl, hab.le⟩) _,
      Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).2 ⟨hab.le, le_rfl⟩) _⟩
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := ν) (X := id) (a := a)
    (b := b) aemeasurable_id hae (by
      show ∫ x, id x ∂ν = 0
      rw [hI id]
      simp only [id]
      field_simp
      ring)
  have := hsub.mgf_le t
  simp only [mgf, id, hI] at this
  convert this using 2
  · field_simp; ring_nf
  · push_cast; rfl

/-- A mean zero random variable with values in `[a, b]` lies in `[a, b]` with `a ≤ 0 ≤ b`. -/
theorem nonpos_nonneg_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {a b : ℝ} (hX : Integrable X μ) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : ∫ ω, X ω ∂μ = 0) : a ≤ 0 ∧ 0 ≤ b := by
  constructor
  · simpa [hmean] using integral_mono_ae (integrable_const a) hX (hbound.mono fun ω h => h.1)
  · simpa [hmean] using integral_mono_ae hX (integrable_const b) (hbound.mono fun ω h => h.2)

/-- Conditional Hoeffding's lemma without regular conditional distributions: the conditional
exponential moment of a conditionally centered random variable with values in `[a, b]`. -/
theorem condExp_exp_mul_le [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {a b : ℝ} (hX : Measurable[mΩ] X) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hmean : μ[X | m] =ᵐ[μ] 0) (t : ℝ) :
    μ[fun ω ↦ exp (t * X ω) | m] ≤ᵐ[μ] fun _ ↦ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) := by
  have hX_int : Integrable X μ := Integrable.of_mem_Icc a b hX.aemeasurable hbound
  have hint : Integrable (fun ω ↦ exp (t * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hX.aemeasurable hbound
  have hzero : ∫ ω, X ω ∂μ = 0 := by
    rw [← integral_condExp hm, integral_congr_ae hmean]; simp
  obtain ⟨ha, hb⟩ := nonpos_nonneg_of_mem_Icc_of_integral_eq_zero (mΩ := mΩ) hX_int hbound hzero
  rcases (ha.trans hb).eq_or_lt with hab | hab
  · have hX0 : ∀ᵐ ω ∂μ, exp (t * X ω) = 1 := by
      filter_upwards [hbound] with ω hω
      have : X ω = 0 := by linarith [hω.1, hω.2]
      simp [this]
    refine (condExp_congr_ae hX0).trans_le ?_
    rw [condExp_const hm, hab]
    exact Filter.Eventually.of_forall fun ω ↦ by simp
  · have hint2 : Integrable (fun ω ↦ (b * exp (t * a) - a * exp (t * b)) / (b - a) +
        (exp (t * b) - exp (t * a)) / (b - a) * X ω) μ :=
      (integrable_const _).add (hX_int.const_mul _)
    have h1 := condExp_mono (m := m) hint hint2
      (hbound.mono fun ω hω => exp_mul_le_add_mul hab hω t)
    have h2 := condExp_add (m := m)
      (integrable_const ((b * exp (t * a) - a * exp (t * b)) / (b - a)))
      (hX_int.const_mul ((exp (t * b) - exp (t * a)) / (b - a)))
    have h3 := condExp_smul (m := m) (μ := μ) ((exp (t * b) - exp (t * a)) / (b - a)) X
    rw [condExp_const hm] at h2
    filter_upwards [h1, h2, h3, hmean] with ω h1 h2 h3 h4
    have h3' : μ[fun x ↦ (exp (t * b) - exp (t * a)) / (b - a) * X x | m] ω =
        (exp (t * b) - exp (t * a)) / (b - a) * μ[X | m] ω := h3
    refine h1.trans ((le_of_eq (h2.trans ?_)).trans (chord_le_exp ha hb hab t))
    rw [Pi.add_apply, h3', h4]
    simp

/-- Pulling out a measurable factor: if `Z ≥ 0` is `m`-measurable and the conditional mean of `W`
is at most `K`, then `∫ Z * W ≤ K * ∫ Z`. -/
theorem integral_mul_le_of_condExp_le [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {Z W : Ω → ℝ} {K : ℝ} (hZ : StronglyMeasurable[m] Z) (hZ0 : 0 ≤ Z)
    (hZint : Integrable Z μ) (hWint : Integrable W μ) (hZW : Integrable (fun ω ↦ Z ω * W ω) μ)
    (hW : μ[W | m] ≤ᵐ[μ] fun _ ↦ K) :
    ∫ ω, Z ω * W ω ∂μ ≤ K * ∫ ω, Z ω ∂μ := by
  have hpull : μ[Z * W | m] =ᵐ[μ] Z * μ[W | m] :=
    condExp_mul_of_stronglyMeasurable_left hZ hZW hWint
  have hint : Integrable (Z * μ[W | m]) μ := integrable_condExp.congr hpull
  calc ∫ ω, Z ω * W ω ∂μ = ∫ ω, μ[Z * W | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, (Z * μ[W | m]) ω ∂μ := integral_congr_ae hpull
    _ ≤ ∫ ω, K * Z ω ∂μ := by
      refine integral_mono_ae hint (hZint.const_mul K) ?_
      filter_upwards [hW] with ω hω
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hω (hZ0 ω)
    _ = K * ∫ ω, Z ω ∂μ := integral_const_mul _ _

/-- A conditionally centered bounded increment adds its Hoeffding variance proxy to a
sub-Gaussian `m`-measurable random variable. -/
theorem hasSubgaussianMGF_add_of_condExp_eq_zero [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {S X : Ω → ℝ} {c : ℝ≥0} {a b : ℝ} (hS : HasSubgaussianMGF S c μ)
    (hSm : StronglyMeasurable[m] S) (hX : Measurable[mΩ] X)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ S ω + X ω) (c + (‖b - a‖₊ / 2) ^ 2) μ := by
  have hZ (t : ℝ) : StronglyMeasurable[m] fun ω ↦ exp (t * S ω) :=
    Real.continuous_exp.comp_stronglyMeasurable (hSm.const_mul t)
  have hWint (t : ℝ) : Integrable (fun ω ↦ exp (t * X ω)) μ :=
    integrable_exp_mul_of_mem_Icc hX.aemeasurable hbound
  have hZW (t : ℝ) : Integrable (fun ω ↦ exp (t * S ω) * exp (t * X ω)) μ := by
    refine (hS.integrable_exp_mul t).mul_bdd (c := exp (|t| * (|a| + |b|)))
      (hX.const_mul t).exp.aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
    calc t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ |t| * (|a| + |b|) := by
        gcongr
        exact abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hω.1],
          by linarith [le_abs_self b, abs_nonneg a, hω.2]⟩
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · simpa [mul_add, exp_add] using hZW t
  · have hmul : mgf (fun ω ↦ S ω + X ω) μ t = ∫ ω, exp (t * S ω) * exp (t * X ω) ∂μ := by
      simp [mgf, mul_add, exp_add]
    rw [hmul]
    calc _ ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) * ∫ ω, exp (t * S ω) ∂μ :=
          integral_mul_le_of_condExp_le (mΩ := mΩ) hm (hZ t) (fun ω ↦ (exp_pos _).le)
            (hS.integrable_exp_mul t) (hWint t) (hZW t)
            (condExp_exp_mul_le (mΩ := mΩ) hm hX hbound hmean t)
      _ ≤ exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) * exp (c * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (hS.mgf_le t) (exp_pos _).le
      _ = _ := by rw [← exp_add]; push_cast; ring_nf

/-- A sum of conditionally centered bounded increments is sub-Gaussian with the sum of the
Hoeffding variance proxies. -/
theorem hasSubgaussianMGF_sum_range_of_mem_Icc [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ} (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (b i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0) (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω)
      (∑ i ∈ Finset.range n, (‖b i - a i‖₊ / 2) ^ 2) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    cases n with
    | zero =>
      simpa using hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        ((h_adapted 0).mono (ℱ.le 0)).measurable.aemeasurable (hbound 0 (by lia)) hmean0
    | succ n =>
      have hS := hn (fun i hi ↦ hbound i (by lia)) (fun i hi ↦ hmean i (by lia))
      have hSm : StronglyMeasurable[ℱ n] fun ω ↦ ∑ i ∈ Finset.range (n + 1), Y i ω :=
        Finset.stronglyMeasurable_fun_sum _ fun i hi ↦
          (h_adapted i).mono (ℱ.mono (by simpa [Nat.lt_succ_iff] using hi))
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      exact hasSubgaussianMGF_add_of_condExp_eq_zero (mΩ := mΩ) (ℱ.le n) hS hSm
        ((h_adapted (n + 1)).mono (ℱ.le (n + 1))).measurable (hbound (n + 1) (by lia))
        (hmean n (by lia))

/-- **Azuma-Hoeffding inequality for interval-bounded martingale differences.** Let `Y i` be a
strongly adapted sequence with conditionally centered increments in `[a i, b i]` almost surely.
Then the upper tail is bounded using Hoeffding's variance proxy
`∑ i < n, ((‖b i - a i‖₊ / 2) ^ 2)`. -/
theorem measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (b i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 /
        (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
  simpa using (hasSubgaussianMGF_sum_range_of_mem_Icc h_adapted n hbound hmean0 hmean).measure_ge_le
    hε

/-- **Azuma-Hoeffding inequality.** Let `Y i` be a strongly adapted sequence of martingale
differences with `|Y i| ≤ b i` almost surely, mean zero at time zero, and conditional mean zero at
each later step. Then the upper tail of the sum of its first `n` terms is bounded by
`exp (-ε ^ 2 / (2 * ∑ i < n, b i ^ 2))`. -/
theorem measureReal_sum_range_ge_le_of_bounded_martingale_differences
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  have hIcc : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact abs_le.mp hω
  have hterm (i : ℕ) :
      ((‖(b i : ℝ) - -(b i : ℝ)‖₊ / 2) ^ 2 : ℝ) = (b i : ℝ) ^ 2 := by
    simp only [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity : 0 ≤ (b i : ℝ) + (b i : ℝ))]
    ring
  have hbound' := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
      (a := fun i => -(b i : ℝ)) (b := fun i => (b i : ℝ))
      h_adapted n hIcc hmean0 hmean hε
  simp_rw [hterm] at hbound'
  exact hbound'

/-- **Two-sided Azuma-Hoeffding inequality for interval-bounded martingale differences.** Under
the assumptions of the one-sided interval theorem, the absolute value of the sum exceeds `ε` with
probability at most twice its one-sided bound. -/
theorem measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (b i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * exp (-ε ^ 2 /
        (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
  have hneg_adapted : StronglyAdapted ℱ (fun i ω ↦ -Y i ω) := by
    intro i
    exact (h_adapted i).neg
  have hneg_bound : ∀ i < n, ∀ᵐ ω ∂μ, -Y i ω ∈ Set.Icc (-b i) (-a i) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact ⟨neg_le_neg hω.2, neg_le_neg hω.1⟩
  have hneg_mean0 : ∫ ω, -Y 0 ω ∂μ = 0 := by
    simp [integral_neg, hmean0]
  have hneg_mean : ∀ i < n - 1, μ[-Y (i + 1) | ℱ i] =ᵐ[μ] 0 := by
    intro i hi
    calc
      μ[-Y (i + 1) | ℱ i] =ᵐ[μ] -μ[Y (i + 1) | ℱ i] := condExp_neg _ _
      _ =ᵐ[μ] 0 := by simpa using (hmean i hi).neg
  have hupper := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    h_adapted n hbound hmean0 hmean hε
  have hlower := measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences
    (a := fun i => -b i) (b := fun i => -a i)
    hneg_adapted n hneg_bound hneg_mean0 hneg_mean hε
  have hwidth (i : ℕ) : abs (-a i + b i) = abs (b i - a i) := by
    congr 1
    ring
  have hlower' :
      μ.real {ω | ε ≤ -∑ i ∈ Finset.range n, Y i ω} ≤
        exp (-ε ^ 2 /
          (2 * ∑ i ∈ Finset.range n, ((‖b i - a i‖₊ / 2) ^ 2 : ℝ))) := by
    simpa [hwidth] using hlower
  calc
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} +
          μ.real {ω | ε ≤ -∑ i ∈ Finset.range n, Y i ω} :=
        TauCeti.measureReal_le_abs_le_add
    _ ≤ _ := (add_le_add hupper hlower').trans (le_of_eq (by ring))

/-- **Two-sided Azuma-Hoeffding inequality.** Under the assumptions of
`measureReal_sum_range_ge_le_of_bounded_martingale_differences`, the absolute value of the sum
exceeds `ε` with probability at most twice the one-sided bound. -/
theorem measureReal_abs_sum_range_ge_le_of_bounded_martingale_differences
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {b : ℕ → ℝ≥0}
    (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (hbound : ∀ i < n, ∀ᵐ ω ∂μ, |Y i ω| ≤ (b i : ℝ))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hmean : ∀ i < n - 1, μ[Y (i + 1) | ℱ i] =ᵐ[μ] 0)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|} ≤
      2 * exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (b i : ℝ) ^ 2)) := by
  have hIcc : ∀ i < n, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-(b i : ℝ)) (b i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    exact abs_le.mp hω
  have hterm (i : ℕ) :
      ((‖(b i : ℝ) - -(b i : ℝ)‖₊ / 2) ^ 2 : ℝ) = (b i : ℝ) ^ 2 := by
    simp only [coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity : 0 ≤ (b i : ℝ) + (b i : ℝ))]
    ring
  have hbound' := measureReal_abs_sum_range_ge_le_of_mem_Icc_martingale_differences
    (a := fun i => -(b i : ℝ)) (b := fun i => (b i : ℝ))
    h_adapted n hIcc hmean0 hmean hε
  simp_rw [hterm] at hbound'
  exact hbound'

end TauCeti.Probability
