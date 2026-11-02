/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Support
public import TauCeti.Probability.Distributions.Hypoexponential.PartialFractions
public import TauCeti.Probability.Density
import TauCeti.Probability.Distributions.Hypoexponential.Transforms
import TauCeti.Probability.Distributions.Gamma.CharFun
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# The density of a hypoexponential law

For a nonempty family of positive rates, group the `r i` by their distinct values `ρ`, with
multiplicities `m ρ`, and let `A ρ k` be the partial-fraction coefficients of
`TauCeti.Probability.hypoexponentialCoeff`. The density of the sum of independent exponential
variables with rates `r` is

`f x = ∑ ρ, ∑ k ∈ [1, m ρ], A ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)!`

for `x > 0`, and zero for `x ≤ 0`. Equivalently, `f` is the combination of the Erlang densities
of shape `k` and rate `ρ` with the weights `A ρ k / ρ ^ k`, which sum to one but may be negative.
For an empty family the chosen formula below is zero, while its law is the point mass at zero.

The identification of `f` with the law compares characteristic functions. Splitting the weights
into their positive and negative parts gives two finite Erlang mixtures, and the partial-fraction
expansion of `∏ i, r i / (r i - I t)` shows that adding the negative mixture to the
hypoexponential law gives the positive one. Cancelling the negative mixture in the
Radon--Nikodym derivative identifies the law with `volume.withDensity f` and shows that `f` is
almost everywhere nonnegative; continuity of the formula on `(0, ∞)` then makes `f` nonnegative
everywhere.

With pairwise distinct rates the formula is the classical sum
`∑ i, r i * exp (-(r i * x)) * ∏ j ≠ i, r j / (r j - r i)`, and with a single common rate it is
the Erlang density.

## Main definitions

* `TauCeti.Probability.hypoexponentialPDFReal r`: the real density, zero for an empty family,
  for invalid rates, and on `(-∞, 0]`.
* `TauCeti.Probability.hypoexponentialPDF r`: its `ℝ≥0∞`-valued version.

## Main results

* `TauCeti.Probability.hypoexponentialMeasure_eq_withDensity`: a nonempty valid hypoexponential
  law has density `hypoexponentialPDF r`.
* `TauCeti.Probability.hypoexponentialPDFReal_nonneg`: the density is nonnegative.
* `TauCeti.Probability.integral_hypoexponentialPDFReal_eq_one`: normalization.
* `TauCeti.Probability.hypoexponentialPDFReal_of_injective`: the distinct-rate formula.
* `TauCeti.Probability.hypoexponentialPDFReal_const`: equal rates give the Erlang density.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory Real
open scoped ENNReal Nat

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {r : ι → ℝ} {x : ℝ}

/-- The real density of the hypoexponential law with rates `r`: on `(0, ∞)` it is the sum over
the distinct rates `ρ` and the orders `1 ≤ k ≤ m ρ` of
`A ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)!`, where `m ρ` is the multiplicity of `ρ` and
`A ρ k = hypoexponentialCoeff r ρ k`. It is zero on `(-∞, 0]`, for an empty family, and for
invalid rates. -/
def hypoexponentialPDFReal (r : ι → ℝ) (x : ℝ) : ℝ :=
  if (∀ i, 0 < r i) ∧ 0 < x then
    ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ},
      hypoexponentialCoeff r ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)!
  else 0

/-- The `ℝ≥0∞`-valued density of the hypoexponential law with rates `r`. -/
def hypoexponentialPDF (r : ι → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (hypoexponentialPDFReal r x)

/-- The extended density is the nonnegative coercion of the real density. -/
theorem hypoexponentialPDF_eq_ofReal (r : ι → ℝ) (x : ℝ) :
    hypoexponentialPDF r x = ENNReal.ofReal (hypoexponentialPDFReal r x) := (rfl)

/-- For positive rates, the density at a positive point is the sum of the principal-part terms. -/
@[simp]
theorem hypoexponentialPDFReal_of_pos (hr : ∀ i, 0 < r i) (hx : 0 < x) :
    hypoexponentialPDFReal r x = ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ},
      hypoexponentialCoeff r ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)! := by
  rw [hypoexponentialPDFReal, ite_eq_left ⟨hr, hx⟩]

/-- The density vanishes on `(-∞, 0]`. -/
@[simp]
theorem hypoexponentialPDFReal_of_nonpos (r : ι → ℝ) (hx : x ≤ 0) :
    hypoexponentialPDFReal r x = 0 := by
  rw [hypoexponentialPDFReal, ite_eq_right fun h ↦ hx.not_gt h.2]

/-- The density of an invalid family of rates is zero. -/
@[simp]
theorem hypoexponentialPDFReal_of_not_pos (hr : ¬ ∀ i, 0 < r i) (x : ℝ) :
    hypoexponentialPDFReal r x = 0 := by
  rw [hypoexponentialPDFReal, ite_eq_right fun h ↦ hr h.1]

/-- The density of the empty family is zero; its law is the point mass at zero. -/
@[simp]
theorem hypoexponentialPDFReal_of_isEmpty [IsEmpty ι] (r : ι → ℝ) (x : ℝ) :
    hypoexponentialPDFReal r x = 0 := by
  simp [hypoexponentialPDFReal]

/-- The real density is measurable. -/
@[fun_prop]
theorem measurable_hypoexponentialPDFReal (r : ι → ℝ) :
    Measurable (hypoexponentialPDFReal r) := by
  unfold hypoexponentialPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The extended density is measurable. -/
@[fun_prop]
theorem measurable_hypoexponentialPDF (r : ι → ℝ) : Measurable (hypoexponentialPDF r) :=
  (measurable_hypoexponentialPDFReal r).ennreal_ofReal

/-- The real density is continuous on the positive half-line, including for empty or
invalid families. -/
@[fun_prop]
theorem continuousOn_hypoexponentialPDFReal (r : ι → ℝ) :
    ContinuousOn (hypoexponentialPDFReal r) (Set.Ioi 0) := by
  by_cases hr : ∀ i, 0 < r i
  · apply ContinuousOn.congr (f := fun x ↦ ∑ ρ ∈ univ.image r,
      ∑ k ∈ Icc 1 #{i | r i = ρ},
        hypoexponentialCoeff r ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)!)
    · fun_prop
    · intro x hx
      exact hypoexponentialPDFReal_of_pos hr hx
  · exact continuousOn_const.congr fun x _ ↦ hypoexponentialPDFReal_of_not_pos hr x

/-- For positive rates and `x > 0`, the density is the combination of Erlang densities with the
weights `A ρ k / ρ ^ k`. For a nonempty family these weights sum to one by
`sum_hypoexponentialCoeff_div_pow`. -/
theorem hypoexponentialPDFReal_eq_sum_gammaPDFReal (hr : ∀ i, 0 < r i) (hx : 0 < x) :
    hypoexponentialPDFReal r x = ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ},
      hypoexponentialCoeff r ρ k / ρ ^ k * gammaPDFReal k ρ x := by
  rw [hypoexponentialPDFReal_of_pos hr hx]
  refine sum_congr rfl fun ρ hρ ↦ sum_congr rfl fun k hk ↦ ?_
  obtain ⟨i, -, rfl⟩ := mem_image.1 hρ
  rw [div_mul_comm, gammaPDFReal_nat_div_pow (mem_Icc.1 hk).1 (hr i).ne' hx.le]
  ring

/-! ### Identification with the law -/

section Law

/-- The pairs `(ρ, k)` indexing the partial-fraction expansion. -/
private abbrev poles (r : ι → ℝ) : Finset (Σ _ : ℝ, ℕ) :=
  (univ.image r).sigma fun ρ ↦ Icc 1 #{i | r i = ρ}

/-- The Erlang weight `A ρ k / ρ ^ k` attached to a pole. -/
private abbrev weight (r : ι → ℝ) (p : Σ _ : ℝ, ℕ) : ℝ :=
  hypoexponentialCoeff r p.1 p.2 / p.1 ^ p.2

private theorem pos_of_mem_poles (hr : ∀ i, 0 < r i) {p : Σ _ : ℝ, ℕ} (hp : p ∈ poles r) :
    0 < p.1 ∧ 0 < p.2 := by
  obtain ⟨hρ, hk⟩ := mem_sigma.1 hp
  obtain ⟨i, -, hi⟩ := mem_image.1 hρ
  exact ⟨hi ▸ hr i, (mem_Icc.1 hk).1⟩

/-- The Erlang mixture with the weights `c p`, clipped at zero. -/
private abbrev erlangMixturePDF (r : ι → ℝ) (c : (Σ _ : ℝ, ℕ) → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ p ∈ poles r, ENNReal.ofReal (c p) * gammaPDF p.2 p.1 x

private theorem measurable_erlangMixturePDF (r : ι → ℝ) (c : (Σ _ : ℝ, ℕ) → ℝ) :
    Measurable (erlangMixturePDF r c) :=
  Finset.measurable_sum _ fun _ _ ↦
    measurable_const.mul (measurable_gammaPDF _ _)

private theorem withDensity_erlangMixturePDF (r : ι → ℝ) (c : (Σ _ : ℝ, ℕ) → ℝ) :
    volume.withDensity (erlangMixturePDF r c) =
      ∑ p ∈ poles r, ENNReal.ofReal (c p) • gammaMeasure p.2 p.1 := by
  ext s hs
  unfold erlangMixturePDF
  rw [withDensity_apply _ hs, Measure.finsetSum_apply,
    lintegral_finsetSum _ fun p _ ↦ (measurable_gammaPDF _ _).const_mul _]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [lintegral_const_mul _ (measurable_gammaPDF _ _), Measure.smul_apply,
    gammaMeasure, withDensity_apply _ hs, smul_eq_mul]

private theorem isFiniteMeasure_withDensity_erlangMixturePDF (hr : ∀ i, 0 < r i)
    (c : (Σ _ : ℝ, ℕ) → ℝ) : IsFiniteMeasure (volume.withDensity (erlangMixturePDF r c)) := by
  refine isFiniteMeasure_withDensity ?_
  unfold erlangMixturePDF
  rw [lintegral_finsetSum _ fun p _ ↦ (measurable_gammaPDF _ _).const_mul _]
  refine (ENNReal.sum_lt_top.2 fun p hp ↦ ?_).ne
  obtain ⟨hρ, hk⟩ := pos_of_mem_poles hr hp
  rw [lintegral_const_mul _ (measurable_gammaPDF _ _),
    lintegral_gammaPDF_eq_one (Nat.cast_pos.2 hk) hρ, mul_one]
  exact ENNReal.ofReal_lt_top

private theorem charFun_withDensity_erlangMixturePDF (hr : ∀ i, 0 < r i)
    (c : (Σ _ : ℝ, ℕ) → ℝ) (t : ℝ) :
    charFun (volume.withDensity (erlangMixturePDF r c)) t =
      ∑ p ∈ poles r, ((max (c p) 0 : ℝ) : ℂ) * charFun (gammaMeasure p.2 p.1) t := by
  have hprob {p : Σ _ : ℝ, ℕ} (hp : p ∈ poles r) : IsProbabilityMeasure (gammaMeasure p.2 p.1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.2 (pos_of_mem_poles hr hp).2)
      (pos_of_mem_poles hr hp).1
  rw [withDensity_erlangMixturePDF, charFun_eq_integral_innerProbChar,
    integral_finsetSum_measure fun p hp ↦ (have := hprob hp;
      BoundedContinuousFunction.integrable _ _).smul_measure ENNReal.ofReal_ne_top]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal', charFun_eq_integral_innerProbChar,
    Complex.real_smul]

/-- The characteristic function of the hypoexponential law is the combination of the Erlang
characteristic functions with the weights `A ρ k / ρ ^ k`. -/
private theorem charFun_hypoexponentialMeasure_eq_sum [Nonempty ι] (hr : ∀ i, 0 < r i)
    (t : ℝ) : charFun (hypoexponentialMeasure r) t =
      ∑ p ∈ poles r, (weight r p : ℂ) * charFun (gammaMeasure p.2 p.1) t := by
  have hz (i : ι) : -(Complex.I * t) + algebraMap ℝ ℂ (r i) ≠ 0 := by
    rw [Complex.coe_algebraMap, neg_add_eq_sub]
    exact Complex.ne_zero_of_re_pos (by simpa using hr i)
  have h := prod_div_add_eq_sum_hypoexponentialCoeff r hz
  simp only [Complex.coe_algebraMap, neg_add_eq_sub] at h
  rw [charFun_hypoexponentialMeasure hr, h, sum_sigma]
  refine sum_congr rfl fun ρ hρ ↦ sum_congr rfl fun k hk ↦ ?_
  obtain ⟨hρ, hk⟩ := pos_of_mem_poles hr (mem_sigma.2 ⟨hρ, hk⟩ : ⟨ρ, k⟩ ∈ poles r)
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hsub : (ρ : ℂ) - Complex.I * t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using hρ)
  rw [charFun_gammaMeasure (Nat.cast_pos.2 hk) hρ, Complex.ofReal_natCast, Complex.cpow_neg,
    Complex.cpow_natCast, Complex.ofReal_div, Complex.ofReal_pow]
  -- Normalize the denominator before taking its natural power.
  have hdenom_normalize :
      (1 : ℂ) - Complex.I * t / ρ = (ρ - Complex.I * t) / ρ := by
    field_simp
  rw [hdenom_normalize, div_pow]
  field_simp

/-- Adding the negative part of the Erlang expansion to the hypoexponential law gives its positive
part. -/
private theorem hypoexponentialMeasure_add_eq [Nonempty ι] (hr : ∀ i, 0 < r i) :
    hypoexponentialMeasure r + volume.withDensity (erlangMixturePDF r fun p ↦ -weight r p) =
      volume.withDensity (erlangMixturePDF r (weight r)) := by
  have := isProbabilityMeasure_hypoexponentialMeasure hr
  have := isFiniteMeasure_withDensity_erlangMixturePDF hr fun p ↦ -weight r p
  have := isFiniteMeasure_withDensity_erlangMixturePDF hr (weight r)
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [charFun_eq_integral_innerProbChar, integral_add_measure
    (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _),
    ← charFun_eq_integral_innerProbChar,
    ← charFun_eq_integral_innerProbChar, charFun_withDensity_erlangMixturePDF hr,
    charFun_withDensity_erlangMixturePDF hr, charFun_hypoexponentialMeasure_eq_sum hr,
    ← sum_add_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [← add_mul, ← Complex.ofReal_add]
  have := max_zero_sub_max_neg_zero_eq_self (weight r p)
  congr 2
  linarith

/-- The real Erlang expansion `∑ (A ρ k / ρ ^ k) * gammaPDFReal k ρ`, which may a priori take
negative values. -/
private abbrev erlangExpansion (r : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ poles r, weight r p * gammaPDFReal p.2 p.1 x

private theorem toReal_erlangMixturePDF (hr : ∀ i, 0 < r i) (c : (Σ _ : ℝ, ℕ) → ℝ) (x : ℝ) :
    (erlangMixturePDF r c x).toReal = ∑ p ∈ poles r, max (c p) 0 * gammaPDFReal p.2 p.1 x := by
  unfold erlangMixturePDF
  rw [ENNReal.toReal_sum fun p _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by simp [gammaPDF])]
  refine sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hρ, hk⟩ := pos_of_mem_poles hr hp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', gammaPDF,
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg (Nat.cast_pos.2 hk) hρ x)]

/-- The Radon--Nikodym derivative of the hypoexponential law is the Erlang expansion, which is
therefore almost everywhere nonnegative. -/
private theorem ae_rnDeriv_hypoexponentialMeasure [Nonempty ι] (hr : ∀ i, 0 < r i) :
    ∀ᵐ x, (hypoexponentialMeasure r).rnDeriv volume x = ENNReal.ofReal (erlangExpansion r x) ∧
      0 ≤ erlangExpansion r x := by
  have := isProbabilityMeasure_hypoexponentialMeasure hr
  set μ := hypoexponentialMeasure r
  have hfin := isFiniteMeasure_withDensity_erlangMixturePDF hr fun p ↦ -weight r p
  have hD := Measure.measurable_rnDeriv μ volume
  have heq : volume.withDensity (μ.rnDeriv volume + erlangMixturePDF r fun p ↦ -weight r p) =
      volume.withDensity (erlangMixturePDF r (weight r)) := by
    rw [withDensity_add_left hD,
      Measure.withDensity_rnDeriv_eq _ _ (hypoexponentialMeasure_absolutelyContinuous r),
      hypoexponentialMeasure_add_eq hr]
  have hlt : ∫⁻ x, (μ.rnDeriv volume + erlangMixturePDF r fun p ↦ -weight r p) x ≠ ∞ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, heq]
    exact (isFiniteMeasure_withDensity_erlangMixturePDF hr (weight r)).measure_univ_lt_top.ne
  filter_upwards [(withDensity_eq_iff (hD.add (measurable_erlangMixturePDF r _)).aemeasurable
    (measurable_erlangMixturePDF r _).aemeasurable hlt).1 heq] with x hx
  have hfinite (c : (Σ _ : ℝ, ℕ) → ℝ) : erlangMixturePDF r c x ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun p _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [gammaPDF])
  rw [Pi.add_apply] at hx
  have hDx : μ.rnDeriv volume x ≠ ∞ := fun h ↦ hfinite (weight r) (by rw [← hx, h, top_add])
  have hreal : (μ.rnDeriv volume x).toReal = erlangExpansion r x := by
    have := congrArg ENNReal.toReal hx
    rw [ENNReal.toReal_add hDx (hfinite _), toReal_erlangMixturePDF hr,
      toReal_erlangMixturePDF hr] at this
    rw [eq_sub_of_add_eq this, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  exact ⟨by rw [← hreal, ENNReal.ofReal_toReal hDx], hreal ▸ ENNReal.toReal_nonneg⟩

private theorem hypoexponentialPDFReal_ae_eq_erlangExpansion (hr : ∀ i, 0 < r i) :
    hypoexponentialPDFReal r =ᵐ[volume] erlangExpansion r := by
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  rcases hx.lt_or_gt with hx | hx
  · rw [hypoexponentialPDFReal_of_nonpos r hx.le]
    exact (sum_eq_zero fun p _ ↦ by simp [gammaPDFReal, hx.not_ge]).symm
  · rw [hypoexponentialPDFReal_eq_sum_gammaPDFReal hr hx]
    unfold erlangExpansion poles
    rw [sum_sigma]

/-- A nonempty hypoexponential law with positive rates has density `hypoexponentialPDF r`. -/
theorem hypoexponentialMeasure_eq_withDensity [Nonempty ι] (hr : ∀ i, 0 < r i) :
    hypoexponentialMeasure r = volume.withDensity (hypoexponentialPDF r) := by
  have := isProbabilityMeasure_hypoexponentialMeasure hr
  rw [← Measure.withDensity_rnDeriv_eq _ _ (hypoexponentialMeasure_absolutelyContinuous r)]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_rnDeriv_hypoexponentialMeasure hr,
    hypoexponentialPDFReal_ae_eq_erlangExpansion hr] with x hx hpdf
  rw [hx.1, hypoexponentialPDF, hpdf]

/-- The principal-part formula for the density, as a function on all of `ℝ`. -/
private abbrev principalPartSum (r : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ ρ ∈ univ.image r, ∑ k ∈ Icc 1 #{i | r i = ρ},
    hypoexponentialCoeff r ρ k * x ^ (k - 1) * exp (-(ρ * x)) / (k - 1)!

/-- The hypoexponential density is nonnegative, for all rates and at every point. -/
theorem hypoexponentialPDFReal_nonneg (r : ι → ℝ) (x : ℝ) : 0 ≤ hypoexponentialPDFReal r x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  by_cases hr : ∀ i, 0 < r i
  swap
  · simp [hr]
  rcases le_or_gt x 0 with hx | hx
  · simp [hx]
  rw [hypoexponentialPDFReal_of_pos hr hx]
  -- The open set where the continuous formula is negative on `(0, ∞)` is Lebesgue-null.
  have hopen : IsOpen (Set.Ioi 0 ∩ principalPartSum r ⁻¹' Set.Iio 0) :=
    isOpen_Ioi.inter (isOpen_Iio.preimage (by fun_prop))
  have hnull : volume (Set.Ioi 0 ∩ principalPartSum r ⁻¹' Set.Iio 0) = 0 := by
    refine measure_mono_null (fun y hy ↦ ?_) (ae_iff.1 ((ae_rnDeriv_hypoexponentialMeasure hr).and
      (hypoexponentialPDFReal_ae_eq_erlangExpansion hr) |>.mono fun y hy ↦ hy.2 ▸ hy.1.2))
    rw [Set.mem_ofPred_eq, not_le, hypoexponentialPDFReal_of_pos hr hy.1]
    exact hy.2
  have hempty := (hopen.measure_eq_zero_iff volume).1 hnull
  exact not_lt.1 fun h ↦ hempty.subset ⟨hx, h⟩

/-- Coercing the extended density back to the reals recovers the real density. -/
@[simp]
theorem toReal_hypoexponentialPDF (r : ι → ℝ) (x : ℝ) :
    (hypoexponentialPDF r x).toReal = hypoexponentialPDFReal r x :=
  ENNReal.toReal_ofReal (hypoexponentialPDFReal_nonneg r x)

/-- The extended density of a nonempty valid hypoexponential law integrates to one. -/
@[simp]
theorem lintegral_hypoexponentialPDF_eq_one [Nonempty ι] (hr : ∀ i, 0 < r i) :
    ∫⁻ x, hypoexponentialPDF r x = 1 := by
  have := isProbabilityMeasure_hypoexponentialMeasure hr
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← hypoexponentialMeasure_eq_withDensity hr, measure_univ]

/-- The real density of a nonempty valid hypoexponential law integrates to one. -/
@[simp]
theorem integral_hypoexponentialPDFReal_eq_one [Nonempty ι] (hr : ∀ i, 0 < r i) :
    ∫ x, hypoexponentialPDFReal r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hypoexponentialPDFReal_nonneg r))
    (measurable_hypoexponentialPDFReal r).aestronglyMeasurable]
  simp [← hypoexponentialPDF_eq_ofReal, lintegral_hypoexponentialPDF_eq_one hr]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a nonempty valid hypoexponential law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_hypoexponentialMeasure [Nonempty ι] (hr : ∀ i, 0 < r i)
    (hX : HasLaw X (hypoexponentialMeasure r) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_hypoexponentialPDF r).aemeasurable
    (by rwa [hypoexponentialMeasure_eq_withDensity hr] at hX)

/-- The density of a variable with a nonempty valid hypoexponential law is
`hypoexponentialPDF r`. -/
theorem pdf_eq_hypoexponentialPDF_of_hasLaw_hypoexponentialMeasure [Nonempty ι]
    (hr : ∀ i, 0 < r i) (hX : HasLaw X (hypoexponentialMeasure r) P) :
    pdf X P =ᵐ[volume] hypoexponentialPDF r :=
  pdf_eq_of_hasLaw_withDensity (measurable_hypoexponentialPDF r).aemeasurable
    (by rwa [hypoexponentialMeasure_eq_withDensity hr] at hX)

/-- The Radon--Nikodym derivative of a nonempty valid hypoexponential law is
`hypoexponentialPDF r`. -/
theorem rnDeriv_hypoexponentialMeasure [Nonempty ι] (hr : ∀ i, 0 < r i) :
    (hypoexponentialMeasure r).rnDeriv volume =ᵐ[volume] hypoexponentialPDF r := by
  rw [hypoexponentialMeasure_eq_withDensity hr]
  exact Measure.rnDeriv_withDensity volume (measurable_hypoexponentialPDF r)

end Law

/-! ### Distinct and equal rates -/

/-- **Distinct rates.** For pairwise distinct positive rates, the density at `x > 0` is
`∑ i, r i * exp (-(r i * x)) * ∏ j ≠ i, r j / (r j - r i)`. -/
theorem hypoexponentialPDFReal_of_injective [DecidableEq ι] (hr : ∀ i, 0 < r i)
    (hinj : Function.Injective r) (hx : 0 < x) :
    hypoexponentialPDFReal r x =
      ∑ i, r i * exp (-(r i * x)) * ∏ j ∈ univ.erase i, r j / (r j - r i) := by
  rw [hypoexponentialPDFReal_of_pos hr hx, sum_image fun i _ j _ h ↦ hinj h]
  refine sum_congr rfl fun i _ ↦ ?_
  have hfilter : ({j | r j = r i} : Finset ι) = {i} := by
    ext j
    simp [hinj.eq_iff]
  have hne : ({j | r j ≠ r i} : Finset ι) = univ.erase i := by
    ext j
    simp [hinj.ne_iff]
  have hA := hypoexponentialCoeff_card r (r i)
  rw [hfilter, card_singleton, hne] at hA
  rw [hfilter, card_singleton, Icc_self, sum_singleton, hA,
    ← mul_prod_erase univ r (mem_univ i), prod_div_distrib]
  simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  ring

/-- **Equal rates.** With a common positive rate `ρ`, the density of a nonempty family away from
zero is the Erlang density of shape `Fintype.card ι` and rate `ρ`. -/
theorem hypoexponentialPDFReal_const [Nonempty ι] {ρ : ℝ} (hρ : 0 < ρ) (hx : x ≠ 0) :
    hypoexponentialPDFReal (fun _ : ι ↦ ρ) x = gammaPDFReal (Fintype.card ι) ρ x := by
  rcases hx.lt_or_gt with hx | hx
  · rw [hypoexponentialPDFReal_of_nonpos _ hx.le, gammaPDFReal, ite_eq_right hx.not_ge]
  have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hcard : #{i : ι | ρ = ρ} = Fintype.card ι := by simp
  rw [hypoexponentialPDFReal_eq_sum_gammaPDFReal (fun _ ↦ hρ) hx, image_const univ_nonempty,
    sum_singleton, hcard, sum_eq_single_of_mem _ (right_mem_Icc.2 hn)]
  · rw [← hcard, hypoexponentialCoeff_card, hcard]
    simp [(pow_pos hρ _).ne']
  · intro k hk hkn
    have : Fintype.card ι - k ≠ 0 := by have := (mem_Icc.1 hk).2; omega
    simp [hypoexponentialCoeff_def, iteratedDeriv_const, this]

end TauCeti.Probability
