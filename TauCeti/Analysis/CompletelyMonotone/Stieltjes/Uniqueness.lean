/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompleteBernstein
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation

/-!
# Uniqueness of the Stieltjes and complete Bernstein representations

A Stieltjes function determines the data representing it: if

`f t = a / t + b + ∫ (t + x)⁻¹ dμ(x)` for all `t > 0`

with `a, b ≥ 0` and `μ` a measure on `ℝ≥0` without an atom at the origin whose standard weight
`x ↦ (1 + x)⁻¹` is integrable, then `a`, `b` and `μ` are uniquely determined by `f`.  This is the
uniqueness half of the Stieltjes representation, and it transfers verbatim to complete Bernstein
functions through `TauCeti.RepresentsCompleteBernstein.representsStieltjes_div`.

The three pieces of data are separated one at a time.

* The coefficient `b` is the limit of `f` at `+∞`, because the Stieltjes integral vanishes there
  (`TauCeti.tendsto_integral_inv_add_atTop_nhds_zero`) and so does `a / t`.
* The singular coefficient `a` is the mass that the measure `a • δ₀ + μ` puts at the origin, since
  `a / t` is exactly the Stieltjes integral of `a • δ₀`.  So once `b` is known, the whole
  representation is the Stieltjes transform of a single measure, and it remains to show that a
  measure is determined by its Stieltjes transform.
* That determinacy (`TauCeti.Measure.ext_of_forall_integral_inv_add_eq`) reduces to Laplace
  determinacy for finite measures.  Differentiating the Stieltjes transform `n` times at `t = 1`
  (`TauCeti.iteratedDeriv_integral_inv_add`) recovers the numbers `∫ (1 + x)^{-1-n} dμ`, which are
  the values at the natural numbers of the Laplace transform of the finite measure obtained by
  weighting `μ` with `(1 + x)⁻¹` and pushing it forward along `x ↦ log (1 + x)`.  A finite measure
  on `ℝ≥0` is determined by those values
  (`TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`), and both the pushforward and the
  weighting are invertible.

## Main declarations

* `TauCeti.tendsto_integral_inv_add_atTop_nhds_zero`: a Stieltjes transform vanishes at `+∞`.
* `TauCeti.Measure.ext_of_forall_integral_inv_add_eq`: **a measure on `ℝ≥0` with integrable
  Stieltjes weight is determined by its Stieltjes transform.**
* `TauCeti.RepresentsStieltjes.unique` and
  `TauCeti.IsStieltjesFunction.existsUnique_representsStieltjes`: **uniqueness of the Stieltjes
  representation.**
* `TauCeti.RepresentsCompleteBernstein.unique` and
  `TauCeti.IsCompleteBernsteinFunction.existsUnique_representsCompleteBernstein`: uniqueness of
  the complete Bernstein representation.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 2.2 and Theorem 6.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {μ ν : Measure ℝ≥0}

/-! ## The Stieltjes transform at infinity -/

/-- **A Stieltjes transform vanishes at infinity.** The integrand `(t + x)⁻¹` is dominated by the
standard Stieltjes weight once `t ≥ 1`, and tends to `0` pointwise. -/
theorem tendsto_integral_inv_add_atTop_nhds_zero (hμ : Integrable stieltjesWeight μ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ) atTop (𝓝 0) := by
  have hzero : (0 : ℝ) = ∫ _x : ℝ≥0, (0 : ℝ) ∂μ := by simp
  rw [hzero]
  refine tendsto_integral_filter_of_dominated_convergence stieltjesWeight ?_ ?_ hμ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (integrable_inv_add hμ ht).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    filter_upwards with x
    have hx : (0 : ℝ) ≤ (x : ℝ) := x.coe_nonneg
    have h1x : (0 : ℝ) < 1 + (x : ℝ) := by positivity
    have htx : (0 : ℝ) < t + (x : ℝ) := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htx), stieltjesWeight_apply]
    exact (inv_le_inv₀ htx h1x).2 (by linarith)
  · filter_upwards with x
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (x : ℝ) tendsto_id)

/-! ## Determinacy of a measure by its Stieltjes transform

The Stieltjes weight is turned into an exponential by the substitution `y = log (1 + x)`, whose
inverse is `x = exp y - 1`; both are recorded as self-maps of `ℝ≥0`, so that the transported
measure is again a measure on `ℝ≥0`.
-/

/-- The substitution `x ↦ log (1 + x)`, as a self-map of `ℝ≥0`. -/
private def logAddOne (x : ℝ≥0) : ℝ≥0 := Real.toNNReal (Real.log (1 + (x : ℝ)))

/-- The inverse substitution `y ↦ exp y - 1`, as a self-map of `ℝ≥0`. -/
private def expSubOne (y : ℝ≥0) : ℝ≥0 := Real.toNNReal (Real.exp (y : ℝ) - 1)

private lemma coe_logAddOne (x : ℝ≥0) : (logAddOne x : ℝ) = Real.log (1 + (x : ℝ)) :=
  Real.coe_toNNReal _ (Real.log_nonneg (by simp))

private lemma measurable_logAddOne : Measurable logAddOne := by
  unfold logAddOne; fun_prop

private lemma measurable_expSubOne : Measurable expSubOne := by
  unfold expSubOne; fun_prop

private lemma expSubOne_logAddOne (x : ℝ≥0) : expSubOne (logAddOne x) = x := by
  have h1x : (0 : ℝ) < 1 + (x : ℝ) := by positivity
  have hx : Real.exp ((logAddOne x : ℝ)) - 1 = (x : ℝ) := by
    rw [coe_logAddOne, Real.exp_log h1x]; ring
  rw [expSubOne, hx, Real.toNNReal_coe]

/-- The density turning a measure with integrable Stieltjes weight into a finite measure. -/
private def weightDensity (x : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (1 + (x : ℝ))⁻¹

/-- The density undoing `TauCeti.weightDensity`. -/
private def weightDensityInv (x : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (1 + (x : ℝ))

private lemma weightDensity_apply (x : ℝ≥0) :
    weightDensity x = ENNReal.ofReal (1 + (x : ℝ))⁻¹ :=
  (rfl)

private lemma weightDensityInv_apply (x : ℝ≥0) :
    weightDensityInv x = ENNReal.ofReal (1 + (x : ℝ)) :=
  (rfl)

private lemma measurable_weightDensity : Measurable weightDensity := by
  unfold weightDensity; fun_prop

private lemma measurable_weightDensityInv : Measurable weightDensityInv := by
  unfold weightDensityInv; fun_prop

private lemma weightDensity_mul_weightDensityInv : weightDensity * weightDensityInv = 1 := by
  funext x
  have h1x : (0 : ℝ) < 1 + (x : ℝ) := by positivity
  rw [Pi.mul_apply, weightDensity_apply, weightDensityInv_apply,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr h1x.le), inv_mul_cancel₀ h1x.ne',
    ENNReal.ofReal_one, Pi.one_apply]

/-- Weighting by `TauCeti.weightDensity` is undone by weighting by
`TauCeti.weightDensityInv`. -/
private lemma withDensity_weightDensity_weightDensityInv (m : Measure ℝ≥0) :
    (m.withDensity weightDensity).withDensity weightDensityInv = m := by
  rw [← withDensity_mul _ measurable_weightDensity measurable_weightDensityInv,
    weightDensity_mul_weightDensityInv, withDensity_one]

private lemma isFiniteMeasure_withDensity_weightDensity (hμ : Integrable stieltjesWeight μ) :
    IsFiniteMeasure (μ.withDensity weightDensity) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hnn : 0 ≤ᵐ[μ] stieltjesWeight :=
    .of_forall fun x => by rw [stieltjesWeight_apply]; positivity
  simpa only [weightDensity_apply, stieltjesWeight_apply] using
    (hasFiniteIntegral_iff_ofReal hnn).1 hμ.2

/-- The Laplace transform at a natural number of the measure obtained from `μ` by weighting with
the Stieltjes weight and substituting `y = log (1 + x)` is the Stieltjes moment
`∫ (1 + x)^{-1-n} dμ`. -/
private lemma laplaceTransform_map_logAddOne_withDensity (n : ℕ) :
    laplaceTransform ((μ.withDensity weightDensity).map logAddOne) (n : ℝ)
      = ∫ x : ℝ≥0, (1 + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ := by
  have hlt : ∀ᵐ x ∂μ, weightDensity x < ∞ :=
    .of_forall fun x => by rw [weightDensity_apply]; exact ENNReal.ofReal_lt_top
  rw [laplaceTransform_apply, integral_map measurable_logAddOne.aemeasurable (by fun_prop),
    integral_withDensity_eq_integral_toReal_smul measurable_weightDensity hlt]
  refine integral_congr_ae (.of_forall fun x => ?_)
  dsimp only
  have h1x : (0 : ℝ) < 1 + (x : ℝ) := by positivity
  have hexp : Real.exp (-((n : ℝ) * (logAddOne x : ℝ))) = (1 + (x : ℝ)) ^ (-(n : ℤ)) := by
    rw [coe_logAddOne, ← Real.rpow_intCast, Real.rpow_def_of_pos h1x]
    push_cast
    congr 1
    ring
  have hsplit : (-1 : ℤ) - (n : ℤ) = -1 + -(n : ℤ) := by ring
  rw [weightDensity_apply, smul_eq_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr h1x.le), hexp,
    hsplit, zpow_add₀ h1x.ne', zpow_neg_one]

/-- **A measure on `ℝ≥0` whose Stieltjes weight is integrable is determined by its Stieltjes
transform.** -/
theorem Measure.ext_of_forall_integral_inv_add_eq (hμ : Integrable stieltjesWeight μ)
    (hν : Integrable stieltjesWeight ν)
    (h : ∀ t : ℝ, 0 < t → ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ = ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂ν) :
    μ = ν := by
  -- Differentiating at `t = 1` turns the transform into the Stieltjes moments.
  have hmoment : ∀ n : ℕ, ∫ x : ℝ≥0, (1 + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ
      = ∫ x : ℝ≥0, (1 + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂ν := by
    intro n
    have hev : (fun u : ℝ => ∫ x : ℝ≥0, (u + (x : ℝ))⁻¹ ∂μ) =ᶠ[𝓝 (1 : ℝ)]
        fun u : ℝ => ∫ x : ℝ≥0, (u + (x : ℝ))⁻¹ ∂ν := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with u hu
      exact h u hu
    have hderiv := hev.iteratedDeriv_eq n
    rw [iteratedDeriv_integral_inv_add hμ n one_pos,
      iteratedDeriv_integral_inv_add hν n one_pos] at hderiv
    have hne : ((-1 : ℝ) ^ n * n.factorial) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.2 n.factorial_ne_zero)
    exact mul_left_cancel₀ hne hderiv
  -- Laplace determinacy for the transported finite measures.
  have _ := isFiniteMeasure_withDensity_weightDensity hμ
  have _ := isFiniteMeasure_withDensity_weightDensity hν
  have hmap : (μ.withDensity weightDensity).map logAddOne
      = (ν.withDensity weightDensity).map logAddOne :=
    TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq fun n => by
      rw [laplaceTransform_map_logAddOne_withDensity n,
        laplaceTransform_map_logAddOne_withDensity n, hmoment n]
  -- Undo the substitution, then the weighting.
  have hdensity : μ.withDensity weightDensity = ν.withDensity weightDensity := by
    have hpush := congrArg (fun m : Measure ℝ≥0 => m.map expSubOne) hmap
    simpa only [Measure.map_map measurable_expSubOne measurable_logAddOne, Function.comp_def,
      expSubOne_logAddOne, Measure.map_id'] using hpush
  calc
    μ = (μ.withDensity weightDensity).withDensity weightDensityInv :=
        (withDensity_weightDensity_weightDensityInv μ).symm
    _ = (ν.withDensity weightDensity).withDensity weightDensityInv := by rw [hdensity]
    _ = ν := withDensity_weightDensity_weightDensityInv ν

/-! ## Uniqueness of the representing data

The singular coefficient is absorbed into the representing measure as an atom at the origin,
which turns a Stieltjes representation into an additive constant plus a single Stieltjes
transform.
-/

variable {a b c d : ℝ≥0} {f : ℝ → ℝ}

/-- The measure recording a Stieltjes representation as a single Stieltjes transform: the
singular coefficient `a` becomes an atom at the origin, where `x ↦ (t + x)⁻¹` takes the value
`t⁻¹`. -/
private def atomize (μ : Measure ℝ≥0) (a : ℝ≥0) : Measure ℝ≥0 :=
  (a : ℝ≥0∞) • Measure.dirac 0 + μ

private lemma integrable_weight_smul_dirac (a : ℝ≥0) :
    Integrable stieltjesWeight ((a : ℝ≥0∞) • Measure.dirac (0 : ℝ≥0)) :=
  (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top

private lemma integrable_weight_atomize (hμ : Integrable stieltjesWeight μ) (a : ℝ≥0) :
    Integrable stieltjesWeight (atomize μ a) :=
  (integrable_weight_smul_dirac a).add_measure hμ

private lemma integral_inv_add_atomize (hμ : Integrable stieltjesWeight μ) (a : ℝ≥0) {t : ℝ}
    (ht : 0 < t) :
    ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂(atomize μ a) = (a : ℝ) / t + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ := by
  rw [atomize,
    integral_add_measure (integrable_inv_add (integrable_weight_smul_dirac a) ht)
      (integrable_inv_add hμ ht),
    integral_smul_measure, integral_dirac]
  simp [div_eq_mul_inv]

private lemma atomize_singleton_zero (hμ : μ {0} = 0) (a : ℝ≥0) :
    atomize μ a {0} = (a : ℝ≥0∞) := by
  simp [atomize, hμ]

private lemma restrict_compl_atomize (hμ : μ {0} = 0) (a : ℝ≥0) :
    (atomize μ a).restrict {(0 : ℝ≥0)}ᶜ = μ := by
  have hdirac : ((a : ℝ≥0∞) • Measure.dirac (0 : ℝ≥0)).restrict {(0 : ℝ≥0)}ᶜ = 0 := by
    rw [Measure.restrict_eq_zero]
    simp [Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ≥0)).compl]
  rw [atomize, Measure.restrict_add, hdirac,
    Measure.restrict_eq_self_of_ae_mem (by simpa [ae_iff] using hμ), zero_add]

/-- **Uniqueness of the Stieltjes representation.** A Stieltjes function determines its singular
coefficient, its additive constant, and its representing measure. -/
protected theorem RepresentsStieltjes.unique (hf : RepresentsStieltjes μ a b f)
    (hg : RepresentsStieltjes ν c d f) :
    a = c ∧ b = d ∧ μ = ν := by
  have hM := integrable_weight_atomize hf.integrable_weight a
  have hN := integrable_weight_atomize hg.integrable_weight c
  -- The representation as an additive constant plus a single Stieltjes transform.
  have hval : ∀ t : ℝ, 0 < t → (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂(atomize μ a)
      = (d : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂(atomize ν c) := by
    intro t ht
    rw [integral_inv_add_atomize hf.integrable_weight a ht,
      integral_inv_add_atomize hg.integrable_weight c ht]
    have h₁ := hf.eq_div_add_add_integral_inv_add ht
    have h₂ := hg.eq_div_add_add_integral_inv_add ht
    linarith
  -- The additive constants are the common limit at `+∞`.
  have hbd : b = d := by
    have hlimb := (tendsto_integral_inv_add_atTop_nhds_zero hM).const_add (b : ℝ)
    have hlimd := (tendsto_integral_inv_add_atTop_nhds_zero hN).const_add (d : ℝ)
    have hcongr : (fun t : ℝ => (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂(atomize μ a))
        =ᶠ[atTop] fun t : ℝ => (d : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂(atomize ν c) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hval t ht
    have hlim := tendsto_nhds_unique (hlimb.congr' hcongr) hlimd
    exact NNReal.coe_injective (by simpa using hlim)
  -- With the constants equal, the two Stieltjes transforms agree, so the measures do.
  have hMN : atomize μ a = atomize ν c := by
    refine Measure.ext_of_forall_integral_inv_add_eq hM hN fun t ht => ?_
    have hv := hval t ht
    rw [hbd] at hv
    linarith
  refine ⟨?_, hbd, ?_⟩
  · have hzero := congrArg (fun m : Measure ℝ≥0 => m {0}) hMN
    rw [atomize_singleton_zero hf.measure_singleton_zero,
      atomize_singleton_zero hg.measure_singleton_zero] at hzero
    exact_mod_cast hzero
  · have hrest := congrArg (fun m : Measure ℝ≥0 => m.restrict {(0 : ℝ≥0)}ᶜ) hMN
    rwa [restrict_compl_atomize hf.measure_singleton_zero,
      restrict_compl_atomize hg.measure_singleton_zero] at hrest

/-- **Uniqueness of the complete Bernstein representation.** A complete Bernstein function
determines its two coefficients and its representing measure, because dividing by the parameter
turns it into a Stieltjes function with the same data. -/
protected theorem RepresentsCompleteBernstein.unique (hf : RepresentsCompleteBernstein μ a b f)
    (hg : RepresentsCompleteBernstein ν c d f) :
    a = c ∧ b = d ∧ μ = ν :=
  hf.representsStieltjes_div.unique hg.representsStieltjes_div

/-- **The Stieltjes representation theorem, uniqueness form.** A Stieltjes function has exactly
one representing triple `(a, b, μ)`. -/
theorem IsStieltjesFunction.existsUnique_representsStieltjes (hf : IsStieltjesFunction f) :
    ∃! p : ℝ≥0 × ℝ≥0 × Measure ℝ≥0, RepresentsStieltjes p.2.2 p.1 p.2.1 f := by
  obtain ⟨a, b, μ, hμ⟩ := isStieltjesFunction_iff.mp hf
  refine ⟨(a, b, μ), hμ, ?_⟩
  rintro ⟨c, d, ν⟩ hν
  obtain ⟨hac, hbd, hμν⟩ := hν.unique hμ
  simp only [Prod.mk.injEq]
  exact ⟨hac, hbd, hμν⟩

/-- **The complete Bernstein representation theorem, uniqueness form.** A complete Bernstein
function has exactly one representing triple `(a, b, μ)`. -/
theorem IsCompleteBernsteinFunction.existsUnique_representsCompleteBernstein
    (hf : IsCompleteBernsteinFunction f) :
    ∃! p : ℝ≥0 × ℝ≥0 × Measure ℝ≥0, RepresentsCompleteBernstein p.2.2 p.1 p.2.1 f := by
  obtain ⟨a, b, μ, hμ⟩ := isCompleteBernsteinFunction_iff.mp hf
  refine ⟨(a, b, μ), hμ, ?_⟩
  rintro ⟨c, d, ν⟩ hν
  obtain ⟨hac, hbd, hμν⟩ := hν.unique hμ
  simp only [Prod.mk.injEq]
  exact ⟨hac, hbd, hμν⟩

end TauCeti

end

end
