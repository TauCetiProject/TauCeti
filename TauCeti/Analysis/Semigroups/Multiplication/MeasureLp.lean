/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Calculus.ExponentialSlope
import TauCeti.Analysis.Semigroups.Resolvent.Identity
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Multiplication semigroups on measure-space Lᵖ

For an almost everywhere measurable nonnegative multiplier `m`, multiplication by `exp (-t * m)`
defines a strongly continuous contraction semigroup on `Lᵖ(μ; E)` for `1 ≤ p < ∞`, where `E`
is a real normed space. The measure is arbitrary and the multiplier may be unbounded. The action is
specified almost everywhere, as required for equivalence classes of measurable functions.

For `lambda > 0`, the Laplace resolvent is multiplication by the bounded almost everywhere
measurable function `a ↦ (lambda + m a)⁻¹`. Thus the abstract contraction estimate is realized by
the pointwise bound `(lambda + m a)⁻¹ ≤ lambda⁻¹`.

Strong continuity comes from dominated convergence in Lᵖ; the multiplier itself need not
belong to any Lᵖ space. This provides multiplication examples with continuous spatial variables,
including Lebesgue measure, in addition to the discrete ℓᵖ examples.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section I.4.c (multiplication semigroups).

The bounded operators use Mathlib's `ContinuousLinearMap.holderL` construction.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Semigroups

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def multiplicationWeight {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound (by fun_prop) 1 (.of_forall fun a => by
    simp only [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (by positivity))).toLp
    (fun a => Real.exp (-((t : ℝ) * m a)))

private theorem multiplicationWeight_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) :
    multiplicationWeight (μ := μ) hm t =ᵐ[μ] fun a => Real.exp (-((t : ℝ) * m a)) :=
  MemLp.coeFn_toLp _

private def measureLpMultiplicationOperator {m : α → ℝ≥0} (hm : AEMeasurable m μ) (t : ℝ≥0) :
    Lp E p μ →L[ℝ] Lp E p μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ p p (multiplicationWeight hm t)

private theorem measureLpMultiplicationOperator_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (t : ℝ≥0) (f : Lp E p μ) :
    measureLpMultiplicationOperator hm t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) • f a := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder
    (r := p) (multiplicationWeight hm t) f, multiplicationWeight_ae hm t] with a ha hw
  simpa only [measureLpMultiplicationOperator, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.lsmul_apply, hw] using ha

private theorem measureLpMultiplicationOperator_norm_le {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (t : ℝ≥0) : ‖measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm t) zero_le_one ?_
  intro f
  rw [one_mul]
  refine Lp.norm_le_norm_of_ae_le (f := measureLpMultiplicationOperator hm t f) (g := f) ?_
  filter_upwards [measureLpMultiplicationOperator_ae hm t f] with a ha
  rw [ha, norm_smul, Real.norm_eq_abs, Real.abs_exp]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))

private theorem measureLpMultiplicationOperator_zero {m : α → ℝ≥0} (hm : AEMeasurable m μ) :
    measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm 0 =
      ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [measureLpMultiplicationOperator_ae hm 0 f] with a ha
  simpa using ha

private theorem measureLpMultiplicationOperator_add {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (s t : ℝ≥0) :
    measureLpMultiplicationOperator (E := E) (p := p) (μ := μ) hm (s + t) =
      (measureLpMultiplicationOperator hm s).comp (measureLpMultiplicationOperator hm t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [measureLpMultiplicationOperator_ae hm (s + t) f,
    measureLpMultiplicationOperator_ae hm s (measureLpMultiplicationOperator hm t f),
    measureLpMultiplicationOperator_ae hm t f] with a hst hs ht
  simp only [ContinuousLinearMap.comp_apply, hst, hs, ht, NNReal.coe_add, smul_smul]
  rw [← Real.exp_add]
  congr 2
  ring

private theorem measureLpMultiplicationOperator_continuous {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous (fun t : ℝ≥0 => measureLpMultiplicationOperator hm t f) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (measureLpMultiplicationOperator hm s f)).2
  have hlim : Tendsto
      (fun t : ℝ≥0 => eLpNorm
        ((fun a => Real.exp (-((t : ℝ) * m a)) • f a) -
          (fun a => Real.exp (-((s : ℝ) * m a)) • f a)) p μ) (𝓝 s) (𝓝 0) := by
    apply TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
      (.of_forall fun t => by fun_prop) (by fun_prop) (Lp.memLp f) (C := 2)
    · filter_upwards with t
      filter_upwards with a
      have hbound (u : ℝ≥0) : ‖Real.exp (-((u : ℝ) * m a)) • f a‖ₑ ≤ ‖f a‖ₑ := by
        rw [enorm_smul]
        apply mul_le_of_le_one_left zero_le
        rw [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_le_coe]
        apply NNReal.coe_le_coe.mp
        simp only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs, Real.abs_exp,
          Real.exp_le_one_iff]
        exact neg_nonpos.mpr (by positivity)
      calc
        ‖Real.exp (-((t : ℝ) * m a)) • f a - Real.exp (-((s : ℝ) * m a)) • f a‖ₑ
            ≤ ‖Real.exp (-((t : ℝ) * m a)) • f a‖ₑ +
              ‖Real.exp (-((s : ℝ) * m a)) • f a‖ₑ := enorm_sub_le
        _ ≤ ‖f a‖ₑ + ‖f a‖ₑ := add_le_add (hbound t) (hbound s)
        _ = (2 : ℝ≥0) * ‖f a‖ₑ := by simp [two_mul]
    · filter_upwards with a
      have hcont : Continuous (fun t : ℝ≥0 => Real.exp (-((t : ℝ) * m a)) • f a) := by
        fun_prop
      exact hcont.tendsto s
  refine hlim.congr fun t => ?_
  apply eLpNorm_congr_ae
  exact ((measureLpMultiplicationOperator_ae hm t f).sub
    (measureLpMultiplicationOperator_ae hm s f)).symm

/-- The multiplication contraction semigroup on measure-space Lᵖ, for `1 ≤ p < ∞`.
The nonnegative almost everywhere measurable multiplier need not be bounded, and the measure
is arbitrary. -/
def ContractionSemigroup.ofMeasureLpMultiplication {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) : ContractionSemigroup (Lp E p μ) where
  toFun := measureLpMultiplicationOperator hm
  map_zero' := measureLpMultiplicationOperator_zero hm
  map_add' := measureLpMultiplicationOperator_add hm
  continuousAt_zero' := fun f => (measureLpMultiplicationOperator_continuous hm hp f).continuousAt
  contracting := measureLpMultiplicationOperator_norm_le hm

/-- The multiplication semigroup acts by `exp (-t * m)` almost everywhere. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_apply_apply_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (t : ℝ≥0) (f : Lp E p μ) :
    ofMeasureLpMultiplication hm hp t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) • f a :=
  measureLpMultiplicationOperator_ae hm t f

/-- Multiplication semigroup orbits are continuous even when the value space is incomplete. -/
@[fun_prop]
theorem ContractionSemigroup.continuous_ofMeasureLpMultiplication {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous (fun t : ℝ≥0 => ofMeasureLpMultiplication hm hp t f) :=
  measureLpMultiplicationOperator_continuous hm hp f

/-- Almost everywhere equal multipliers define the same multiplication semigroup. -/
theorem ContractionSemigroup.ofMeasureLpMultiplication_congr_ae {m n : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) (h : m =ᵐ[μ] n) :
    ofMeasureLpMultiplication (E := E) hm hp = ofMeasureLpMultiplication (hm.congr h) hp := by
  apply ContractionSemigroup.ext
  intro t
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [ofMeasureLpMultiplication_apply_apply_ae hm hp t f,
    ofMeasureLpMultiplication_apply_apply_ae (hm.congr h) hp t f, h] with a hm hn hmn
  rw [hm, hn, hmn]

private theorem ofMeasureLpMultiplication_realOperator_apply_ae {m : α → ℝ≥0}
    (hm : AEMeasurable m μ) (hp : p ≠ ∞) {t : ℝ} (ht : 0 ≤ t) (f : Lp E p μ) :
    (ContractionSemigroup.ofMeasureLpMultiplication hm hp).realOperator t f =ᵐ[μ]
      fun a => Real.exp (-(t * m a)) • f a := by
  filter_upwards [ContractionSemigroup.ofMeasureLpMultiplication_apply_apply_ae
    hm hp t.toNNReal f] with a ha
  rw [StronglyContinuousSemigroup.realOperator_def,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply, ha, Real.coe_toNNReal t ht]

private def measureLpResolventWeight {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (lambda : ℝ) (hlambda : 0 < lambda) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound (by fun_prop) lambda⁻¹ (.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
    exact (inv_le_inv₀ (by positivity) hlambda).2 (by linarith [(m a).coe_nonneg]))).toLp
    (fun a => (lambda + (m a : ℝ))⁻¹)

private theorem measureLpResolventWeight_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    measureLpResolventWeight hm lambda hlambda =ᵐ[μ] fun a => (lambda + (m a : ℝ))⁻¹ :=
  MemLp.coeFn_toLp _

private def measureLpResolventOperator {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (lambda : ℝ) (hlambda : 0 < lambda) : Lp E p μ →L[ℝ] Lp E p μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ p p
    (measureLpResolventWeight hm lambda hlambda)

private theorem measureLpResolventOperator_ae {m : α → ℝ≥0} (hm : AEMeasurable m μ)
    (lambda : ℝ) (hlambda : 0 < lambda) (f : Lp E p μ) :
    measureLpResolventOperator hm lambda hlambda f =ᵐ[μ]
      fun a => (lambda + (m a : ℝ))⁻¹ • f a := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder
    (r := p) (measureLpResolventWeight hm lambda hlambda) f,
    measureLpResolventWeight_ae hm lambda hlambda] with a ha hw
  simpa only [measureLpResolventOperator, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.lsmul_apply, hw] using ha

private theorem tendsto_measureLpResolventGeneratorScalar (c : ℝ≥0) (lambda : ℝ) :
    Tendsto
      (fun t : ℝ => (1 / t) * (Real.exp (-(t * c)) - 1) * (lambda + c)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(c : ℝ) * (lambda + c)⁻¹)) := by
  have h := (TauCeti.tendsto_exp_mul_sub_one_div (-(c : ℝ))).mul_const
    (lambda + c)⁻¹
  convert h using 1
  funext t
  have harg : -(t * (c : ℝ)) = -(c : ℝ) * t := by ring
  rw [harg]
  ring

private theorem abs_measureLpResolventGeneratorScalar_le_one (c : ℝ≥0) {lambda t : ℝ}
    (hlambda : 0 < lambda) (ht : 0 < t) :
    |(1 / t) * (Real.exp (-(t * c)) - 1) * (lambda + c)⁻¹| ≤ 1 := by
  have htc : 0 ≤ t * (c : ℝ) := mul_nonneg ht.le c.coe_nonneg
  have hexp : Real.exp (-(t * c)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr htc)
  have hsub : 1 - Real.exp (-(t * c)) ≤ t * c := by
    linarith [Real.one_sub_le_exp_neg (t * (c : ℝ))]
  have hslope : |(1 / t) * (Real.exp (-(t * c)) - 1)| ≤ c := by
    rw [abs_of_nonpos]
    · calc
        -(1 / t * (Real.exp (-(t * c)) - 1)) =
            (1 - Real.exp (-(t * c))) / t := by ring
        _ ≤ c := (div_le_iff₀ ht).2 (by simpa only [mul_comm] using hsub)
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hexp)
  have hden : 0 < lambda + (c : ℝ) := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr hden)]
  calc
    |(1 / t) * (Real.exp (-(t * c)) - 1)| * (lambda + c)⁻¹
        ≤ c * (lambda + c)⁻¹ :=
      mul_le_mul_of_nonneg_right hslope (inv_nonneg.mpr (by positivity))
    _ ≤ 1 := (mul_inv_le_iff₀ (by positivity)).2 (by linarith)

private theorem abs_neg_mul_add_inv_le_one (c : ℝ≥0) {lambda : ℝ}
    (hlambda : 0 < lambda) : |-(c : ℝ) * (lambda + c)⁻¹| ≤ 1 := by
  rw [abs_mul, abs_neg, abs_of_nonneg c.coe_nonneg,
    abs_of_pos (inv_pos.mpr (by positivity))]
  exact (mul_inv_le_iff₀ (by positivity)).2 (by linarith)

private theorem measureLpResolventOperator_mem_domain_generator_ae
    {m : α → ℝ≥0} (hm : AEMeasurable m μ) (hp : p ≠ ∞) {lambda : ℝ}
    (hlambda : 0 < lambda) (f : Lp E p μ) :
    let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
    let g := measureLpResolventOperator hm lambda hlambda f
    ∃ hg : g ∈ S.domain,
      S.generator ⟨g, by rw [StronglyContinuousSemigroup.generator_domain]; exact hg⟩ =ᵐ[μ]
        fun a => (-(m a : ℝ) * (lambda + (m a : ℝ))⁻¹) • f a := by
  dsimp only
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  let g := measureLpResolventOperator hm lambda hlambda f
  let v : α → E := fun a => (-(m a : ℝ) * (lambda + (m a : ℝ))⁻¹) • f a
  -- The proposed generator value is in `Lᵖ` because its scalar multiplier has norm at most one.
  have hv : MemLp v p μ := by
    apply (Lp.memLp f).mono (by fun_prop)
    filter_upwards with a
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_neg_mul_add_inv_le_one (m a) hlambda)
  let vLp : Lp E p μ := hv.toLp v
  have hvLp : vLp =ᵐ[μ] v := MemLp.coeFn_toLp _
  -- Dominated convergence computes the strong derivative of the candidate resolvent vector.
  have hlim : Tendsto (fun t => (1 / t) • (S.realOperator t g - g))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds vLp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm]
    refine (TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto
      (f := fun t a => ((1 / t) * (Real.exp (-(t * m a)) - 1) *
        (lambda + (m a : ℝ))⁻¹) • f a) (g := v)
      (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
      (.of_forall fun t => by fun_prop) (by fun_prop) (Lp.memLp f) (C := 2) ?_ ?_).congr' ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards with a
      have hcoeff := abs_measureLpResolventGeneratorScalar_le_one (m a) hlambda ht
      have htarget := abs_neg_mul_add_inv_le_one (m a) hlambda
      have hnorm :
          ‖((1 / t) * (Real.exp (-(t * m a)) - 1) *
                (lambda + (m a : ℝ))⁻¹) • f a - v a‖ ≤ 2 * ‖f a‖ := by
        dsimp only [v]
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ (|(1 / t) * (Real.exp (-(t * m a)) - 1) *
                (lambda + (m a : ℝ))⁻¹| +
              |-(m a : ℝ) * (lambda + (m a : ℝ))⁻¹|) * ‖f a‖ := by
            gcongr
            exact abs_sub _ _
          _ ≤ (1 + 1) * ‖f a‖ :=
            mul_le_mul_of_nonneg_right (add_le_add hcoeff htarget) (norm_nonneg _)
          _ = 2 * ‖f a‖ := by ring
      rw [← ofReal_norm, ← ofReal_norm]
      calc
        _ ≤ ENNReal.ofReal (2 * ‖f a‖) := ENNReal.ofReal_le_ofReal hnorm
        _ = (2 : ℝ≥0) * ENNReal.ofReal ‖f a‖ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    · filter_upwards with a
      exact (tendsto_measureLpResolventGeneratorScalar (m a) lambda).smul_const (f a)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_smul (1 / t) (S.realOperator t g - g),
        Lp.coeFn_sub (S.realOperator t g) g,
        ofMeasureLpMultiplication_realOperator_apply_ae hm hp ht.le g,
        measureLpResolventOperator_ae hm lambda hlambda f] with a hs hsub htime hg
      simp only [Pi.sub_apply]
      rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, htime, hg]
      simp only [smul_sub, smul_smul]
      module
  -- The generator's defining limit identifies its value with the pointwise multiplier above.
  have hgdom : g ∈ S.domain := (S.mem_domain_iff_tendsto g).2 ⟨vLp, hlim⟩
  refine ⟨hgdom, ?_⟩
  have hgen := S.generator_eq_of_tendsto hgdom hlim
  rw [hgen]
  exact hvLp

/-- The Laplace resolvent of the measure-space multiplication semigroup acts by pointwise
multiplication with `(lambda + m)⁻¹`, almost everywhere. -/
@[simp]
theorem ContractionSemigroup.ofMeasureLpMultiplication_resolvent_apply_ae
    [CompleteSpace (Lp E p μ)] {m : α → ℝ≥0} (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    {lambda : ℝ} (hlambda : 0 < lambda) (f : Lp E p μ) :
    (ofMeasureLpMultiplication hm hp).resolvent lambda hlambda f =ᵐ[μ]
      fun a => (lambda + (m a : ℝ))⁻¹ • f a := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) hm hp
  let R := measureLpResolventOperator (E := E) (p := p) hm lambda hlambda
  obtain ⟨hRfdom, hgen⟩ :=
    measureLpResolventOperator_mem_domain_generator_ae hm hp hlambda f
  have hRfgen : R f ∈ S.generator.domain := by
    rw [StronglyContinuousSemigroup.generator_domain]
    exact hRfdom
  have hright : lambda • R f - S.generator ⟨R f, hRfgen⟩ = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (lambda • R f)
        (S.generator ⟨R f, hRfgen⟩),
      Lp.coeFn_smul lambda (R f), measureLpResolventOperator_ae hm lambda hlambda f,
      hgen] with a hsub hsmul hR hgen'
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hR, hgen']
    have hne : lambda + (m a : ℝ) ≠ 0 := by positivity
    simp only [smul_smul]
    rw [← sub_smul]
    have hcoeff : lambda * (lambda + (m a : ℝ))⁻¹ -
        -(m a : ℝ) * (lambda + (m a : ℝ))⁻¹ = 1 := by
      field_simp [hne]
      ring
    rw [hcoeff, one_smul]
  have hleft := S.resolventLeftInv lambda hlambda ⟨R f, hRfdom⟩
  rw [hright] at hleft
  rw [hleft]
  exact measureLpResolventOperator_ae hm lambda hlambda f

end TauCeti.Semigroups
