/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Adapted
public import TauCeti.Probability.Process.Filtration.Comp
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Pre-Brownian motion relative to a filtration

Mathlib's `ProbabilityTheory.IsPreBrownianReal` prescribes only the finite-dimensional laws of
`W`. A martingale statement needs a filtration, and the law of `W` alone does not say how `W`
interacts with it: `TauCeti.Probability.IsFilteredPreBrownianReal ℱ W P` adds that `W` is adapted
to `ℱ` and that every increment `W_t - W_s`, `s ≤ t`, is independent of `ℱ_s`. A pre-Brownian
motion is a pre-Brownian motion relative to its own natural filtration
(`ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`). Conversely, an adapted
process started at `0` whose increments `W_t - W_s` have law `N(0, t - s)` and are independent of
`ℱ_s` is a pre-Brownian motion relative to `ℱ`
(`MeasureTheory.Adapted.isFilteredPreBrownianReal`); this is how a change of measure is shown to
produce a new Brownian motion.

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownianReal`: a pre-Brownian motion relative to a
  filtration.
* `TauCeti.Probability.IsFilteredPreBrownianReal.indep_shift` and
  `TauCeti.Probability.IsFilteredPreBrownianReal.shift`: deterministic time shifts have full
  future increment path independent of `ℱ s` and remain filtered pre-Brownian relative to
  `ℱ.comp (monotone_id.const_add s)`.
* `ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`: the natural
  filtration.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_sub_of_le`: for `s ≤ t`, the increment
  `W_t - W_s` has law `N(0, t - s)`.
* `ProbabilityTheory.IsPreBrownianReal.integral_sq_sub_of_le` and
  `ProbabilityTheory.IsPreBrownianReal.integral_pow_four_sub_of_le`: second and fourth moments
  of increments; the centered square is square integrable with mean zero and second moment
  twice the squared interval length.
* `ProbabilityTheory.IsPreBrownianReal.integral_sq_sub_sub_eq_zero`: the centered square
  of an increment has mean zero.
* `MeasureTheory.Adapted.isFilteredPreBrownianReal`: the characterization by Gaussian increments
  independent of the past.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `W` is a **pre-Brownian motion relative to the filtration `ℱ`** under `P`: its
finite-dimensional laws are those of Brownian motion, it is adapted to `ℱ`, and for `s ≤ t` the
increment `W t - W s` is independent of `ℱ s`. -/
structure IsFilteredPreBrownianReal (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownianReal W P where
  /-- `W t` is `ℱ t`-measurable. -/
  adapted : Adapted ℱ W
  /-- The increment `W t - W s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P

/-- A random variable measurable at the left endpoint is independent of the following
Brownian increment. -/
theorem IsFilteredPreBrownianReal.indepFun_sub {ℱ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t : ℝ≥0} (hst : s ≤ t) {E : Type*} [MeasurableSpace E] {Y : Ω → E}
    (hY : Measurable[ℱ s] Y) : IndepFun Y (W t - W s) P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_left (hW.indep_sub hst).symm hY.comap_le)

namespace IsFilteredPreBrownianReal

/-- A Brownian value is independent of every random variable known at time zero. -/
theorem indepFun_eval_of_measurable_zero {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} (hW : IsFilteredPreBrownianReal ℱ W P)
    {E : Type*} [MeasurableSpace E] {ξ : Ω → E} (hξ : Measurable[ℱ 0] ξ) (t : ℝ≥0) :
    IndepFun (W t) ξ P := by
  have h : IndepFun (W t - W 0) ξ P :=
    indep_of_indep_of_le_right (hW.indep_sub (zero_le (a := t))) hξ.comap_le
  refine h.congr ?_ Filter.EventuallyEq.rfl
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

/-- At a deterministic time `s`, the entire shifted increment process `t ↦ W (s + t) - W s`
is independent of `ℱ s`. -/
theorem indep_shift {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsFilteredPreBrownianReal ℱ W P) (s : ℝ≥0) :
    Indep (.comap (fun ω t ↦ W (s + t) ω - W s ω) inferInstance) (ℱ s) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact hW.adapted.indep_comap_shift_sub hW.indep_sub s

/-- Shifting time by `s` and recentering at `W s` produces a filtered pre-Brownian motion
relative to the shifted filtration `ℱ.comp (monotone_id.const_add s)`. -/
theorem shift {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hW : IsFilteredPreBrownianReal ℱ W P) (s : ℝ≥0) :
    IsFilteredPreBrownianReal (ℱ.comp (monotone_id.const_add s))
      (fun t ω ↦ W (s + t) ω - W s ω) P where
  toIsPreBrownianReal := hW.toIsPreBrownianReal.shift s
  adapted t := by
    rw [Filtration.measurable_comp_iff]
    exact (hW.adapted (s + t)).sub ((hW.adapted s).mono (ℱ.mono le_self_add) le_rfl)
  indep_sub u v huv := by
    rw [Filtration.comp_apply]
    dsimp only [id_eq]
    have heq : ((fun ω ↦ W (s + v) ω - W s ω) - fun ω ↦ W (s + u) ω - W s ω) =
        W (s + v) - W (s + u) := funext fun ω ↦ sub_sub_sub_cancel_right _ _ _
    rw [heq]
    exact hW.indep_sub (add_le_add_right huv s)

end IsFilteredPreBrownianReal

/-- Fixed-time almost-sure equality preserves the filtered pre-Brownian property, provided
the replacement is adapted to the same filtration. Adaptedness is not inferred from a.e. equality
on a raw filtration. -/
theorem IsFilteredPreBrownianReal.congr {ℱ : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} (hB : IsFilteredPreBrownianReal ℱ B P) (hW : Adapted ℱ W)
    (h : ∀ t, B t =ᵐ[P] W t) : IsFilteredPreBrownianReal ℱ W P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.congr h
  adapted := hW
  indep_sub s t hst := by
    have hi : @IndepFun Ω ℝ Ω mΩ inferInstance (ℱ s) (B t - B s) id P := by
      simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hB.indep_sub hst
    have hj := hi.congr ((h t).sub (h s)) (Filter.EventuallyEq.refl ..)
    simpa only [IndepFun_iff_Indep, MeasurableSpace.comap_id] using hj

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A pre-Brownian motion is a pre-Brownian motion relative to its natural filtration: by the weak
Markov property `ProbabilityTheory.IsPreBrownianReal.indepFun_shift`, the increments after time
`s` are independent of `(B u, u ≤ s)`. -/
theorem isFilteredPreBrownianReal_natural (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t)) :
    IsFilteredPreBrownianReal (Filtration.natural B hmeas) B P where
  toIsPreBrownianReal := hB
  adapted t := (Filtration.stronglyAdapted_natural hmeas t).measurable
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    refine indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).mp (hB.indepFun_shift s)) ?_
    have : B t - B s = (fun x : ℝ≥0 → ℝ ↦ x (t - s)) ∘ fun ω u ↦ B (s + u) ω - B s ω := by
      ext ω
      simp [add_tsub_cancel_of_le hst]
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- Every natural power of a pre-Brownian value has every finite `Lᵖ` moment. -/
theorem memLp_pow_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) {p : ℝ≥0∞}
    (hp : p ≠ ∞) : MemLp (fun ω ↦ B t ω ^ n) p P := by
  rcases eq_or_ne n 0 with rfl | hn
  · have := (hB.hasLaw_eval 0).isProbabilityMeasure
    simpa only [pow_zero] using (memLp_const (μ := P) (p := p) (1 : ℝ))
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have h := (hB.hasLaw_eval t).memLp (memLp_id_gaussianReal' (p * n) (by finiteness))
  have hpow : MemLp (fun ω ↦ ‖B t ω‖ ^ n) p P := by
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast,
      ENNReal.mul_div_cancel_right hn' (ENNReal.natCast_ne_top n)] using h.norm_rpow_div n
  exact hpow.congr_norm (h.aestronglyMeasurable.pow n)
    (ae_of_all _ fun ω ↦ by simp [norm_pow])

/-- Every natural power of a pre-Brownian value is integrable. -/
theorem integrable_pow_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ B t ω ^ n) P :=
  memLp_one_iff_integrable.mp (hB.memLp_pow_eval t n ENNReal.one_ne_top)

/-- The second moment of a pre-Brownian value is its time. -/
theorem integral_sq_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∫ ω, B t ω ^ 2 ∂P = (t : ℝ) := by
  have h := (hB.hasLaw_eval t).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  simpa only [Function.comp_apply, integral_sq_gaussianReal, zero_pow two_ne_zero,
    add_zero] using h

/-- For `s ≤ t`, the increment `B t - B s` of a pre-Brownian motion has law `N(0, t - s)`. -/
theorem hasLaw_sub_of_le (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (B t - B s) (gaussianReal 0 (t - s)) P := by
  convert hB.hasLaw_sub t s using 2
  ext
  simp [Real.nndist_eq, hst]

/-- Every natural power of a pre-Brownian increment is integrable, in either time order. -/
theorem integrable_pow_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ (B t ω - B s ω) ^ n) P := by
  simpa only [Function.comp_def, Pi.sub_apply] using
    (hB.hasLaw_sub t s).integrable_comp
      (TauCeti.integrable_pow_gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) n)

/-- The second moment of a Brownian increment is the elapsed time. -/
theorem integral_sq_sub_of_le (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ^ 2 ∂P = (t : ℝ) - s := by
  have h := (hB.hasLaw_sub_of_le hst).integral_comp
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  simpa only [Function.comp_apply, Pi.sub_apply, integral_sq_gaussianReal,
    zero_pow two_ne_zero, add_zero, NNReal.coe_sub hst] using h

/-- The fourth moment of a Brownian increment is three times the squared elapsed time. -/
theorem integral_pow_four_sub_of_le (hB : IsPreBrownianReal B P) {s t : ℝ≥0}
    (hst : s ≤ t) : ∫ ω, (B t ω - B s ω) ^ 4 ∂P = 3 * ((t : ℝ) - s) ^ 2 := by
  have hm : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (t - s) = 3 * ((t : ℝ) - s) ^ 2 := by
    simpa only [sub_zero, NNReal.coe_sub hst] using
      integral_sub_pow_four_gaussianReal 0 (t - s)
  simpa only [Function.comp_apply, Pi.sub_apply] using
    ((hB.hasLaw_sub_of_le hst).integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)).trans hm

/-- The square of every Brownian increment is square integrable, in either time order. -/
theorem memLp_sq_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    MemLp (fun ω ↦ (B s ω - B t ω) ^ 2) 2 P := by
  let : ENNReal.HolderTriple 4 4 2 := .of_toReal (by
    norm_num [Real.holderTriple_iff])
  have h := (hB.hasLaw_sub s t).memLp (memLp_id_gaussianReal' 4 (by norm_num))
  simpa only [pow_two, Pi.mul_def, Pi.sub_def] using
    (h.mul h : MemLp ((B s - B t) * (B s - B t)) 2 P)

/-- The square of a Brownian increment minus the signed time difference is square integrable,
in either time order. This expression is centered when `s ≤ t`. -/
theorem memLp_sq_sub_sub (hB : IsPreBrownianReal B P) {s t : ℝ≥0} :
    MemLp (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) 2 P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (hB.memLp_sq_sub t s).sub (memLp_const _)

/-- The centered square of a Brownian increment has mean zero. -/
theorem integral_sq_sub_sub_eq_zero (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 2 - ((t : ℝ) - s) ∂P) = 0 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [integral_sub (hB.integrable_pow_sub s t 2) (integrable_const _),
    hB.integral_sq_sub_of_le hst, integral_const]
  simp

/-- The second moment of a centered squared Brownian increment is twice the squared
length of its time interval. -/
theorem integral_sq_sq_sub_sub (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 ∂P) =
      2 * ((t : ℝ) - s) ^ 2 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h4i := hB.integrable_pow_sub s t 4
  have h2i := hB.integrable_pow_sub s t 2
  have hexp : ∀ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 =
      (B t ω - B s ω) ^ 4 - 2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2 +
        ((t : ℝ) - s) ^ 2 := fun ω ↦ by ring
  simp_rw [hexp]
  have hsub : Integrable (fun ω ↦ (B t ω - B s ω) ^ 4 -
      2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2) P := by
    simpa only [Pi.sub_def] using h4i.sub (h2i.const_mul (2 * ((t : ℝ) - s)))
  rw [integral_add hsub (integrable_const _),
    integral_sub h4i (h2i.const_mul _), integral_const_mul,
    hB.integral_pow_four_sub_of_le hst, hB.integral_sq_sub_of_le hst, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

end ProbabilityTheory.IsPreBrownianReal

namespace MeasureTheory.Adapted

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

/-- An adapted process that starts at `0` and whose increments `X t - X s`, `s ≤ t`, have law
`N(0, t - s)` and are independent of `ℱ s` is a pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal (hX : Adapted ℱ X) (h0 : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → HasLaw (X t - X s) (gaussianReal 0 (t - s)) P)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) P) :
    IsFilteredPreBrownianReal ℱ X P := by
  have := (hlaw (le_refl 0)).isProbabilityMeasure
  refine ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_)
    (hX.hasIndepIncrements hindep), hX, hindep⟩
  refine (tsub_zero t ▸ hlaw (zero_le (a := t))).congr ?_
  filter_upwards [h0] with ω hω
  simp [hω]

end MeasureTheory.Adapted
