/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Probability.LargeDeviations.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.MeasureTheory.Integral.Lebesgue.Slabs
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.Basic
import TauCeti.Analysis.SpecialFunctions.Log.ENNRealLog.LargestTerm
import TauCeti.Data.EReal.Operations
import TauCeti.Topology.Instances.EReal

/-!
# Varadhan's lemma and the Laplace principle

A family of measures `μ i`, indexed along a filter `l`, satisfies the *Laplace principle* with
inverse speed `ε` and rate function `I` when, for every bounded continuous `f`, the normalized
logarithms of the exponential moments `ε i * log ∫⁻ exp (f / ε i) dμ i` tend to
`sup_x (f x - I x)` in `EReal`.

Varadhan's lemma says that a large deviation principle implies the Laplace principle with the
same rate, at an inverse speed tending to `0`. The lower bound holds for every lower
semicontinuous `f`: near a point `x` the integrand exceeds `exp ((f x - δ) / ε i)` on the open
set `{f > f x - δ}`, whose rate is bounded below by the principle. The upper bound holds for
every bounded upper semicontinuous `f`: it splits the range of `f` into finitely many closed slabs
of width `δ` (`TauCeti.lintegral_ofReal_exp_div_le_sum_slabs`) and combines the upper bound of the
principle on each slab with the principle of the largest term. Neither goodness of the rate
function nor total mass `1` is needed.

The *moment condition* is a criterion for the tail condition of Varadhan's lemma for unbounded
functions: if the exponential moments of `γ * φ` have finite limsup rate for some `γ > 1`, then
the rate of the exponential moment of `φ` restricted to `{M ≤ φ}` tends to `-∞` as `M → ∞`.

## Main definitions

* `TauCeti.Probability.LaplacePrinciple l ε μ I`: the Laplace principle.

## Main results

* `TauCeti.Probability.HasLDP.le_liminf_coe_mul_log_lintegral_exp`: the lower bound of
  Varadhan's lemma, for every lower semicontinuous function.
* `TauCeti.Probability.HasLDP.limsup_coe_mul_log_lintegral_exp_le`: the upper bound of
  Varadhan's lemma, for bounded upper semicontinuous functions.
* `TauCeti.Probability.HasLDP.laplacePrinciple`: Varadhan's lemma for bounded continuous
  functions.
* `TauCeti.Probability.tendsto_limsup_log_setLIntegral_exp_of_moment`: the moment condition
  implies the tail condition.

## Implementation notes

As for `TauCeti.Probability.HasLDP`, the results are stated at an inverse speed `ε i ≥ 0` along
an arbitrary filter. A family indexed by `n` at a speed `a n → ∞` is covered by taking
`ε n = (a n)⁻¹`, which tends to `0`; the exponent `a n * f x` then reads `f x / ε n`, and the
normalized logarithm `(a n)⁻¹ * log ∫⁻ exp (a n * f) dμ n` reads `ε n * log ∫⁻ exp (f / ε n) dμ n`.

The proof of `HasLDP.laplacePrinciple` follows `CKMA.varadhan` in lean-CKMA
(`CKMA/Probability/LargeDeviations.lean`), adapted from real Bochner integrals at speed `n + 1`
to lower integrals at a general inverse speed.

## References

* A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer
  (1998), Theorem 4.3.1 and (4.3.3).
* P. Dupuis, R. S. Ellis, *A Weak Convergence Approach to the Theory of Large Deviations*,
  Wiley (1997), Definition 1.2.2 and Theorem 1.2.1.
-/

public section

open Filter Topology MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.Probability

section Laplace

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The family `μ i`, `i` along the filter `l`, satisfies the *Laplace principle* with inverse
speed `ε` and rate function `I`: for every bounded continuous `f`,
`ε i * log ∫⁻ exp (f / ε i) dμ i` tends to `sup_x (f x - I x)` in `EReal` (Dupuis–Ellis,
Definition 1.2.2, with the sign of `f` reversed). -/
def LaplacePrinciple (l : Filter ι) (ε : ι → ℝ≥0) (μ : ι → Measure X) (I : X → ℝ≥0∞) : Prop :=
  ∀ f : X →ᵇ ℝ, Tendsto (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l
    (𝓝 (⨆ x, ((f x : EReal) - I x)))

variable {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞}

/-- Unfolding of `LaplacePrinciple`. -/
theorem laplacePrinciple_def : LaplacePrinciple l ε μ I ↔ ∀ f : X →ᵇ ℝ,
    Tendsto (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l
    (𝓝 (⨆ x, ((f x : EReal) - I x))) :=
  Iff.rfl

/-- Under the Laplace principle, the normalized logarithms of the exponential moments of a
bounded continuous `f` tend to `sup_x (f x - I x)`. -/
theorem LaplacePrinciple.tendsto (h : LaplacePrinciple l ε μ I) (f : X →ᵇ ℝ) :
    Tendsto (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l
    (𝓝 (⨆ x, ((f x : EReal) - I x))) :=
  h f

/-- **Lower bound of Varadhan's lemma.** Under a large deviation principle, every lower
semicontinuous `f` satisfies `sup_x (f x - I x) ≤ liminf ε i * log ∫⁻ exp (f / ε i) dμ i`. -/
theorem HasLDP.le_liminf_coe_mul_log_lintegral_exp [OpensMeasurableSpace X]
    (h : HasLDP l ε μ I) {f : X → ℝ} (hf : LowerSemicontinuous f) :
    ⨆ x, ((f x : EReal) - I x) ≤ liminf (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l := by
  set L := liminf (fun i => ((ε i : ℝ) : EReal) *
    ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l
  -- Every level `c < f x` gives `c - I x ≤ L`, through the open set `{c < f}`.
  have hc (x : X) (c : ℝ) (hcx : c < f x) : (c : EReal) - I x ≤ L := by
    set U := {y | c < f y}
    have hU : IsOpen U := hf.isOpen_preimage c
    have hle (i : ι) (hi : 0 < ε i) : (c : EReal) + ((ε i : ℝ) : EReal) * ENNReal.log (μ i U) ≤
        ((ε i : ℝ) : EReal) *
          ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i) := by
      rw [← ENNReal.coe_mul_log_ofReal_exp_div_mul hi]
      refine ENNReal.coe_mul_log_monotone _ ?_
      rw [← lintegral_indicator_const hU.measurableSet]
      refine lintegral_mono (Set.indicator_le fun y hy => ?_)
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
        (div_le_div_of_nonneg_right (le_of_lt hy) (ε i).coe_nonneg))
    calc (c : EReal) - I x ≤ (c : EReal) + -((⨅ y ∈ U, I y : ℝ≥0∞) : EReal) := by
          rw [sub_eq_add_neg]
          -- `x ∈ U` unfolds to `c < f x`.
          exact add_le_add le_rfl (EReal.neg_le_neg_iff.2
            (EReal.coe_ennreal_le_coe_ennreal_iff.2 (biInf_le _ (show x ∈ U from hcx))))
      _ ≤ (c : EReal) + liminf (fun i => ((ε i : ℝ) : EReal) * ENNReal.log (μ i U)) l :=
          add_le_add le_rfl (h.lower_bound U hU)
      _ ≤ L := by
          rw [← EReal.liminf_coe_add]
          exact liminf_le_liminf (h.eventually_pos.mono hle)
  refine iSup_le fun x => ?_
  by_cases hI : I x = ∞
  · simp [hI]
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_sub]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz => ?_
  have hz' := hc x (z + (I x).toReal) (by linarith [EReal.coe_lt_coe_iff.1 hz])
  rwa [← EReal.coe_ennreal_toReal hI, ← EReal.coe_sub, add_sub_cancel_right] at hz'

/-- **Upper bound of Varadhan's lemma.** Under a large deviation principle at an inverse speed
tending to `0`, every upper semicontinuous `f` with `|f| ≤ M` satisfies
`limsup ε i * log ∫⁻ exp (f / ε i) dμ i ≤ sup_x (f x - I x)`. -/
theorem HasLDP.limsup_coe_mul_log_lintegral_exp_le (h : HasLDP l ε μ I)
    (hε : Tendsto ε l (𝓝 0)) {f : X → ℝ} (hf : UpperSemicontinuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) :
    limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l ≤
      ⨆ x, ((f x : EReal) - I x) := by
  set S := ⨆ x, ((f x : EReal) - I x)
  -- By the slab bound and the principle of the largest term, the limsup is at most `S + δ`.
  have hδ (δ : ℝ) (hδ : 0 < δ) : limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (f x / ε i)) ∂μ i)) l ≤ S + δ := by
    set F : ℕ → Set X := fun k => {x | -M + k * δ ≤ f x}
    refine (ENNReal.limsup_coe_mul_log_mono (Eventually.of_forall fun i =>
      lintegral_ofReal_exp_div_le_sum_slabs hM hδ (ε i) (μ i))).trans ?_
    rw [ENNReal.limsup_coe_mul_log_sum _ _ hε fun h0 =>
      absurd (Finset.range_eq_empty_iff.1 h0) (Nat.add_one_ne_zero _)]
    refine iSup₂_le fun k _ => ?_
    -- The slab `F k` has rate at most `S + δ`, since `f ≥ -M + k δ` on it.
    rw [limsup_congr (h.eventually_pos.mono fun i hi =>
      ENNReal.coe_mul_log_ofReal_exp_div_mul hi _ (μ i (F k))), EReal.limsup_coe_add]
    refine (add_le_add le_rfl
      (h.upper_bound _ (hf.isClosed_preimage _))).trans ?_
    rw [add_comm, ← EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))]
    refine TauCeti.EReal.neg_coe_ennreal_biInf_le_iff.2 fun x hx => ?_
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
      add_comm, EReal.coe_add, add_right_comm]
    refine add_le_add (le_trans ?_ (le_iSup (fun y => (f y : EReal) - I y) x)) le_rfl
    exact add_le_add (EReal.coe_le_coe_iff.2 hx) le_rfl
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  -- Choose `δ > 0` with `S + δ ≤ z`.
  have key (s : EReal) (hs : s < z) : ∃ δ : ℝ, 0 < δ ∧ s + δ ≤ z := by
    induction s using EReal.rec with
    | bot => exact ⟨1, one_pos, by simp⟩
    | coe s =>
      refine ⟨z - s, sub_pos.2 (EReal.coe_lt_coe_iff.1 hs), ?_⟩
      rw [← EReal.coe_add, add_sub_cancel]
    | top => exact absurd hs (not_lt_of_ge le_top)
  obtain ⟨δ, hδ0, hδz⟩ := key S hz
  exact (hδ δ hδ0).trans hδz

/-- **Varadhan's lemma** for bounded continuous functions: at an inverse speed tending to `0`, a
large deviation principle implies the Laplace principle with the same rate (Dupuis–Ellis,
Theorem 1.2.1; Dembo–Zeitouni, Theorem 4.3.1). -/
theorem HasLDP.laplacePrinciple [OpensMeasurableSpace X] (h : HasLDP l ε μ I)
    (hε : Tendsto ε l (𝓝 0)) : LaplacePrinciple l ε μ I := fun f =>
  tendsto_of_le_liminf_of_limsup_le
    (h.le_liminf_coe_mul_log_lintegral_exp f.continuous.lowerSemicontinuous)
    (h.limsup_coe_mul_log_lintegral_exp_le hε f.continuous.upperSemicontinuous
      fun x => (Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm x))

end Laplace

section Moment

variable {ι X : Type*} [MeasurableSpace X] {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X}

/-- **The moment condition.** At an eventually positive inverse speed, if for some `γ > 1` the
exponential moments of `γ * φ` have limsup rate `< ⊤`, then the exponential moments of a
measurable `φ` restricted to `{M ≤ φ}` have limsup rate tending to `⊥` as `M → ∞`: this is the
tail condition of Varadhan's lemma (Dembo–Zeitouni, (4.3.3)). -/
theorem tendsto_limsup_log_setLIntegral_exp_of_moment (hε : ∀ᶠ i in l, 0 < ε i) {φ : X → ℝ}
    (hφ : Measurable φ) {γ : ℝ} (hγ : 1 < γ)
    (hmom : limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (γ * φ x / ε i)) ∂μ i)) l < ⊤) :
    Tendsto (fun M : ℝ => limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x in {x | M ≤ φ x}, ENNReal.ofReal (Real.exp (φ x / ε i)) ∂μ i)) l)
      atTop (𝓝 ⊥) := by
  set C := limsup (fun i => ((ε i : ℝ) : EReal) *
    ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (γ * φ x / ε i)) ∂μ i)) l
  -- On `{M ≤ φ}`, `exp (φ / ε) ≤ exp ((1 - γ) M / ε) * exp (γ φ / ε)`.
  have hbound (M : ℝ) : limsup (fun i => ((ε i : ℝ) : EReal) *
      ENNReal.log (∫⁻ x in {x | M ≤ φ x}, ENNReal.ofReal (Real.exp (φ x / ε i)) ∂μ i)) l ≤
      (((1 - γ) * M : ℝ) : EReal) + C := by
    rw [← EReal.limsup_coe_add]
    refine limsup_le_limsup (hε.mono fun i hi => ?_)
    rw [← ENNReal.coe_mul_log_ofReal_exp_div_mul hi]
    refine ENNReal.coe_mul_log_monotone _ ?_
    calc ∫⁻ x in {x | M ≤ φ x}, ENNReal.ofReal (Real.exp (φ x / ε i)) ∂μ i
        ≤ ∫⁻ x in {x | M ≤ φ x}, ENNReal.ofReal (Real.exp ((1 - γ) * M / ε i)) *
            ENNReal.ofReal (Real.exp (γ * φ x / ε i)) ∂μ i := by
          refine setLIntegral_mono' (measurableSet_le measurable_const hφ) fun x hx => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← add_div]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (div_le_div_of_nonneg_right ?_ (ε i).coe_nonneg))
          nlinarith [mul_nonneg (sub_nonneg.2 hγ.le) (sub_nonneg.2 (Set.mem_ofPred.1 hx))]
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp ((1 - γ) * M / ε i)) *
            ENNReal.ofReal (Real.exp (γ * φ x / ε i)) ∂μ i :=
          setLIntegral_le_lintegral _ _
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- The bound `(1 - γ) M + C` tends to `⊥`, since `C < ⊤`.
  have hlim : Tendsto (fun M : ℝ => (((1 - γ) * M : ℝ) : EReal) + C) atTop (𝓝 ⊥) := by
    have h1 : Tendsto (fun M : ℝ => (((1 - γ) * M : ℝ) : EReal)) atTop (𝓝 ⊥) :=
      EReal.tendsto_coe_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have h2 := (EReal.continuousAt_add (p := (⊥, C)) (.inl bot_ne_top)
      (.inr hmom.ne)).tendsto.comp (h1.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def, EReal.bot_add] using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

end Moment

end TauCeti.Probability
