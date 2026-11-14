/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Predictable representatives of classical delta hedges

For a price `C(s,t)`, the delta hedge holds `C_s(S_t,t)` stock shares and
`(C(S_t,t) - S_t C_s(S_t,t)) / β_t` bond shares. If the price and its delta are jointly
continuous at positive spot before maturity, these holdings have predictable representatives
along an adapted stock with almost surely left-continuous, positive paths. Continuity of the
stock paths, as in a diffusion market, is sufficient.

The representatives agree with the stated holdings simultaneously at every time outside one
null set. The filtration need not be complete or right-continuous. In particular, we do not
assert literal predictability of holdings evaluated on an arbitrary raw stock version.
Both holdings are extended by zero at and after maturity; no terminal delta limit or regularity
at zero spot is required. The bond may be any deterministic Borel function. Predictability
alone implies neither integrability nor self-financing.

The construction uses the raw-filtration representative selection in
`MeasureTheory.StronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5 and §5.2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m} {S : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- Classical delta holdings along a positive, almost surely left-continuous adapted stock
have predictable representatives on the original filtration. Equality holds for all times on
one common full-measure event, including the zero extension at and after maturity.
Only continuity of the price and delta on the positive-spot, pre-maturity domain is required;
no moment, terminal-delta, or usual-filtration assumptions are imposed. -/
theorem exists_isStronglyPredictable_deltaHedge
    (hS : StronglyAdapted ℱ S)
    (hc : ∀ᵐ ω ∂P, IsLeftContinuous (S · ω))
    (hpos : ∀ᵐ ω ∂P, ∀ t < T, 0 < S t ω)
    {C : ℝ → ℝ≥0 → ℝ}
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Iio T))
    (hD : ContinuousOn (fun p : ℝ × ℝ≥0 => deriv (C · p.2) p.1) (Ioi 0 ×ˢ Iio T))
    {β : ℝ≥0 → ℝ} (hβ : Measurable β) :
    ∃ a b : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable ℱ a ∧ IsStronglyPredictable ℱ b ∧
      ∀ᵐ ω ∂P, ∀ t,
        a t ω = (if t < T then deriv (C · t) (S t ω) else 0) ∧
        b t ω = (if t < T then
          (C (S t ω) t - S t ω * deriv (C · t) (S t ω)) / β t else 0) := by
  classical
  obtain ⟨X, hX, hXS⟩ := hS.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous hc
  let U : Set (ℝ × ℝ≥0) := Ioi 0 ×ˢ Iio T
  -- Extend the pair together: neither the price nor its delta is assumed regular on
  -- the excluded boundary, and selection may leave exceptional stock paths nonpositive.
  let F : ℝ × ℝ≥0 → ℝ × ℝ := U.piecewise
    (fun p => (C p.1 p.2, deriv (C · p.2) p.1)) 0
  have hF : Measurable F :=
    (hC.prodMk hD).measurable_piecewise continuousOn_const
      (measurableSet_Ioi.prod measurableSet_Iio)
  have htime := ℱ.measurable_fst_predictable
  have hXt : Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω => (X p.1 p.2, p.1)) :=
    hX.measurable.prodMk htime
  have hFX := hF.comp hXt
  let a : ℝ≥0 → Ω → ℝ := fun t ω => (F (X t ω, t)).2
  let b : ℝ≥0 → Ω → ℝ := fun t ω =>
    ((F (X t ω, t)).1 - X t ω * a t ω) / β t
  have ha : IsStronglyPredictable ℱ a := hFX.snd.stronglyMeasurable
  have hb : IsStronglyPredictable ℱ b :=
    (hFX.fst.sub (hX.measurable.mul hFX.snd)).div
      (hβ.comp htime) |>.stronglyMeasurable
  refine ⟨a, b, ha, hb, ?_⟩
  filter_upwards [hXS, hpos] with ω hω hp
  intro t
  by_cases ht : t < T
  · have hmem : (S t ω, t) ∈ U := ⟨hp t ht, ht⟩
    simp [a, b, F, hω t, hmem, ht]
  · have hmem : (S t ω, t) ∉ U := fun h => ht h.2
    simp [a, b, F, hω t, hmem, ht]

end MeasureTheory.StronglyAdapted
