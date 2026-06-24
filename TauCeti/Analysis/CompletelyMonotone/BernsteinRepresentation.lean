/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.CompletelyMonotone.BernsteinChafaiIdentity
public import TauCeti.Analysis.CompletelyMonotone.BernsteinKernelConv

/-!
# Bernstein's representation theorem (forward direction)

Bernstein's theorem represents a completely monotone function as the Laplace transform of a
positive measure on `[0, ∞)`. This file assembles the **forward direction** for
`TauCeti.IsCompletelyMonotone`, the closed-half-line notion from
`TauCeti.Analysis.CompletelyMonotone.Basic`: every completely monotone `f` is the Laplace
transform of a finite measure on `ℝ≥0` (`IsCompletelyMonotone.exists_measure`).

The Chafaï construction lives in the supporting files (`BernsteinAux`, `BernsteinMeasures`,
`BernsteinChafaiIdentity`, `BernsteinProkhorov`, `BernsteinKernelConv`); here we tie the pieces
together (`bernstein_theorem` on `Measure ℝ`) and transport the measure to `ℝ≥0` per the TauCeti
convention. Ported from the sorry-free `mrdouglasny/hille-yosida` (`HilleYosida.Bernstein`).

## Scope and the finite-vs-all-moments subtlety

We state only the forward existence here, with a **finite** representing measure — exactly what
complete monotonicity on the closed half-line yields. The *biconditional* is deferred (PR #2):
the converse "finite measure ⟹ completely monotone" is **false** for this closed-half-line
class — e.g. `t ↦ ∫₀^∞ e^{-x t}(1+x)⁻² dx` comes from a finite measure yet has `f'(0⁺) = -∞`,
so it is not `C^∞` at `0`. The class that closed complete monotonicity matches biconditionally
is the measures with **all moments finite**. See the `TODO` block at the end.

## Main declarations

* `TauCeti.laplaceTransformMeasure`: `t ↦ ∫ e^{-t x} dμ`, the Laplace transform of a measure
  on `ℝ≥0`.
* `TauCeti.IsCompletelyMonotone.exists_measure`: every completely monotone function on
  `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- The **Laplace transform** of a measure `μ` on `ℝ≥0`, evaluated at `t : ℝ`:
`t ↦ ∫ e^{-t x} dμ(x)`. By Bernstein's theorem every completely monotone function on
`[0, ∞)` is of this form for a finite `μ` (`IsCompletelyMonotone.exists_measure`). -/
noncomputable def laplaceTransformMeasure (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * (x : ℝ)) ∂μ

/-- **Prokhorov extraction + Laplace verification** (Chafaï 2013). Assembles the Chafaï identity
with the Prokhorov limit identification to represent `f t - L` as `∫ e^{-tp} dμ₀`. -/
private lemma cm_prokhorov_and_verify (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) (hL_nn : 0 ≤ L)
    (hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) univ ≤ ENNReal.ofReal (f 0 - L))
    (hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Iio 0) = 0) :
    ∃ μ₀ : Measure ℝ, IsFiniteMeasure μ₀ ∧ μ₀ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  have hfin_rescaled : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_rescaled f n) := by
    intro n hn; haveI := (hmass n hn).1; exact cm_rescaled_isFiniteMeasure f n
  have hmass_rescaled : ∀ n, 2 ≤ n →
      (cm_rescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
    intro n hn; rw [cm_rescaled_mass_eq]; exact (hmass n hn).2
  have hchafai : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n) :=
    fun n hn x hx => chafai_identity f hcm n hn x hx L hL
  exact prokhorov_limit_identification f hcm L hL hL_nn hmass_rescaled hsupp
    hfin_rescaled hchafai

/-- For a completely monotone `f` with limit `L ≥ 0` at infinity, there is a finite positive
measure `μ₀` on `[0, ∞)` with `f t = L + ∫ e^{-tp} dμ₀`. -/
private lemma cm_laplace_representation (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) (hL_nn : 0 ≤ L) :
    ∃ μ₀ : Measure ℝ, IsFiniteMeasure μ₀ ∧ μ₀ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  have hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) univ ≤ ENNReal.ofReal (f 0 - L) :=
    fun n hn => cm_measure_finite_mass f hcm n hn L hL
  have hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Iio 0) = 0 :=
    fun n hn => cm_rescaled_Iio_zero f n hn
  exact cm_prokhorov_and_verify hcm L hL hL_nn hmass hsupp

/-- **Bernstein's theorem** on `Measure ℝ`: every completely monotone `f` on `[0, ∞)` is the
Laplace transform of a finite measure supported on `[0, ∞)`. -/
private lemma bernstein_theorem_real (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Iio 0) = 0 ∧
      ∀ t : ℝ, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  obtain ⟨L, hL_tendsto, hL_nonneg⟩ := hcm.tendsto_atTop
  obtain ⟨μ₀, hfin₀, hsupp₀, hrep⟩ := cm_laplace_representation hcm L hL_tendsto hL_nonneg
  exact bernstein_packaging hL_nonneg hsupp₀ hrep

/-- **Bernstein's theorem, forward direction.** Every completely monotone function on the
closed half-line `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

Port of `HilleYosida.Bernstein.bernstein_theorem`, with the representing measure transported
from `Measure ℝ` (supported on `[0, ∞)`) to `Measure ℝ≥0` by pushforward along `Real.toNNReal`. -/
theorem IsCompletelyMonotone.exists_measure (hf : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
  obtain ⟨μ, hfin, hsupp, hrep⟩ := bernstein_theorem_real hf
  have hmeas : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  haveI hfin_map : IsFiniteMeasure (μ.map Real.toNNReal) := by
    constructor
    rw [Measure.map_apply hmeas MeasurableSet.univ]
    exact measure_lt_top μ _
  refine ⟨μ.map Real.toNNReal, hfin_map, fun t ht => ?_⟩
  have hnn : ∀ᵐ p ∂μ, (0 : ℝ) ≤ p := by
    have hset : {p : ℝ | ¬ (0 : ℝ) ≤ p} = Iio 0 := by ext p; simp [not_le]
    rw [ae_iff, hset]; exact hsupp
  rw [hrep t ht]
  unfold laplaceTransformMeasure
  rw [integral_map hmeas.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ≥0 => Real.exp (-t * (x : ℝ))) _)]
  refine integral_congr_ae ?_
  filter_upwards [hnn] with p hp
  rw [Real.coe_toNNReal' p, max_eq_left hp]
  ring_nf

-- TODO (PR #2 — the biconditional, all-moments form). The textbook iff requires the
-- *all-moments* condition on the measure side, not mere finiteness (see the scope note above):
--   def HasAllMoments (μ : Measure ℝ≥0) : Prop := ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x:ℝ)^n) μ
--   theorem isCompletelyMonotone_laplaceTransformMeasure (hμ : HasAllMoments μ) :
--       IsCompletelyMonotone (laplaceTransformMeasure μ)              -- ⇐, differentiate under ∫
--   theorem laplaceTransformMeasure_injective ...                    -- uniqueness
--   theorem bernstein (f : ℝ → ℝ) :
--     IsCompletelyMonotone f ↔
--       ∃! μ : Measure ℝ≥0, HasAllMoments μ ∧ ∀ t ≥ 0, f t = laplaceTransformMeasure μ t

end TauCeti
