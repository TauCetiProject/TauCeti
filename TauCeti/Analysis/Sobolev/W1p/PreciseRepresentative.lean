/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative

/-!
# The precise representative of a `W^{1,p}` function

A Sobolev function is locally integrable on its domain, so by the Lebesgue differentiation
theorem it agrees almost everywhere there with its precise representative
`TauCeti.MeasureTheory.preciseRepresentative`, the limit of its averages over shrinking balls.

## Main declarations

* `TauCeti.W1p.ae_eq_preciseRepresentative`: a Sobolev function agrees almost everywhere with its
  precise representative.
* `TauCeti.W1p.ae_eq_preciseRepresentative_indicator`: the same for the precise representative of
  its extension by zero.
* `TauCeti.W1p.gradient_ae_eq_preciseRepresentative_restrict`: on `s ∩ t ⊆ Ω` with `s` open, the
  gradient of a Sobolev function agrees almost everywhere with its precise representative for the
  measure restricted to `t`.
* `TauCeti.W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative`: a Sobolev
  function whose gradient has a continuous precise representative on an open set has a `C¹`
  representative there.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Sobolev function agrees almost everywhere on its domain with its precise representative. -/
theorem W1p.ae_eq_preciseRepresentative (u : W1p mu Omega p) :
    W1p.value u =ᵐ[mu.restrict Omega] preciseRepresentative mu (W1p.value u) :=
  ae_eq_restrict_preciseRepresentative Omega.isOpen (W1p.hasWeakFDerivOn u).locallyIntegrableOn

/-- A Sobolev function agrees almost everywhere on its domain with the precise representative of
its extension by zero. This is the representative that global estimates up to the boundary
control on the whole space. -/
theorem W1p.ae_eq_preciseRepresentative_indicator (u : W1p mu Omega p) :
    W1p.value u =ᵐ[mu.restrict Omega]
      preciseRepresentative mu ((Omega : Set E).indicator (W1p.value u)) := by
  have hΩ : MeasurableSet (Omega : Set E) := Omega.isOpen.measurableSet
  have hli : LocallyIntegrable ((Omega : Set E).indicator (W1p.value u)) mu :=
    ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2
      (Lp.memLp (W1p.value u))).locallyIntegrable Fact.out
  filter_upwards [ae_restrict_of_ae (MeasureTheory.ae_eq_preciseRepresentative hli),
    ae_restrict_mem hΩ] with x h hx
  rwa [Set.indicator_of_mem hx] at h

/-- For an open set `s` and a set `t` with `s ∩ t ⊆ Ω`, the gradient of `u ∈ W^{1,p}(Ω)` agrees
almost everywhere on `s ∩ t` with its precise representative for `mu` restricted to `t`. -/
theorem W1p.gradient_ae_eq_preciseRepresentative_restrict (u : W1p mu Omega p) {s t : Set E}
    (hs : IsOpen s) (hst : s ∩ t ⊆ Omega) :
    (W1p.gradient u : E → E) =ᵐ[mu.restrict (s ∩ t)]
      preciseRepresentative (mu.restrict t) (W1p.gradient u : E → E) :=
  ae_eq_restrict_inter_preciseRepresentative_restrict hs
    (((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hst le_rfl)).locallyIntegrable
      Fact.out)

/-- If the precise representative of the weak gradient of a Sobolev function is continuous on an
open subset `V` of its domain, then the function agrees almost everywhere on `V` with a `C¹`
function whose derivative at every point of `V` is given by that precise representative. -/
theorem W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative
    (u : W1p mu Omega p) {V : Opens E} (hV : V ≤ Omega)
    (hP : ContinuousOn (preciseRepresentative mu (W1p.gradient u : E → E)) V) :
    ∃ g : E → ℝ, ContDiffOn ℝ 1 g V ∧ W1p.value u =ᵐ[mu.restrict V] g ∧
      ∀ x ∈ V, HasFDerivAt g (innerSL ℝ (preciseRepresentative mu (W1p.gradient u : E → E) x))
        x := by
  have hG : (W1p.gradient u : E → E) =ᵐ[mu.restrict V]
      preciseRepresentative mu (W1p.gradient u : E → E) :=
    ae_restrict_of_ae_restrict_of_subset hV
      (ae_eq_restrict_preciseRepresentative Omega.isOpen (W1p.locallyIntegrableOn_gradient u))
  exact (((W1p.hasWeakFDerivOn u).mono hV).congr_ae_deriv
    (hG.fun_comp (innerSL ℝ))).exists_contDiffOn_one_ae_eq
    ((innerSL ℝ).continuous.comp_continuousOn hP)

end TauCeti
