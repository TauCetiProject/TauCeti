/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.MeasureTheory.OptimalTransport.Coupling

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Limits of coupling densities in L¹

For finite marginals, the coupling constraint is closed under L¹ convergence of densities
against a σ-finite reference measure. An integrable, almost everywhere nonnegative limit defines a
coupling of the same marginals. No topology on the underlying measurable spaces is required, and
the reference measure may have infinite mass.

`TauCeti.isCoupling_withDensity_of_tendsto_eLpNorm` applies along any nontrivial filter. It is the
measure-theoretic closure step used when constructing a transport plan from a convergent family
of densities, independently of the functional that is being minimized.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {R : Measure (X × Y)} {l : Filter ι}

/-- If the densities of couplings of `μ` and `ν` against a σ-finite reference `R` converge in
`L¹(R)` along a nontrivial filter to an integrable, almost everywhere nonnegative function, that
function is the density of a coupling of `μ` and `ν`. The source measure `μ` is finite. -/
theorem isCoupling_withDensity_of_tendsto_eLpNorm [IsFiniteMeasure μ] [SigmaFinite R] [l.NeBot]
    {π : ι → Measure (X × Y)} (hπ : ∀ i, IsCoupling (π i) μ ν) (hac : ∀ i, π i ≪ R)
    {g : X × Y → ℝ} (hgint : Integrable g R) (hg0 : 0 ≤ᵐ[R] g)
    (hL1 : Tendsto (fun i ↦ eLpNorm ((fun z ↦ ((π i).rnDeriv R z).toReal) - g) 1 R) l
      (𝓝 0)) :
    IsCoupling (R.withDensity fun z ↦ ENNReal.ofReal (g z)) μ ν := by
  have hfin (i : ι) : IsFiniteMeasure (π i) := (hπ i).isFiniteMeasure
  obtain ⟨i⟩ := Filter.nonempty_of_neBot l
  have : IsFiniteMeasure ν := ⟨by
    rw [← (hπ i).measure_univ_eq]
    exact measure_lt_top μ Set.univ⟩
  -- On a measurable set where every plan has the same finite mass, the limit has that mass.
  have key (s : Set (X × Y)) (hs : MeasurableSet s) {a : ℝ≥0∞} (ha : a ≠ ∞)
      (hconst : ∀ i, π i s = a) :
      R.withDensity (fun z ↦ ENNReal.ofReal (g z)) s = a := by
    have hlim := tendsto_setIntegral_of_L1' g
      (Eventually.of_forall fun i ↦ Measure.integrable_toReal_rnDeriv) hL1 s
    simp only [Measure.setIntegral_toReal_rnDeriv (hac _), measureReal_def, hconst,
      tendsto_const_nhds_iff] at hlim
    rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal hgint.integrableOn
      (ae_restrict_of_ae hg0), ← hlim, ENNReal.ofReal_toReal ha]
  refine isCoupling_of_measure_prod_univ_of_measure_univ_prod (fun s hs ↦ ?_) fun s hs ↦ ?_
  · exact key _ (hs.prod .univ) (measure_ne_top μ s) fun i ↦ (hπ i).measure_prod_univ hs
  · exact key _ (MeasurableSet.univ.prod hs) (measure_ne_top ν s) fun i ↦
      (hπ i).measure_univ_prod hs

end TauCeti
