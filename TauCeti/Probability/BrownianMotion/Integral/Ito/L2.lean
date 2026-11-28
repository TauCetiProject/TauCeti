/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Deterministic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.Probability.BrownianMotion.Integral.Restriction

/-!
# `L²(P)` time continuity, zero expectation, and Wiener identifications of Brownian Itô integrals

Extending `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, this module establishes:

* `TauCeti.Probability.IsFilteredPreBrownianReal.ae_eq_wienerIntegral_of_isItoIntegral`:
  identification of Itô integrals of deterministic `L²(timeMeasure t)` integrands with the Wiener
  integral.
* `TauCeti.Probability.IsItoIntegral.continuous_toLp`: `L²(P)` continuity in time of any Itô
  integral of a `BrownianIntegrable` integrand.
* `TauCeti.Probability.IsItoIntegral.integral_eq_zero`: zero expectation at every horizon.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsFilteredPreBrownianReal

variable {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- At any time `t`, an Itô integral of a deterministic integrand `f ∈ L²(timeMeasure t)` agrees
almost surely with its Wiener integral `hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f)`. -/
theorem ae_eq_wienerIntegral_of_isItoIntegral (hW : IsFilteredPreBrownianReal ℱ W P)
    {f : ℝ≥0 → ℝ} {I : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} (hf : MemLp f 2 (timeMeasure t))
    (hI : IsItoIntegral ℱ P W (fun s _ ↦ f s) I) :
    I t =ᵐ[P] hW.toIsPreBrownianReal.wienerIntegral t (hf.toLp f) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hf_prod : MemLp (Function.uncurry fun s (_ : Ω) ↦ f s) 2 ((timeMeasure t).prod P) :=
    (hf.comp_measurePreserving (measurePreserving_fst (μ := timeMeasure t) (ν := P))).ae_eq
      (.of_forall fun _ ↦ rfl)
  have hfp := (ℱ.memLp_predictableMeasure_iff P hI.isStronglyPredictable t 2).mpr hf_prod
  have hl2 : hfp.toLp (Function.uncurry fun s (_ : Ω) ↦ f s) =
      (hf.comp_measurePreserving (ℱ.measurePreserving_fst_predictableMeasure P t)).toLp
        (fun p : ℝ≥0 × Ω ↦ f p.1) :=
    Lp.ext (hfp.coeFn_toLp.trans
      ((hf.comp_measurePreserving
        (ℱ.measurePreserving_fst_predictableMeasure P t)).coeFn_toLp.mono fun _ h ↦ h.symm))
  have hcomp := (Lp.toLp_compMeasurePreserving hf
    (ℱ.measurePreserving_fst_predictableMeasure P t)).symm
  dsimp only [Function.comp_def] at hcomp
  refine (hW.ae_eq_l2Integral_of_memLp hf_prod hI).trans ?_
  rw [hl2, hcomp, hW.l2Integral_compMeasurePreserving_fst t (hf.toLp f)]

end IsFilteredPreBrownianReal

namespace IsItoIntegral

variable {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {W H I : ℝ≥0 → Ω → ℝ}

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  simpa only [hI.toLp_eq_l2Integral hW hH] using hW.continuous_l2Integral hH

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

end IsItoIntegral

end TauCeti.Probability
