/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
import TauCeti.RingTheory.MvPowerSeries.Ideal.Basic

/-!
# Ideal bounds for finite-variable power-series evaluation

With finitely many variables, admissible arguments can be evaluated modulo any ideal, with
no closedness or adicity hypothesis on that ideal.

* `MvPowerSeries.eval₂_sub_constantCoeff_mem_of_finite`: evaluation is congruent to the image
  of the constant coefficient modulo an ideal containing the arguments.
* `MvPowerSeries.eval₂_mem_of_finite`: if the ideal also contains the image of the constant
  coefficient, it contains the evaluated series.
-/

public section

namespace MvPowerSeries

variable {σ R S : Type*} [CommRing R] [UniformSpace R] [IsTopologicalSemiring R]
  [IsUniformAddGroup R] [CommRing S] [UniformSpace S] [IsUniformAddGroup S]
  [CompleteSpace S] [T2Space S] [Finite σ] [IsTopologicalRing S] [IsLinearTopology S S]
  {φ : R →+* S} {a : σ → S} {I : Ideal S}

/-- In finitely many variables, evaluation at admissible arguments in an ideal is congruent
to the image of the constant term modulo that ideal. -/
theorem eval₂_sub_constantCoeff_mem_of_finite (f : MvPowerSeries σ R)
    (hφ : Continuous φ) (ha : HasEval a) (hmem : ∀ i, a i ∈ I) :
    eval₂ φ a f - φ (constantCoeff f) ∈ I := by
  let e := eval₂Hom (φ := φ) hφ ha
  have hle : Ideal.span (Set.range X) ≤ I.comap e := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    simpa only [SetLike.mem_coe, Ideal.mem_comap, e, coe_eval₂Hom, eval₂_X] using hmem i
  have he : e (f - C (constantCoeff f)) ∈ I :=
    hle (mem_span_range_X_iff.mpr (by simp))
  simpa only [map_sub, e, coe_eval₂Hom, eval₂_C] using he

/-- In finitely many variables, evaluation lies in any ideal containing the admissible
arguments and the image of the constant term. Taking the ideal to be `I ^ k` gives the
bound for an ideal power. -/
theorem eval₂_mem_of_finite (f : MvPowerSeries σ R) (hφ : Continuous φ) (ha : HasEval a)
    (hmem : ∀ i, a i ∈ I) (hcc : φ (constantCoeff f) ∈ I) : eval₂ φ a f ∈ I := by
  simpa only [sub_add_cancel] using I.add_mem
    (f.eval₂_sub_constantCoeff_mem_of_finite hφ ha hmem) hcc

end MvPowerSeries
