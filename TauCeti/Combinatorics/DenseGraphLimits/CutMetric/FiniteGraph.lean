/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Constant
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic

/-!
# Cut distance of a finite graphon

The complete graph on the uniform two-point carrier has cut distance `1/8` from the constant
graphon `1/2` on any probability carrier. The distance is the cut norm of the difference kernel;
its value follows by checking the finitely many rectangles of `Fin 2`.

## Main results

* `cutDist_finiteGraphGraphonOnFin_top_two_const_half` — the exact distance `1/8`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- **The complete graph on the uniform two-point carrier is at cut distance `1/8` from the
constant graphon `1/2`**, whatever the probability carrier of the constant graphon.

The difference kernel is `1/2` on the two off-diagonal cells and `-1/2` on the two diagonal cells,
each of mass `1/4`; an off-diagonal cell attains `1/8`, and no rectangle does better. -/
theorem cutDist_finiteGraphGraphonOnFin_top_two_const_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cutDist (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2)))
      (Graphon.const μ ⟨1 / 2, by norm_num, by norm_num⟩) = 1 / 8 := by
  rw [cutDist_const_right]
  set K := (finiteGraphGraphonOnFin (⊤ : SimpleGraph (Fin 2))).toSymmKernel -
    (Graphon.const (uniformOn Set.univ) ⟨1 / 2, by norm_num, by norm_num⟩).toSymmKernel
  have hK (i j : Fin 2) : K i j = ((if i = j then -1 else 1 : ℤ) : ℝ) / 2 := by
    by_cases h : i = j <;> simp [K, h] <;> norm_num
  have hrect (S T : Finset (Fin 2)) : K.rectIntegral (uniformOn Set.univ) S T =
      (∑ i ∈ S, ∑ j ∈ T, ((if i = j then -1 else 1 : ℤ) : ℝ)) / 8 := by
    rw [SymmKernel.rectIntegral_uniformOn_univ, Fintype.card_fin]
    simp_rw [hK, ← Finset.sum_div, div_div]
    norm_num
  -- The signed sum over a rectangle is decided over the sixteen rectangles of `Fin 2`.
  have hbound : ∀ S T : Finset (Fin 2),
      |∑ i ∈ S, ∑ j ∈ T, (if i = j then -1 else 1 : ℤ)| ≤ 1 := by decide
  refine le_antisymm (cutNorm_le _ fun S _ T _ => ?_) ?_
  · rw [← S.toFinite.coe_toFinset, ← T.toFinite.coe_toFinset, hrect, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 8), div_le_div_iff_of_pos_right (by norm_num)]
    exact_mod_cast hbound _ _
  · have h := abs_rectIntegral_le_cutNorm _ K
      (MeasurableSet.of_discrete (s := ((({0} : Finset (Fin 2))) : Set (Fin 2))))
      (MeasurableSet.of_discrete (s := ((({1} : Finset (Fin 2))) : Set (Fin 2))))
    rw [hrect] at h
    simpa using h

end DenseGraphLimits

end TauCeti
