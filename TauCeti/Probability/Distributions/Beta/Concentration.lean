/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Concentration

/-!
# Beta concentration at a fixed mean

For `0 < p < 1`, the Beta laws with shapes `c * p` and `c * (1 - p)` converge weakly to
the point mass at `p` as `c` tends to infinity. This is the first-coordinate marginal of
the corresponding two-category Dirichlet concentration limit.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- Beta laws with increasing total concentration and fixed interior mean converge weakly
to the point mass at that mean. -/
theorem tendsto_betaMeasure_concentration_atTop {p : ℝ} (hp : p ∈ Ioo 0 1) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun c : Ioi (0 : ℝ) ↦
      (⟨betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p)),
        isProbabilityMeasureBeta (mul_pos c.2 hp.1) (mul_pos c.2 (sub_pos.mpr hp.2))⟩ :
          ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let w : Convexity.StdSimplex ℝ (Fin 2) :=
    .duple 0 1 hp.1.le (sub_nonneg.mpr hp.2.le) (by ring)
  have hw0 : w.weights 0 = p := by simp [w]
  have hw1 : w.weights 1 = 1 - p := by simp [w]
  have hw (i : Fin 2) : 0 < w.weights i := by
    fin_cases i
    · simpa [w] using hp.1
    · simpa [w] using sub_pos.mpr hp.2
  have h := (ProbabilityMeasure.continuous_map
    (f := fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) (by fun_prop)).tendsto
      (⟨Measure.dirac ((EuclideanSpace.equiv (Fin 2) ℝ).symm w.weights), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) |>.comp
          (tendsto_dirichletMeasure_concentration_atTop w hw)
  have hmap (c : Ioi (0 : ℝ)) :
      ProbabilityMeasure.map (⟨dirichletMeasure (fun i ↦ (c : ℝ) * w.weights i),
        isProbabilityMeasure_dirichletMeasure (fun i ↦ mul_pos c.2 (hw i))⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) =
      (⟨betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p)),
        isProbabilityMeasureBeta (mul_pos c.2 hp.1) (mul_pos c.2 (sub_pos.mpr hp.2))⟩ :
          ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    refine (ProbabilityMeasure.toMeasure_map _).trans ?_
    simpa only [ProbabilityMeasure.coe_mk, hw0, hw1] using
      map_eval_zero_dirichletMeasure_fin_two (fun i ↦ mul_pos c.2 (hw i))
  have hdirac :
      ProbabilityMeasure.map
        (⟨Measure.dirac ((EuclideanSpace.equiv (Fin 2) ℝ).symm w.weights), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) =
      (⟨Measure.dirac p, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    refine (ProbabilityMeasure.toMeasure_map _).trans ?_
    simp [hw0]
  rw [hdirac] at h
  exact h.congr (fun c ↦ hmap c)

end TauCeti.Probability
