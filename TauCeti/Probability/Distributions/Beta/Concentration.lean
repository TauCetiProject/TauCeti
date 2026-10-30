/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Concentration
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Beta concentration at a fixed mean

For `0 < p < 1`, the Beta laws with shapes `c * p` and `c * (1 - p)` converge weakly to
the point mass at `p` as `c` tends to infinity, and to the Bernoulli law with success probability
`p` as `c` tends to zero. These are the first-coordinate marginals of the corresponding
two-category Dirichlet concentration limits.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Weak convergence of two-category Dirichlet laws carries over to their first-coordinate Beta
marginals. -/
theorem tendsto_betaMeasure_of_tendsto_dirichletMeasure {α : Type*} {l : Filter α}
    {a : α → Fin 2 → ℝ} (ha : ∀ x i, 0 < a x i)
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))}
    (h : Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (fun x ↦
      (⟨dirichletMeasure (a x), isProbabilityMeasure_dirichletMeasure (ha x)⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))) l (𝓝 ν)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun x ↦
      (⟨betaMeasure (a x 0) (a x 1), isProbabilityMeasureBeta (ha x 0) (ha x 1)⟩ :
        ProbabilityMeasure ℝ)) l (𝓝 (ν.map fun y ↦ y 0)) := by
  refine ((ProbabilityMeasure.continuous_map (by fun_prop)).tendsto ν |>.comp h).congr
    fun x ↦ ProbabilityMeasure.toMeasure_injective ?_
  exact (ProbabilityMeasure.toMeasure_map _).trans (map_eval_zero_dirichletMeasure_fin_two (ha x))

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
  have h := tendsto_betaMeasure_of_tendsto_dirichletMeasure (fun c i ↦ mul_pos c.2 (hw i))
    (tendsto_dirichletMeasure_concentration_atTop w hw)
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
  exact h.congr fun c ↦ ProbabilityMeasure.toMeasure_injective (by simp [hw0, hw1])

/-- Beta laws with decreasing total concentration and fixed interior mean converge weakly to the
Bernoulli law that gives mass `1 - p` to zero and mass `p` to one. -/
theorem tendsto_betaMeasure_concentration_atBot {p : ℝ} (hp : p ∈ Ioo 0 1) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun c : Ioi (0 : ℝ) ↦
      (⟨betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p)),
        isProbabilityMeasureBeta (mul_pos c.2 hp.1) (mul_pos c.2 (sub_pos.mpr hp.2))⟩ :
          ProbabilityMeasure ℝ)) atBot
      (𝓝 (⟨bernoulliMeasure (1 : ℝ) 0 ⟨p, hp.1.le, hp.2.le⟩, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  let q : unitInterval := ⟨p, hp.1.le, hp.2.le⟩
  let w : Convexity.StdSimplex ℝ≥0 (Fin 2) :=
    .duple 0 1 zero_le zero_le (unitInterval.toNNReal_add_toNNReal_symm q)
  have hw0 : (w.weights 0 : ℝ) = p := by simp [w, q]
  have hw1 : (w.weights 1 : ℝ) = 1 - p := by simp [w, q]
  have hw (i : Fin 2) : 0 < w.weights i := by
    rw [← NNReal.coe_pos]
    fin_cases i
    · simpa [hw0] using hp.1
    · simpa [hw1] using hp.2
  have h := tendsto_betaMeasure_of_tendsto_dirichletMeasure
    (fun c i ↦ mul_pos c.2 (NNReal.coe_pos.2 (hw i)))
    (tendsto_dirichletMeasure_concentration_atBot w hw)
  have hcat : categoricalMeasure w = bernoulliMeasure 0 1 q := by
    simp [categoricalMeasure_def, bernoulliMeasure_def, Fin.sum_univ_two, w]
  have hlimit :
      ProbabilityMeasure.map
          ((categoricalMeasure w).map (EuclideanSpace.basisFun (Fin 2) ℝ)).toProbabilityMeasure
          (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) =
        (⟨bernoulliMeasure (1 : ℝ) 0 q, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    refine (ProbabilityMeasure.toMeasure_map _).trans ?_
    simp [hcat, map_bernoulliMeasure]
  rw [hlimit] at h
  exact h.congr fun c ↦ ProbabilityMeasure.toMeasure_injective (by simp [hw0, hw1])

end TauCeti.Probability
