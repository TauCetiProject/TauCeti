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

/-- Beta laws with decreasing total concentration and fixed interior mean converge weakly to the
Bernoulli law that gives mass `1 - p` to zero and mass `p` to one. -/
theorem tendsto_betaMeasure_concentration_atBot {p : ℝ} (hp : p ∈ Ioo 0 1) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun c : Ioi (0 : ℝ) ↦
      (⟨betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p)),
        isProbabilityMeasureBeta (mul_pos c.2 hp.1) (mul_pos c.2 (sub_pos.mpr hp.2))⟩ :
          ProbabilityMeasure ℝ)) atBot
      (𝓝 (⟨bernoulliMeasure (1 : ℝ) 0 ⟨p, hp.1.le, hp.2.le⟩, inferInstance⟩ :
        ProbabilityMeasure ℝ)) := by
  let pnn : ℝ≥0 := ⟨p, hp.1.le⟩
  let qnn : ℝ≥0 := ⟨1 - p, sub_nonneg.mpr hp.2.le⟩
  have htotal : pnn + qnn = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_one]
    change p + (1 - p) = 1
    ring
  let w : Convexity.StdSimplex ℝ≥0 (Fin 2) :=
    .duple 0 1 (s := pnn) (t := qnn) (by positivity) (by positivity) htotal
  have hwweights : w.weights = Finsupp.single 0 pnn + Finsupp.single 1 qnn := by
    simpa only [w] using Convexity.StdSimplex.weights_duple 0 1
      (by positivity : 0 ≤ pnn) (by positivity : 0 ≤ qnn) htotal
  have hw0 : (w.weights 0 : ℝ) = p := by
    rw [hwweights]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    have h10 : (Finsupp.single (1 : Fin 2) qnn) 0 = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    rw [h10, add_zero]
    rfl
  have hw1 : (w.weights 1 : ℝ) = 1 - p := by
    rw [hwweights]
    rw [Finsupp.add_apply]
    have h01 : (Finsupp.single (0 : Fin 2) pnn) 1 = 0 :=
      Finsupp.single_eq_of_ne (by decide)
    rw [h01, Finsupp.single_eq_same, zero_add]
    rfl
  have hw (i : Fin 2) : 0 < w.weights i := by
    fin_cases i
    · exact_mod_cast (show 0 < (w.weights 0 : ℝ) by rw [hw0]; exact hp.1)
    · exact_mod_cast (show 0 < (w.weights 1 : ℝ) by rw [hw1]; exact sub_pos.mpr hp.2)
  have hweight0 : w.weights 0 = unitInterval.toNNReal ⟨p, hp.1.le, hp.2.le⟩ := by
    apply NNReal.eq
    simpa using hw0
  have hweight1 : w.weights 1 = unitInterval.toNNReal (unitInterval.symm
      ⟨p, hp.1.le, hp.2.le⟩) := by
    apply NNReal.eq
    rw [hw1]
    simp
  have h := (ProbabilityMeasure.continuous_map
    (f := fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) (by fun_prop)).tendsto
      (⟨∑ i, w.weights i • Measure.dirac (EuclideanSpace.basisFun (Fin 2) ℝ i),
        TauCeti.isProbabilityMeasure_sum_smul_dirac w.total_of_fintype
          (EuclideanSpace.basisFun (Fin 2) ℝ)⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) |>.comp
          (tendsto_dirichletMeasure_concentration_atBot w hw)
  have hmap (c : Ioi (0 : ℝ)) :
      ProbabilityMeasure.map (⟨dirichletMeasure
          (fun i ↦ (c : ℝ) * (w.weights i : ℝ)),
        isProbabilityMeasure_dirichletMeasure
          (fun i ↦ mul_pos c.2 (by exact_mod_cast hw i))⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
        (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) =
      (⟨betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p)),
        isProbabilityMeasureBeta (mul_pos c.2 hp.1) (mul_pos c.2 (sub_pos.mpr hp.2))⟩ :
          ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0)
        (dirichletMeasure (fun i ↦ (c : ℝ) * (w.weights i : ℝ))) =
      betaMeasure ((c : ℝ) * p) ((c : ℝ) * (1 - p))
    have ha (i : Fin 2) : 0 < (c : ℝ) * (w.weights i : ℝ) :=
      mul_pos c.2 (by exact_mod_cast hw i)
    calc
      _ = betaMeasure ((c : ℝ) * (w.weights 0 : ℝ))
          ((c : ℝ) * (w.weights 1 : ℝ)) :=
        map_eval_zero_dirichletMeasure_fin_two
          (a := fun i ↦ (c : ℝ) * (w.weights i : ℝ)) ha
      _ = _ := by rw [hw0, hw1]
  have hlimit :
      ProbabilityMeasure.map
          (⟨∑ i, w.weights i • Measure.dirac (EuclideanSpace.basisFun (Fin 2) ℝ i),
            TauCeti.isProbabilityMeasure_sum_smul_dirac w.total_of_fintype
              (EuclideanSpace.basisFun (Fin 2) ℝ)⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
          (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) =
        (⟨bernoulliMeasure (1 : ℝ) 0 ⟨p, hp.1.le, hp.2.le⟩, inferInstance⟩ :
          ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0)
        (∑ i, w.weights i • Measure.dirac (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      bernoulliMeasure (1 : ℝ) 0 ⟨p, hp.1.le, hp.2.le⟩
    rw [Measure.map_finset_sum' (by fun_prop), Fin.sum_univ_two,
      Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop),
      Measure.map_dirac' (by fun_prop), Measure.map_dirac' (by fun_prop),
      EuclideanSpace.basisFun_apply]
    simp [hweight0, hweight1, bernoulliMeasure_def]
  rw [hlimit] at h
  exact h.congr (fun c ↦ hmap c)

end TauCeti.Probability
