/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Products of standard Gaussian vectors

Grouping independent standard Gaussian scalars by their first index produces independent
standard Gaussian vectors.

## Main results

* `TauCeti.Probability.map_pi_gaussianReal_to_vectors`: the grouped product law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Grouping a product of standard Gaussian scalars into vectors gives a product of
standard multivariate Gaussian laws. -/
theorem map_pi_gaussianReal_to_vectors {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] :
    (Measure.pi fun _ : ι × κ ↦ gaussianReal 0 1).map
        (fun z j ↦ WithLp.toLp 2 fun i : κ ↦ z (j, i)) =
      Measure.pi fun _ : ι ↦ multivariateGaussian 0 (1 : Matrix κ κ ℝ) := by
  classical
  let fiber (j : ι) := {p : ι × κ // p.1 = j}
  let e (j : ι) : κ ≃ fiber j :=
    { toFun := fun i ↦ ⟨(j, i), rfl⟩
      invFun := fun p ↦ p.1.2
      left_inv := fun _ ↦ rfl
      right_inv := fun p ↦ by
        apply Subtype.ext
        exact Prod.ext p.2.symm rfl }
  have hfiber (j : ι) :
      MeasurePreserving
        (fun z : fiber j → ℝ ↦ WithLp.toLp 2 fun i : κ ↦ z (e j i))
        (Measure.pi fun _ : fiber j ↦ gaussianReal 0 1)
        (multivariateGaussian 0 (1 : Matrix κ κ ℝ)) := by
    refine ⟨(WithLp.measurable_toLp 2 _).comp
      (MeasurableEquiv.piCongrLeft (fun _ : fiber j ↦ ℝ) (e j)).symm.measurable, ?_⟩
    calc
      Measure.map (fun z : fiber j → ℝ ↦ WithLp.toLp 2 fun i : κ ↦ z (e j i))
          (Measure.pi fun _ : fiber j ↦ gaussianReal 0 1) =
        Measure.map (WithLp.toLp 2 ∘
          (MeasurableEquiv.piCongrLeft (fun _ : fiber j ↦ ℝ) (e j)).symm)
          (Measure.pi fun _ : fiber j ↦ gaussianReal 0 1) := by
            congr 1
      _ = Measure.map (WithLp.toLp 2)
          (Measure.map
            (MeasurableEquiv.piCongrLeft (fun _ : fiber j ↦ ℝ) (e j)).symm
            (Measure.pi fun _ : fiber j ↦ gaussianReal 0 1)) := by
              rw [← Measure.map_map (WithLp.measurable_toLp 2 _)
                (MeasurableEquiv.piCongrLeft (fun _ : fiber j ↦ ℝ) (e j)).symm.measurable]
      _ = Measure.map (WithLp.toLp 2)
          (Measure.pi fun _ : κ ↦ gaussianReal 0 1) := by
            rw [(measurePreserving_piCongrLeft
              (fun _ : fiber j ↦ gaussianReal 0 1) (e j)).symm.map_eq]
      _ = multivariateGaussian 0 (1 : Matrix κ κ ℝ) :=
        (multivariateGaussian_one_eq_map_pi (0 : EuclideanSpace ℝ κ)).symm
  have hregroup := measurePreserving_pi_fiberwise
    (f := fun p : ι × κ ↦ p.1)
    (μ := fun _ : ι × κ ↦ gaussianReal 0 1)
    (ν := fun _ : ι ↦ multivariateGaussian 0 (1 : Matrix κ κ ℝ))
    (g := fun j z ↦ WithLp.toLp 2 fun i : κ ↦ z (e j i))
    hfiber
  convert hregroup.map_eq using 1

end TauCeti.Probability
