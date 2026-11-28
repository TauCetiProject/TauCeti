/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Basic
public import TauCeti.Geometry.Neuromanifold.Activation.PiecewiseAffine
import TauCeti.Geometry.Neuromanifold.MLP.PiecewiseAffine

/-!
# ReLU networks compute piecewise affine functions

On each closed coordinate orthant, the rectifier is a linear projection. Composing its
finite polyhedral cover with the affine layers gives a finite cover for every prefix of a
network, including the vector-valued output. In particular, every scalar function computed
by the network is piecewise affine and hence continuous by `IsPiecewiseAffineOn.continuousOn`.

This is the forward direction of Theorem 2.1 of Arora, Basu, Mianjy and Mukherjee,
*Understanding Deep Neural Networks with Rectified Linear Units*.
-/

public section

open Set

namespace TauCeti

open Neuromanifold

variable {L n : ℕ} {d : Fin (L + 1) → ℕ}

/-- Every vector-valued prefix of a ReLU network is affine on the cells of a finite
polyhedral cover of the input space. This includes the final, unrectified output. -/
theorem isPiecewiseAffineOn_evalPrefix_reluSpec (θ : (reluSpec d).Parameters)
    (i : Fin (L + 1)) :
    IsPiecewiseAffineOn (fun x => (reluSpec d).evalPrefix θ x i) univ := by
  refine (reluSpec d).isPiecewiseAffineOn_evalPrefix θ ?_ i
  intro j _
  simpa only [reluSpec_activation, reluActivation_def] using
    isPiecewiseAffineOn_reluActivation (ι := Fin ((reluSpec d).width j.succ)) () univ

/-- A scalar function computed by a ReLU network agrees with a continuous affine map on
each cell of a finite cover of the whole input space by convex polyhedra. -/
theorem isPiecewiseAffineOn_of_reluNetComputes {f : (Fin n → ℝ) → ℝ}
    (hf : ReLUNetComputes d f) : IsPiecewiseAffineOn f univ := by
  obtain ⟨rfl, hout, θ, hθ⟩ := hf
  let output : (Fin (d (Fin.last L)) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (Fin.cast hout.symm 0)
  have houtput (y : Fin (d (Fin.last L)) → ℝ) :
      output.toContinuousAffineMap y = y (Fin.cast hout.symm 0) := by
    simp only [ContinuousLinearMap.coe_toContinuousAffineMap, output,
      ContinuousLinearMap.proj_apply]
  refine ((isPiecewiseAffineOn_continuousAffineMap output.toContinuousAffineMap univ).comp
    (isPiecewiseAffineOn_evalPrefix_reluSpec θ (Fin.last L)) (mapsTo_univ _ _)).congr ?_
  intro x _
  have hinput (y : Fin (d 0) → ℝ) : y ∘ (Fin.cast rfl : Fin (d 0) → Fin (d 0)) = y := by
    rw [Fin.cast_refl, Function.comp_id]
  have hx := congrArg (fun y : Fin (d 0) → ℝ => (reluSpec d).realize θ y (Fin.cast hout.symm 0))
    (hinput x)
  calc
    f x = (reluSpec d).realize θ x (Fin.cast hout.symm 0) := (hθ x).symm.trans hx
    _ = (reluSpec d).evalPrefix θ x (Fin.last L) (Fin.cast hout.symm 0) :=
      congrFun ((reluSpec d).realize_def θ x) _
    _ = output.toContinuousAffineMap ((reluSpec d).evalPrefix θ x (Fin.last L)) := (houtput _).symm

end TauCeti
