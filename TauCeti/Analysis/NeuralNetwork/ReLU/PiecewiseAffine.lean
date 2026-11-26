/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Basic
public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Topology.PL.Map
import TauCeti.Geometry.Neuromanifold.MLP.Composition
import TauCeti.Topology.Algebra.Module.Matrix

/-!
# ReLU networks compute piecewise affine functions

On each closed coordinate orthant, the rectifier is a linear projection. Composing its
finite polyhedral cover with the affine layers gives a finite cover for every prefix of a
network, including the vector-valued output. In particular, every scalar function computed
by the network is continuous piecewise linear.

This is the forward direction of Theorem 2.1 of Arora, Basu, Mianjy and Mukherjee,
*Understanding Deep Neural Networks with Rectified Linear Units*.
-/

public section

open Set

namespace TauCeti

open Neuromanifold

/-- On a finite coordinate space the ReLU layer is piecewise affine. Its cells are the
closed orthants, with one choice of sign for each coordinate. -/
theorem isPiecewiseAffineOn_reluActivation {ι : Type*} [Finite ι] (p : PUnit)
    (s : Set (ι → ℝ)) : IsPiecewiseAffineOn (reluActivation p) s := by
  classical
  let coord (i : ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let test (J : Set ι) (i : ι) : (ι → ℝ) →ᴬ[ℝ] ℝ :=
    if i ∈ J then -(coord i).toContinuousAffineMap else (coord i).toContinuousAffineMap
  let piece (J : Set ι) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i => if i ∈ J then coord i else 0
  refine isPiecewiseAffineOn_of_finite (A := fun J => (piece J).toContinuousAffineMap)
    (fun J => isConvexPolyhedron_setOf_forall (test J)) ?_ ?_
  · intro x _
    refine mem_iUnion.mpr ⟨{i | 0 ≤ x i}, ?_⟩
    intro i
    by_cases hi : 0 ≤ x i <;> simp [test, coord, hi, le_of_not_ge]
  · intro J x hx
    funext i
    have hi := hx.2 i
    by_cases hJ : i ∈ J
    · simp [test, coord, hJ] at hi
      simp [piece, coord, hJ, max_eq_right hi]
    · simp [test, coord, hJ] at hi
      simp [piece, hJ, max_eq_left hi]

variable {L n : ℕ} {d : Fin (L + 1) → ℕ}

/-- Every vector-valued prefix of a ReLU network is affine on the cells of a finite
polyhedral cover of the input space. This includes the final, unrectified output. -/
theorem isPiecewiseAffineOn_evalPrefix_reluSpec (θ : (reluSpec d).Parameters)
    (i : Fin (L + 1)) :
    IsPiecewiseAffineOn (fun x => (reluSpec d).evalPrefix θ x i) univ := by
  induction i using Fin.induction with
  | zero =>
    exact (isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ _) univ).congr
      fun x _ => (reluSpec d).evalPrefix_zero θ x
  | succ i ih =>
    let A := reluSpec d
    have hAffine : IsPiecewiseAffineOn (dense (θ i)) univ := by
      let layer := (θ i).1.mulVecCLM.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (θ i).2
      exact (isPiecewiseAffineOn_continuousAffineMap layer univ).congr
        (fun x _ => by simp [layer])
    have hAct : IsPiecewiseAffineOn
        (activation (ι := Fin (d i.succ)) (A.layerActivation i) ()) univ := by
      by_cases hi : i.val + 1 < L
      · rw [A.layerActivation_of_lt _ hi, reluSpec_activation]
        simpa only [reluActivation_def] using isPiecewiseAffineOn_reluActivation
          (ι := Fin (d i.succ)) () univ
      · rw [A.layerActivation_of_val_add_one_eq _ (by omega), activation_id]
        exact isPiecewiseAffineOn_continuousAffineMap (ContinuousAffineMap.id ℝ _) univ
    exact (hAct.comp (hAffine.comp ih (mapsTo_univ _ _)) (mapsTo_univ _ _)).congr
      fun x _ => A.evalPrefix_succ_eq_activation_dense θ x i

/-- Every scalar function computed by a ReLU network is continuous piecewise linear, in
the sense of a finite cover of the whole input space by convex polyhedra. -/
theorem isPiecewiseAffineOn_of_reluNetComputes {f : (Fin n → ℝ) → ℝ}
    (hf : ReLUNetComputes d f) : IsPiecewiseAffineOn f univ := by
  obtain ⟨rfl, hout, θ, hθ⟩ := hf
  let output : (Fin (d (Fin.last L)) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (Fin.cast hout.symm 0)
  exact ((isPiecewiseAffineOn_continuousAffineMap output.toContinuousAffineMap univ).comp
    (isPiecewiseAffineOn_evalPrefix_reluSpec θ (Fin.last L)) (mapsTo_univ _ _)).congr
      fun x _ => (hθ x).symm.trans (congrFun ((reluSpec d).realize_def θ x) _)

end TauCeti
