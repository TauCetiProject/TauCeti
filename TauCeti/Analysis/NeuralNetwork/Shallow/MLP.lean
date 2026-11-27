/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.Shallow.Basic
public import TauCeti.Geometry.Neuromanifold.MLP.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation

/-!
# One-hidden-layer networks as depth-two multilayer perceptrons

For Euclidean inputs a one-hidden-layer network is a depth-two `Neuromanifold.MLPSpec` with
one output coordinate. Its first matrix stores the hidden weight vectors as rows and its second
matrix has one row of output coefficients.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti.ShallowNet

open Neuromanifold

variable {n m : ℕ}

/-- The depth-two perceptron with input width `n`, hidden width `m`, and one affine output. -/
abbrev mlpSpec (n m : ℕ) (σ : ℝ → ℝ) : MLPSpec ℝ 2 :=
  ⟨![n, m, 1], fun _ => σ⟩

/-- The weight matrices and biases of a shallow Euclidean network as depth-two MLP parameters. -/
def toMLPParameters (N : ShallowNet (EuclideanSpace ℝ (Fin n)) m) (σ : ℝ → ℝ) :
    (mlpSpec n m σ).Parameters :=
  Fin.cons (fun i j => N.weight i j, N.bias)
    (Fin.cons (fun _ i => N.coeff i, fun _ => N.outBias) (fun i => i.elim0))

/-- The hidden matrix has the weight vectors as rows, with their corresponding biases. -/
@[simp] theorem toMLPParameters_zero (N : ShallowNet (EuclideanSpace ℝ (Fin n)) m)
    (σ : ℝ → ℝ) :
    N.toMLPParameters σ 0 = (fun i j => N.weight i j, N.bias) := (rfl)

/-- The output matrix has the output coefficients as its sole row. -/
@[simp] theorem toMLPParameters_one (N : ShallowNet (EuclideanSpace ℝ (Fin n)) m)
    (σ : ℝ → ℝ) :
    N.toMLPParameters σ 1 = (fun _ i => N.coeff i, fun _ => N.outBias) := (rfl)

/-- The scalar realization equals the single coordinate of the depth-two MLP output. -/
theorem realize_toMLPParameters (N : ShallowNet (EuclideanSpace ℝ (Fin n)) m)
    (σ : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (mlpSpec n m σ).realize (N.toMLPParameters σ) x (0 : Fin 1) = N.eval σ x := by
  let input : Fin ((mlpSpec n m σ).width 0) → ℝ := x.ofLp
  let output : Fin ((mlpSpec n m σ).width (Fin.last 2)) := (0 : Fin 1)
  suffices (mlpSpec n m σ).realize (N.toMLPParameters σ) input output = N.eval σ x from this
  have hHidden : (mlpSpec n m σ).layerActivation 0 = σ :=
    (mlpSpec n m σ).layerActivation_of_lt 0 (by decide)
  let hidden : Fin ((mlpSpec n m σ).width (Fin.last 1).castSucc) → ℝ :=
    fun i => σ (⟪N.weight i, x⟫ + N.bias i)
  have hprefix :
      (mlpSpec n m σ).evalPrefix (N.toMLPParameters σ) input (Fin.last 1).castSucc = hidden := by
    refine ((mlpSpec n m σ).evalPrefix_succ (N.toMLPParameters σ) input 0).trans ?_
    -- The preceding index is `Fin.castSucc 0`. Reducing it also identifies the input widths.
    erw [(mlpSpec n m σ).evalPrefix_zero (N.toMLPParameters σ) input]
    simp [hidden, input, hHidden, Matrix.mulVec, dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
    rfl
  rw [(mlpSpec n m σ).realize_succ (L := 1), hprefix, eval_apply]
  rfl

end TauCeti.ShallowNet
