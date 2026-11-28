/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.MLP.Composition
public import TauCeti.Topology.Algebra.Module.Matrix
public import TauCeti.Topology.PL.Map

/-!
# Piecewise-affine multilayer perceptrons

Dense layers are continuous affine maps. A real multilayer perceptron with piecewise-affine
hidden activations has piecewise-affine prefix maps, including its output.
-/

public section

open Set

namespace TauCeti.Neuromanifold

variable {ι ο R : Type*} [Fintype ι] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The continuous affine map of a dense layer with fixed weights and bias. -/
def denseContinuousAffineMap (p : Matrix ο ι R × (ο → R)) : (ι → R) →ᴬ[R] (ο → R) :=
  p.1.mulVecCLM.toContinuousAffineMap + ContinuousAffineMap.const R _ p.2

/-- Evaluating the continuous affine map gives the dense layer at the same parameters. -/
@[simp] theorem denseContinuousAffineMap_apply (p : Matrix ο ι R × (ο → R)) (x : ι → R) :
    denseContinuousAffineMap p x = dense p x := by
  simp [denseContinuousAffineMap]

/-- Every prefix of a real MLP with piecewise-affine coordinatewise hidden activations is
piecewise affine on the whole input space. The output uses the identity activation. -/
theorem MLPSpec.isPiecewiseAffineOn_evalPrefix {L : ℕ} (A : MLPSpec ℝ L) (θ : A.Parameters)
    (hactivation : ∀ (i : Fin L) (hi : i.val + 1 < L),
      IsPiecewiseAffineOn
        (Neuromanifold.activation (ι := Fin (A.width i.succ))
          (A.activation ⟨i.val, by omega⟩) ()) univ)
    (i : Fin (L + 1)) : IsPiecewiseAffineOn (fun x => A.evalPrefix θ x i) univ := by
  induction i using Fin.induction with
  | zero =>
    have hid := isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.id ℝ (Fin (A.width 0) → ℝ)) univ
    rw [ContinuousAffineMap.coe_id] at hid
    exact hid.congr fun x _ => A.evalPrefix_zero θ x
  | succ i ih =>
    have hdense : IsPiecewiseAffineOn (dense (θ i)) univ :=
      (isPiecewiseAffineOn_continuousAffineMap (denseContinuousAffineMap (θ i)) univ).congr
        fun x _ => (denseContinuousAffineMap_apply _ x).symm
    have hact : IsPiecewiseAffineOn
        (Neuromanifold.activation (ι := Fin (A.width i.succ)) (A.layerActivation i) ()) univ := by
      by_cases hi : i.val + 1 < L
      · rw [A.layerActivation_of_lt i hi]
        exact hactivation i hi
      · rw [A.layerActivation_of_val_add_one_eq i (by omega), activation_id]
        simpa only [ContinuousAffineMap.coe_id] using
          isPiecewiseAffineOn_continuousAffineMap
            (ContinuousAffineMap.id ℝ (Fin (A.width i.succ) → ℝ)) univ
    exact (hact.comp (hdense.comp ih (mapsTo_univ _ _)) (mapsTo_univ _ _)).congr
      fun x _ => A.evalPrefix_succ_eq_activation_dense θ x i

end TauCeti.Neuromanifold
