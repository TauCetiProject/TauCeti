/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.NeuralNetwork.ReLU.Basic
public import TauCeti.Topology.PL.PiecewiseAffine
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# ReLU networks compute piecewise-affine maps

Every prefix evaluation and hence every map realized or computed by a ReLU network is globally
piecewise affine (`isPiecewiseAffineOn_reluSpec_evalPrefix`, `isPiecewiseAffineOn_reluSpec_realize`,
`isPiecewiseAffineOn_of_reluNetRealizes`, `isPiecewiseAffineOn_of_reluNetComputes`), and since
`x ↦ |x 0|` is not continuous affine, no depth-1 ReLU network computes it
(`not_reluNetComputes_depth_one_abs`).

## References

* Raman Arora, Amitabh Basu, Poorya Mianjy, and Anirbit Mukherjee, *Understanding deep neural
  networks with rectified linear units*, ICLR 2018;
  [arXiv:1611.01491v6](https://arxiv.org/abs/1611.01491v6), Theorem 2.1.
-/

public section

open Matrix Set

namespace TauCeti

open Neuromanifold

/-- No depth-1 ReLU network computes `x ↦ |x 0|`, since depth-1 networks compute only affine
functions. -/
theorem not_reluNetComputes_depth_one_abs :
    ¬∃ d : Fin 2 → ℕ, ReLUNetComputes d (fun x : Fin 1 → ℝ => |x 0|) := by
  rw [exists_reluNetComputes_depth_one_iff]
  rintro ⟨A, hA⟩
  let e : ℝ →ᴬ[ℝ] (Fin 1 → ℝ) :=
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.toContinuousLinearMap.toContinuousAffineMap
  exact not_exists_continuousAffineMap_eq_abs
    ⟨A.comp e, fun t => congrFun hA (fun _ => t)⟩

/-- Every prefix evaluation of `reluSpec d` is globally piecewise affine on `Fin (d 0) → ℝ`. -/
theorem isPiecewiseAffineOn_reluSpec_evalPrefix {L : ℕ} (d : Fin (L + 1) → ℕ)
    (θ : (reluSpec d).Parameters) (i : Fin (L + 1)) :
    IsPiecewiseAffineOn (fun x => (reluSpec d).evalPrefix θ x i)
      (univ : Set (Fin (d 0) → ℝ)) := by
  induction i using Fin.induction with
  | zero =>
    exact (isPiecewiseAffineOn_continuousAffineMap
      (ContinuousAffineMap.id ℝ (Fin ((reluSpec d).width 0) → ℝ)) univ).congr fun x _ =>
      MLPSpec.evalPrefix_zero (reluSpec d) θ x
  | succ i ih =>
    let Lmap := LinearMap.toContinuousLinearMap (Matrix.toLin' (θ i).1)
    have haff : IsPiecewiseAffineOn
        (fun v : Fin ((reluSpec d).width i.castSucc) → ℝ => (θ i).1 *ᵥ v + (θ i).2) univ :=
      (isPiecewiseAffineOn_continuousAffineMap
        (Lmap.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (θ i).2)
        univ).congr fun _ _ => by
          simp [Lmap]
    have hstep := haff.comp ih (mapsTo_univ _ _)
    by_cases hlt : i.val + 1 < L
    · have hact : ∀ x, (reluSpec d).evalPrefix θ x i.succ =
          fun j => max 0 (((θ i).1 *ᵥ (reluSpec d).evalPrefix θ x i.castSucc) j + (θ i).2 j) :=
        fun x => by
          simp [MLPSpec.evalPrefix_succ, (reluSpec d).layerActivation_of_lt i hlt]
      exact ((isPiecewiseAffineOn_pi_max_zero (Fin ((reluSpec d).width i.succ))).comp hstep
        (mapsTo_univ _ _)).congr fun x _ => hact x
    · have heq : i.val + 1 = L := by omega
      have hact : ∀ x, (reluSpec d).evalPrefix θ x i.succ =
          (θ i).1 *ᵥ (reluSpec d).evalPrefix θ x i.castSucc + (θ i).2 :=
        fun x => (reluSpec d).evalPrefix_succ_of_val_add_one_eq θ x i heq
      exact hstep.congr fun x _ => hact x

/-- The realization map of `reluSpec d` at any parameters `θ` is globally piecewise affine. -/
theorem isPiecewiseAffineOn_reluSpec_realize {L : ℕ} (d : Fin (L + 1) → ℕ)
    (θ : (reluSpec d).Parameters) :
    IsPiecewiseAffineOn ((reluSpec d).realize θ) (univ : Set (Fin (d 0) → ℝ)) :=
  (isPiecewiseAffineOn_reluSpec_evalPrefix d θ (Fin.last L)).congr fun x _ =>
    (reluSpec d).realize_def θ x

/-- Every function `(Fin n → ℝ) → (Fin m → ℝ)` realized by a ReLU network is globally
piecewise affine. -/
theorem isPiecewiseAffineOn_of_reluNetRealizes {n m L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)} (hf : ReLUNetRealizes d f) :
    IsPiecewiseAffineOn f (univ : Set (Fin n → ℝ)) := by
  obtain ⟨h0, hL, θ, hθ⟩ := reluNetRealizes_iff.mp hf
  have h0' : (reluSpec d).width 0 = n := (congrFun (reluSpec_width d) 0).trans h0
  have hL' : (reluSpec d).width (Fin.last L) = m :=
    (congrFun (reluSpec_width d) (Fin.last L)).trans hL
  let eIn :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ)
      (finCongr h0')).symm.toContinuousLinearMap.toContinuousAffineMap
  let eOut :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ)
      (finCongr hL')).toContinuousLinearMap.toContinuousAffineMap
  have h1 := (isPiecewiseAffineOn_reluSpec_realize d θ).comp
    (isPiecewiseAffineOn_continuousAffineMap eIn univ) (mapsTo_univ _ _)
  have h2 := (isPiecewiseAffineOn_continuousAffineMap eOut univ).comp
    h1 (mapsTo_univ _ _)
  exact h2.congr fun x _ => by
    ext j
    exact (hθ x j).symm

/-- Every scalar function `(Fin n → ℝ) → ℝ` computed by a ReLU network is continuous
piecewise linear (piecewise affine on the whole space). -/
theorem isPiecewiseAffineOn_of_reluNetComputes {n L : ℕ} {d : Fin (L + 1) → ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ReLUNetComputes d f) :
    IsPiecewiseAffineOn f (univ : Set (Fin n → ℝ)) := by
  have hvec := isPiecewiseAffineOn_of_reluNetRealizes (reluNetComputes_iff_reluNetRealizes.mp hf)
  have hproj := isPiecewiseAffineOn_continuousAffineMap
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ)
      (0 : Fin 1)).toContinuousAffineMap
    univ
  exact (hproj.comp hvec (mapsTo_univ _ _)).congr fun _ _ => by simp

end TauCeti
