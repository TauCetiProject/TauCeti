/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Pointwise and Hölder bounds for the Laplacian

On a finite-dimensional real inner product space `E` of dimension `n`, the Laplacian
`Δ f x = ∑ᵢ D²f x (eᵢ, eᵢ)` is a sum of `n` evaluations of the second derivative on unit
vectors. Hence it is controlled by the second derivative:

* `‖Δ f x‖ ≤ n ‖D²f x‖`;
* `‖Δ f x - Δ f y‖ ≤ n ‖D²f x - D²f y‖`, so if `D²f` is `α`-Hölder with constant `C`, then
  `Δ f` is `α`-Hölder with constant `n C`.

These bounds hold for every function, with Mathlib's totalized iterated derivative. They control
the Laplacian in Hölder norms, as needed for Schauder theory, where the data of the heat equation
`∂ₜu = Δu` are measured in `C^{2,α}` and its time derivative in `C^α`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sum of the diagonal values of a bilinear map on the standard orthonormal basis is at most
the dimension times its norm. -/
private theorem norm_sum_apply_stdOrthonormalBasis_le
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) :
    ‖∑ i, A ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]‖ ≤ finrank ℝ E * ‖A‖ := by
  calc ‖∑ i, A ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]‖
      ≤ ∑ i, ‖A ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ E), ‖A‖ :=
        Finset.sum_le_sum fun i _ => (A.le_opNorm _).trans_eq (by simp [Fin.prod_univ_two])
    _ = finrank ℝ E * ‖A‖ := by simp

/-- **The Laplacian is bounded by the second derivative.** In dimension `n`,
`‖Δ f x‖ ≤ n ‖D²f x‖`. -/
theorem norm_laplacian_le (f : E → F) (x : E) :
    ‖Δ f x‖ ≤ finrank ℝ E * ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact norm_sum_apply_stdOrthonormalBasis_le _

/-- The difference of two values of the Laplacian is bounded by the difference of the second
derivatives: `‖Δ f x - Δ f y‖ ≤ n ‖D²f x - D²f y‖` in dimension `n`. -/
theorem norm_laplacian_sub_laplacian_le (f : E → F) (x y : E) :
    ‖Δ f x - Δ f y‖ ≤ finrank ℝ E * ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, ← Finset.sum_sub_distrib]
  simpa only [sub_apply] using
    norm_sum_apply_stdOrthonormalBasis_le (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y)

/-- **Hölder continuity of the Laplacian.** If the second derivative of `f` is `α`-Hölder with
constant `C`, then `Δ f` is `α`-Hölder with constant `n C`, where `n` is the dimension. -/
theorem holderWith_laplacian {C α : NNReal} {f : E → F}
    (hf : HolderWith C α (iteratedFDeriv ℝ 2 f)) :
    HolderWith (finrank ℝ E * C) α (Δ f) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ => ?_
  rw [dist_eq_norm, NNReal.coe_mul, NNReal.coe_natCast, mul_assoc]
  refine (norm_laplacian_sub_laplacian_le f x y).trans ?_
  gcongr
  rw [← dist_eq_norm]
  exact hf.dist_le x y

end TauCeti
