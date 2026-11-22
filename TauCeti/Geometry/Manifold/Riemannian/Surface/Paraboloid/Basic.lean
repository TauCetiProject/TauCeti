/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Cartesian paraboloid graph

The Cartesian graph `F(x₀,x₁)=(x₀,x₁,x₀²+x₁²)` covers the vertex where polar
coordinates degenerate. This file works with
`paraboloidGraph : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)`:
it proves smoothness, closed embedding, and injectivity of the Fréchet derivative,
with `EuclideanSpace.take` as the left-inverse coordinate projection.
The pullback inner product is `⟪u,v⟫+4⟪x,u⟫⟪x,v⟫`, providing the Euclidean
calculation for the induced Riemannian metric on the paraboloid surface.

The formalization is by Yangyang Li, ported to Tau Ceti by Riccardo Brasca.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Chapter 2,
  §§2-2, 2-4, 2-5 (regular surfaces, differentials, and the first fundamental form).
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The global Cartesian graph of the paraboloid `z=x²+y²`. -/
def paraboloidGraph (x : V₂) : E₃ :=
  LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (by decide : 2 ≤ 3)) x +
    ‖x‖ ^ 2 • EuclideanSpace.basisFun (Fin 3) ℝ 2

@[simp]
theorem paraboloidGraph_apply_zero (x : V₂) : paraboloidGraph x 0 = x 0 := by
  have h := EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE
    (n := 3) (by decide) x (0 : Fin 2)
  norm_num [Fin.castLE] at h
  simpa [paraboloidGraph, EuclideanSpace.basisFun_apply] using h

@[simp]
theorem paraboloidGraph_apply_one (x : V₂) : paraboloidGraph x 1 = x 1 := by
  have h := EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE
    (n := 3) (by decide) x (1 : Fin 2)
  norm_num [Fin.castLE] at h
  simpa [paraboloidGraph, EuclideanSpace.basisFun_apply] using h

@[simp]
theorem paraboloidGraph_apply_two (x : V₂) : paraboloidGraph x 2 = ‖x‖ ^ 2 := by
  rw [paraboloidGraph, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.piLpExtendByZero_castLEEmb_apply_of_le (by decide : 2 ≤ 3) x
      (j := 2) (by decide)]
  norm_num [EuclideanSpace.basisFun_apply]

/-- The ambient coordinates of the Cartesian graph. -/
theorem paraboloidGraph_apply (x : V₂) :
    paraboloidGraph x = !₂[x 0, x 1, x 0 ^ 2 + x 1 ^ 2] := by
  ext i
  fin_cases i <;> simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Taking the first two coordinates is a left inverse of the Cartesian graph. -/
@[simp]
theorem take_paraboloidGraph (x : V₂) :
    EuclideanSpace.take (by decide : 2 ≤ 3) (paraboloidGraph x) = x := by
  ext i
  fin_cases i <;> simp

/-- The Cartesian graph is injective. -/
theorem paraboloidGraph_injective : Function.Injective paraboloidGraph :=
  Function.LeftInverse.injective take_paraboloidGraph

/-- The Cartesian graph is smooth at every differentiability order, including analytic order. -/
@[fun_prop]
theorem contDiff_paraboloidGraph {n : ℕ∞ω} : ContDiff ℝ n paraboloidGraph :=
  (LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (by decide : 2 ≤ 3))).contDiff.add
    ((contDiff_norm_sq ℝ).smul contDiff_const)

/-- The Cartesian graph is a closed topological embedding. -/
theorem isClosedEmbedding_paraboloidGraph : Topology.IsClosedEmbedding paraboloidGraph :=
  Function.LeftInverse.isClosedEmbedding take_paraboloidGraph
    (EuclideanSpace.continuous_take _) (contDiff_paraboloidGraph (n := 0)).continuous

/-- The Fréchet derivative of the Cartesian graph applied to a vector. -/
theorem fderiv_paraboloidGraph_apply (x w : V₂) :
    fderiv ℝ paraboloidGraph x w =
      LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (by decide : 2 ≤ 3)) w +
        (2 * inner ℝ x w) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  have h : HasFDerivAt paraboloidGraph
      ((LinearIsometry.piLpExtendByZero 2 ℝ ℝ
        (Fin.castLEEmb (by decide : 2 ≤ 3))).toContinuousLinearMap +
          (2 • innerSL ℝ x).smulRight (EuclideanSpace.basisFun (Fin 3) ℝ 2)) x :=
    (LinearIsometry.piLpExtendByZero 2 ℝ ℝ
      (Fin.castLEEmb (by decide : 2 ≤ 3))).toContinuousLinearMap.hasFDerivAt.add
        ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul_const
          (EuclideanSpace.basisFun (Fin 3) ℝ 2))
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, LinearIsometry.coe_toContinuousLinearMap]

@[simp]
theorem fderiv_paraboloidGraph_apply_zero (x w : V₂) :
    fderiv ℝ paraboloidGraph x w 0 = w 0 := by
  have h := EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE
    (n := 3) (by decide) w (0 : Fin 2)
  norm_num [Fin.castLE] at h
  simpa [fderiv_paraboloidGraph_apply, EuclideanSpace.basisFun_apply] using h

@[simp]
theorem fderiv_paraboloidGraph_apply_one (x w : V₂) :
    fderiv ℝ paraboloidGraph x w 1 = w 1 := by
  have h := EuclideanSpace.piLpExtendByZero_castLEEmb_apply_castLE
    (n := 3) (by decide) w (1 : Fin 2)
  norm_num [Fin.castLE] at h
  simpa [fderiv_paraboloidGraph_apply, EuclideanSpace.basisFun_apply] using h

@[simp]
theorem fderiv_paraboloidGraph_apply_two (x w : V₂) :
    fderiv ℝ paraboloidGraph x w 2 = 2 * inner ℝ x w := by
  rw [fderiv_paraboloidGraph_apply, PiLp.add_apply, PiLp.smul_apply,
    EuclideanSpace.piLpExtendByZero_castLEEmb_apply_of_le (by decide : 2 ≤ 3) w
      (j := 2) (by decide)]
  norm_num [EuclideanSpace.basisFun_apply]

/-- The ambient inner product of two images under the Fréchet derivative. -/
theorem inner_fderiv_paraboloidGraph (x w z : V₂) :
    inner ℝ (fderiv ℝ paraboloidGraph x w) (fderiv ℝ paraboloidGraph x z) =
      inner ℝ w z + 4 * inner ℝ x w * inner ℝ x z := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two, Real.inner_apply,
    fderiv_paraboloidGraph_apply_zero, fderiv_paraboloidGraph_apply_one,
    fderiv_paraboloidGraph_apply_two]
  ring

/-- The Fréchet derivative is injective at every point, including the vertex. -/
theorem fderiv_paraboloidGraph_injective (x : V₂) :
    Function.Injective (fderiv ℝ paraboloidGraph x) := by
  refine (injective_iff_map_eq_zero _).mpr fun w hw ↦ real_inner_self_nonpos.mp ?_
  have hi := inner_fderiv_paraboloidGraph x w w
  rw [hw, inner_zero_left] at hi
  nlinarith [sq_nonneg (inner ℝ x w)]

/-- The Cartesian vertex maps to the ambient origin. -/
@[simp]
theorem paraboloidGraph_zero : paraboloidGraph 0 = 0 := by
  simp [paraboloidGraph]

/-- The vertex differential is the horizontal plane inclusion. -/
theorem fderiv_paraboloidGraph_zero_apply (w : V₂) : fderiv ℝ paraboloidGraph 0 w =
    LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (by decide : 2 ≤ 3)) w := by
  simp [fderiv_paraboloidGraph_apply]

end TauCeti.Manifold
