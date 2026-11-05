/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Curvature in a moving frame

For a local frame `s` write `Aˡⱼ(X)` for the coefficient of `∇_X sⱼ` along `sₗ`.
The coefficients of curvature in this frame are

`Rˡⱼ(X,Y) = X(Aˡⱼ(Y)) - Y(Aˡⱼ(X)) - Aˡⱼ([X,Y])`
`  + Σₘ (Aˡₘ(X) Aᵐⱼ(Y) - Aˡₘ(Y) Aᵐⱼ(X))`.

Thus, with section coefficients read as columns, the matrix convention is `F = dA + A∧A`.
The Lie bracket term is retained: neither the frame nor the direction fields need be coordinate
fields. On the tangent bundle, expanding that bracket gives the usual structure-coefficient
correction to the coordinate curvature formula. These formulas allow curvature computations in
orthonormal and other noncoordinate frames using the native `IsLocalFrameOn` and its coefficients.

Only a C² frame, a C¹ connection on its open domain and C¹ direction fields are required.
No metric or torsion condition is imposed, and the bundle need not be the tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (curvature in local frames).
* The local differentiation formula extends
  `TauCeti.Manifold.covariantDerivative_eq_frameCovariantDerivative_add_sum` from
  trivialization frames to arbitrary local frames; coefficient regularity uses
  `IsLocalFrameOn.trivialization_mem_maximalAtlas`.
-/

public section

open Bundle CovariantDerivative Set VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace IsLocalFrameOn

section Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 2 F V I]
  {ι : Type*} [Fintype ι] {s : ι → Π x, V x} {u : Set M}
  (hs : IsLocalFrameOn I F 2 s u) (hu : IsOpen u)
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivativeOn F 1 cov.toFun u]
  {X Y : Π x : M, TangentSpace I x} {x : M}

-- The input frame index precedes the output coefficient, as in the existing Christoffel symbols.
local notation "A" => fun j l Z y ↦
  hs.coeff l y (cov (s j) y (Z y))

include hu in
/-- The curvature matrix in a C² moving frame is `dA + A∧A`, evaluated on arbitrary C¹
vector fields. The exterior derivative includes the noncoordinate term `-A([X,Y])`. -/
theorem coeff_curvatureOperator (hx : x ∈ u)
    (hX : CMDiff[u] 1 (T% X)) (hY : CMDiff[u] 1 (T% Y)) (j l : ι) :
    hs.coeff l x (cov.curvatureOperator X Y (s j) x) =
      mvfderiv I (A j l Y) x (X x) - mvfderiv I (A j l X) x (Y x) +
        ∑ m, (A j m Y x * A m l X x - A j m X x * A m l Y x) -
          hs.coeff l x (cov (s j) x (mlieBracket I X Y x)) := by
  classical
  let : ContMDiffVectorBundle 1 F V I := ContMDiffVectorBundle.of_le one_le_two
  have hcov (Z : Π y : M, TangentSpace I y) (hZ : CMDiff[u] 1 (T% Z)) :
      CMDiff[u] 1 (T% (fun y ↦ cov (s j) y (Z y))) :=
    ContMDiffOn.clm_bundle_apply
      (ContMDiffCovariantDerivativeOn.contMDiff (hs.contMDiffOn j)) hZ
  have hcoeff (Z : Π y : M, TangentSpace I y) (hZ : CMDiff[u] 1 (T% Z)) (k : ι) :
      MDiffAt (A j k Z) x :=
    ((hs.contMDiffOn_coeff hu one_le_two (hcov Z hZ) k).contMDiffAt
      (hu.mem_nhds hx)).mdifferentiableAt one_ne_zero
  have hfirst := hs.covariantDerivative_eq_sum one_le_two (hu.mem_nhds hx)
    (cov.isCovariantDerivativeOn (s := u)) (hcoeff Y hY)
  have hsecond := hs.covariantDerivative_eq_sum one_le_two (hu.mem_nhds hx)
    (cov.isCovariantDerivativeOn (s := u)) (hcoeff X hX)
  rw [curvatureOperator_apply, hfirst, hsecond]
  simp only [sum_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, map_sub, map_sum,
    map_add, map_smul, smul_eq_mul]
  have hdual (k : ι) : hs.coeff l x (s k x) = if k = l then 1 else 0 := by
    rw [IsLocalFrameOn.coeff, dite_eq_left hx, Module.Basis.coord_apply,
      ← hs.toBasisAt_coe hx k, Module.Basis.repr_self_apply]
  simp only [hdual]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_sub_distrib]
  ring

end Bundle

section Tangent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  {ι : Type*} [Fintype ι] {s : ι → Π x : M, TangentSpace I x} {u : Set M}
  (hs : IsLocalFrameOn I E 2 s u) (hu : IsOpen u)
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivativeOn E 1 cov.toFun u] {x : M}

local notation "Γ" => fun i j l y ↦ hs.coeff l y (cov (s j) y (s i y))

include hu in
/-- The curvature coefficients in a C² tangent frame, with the Lie bracket expanded in the
same frame. Its structure coefficients supply the correction absent from a coordinate frame. -/
theorem coeff_curvatureOperator_frame (hx : x ∈ u) (i j k l : ι) :
    hs.coeff l x (cov.curvatureOperator (s i) (s j) (s k) x) =
      mvfderiv I (Γ j k l) x (s i x) - mvfderiv I (Γ i k l) x (s j x) +
        ∑ m, (Γ j k m x * Γ i m l x - Γ i k m x * Γ j m l x) -
          ∑ m, hs.coeff m x (mlieBracket I (s i) (s j) x) * Γ m k l x := by
  have : IsManifold I (2 + 1) M := IsManifold.of_le (n := 3) (by norm_num)
  let : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  rw [hs.coeff_curvatureOperator hu cov hx ((hs.contMDiffOn i).of_le one_le_two)
    ((hs.contMDiffOn j).of_le one_le_two)]
  congr 1
  conv_lhs => rw [hs.coeff_sum_eq (mlieBracket I (s i) (s j)) hx]
  simp only [map_sum, map_smul, smul_eq_mul]

end Tangent

end IsLocalFrameOn
