/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Components of the covariant curvature derivative

In a smooth local tangent frame, write `Rⁱⱼₖₗ` for the components of `R` and `Γⁱₐⱼ`
for the connection coefficients. The components of `∇R` are

`(∇ₐR)ⁱⱼₖₗ = eₐ(Rⁱⱼₖₗ) + Σₘ Γⁱₐₘ Rᵐⱼₖₗ
  - Σₘ Γᵐₐⱼ Rⁱₘₖₗ - Σₘ Γᵐₐₖ Rⁱⱼₘₗ - Σₘ Γᵐₐₗ Rⁱⱼₖₘ`.

The formula uses the existing pointwise curvature derivative and the coefficient maps of
bundle trivializations. It applies to noncoordinate frames as well as coordinate frames,
without a metric or a torsion condition. All identities hold on the frame domain, including
boundary points. This reads the tensor used in curvature differentiation and metric jets
in terms of scalar functions and connection coefficients.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (covariant differentiation of tensors) and Chapter 7 (curvature).
* `CovariantDerivative.derivCurvatureTensor` and
  `TauCeti.Manifold.covariantDerivative_apply_localFrame_eq_sum` supply the intrinsic
  tensor and the local connection formula used here.
-/

public section

noncomputable section

open Bundle FiberBundle Module TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ E)
  (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M))
  [MemTrivializationAtlas e]

local notation "X" => e.localFrame b
local notation "Γ" => christoffelSymbol I b e cov
local notation "R" => fun i j k l y ↦
  e.localFrameCoeff I b l y (cov.curvatureTensor y (X i y) (X j y) (X k y))

/-- The component formula for the covariant derivative of curvature in a smooth local frame.
There is one positive connection correction for the output and one negative correction for
each of the three input slots. The frame need not be a coordinate frame. -/
theorem localFrameCoeff_derivCurvatureTensor {x : M} (hx : x ∈ e.baseSet)
    (a i j k l : ι) :
    e.localFrameCoeff I b l x
        (cov.derivCurvatureTensor cov x (X a x) (X i x) (X j x) (X k x)) =
      mvfderiv I (R i j k l) x (X a x) +
        ∑ m, R i j k m x * Γ a m l x -
        ∑ m, Γ a i m x * R m j k l x -
        ∑ m, Γ a j m x * R i m k l x -
        ∑ m, Γ a k m x * R i j m l x := by
  classical
  have hX (m : ι) : CMDiff[e.baseSet] ∞ (T% (X m)) :=
    e.contMDiffOn_localFrame_baseSet ∞ b m
  -- Local regularity is needed to differentiate the curvature section in this frame.
  have hcov := cov.contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) e.open_baseSet
  have hD {Y Z : Π y : M, TangentSpace I y}
      (hY : CMDiff[e.baseSet] ∞ (T% Y)) (hZ : CMDiff[e.baseSet] ∞ (T% Z)) :
      CMDiff[e.baseSet] ∞ (T% (fun y ↦ cov Z y (Y y))) :=
    (hcov.contMDiff hZ).clm_bundle_apply hY
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hbr : CMDiff[e.baseSet] ∞ (T% (VectorField.mlieBracket I (X i) (X j))) := by
    intro y hy
    exact ((hX i |>.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
      (hX j |>.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (by simp)).contMDiffWithinAt
  have hRop : CMDiff[e.baseSet] ∞ (T% (curvatureOperator cov (X i) (X j) (X k))) := by
    simpa only [curvatureOperator_apply, Pi.sub_apply] using
      ((hD (hX i) (hD (hX j) (hX k))).sub_section
        (hD (hX j) (hD (hX i) (hX k)))).sub_section (hD hbr (hX k))
  let S : Π y : M, TangentSpace I y :=
    fun y ↦ cov.curvatureTensor y (X i y) (X j y) (X k y)
  have hS : CMDiff[e.baseSet] ∞ (T% S) := by
    apply hRop.congr
    intro y hy
    exact congrArg (TotalSpace.mk' E y)
      (cov.curvatureTensor_apply_of_contMDiffOn y e.open_baseSet hy
        (hX i) (hX j) (hX k))
  have heq : ∀ᶠ y in 𝓝 x, curvatureOperator cov (X i) (X j) (X k) y = S y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact (cov.curvatureTensor_apply_of_contMDiffOn y e.open_baseSet hy
      (hX i) (hX j) (hX k)).symm
  have hdS := (hS.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdR := (hRop.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  -- Expand the output derivative and the three input derivatives in the same frame.
  rw [cov.derivCurvatureTensor_apply_of_contMDiffOn cov x e.open_baseSet hx (X a x)
    (hX i) (hX j) (hX k),
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hdR hdS Filter.univ_mem heq,
    covariantDerivative_apply_localFrame_eq_sum b cov.isCovariantDerivativeOn hx hdS a,
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b a i,
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b a j,
    covariantDerivative_localFrame_eq_sum_christoffelSymbol b a k]
  simp [map_sub, map_sum, map_smul, localFrameCoeff_localFrame b hx, S]

end CovariantDerivative
