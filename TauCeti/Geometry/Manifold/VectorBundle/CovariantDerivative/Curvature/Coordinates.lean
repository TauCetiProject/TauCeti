/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# Curvature in a coordinate frame

The `l`-th coefficient of `R(∂ᵢ, ∂ⱼ)∂ₖ` is
`∂ᵢΓˡⱼₖ - ∂ⱼΓˡᵢₖ + ∑ₘ (Γᵐⱼₖ Γˡᵢₘ - Γᵐᵢₖ Γˡⱼₘ)`.
The first two arguments are the curvature directions, the third is the vector being
differentiated, and the last index is the output coefficient.

Both the vector-valued expansion and its scalar coefficients are provided. They use the
existing tangent trivialization and `TauCeti.Manifold.christoffelSymbol`, so an explicit
metric's Christoffel calculation can be substituted directly to compute its curvature.
Only `C¹` regularity of the connection on the chosen chart is required. The manifold is
`C³` over the real or complex numbers, and analytic over other complete normed fields,
as prescribed by `minSmoothness`. No metric or torsion hypothesis is needed. The formulas
hold on chart sources, including boundary points.

The sign convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7, pp. 196–198:
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

namespace CovariantDerivative

open TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (minSmoothness 𝕜 3) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E) (x₀ : M)

local notation "e" => trivializationAt E (TangentSpace I) x₀
variable [ContMDiffCovariantDerivativeOn E 1 cov.toFun
  (trivializationAt E (TangentSpace I) x₀).baseSet]

local notation "Γ" => christoffelSymbol I b e cov
local notation "X" => Bundle.Trivialization.localFrame (trivializationAt E (TangentSpace I) x₀) b

/-- The coordinate expansion of `R(∂ᵢ, ∂ⱼ)∂ₖ`. Its coefficients are the difference of
the directional derivatives of the Christoffel symbols plus their quadratic contraction.
This is valid for any `C¹` connection, without a metric or a torsion hypothesis. -/
theorem curvatureOperator_localFrame_eq_sum {x : M}
    (hx : x ∈ (extChartAt I x₀).source) (i j k : ι) :
    cov.curvatureOperator (X i) (X j) (X k) x =
      ∑ l, (mvfderiv I (Γ j k l) x (X i x) - mvfderiv I (Γ i k l) x (X j x) +
        ∑ m, (Γ j k m x * Γ i m l x - Γ i k m x * Γ j m l x)) • X l x := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hbase : x ∈ (e).baseSet := by simpa using hx
  have : IsManifold I ((2 : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := minSmoothness 𝕜 3)
      (le_trans (by norm_num) (le_minSmoothness (𝕜 := 𝕜)))
  have : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hframe (l : ι) : CMDiff[(e).baseSet] 2 (T% (X l)) :=
    (e).contMDiffOn_localFrame_baseSet 2 b l
  have hcovFrame (a c : ι) :
      CMDiff[(e).baseSet] 1 (T% (fun y => cov (X c) y (X a y))) := by
    have hclm : ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) 1
        (fun y => TotalSpace.mk' (E →L[𝕜] E) y (cov (X c) y)) (e).baseSet :=
      ContMDiffCovariantDerivativeOn.contMDiff (hframe c)
    exact ContMDiffOn.clm_bundle_apply hclm ((hframe a).of_le one_le_two)
  have hdiff (a c : ι) : MDiffAt (T% (fun y => cov (X c) y (X a y))) x :=
    ((hcovFrame a c).contMDiffAt ((e).open_baseSet.mem_nhds hbase)).mdifferentiableAt
      one_ne_zero
  have hfirst := covariantDerivative_apply_localFrame_eq_sum b
    cov.isCovariantDerivativeOn hbase (hdiff j k) i
  have hsecond := covariantDerivative_apply_localFrame_eq_sum b
    cov.isCovariantDerivativeOn hbase (hdiff i k) j
  -- The coefficient functions of these differentiated frame sections are exactly Γ.
  simp only [LinearMap.piApply_apply, ← christoffelSymbol_apply] at hfirst hsecond
  have : IsManifold I (minSmoothness 𝕜 2) M :=
    IsManifold.of_le (n := minSmoothness 𝕜 3)
      (minSmoothness_monotone (𝕜 := 𝕜) (by norm_num))
  rw [curvatureOperator_apply, mlieBracket_localFrame_trivializationAt b x₀ hx i j,
    map_zero, sub_zero, hfirst, hsecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← sub_smul]
  congr 1
  rw [Finset.sum_sub_distrib]
  ring

/-- The scalar coordinate formula for `R(∂ᵢ, ∂ⱼ)∂ₖ`, in the output component `l`.
The order of the indices agrees with `christoffelSymbol`: `Γ i k l` is the `l`-th
component of `∇_{∂ᵢ} ∂ₖ`. -/
theorem localFrameCoeff_curvatureOperator {x : M}
    (hx : x ∈ (extChartAt I x₀).source) (i j k l : ι) :
    (e).localFrameCoeff I b l x (cov.curvatureOperator (X i) (X j) (X k) x) =
      mvfderiv I (Γ j k l) x (X i x) - mvfderiv I (Γ i k l) x (X j x) +
        ∑ m, (Γ j k m x * Γ i m l x - Γ i k m x * Γ j m l x) := by
  classical
  have hbase : x ∈ (e).baseSet := by simpa using hx
  rw [curvatureOperator_localFrame_eq_sum cov b x₀ hx i j k]
  simp [localFrameCoeff_localFrame b hbase]

end CovariantDerivative
