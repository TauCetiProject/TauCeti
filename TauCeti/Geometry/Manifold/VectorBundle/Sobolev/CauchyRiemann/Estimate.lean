/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Estimate

/-!
# The elliptic estimate for smooth real Cauchy–Riemann operators on closed surfaces

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre, smooth as a real vector bundle, with a finite bundle atlas `A` (so
`M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves the elliptic estimate

`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`

for every `ξ ∈ W^{1,p}(Σ, V)`, where `D ξ` is the bounded realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)` and
`‖ξ‖_{Lᵖ}` is the norm of `ξ` in `W^{0,p}(Σ, V)`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`). The `Lᵖ` term
cannot be dropped: a nonzero element of the kernel of `D`, such as a constant function for `∂bar`
on the trivial line bundle, has `D ξ = 0`.

## The argument

This is the case `k = 0` of the elliptic estimate one order up,
`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`, since
the realization `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL` at order `0` is
`TauCeti.IsRealCauchyRiemannOperator.sobolevL`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL_zero`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`: the elliptic
  estimate on `W^{1,p}(Σ, V)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.2 (the elliptic estimate for real
  Cauchy–Riemann operators on closed surfaces) and Appendix B.4 (the interior Calderón–Zygmund
  estimate for `\bar∂`).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

section Global

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannEstimate : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- **The elliptic estimate for a smooth real Cauchy–Riemann operator on a closed surface.** Let
`D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a compact
boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < p < ∞`. There is a
constant `C` such that every `ξ ∈ W^{1,p}(Σ, V)` satisfies
`‖ξ‖_{W^{1,p}} ≤ C (‖D ξ‖_{Lᵖ} + ‖ξ‖_{Lᵖ})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevL` and `‖ξ‖_{Lᵖ}` is the norm of `ξ` in
`W^{0,p}(Σ, V)`. -/
theorem exists_norm_le_norm_sobolevL_add_norm (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p 1,
      ‖w‖ ≤ C * (‖hD.sobolevL A hDs volume p w‖ +
        ‖A.sectionChartData.lowerOrderL volume p 0 w‖) := by
  obtain ⟨C, hC⟩ := exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL A hD hDs hp hp_top 0
  exact ⟨C, fun w ↦ by simpa only [sobolevSuccL_zero] using hC w⟩

end IsRealCauchyRiemannOperator

end Global

end TauCeti
