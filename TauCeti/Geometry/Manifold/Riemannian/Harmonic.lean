/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Integral.ConnectedComponent

/-!
# Harmonic functions on closed Riemannian manifolds

A real `C²` function with vanishing Laplace–Beltrami operator on a compact manifold without
boundary has zero gradient. On a preconnected manifold it is therefore constant, and two `C²`
functions with equal Laplacians and equal Riemannian integrals coincide
(`TauCeti.Manifold.eq_of_laplaceBeltrami_eq_of_integral_eq`). This is the energy argument for the
scalar-flat case of conformal metric rigidity and classical Poisson uniqueness: Green's first
identity gives zero Dirichlet energy, and the full support of Riemannian volume turns
almost-everywhere vanishing into pointwise vanishing.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2 (the Laplacian).
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

local instance instIsContinuousRiemannianBundleHarmonic :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)

/-- A harmonic `C²` function on a compact boundaryless Riemannian manifold has zero gradient.
No connectedness assumption is needed. -/
theorem mgradient_eq_zero_of_laplaceBeltrami_eq_zero {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hΔ : ∀ x, laplaceBeltrami I u x = 0) (x : M) :
    mgradient I u x = 0 := by
  have hcont : Continuous fun y ↦ ‖mgradient I u y‖ ^ 2 :=
    continuous_norm_sq_mgradient (hu.of_le one_le_two)
  have hint := integral_mul_laplaceBeltrami (hu.of_le one_le_two)
    (HasCompactSupport.of_compactSpace u) hu
  simp only [hΔ, mul_zero, integral_zero, real_inner_self_eq_norm_sq, zero_eq_neg] at hint
  have hae := (integral_eq_zero_iff_of_nonneg (fun y ↦ sq_nonneg ‖mgradient I u y‖)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint
  have hzero := congrFun ((hcont.ae_eq_iff_eq _ continuous_zero).mp hae) x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- A harmonic `C²` function on a preconnected compact boundaryless Riemannian manifold takes
the same value at any two points. -/
theorem apply_eq_of_laplaceBeltrami_eq_zero [PreconnectedSpace M] {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hΔ : ∀ x, laplaceBeltrami I u x = 0) (x y : M) :
    u x = u y := by
  apply (hu.mdifferentiable (by norm_num)).apply_eq_of_mfderiv_eq_zero _ x y
  intro z
  exact mvfderiv_eq_zero_iff.mp
    (mgradient_eq_zero_iff.mp (mgradient_eq_zero_of_laplaceBeltrami_eq_zero hu hΔ z))

/-- Two `C²` functions on a closed connected Riemannian manifold with a `C¹` metric that have the
same Laplace–Beltrami operator and the same Riemannian integral are equal. -/
theorem eq_of_laplaceBeltrami_eq_of_integral_eq [PreconnectedSpace M] {u v : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hv : ContMDiff I 𝓘(ℝ) 2 v)
    (hΔ : ∀ x, laplaceBeltrami I u x = laplaceBeltrami I v x)
    (hint : ∫ x, u x ∂riemannianVolume I M = ∫ x, v x ∂riemannianVolume I M) :
    u = v := by
  have : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  have hΔ0 : ∀ x, laplaceBeltrami I (u - v) x = 0 := fun x ↦ by
    rw [laplaceBeltrami_sub I hu hv, hΔ x, sub_self]
  have hconst : ∀ x y, (u - v) x = (u - v) y :=
    apply_eq_of_laplaceBeltrami_eq_zero (hu.sub hv) hΔ0
  have hlc : IsLocallyConstant (u - v) :=
    IsLocallyConstant.of_constant_on_connected_components fun x y _ ↦ (hconst x y).symm
  have hint0 : ∫ x, (u - v) x ∂riemannianVolume I M = 0 := by
    rw [Pi.sub_def, integral_sub
      (hu.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u))
      (hv.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)),
      hint, sub_self]
  ext x
  refine sub_eq_zero.1
    (hlc.apply_eq_zero_of_setIntegral_connectedComponent_eq_zero
      (measure_ne_top (riemannianVolume I M) _) ?_)
  simpa [PreconnectedSpace.connectedComponent_eq_univ x] using hint0

end TauCeti.Manifold
