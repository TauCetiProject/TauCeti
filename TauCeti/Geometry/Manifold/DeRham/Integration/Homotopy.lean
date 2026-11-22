/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.HomotopyInvariance
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
public import Mathlib.Topology.Homotopy.Contractible
import TauCeti.Geometry.Manifold.SmoothApprox

/-!
# Integrals of closed forms along homotopic maps

Let `M` be a compact oriented boundaryless manifold of dimension `n`. Integration on top de Rham
cohomology, `∫_M : H^n_dR(M) → ℝ` (`TauCeti.deRhamCohomology.integral`), is computed on the class
of a closed form by integrating the form (`TauCeti.deRhamCohomology.integral_mk`). Since homotopic
smooth maps induce the same map on de Rham cohomology, the integral of the pullback of a closed form
along a map out of `M` only depends on the homotopy class of the map. For a closed `n`-form `φ` on
a manifold `N` of any dimension and smooth maps `f g : M → N`,

`∫_M f^*φ = ∫_M g^*φ`

as soon as `f` and `g` are joined by a smooth homotopy
(`TauCeti.integralTopForm_mpullback_eq_of_homotopy`), or merely by a continuous one when `N` is a
finite-dimensional Hausdorff manifold without boundary points
(`TauCeti.integralTopForm_mpullback_eq_of_homotopic`): Whitney approximation replaces a continuous
homotopy between smooth maps out of the compact `M` by a smooth one
(`ContinuousMap.Homotopic.exists_contMDiff_homotopy_Icc`). The pullback of a form of positive
degree along a constant map vanishes (`TauCeti.mpullback_const`), so for such `N` a null-homotopic
smooth map pulls every closed form of positive degree back to a form of integral zero
(`TauCeti.integralTopForm_mpullback_eq_zero_of_nullhomotopic`). Contrapositively, a smooth map
pulling some closed form of positive degree back to a form of nonzero integral is not
null-homotopic (`TauCeti.not_nullhomotopic_of_integralTopForm_mpullback_ne_zero`).

This is the de Rham obstruction by which Barraud, Damian, Humilière and Oancea detect higher
homotopy of compact Lie groups: the bi-invariant Cartan three-form of a compact semisimple group
pulls back along a root homomorphism `SU(2) → K` to a nowhere-vanishing top form of `SU(2) ≅ S³`,
whose integral is nonzero, so the root homomorphism represents a nonzero element of `π₃(K)`.

## Main results

* `TauCeti.integralTopForm_mpullback_eq_of_homotopy`: smoothly homotopic maps pull a closed form
  back to forms with the same integral.
* `TauCeti.integralTopForm_mpullback_eq_of_homotopic`: the same for smooth maps joined by a
  continuous homotopy, into a finite-dimensional Hausdorff manifold without boundary points.
* `TauCeti.integralTopForm_mpullback_eq_zero_of_nullhomotopic` and
  `TauCeti.not_nullhomotopic_of_integralTopForm_mpullback_ne_zero`: a null-homotopic smooth map
  into a finite-dimensional Hausdorff manifold without boundary points pulls closed forms of
  positive degree back to forms of integral zero.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17 (homotopy invariance of de
  Rham cohomology) and Theorem 6.29 (smooth homotopies between homotopic smooth maps).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, proof of Proposition 6.31.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ}

/-- **Integrals of closed forms along smoothly homotopic maps.** Let `M` be a compact oriented
boundaryless manifold of dimension `n` and `φ` a closed smooth `n`-form on a manifold `N`. If
`F : M × [0, 1] → N` is a smooth homotopy from `f` to `g`, then `∫_M f^*φ = ∫_M g^*φ`. -/
theorem integralTopForm_mpullback_eq_of_homotopy [IsManifold I' 2 N]
    (o : Manifold.Orientation I M (Fin n)) {f g : M → N} (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I I' ∞ g) {F : M × Icc (0 : ℝ) 1 → N}
    (hF : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ F) (h₀ : ∀ x, F (x, 0) = f x)
    (h₁ : ∀ x, F (x, 1) = g x) {φ : SmoothForm I' N ℝ n} (hφ : φ ∈ closedForms I' N n) :
    integralTopForm o (mpullback I I' f φ.val) = integralTopForm o (mpullback I I' g φ.val) := by
  have h := congrArg (deRhamCohomology.integral o) (LinearMap.congr_fun
    (deRhamCohomology.map_eq_of_homotopy hf hg hF h₀ h₁ n) (deRhamCohomology.mk I' n ⟨φ, hφ⟩))
  simpa only [deRhamCohomology.map_mk, deRhamCohomology.integral_mk, closedForms.coe_mpullback,
    SmoothForm.coe_mpullback] using h

/-- **Integrals of closed forms along homotopic maps.** Let `M` be a compact oriented boundaryless
manifold of dimension `n` and `φ` a closed smooth `n`-form on a finite-dimensional Hausdorff
manifold `N` without boundary points. If two smooth maps `f g : M → N` are homotopic, then
`∫_M f^*φ = ∫_M g^*φ`. The homotopy need not be smooth: by Whitney approximation, homotopic smooth
maps out of the compact `M` are smoothly homotopic. -/
theorem integralTopForm_mpullback_eq_of_homotopic [FiniteDimensional ℝ E'] [IsManifold I' ∞ N]
    [BoundarylessManifold I' N] [T2Space N] (o : Manifold.Orientation I M (Fin n))
    {f g : C(M, N)} (hf : ContMDiff I I' ∞ f) (hg : ContMDiff I I' ∞ g) (h : f.Homotopic g)
    {φ : SmoothForm I' N ℝ n} (hφ : φ ∈ closedForms I' N n) :
    integralTopForm o (mpullback I I' f φ.val) = integralTopForm o (mpullback I I' g φ.val) := by
  obtain ⟨F, hF, hF₀, hF₁⟩ := h.exists_contMDiff_homotopy_Icc ⊤ hf hg
  exact integralTopForm_mpullback_eq_of_homotopy o hf hg hF hF₀ hF₁ hφ

/-- **A null-homotopic map pulls closed forms back to forms of integral zero.** Let `M` be a
compact oriented boundaryless manifold of dimension `n + 1` and `φ` a closed smooth `(n + 1)`-form
on a finite-dimensional Hausdorff manifold `N` without boundary points. If a smooth map
`f : M → N` is null-homotopic, then `∫_M f^*φ = 0`. -/
theorem integralTopForm_mpullback_eq_zero_of_nullhomotopic [FiniteDimensional ℝ E']
    [IsManifold I' ∞ N] [BoundarylessManifold I' N] [T2Space N]
    (o : Manifold.Orientation I M (Fin (n + 1))) {f : C(M, N)} (hf : ContMDiff I I' ∞ f)
    (h : f.Nullhomotopic) {φ : SmoothForm I' N ℝ (n + 1)} (hφ : φ ∈ closedForms I' N (n + 1)) :
    integralTopForm o (mpullback I I' f φ.val) = 0 := by
  obtain ⟨y, h⟩ := h
  rw [integralTopForm_mpullback_eq_of_homotopic (g := ContinuousMap.const M y) o hf
    contMDiff_const h hφ, ContinuousMap.coe_const, ← Function.const_def,
    mpullback_const n.succ_ne_zero, integralTopForm_zero]

/-- **A map pulling a closed form back to a form of nonzero integral is not null-homotopic.** Let
`M` be a compact oriented boundaryless manifold of dimension `n + 1` and `φ` a closed smooth
`(n + 1)`-form on a finite-dimensional Hausdorff manifold `N` without boundary points. If a smooth
map `f : M → N` satisfies `∫_M f^*φ ≠ 0`, then `f` is not null-homotopic. -/
theorem not_nullhomotopic_of_integralTopForm_mpullback_ne_zero [FiniteDimensional ℝ E']
    [IsManifold I' ∞ N] [BoundarylessManifold I' N] [T2Space N]
    (o : Manifold.Orientation I M (Fin (n + 1))) {f : C(M, N)} (hf : ContMDiff I I' ∞ f)
    {φ : SmoothForm I' N ℝ (n + 1)} (hφ : φ ∈ closedForms I' N (n + 1))
    (hne : integralTopForm o (mpullback I I' f φ.val) ≠ 0) : ¬f.Nullhomotopic :=
  fun h ↦ hne (integralTopForm_mpullback_eq_zero_of_nullhomotopic o hf h hφ)

end TauCeti
