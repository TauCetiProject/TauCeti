/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Joint regularity of Christoffel symbols in metric families

For a family of nondegenerate bilinear forms `g p x` in linear coordinates, the Christoffel
symbols of `g p` depend jointly on the parameter `p` and the base point `x`. The parameter may
range over an arbitrary smooth manifold. Only the base direction is differentiated when forming
the Christoffel symbols. For symmetric forms these are the coefficients of the individual
Levi-Civita connections.

The results apply on open subsets of the parameter/base product, as required for families of
metrics read in local charts. A `C^m` family has `C^n` Christoffel symbols when `n + 1 ≤ m`.
Nondegeneracy is needed at the point in the local theorem and throughout the domain in the
setwise theorem. Symmetry is unnecessary for regularity; no signature or positivity is assumed.

Joint regularity of `christoffelSecondKind` supplies the local analytic input for smooth
families of Levi-Civita connections.

## Formal sources

* Tau Ceti's `christoffelSecondKind`.
* Mathlib's `ContMDiffAt.mfderiv` and smooth inversion of continuous linear maps.

## References

* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press (1983),
  Chapter 3, the coordinate formula for the Levi-Civita connection.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → E →L[ℝ] E →L[ℝ] ℝ} {m n : ℕ∞ω} {z : P × E}

/-- The Christoffel symbols of a `C^m` family of nondegenerate bilinear forms are jointly `C^n`
in parameter and base point at every nondegenerate point, for `n + 1 ≤ m`. -/
theorem contMDiffAt_christoffelSecondKind_family
    (hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) (hnd : (g z.1 z.2).toBilinForm.Nondegenerate) :
    ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) z := by
  -- Fix the canonical target-space instances before synthesizing the derivative-space layer.
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  simpa only [christoffelSecondKind_eq_christoffelSecondKindOfJet, Function.comp_def] using
    (contDiffAt_christoffelSecondKindOfJet (j := (g z.1 z.2, fderiv ℝ (g z.1) z.2))
      (isInvertible_of_separatingLeft hnd.1)).comp_contMDiffAt
      (f := fun q : P × E ↦ (g q.1 q.2, fderiv ℝ (g q.1) q.2))
      ((hg.of_le (le_self_add.trans hnm)).prodMk_space (contMDiffAt_fderiv_family hg hnm))

/-- On an open parameter/base domain, the Christoffel symbols of a `C^m` nondegenerate family
are jointly `C^n`, for `n + 1 ≤ m`. No product decomposition of the domain is required. -/
theorem contMDiffOn_christoffelSecondKind_family {U : Set (P × E)} (hU : IsOpen U)
    (hg : ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) U)
    (hnm : n + 1 ≤ m) (hnd : ∀ q ∈ U, (g q.1 q.2).toBilinForm.Nondegenerate) :
    ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) U :=
  fun q hq ↦ (contMDiffAt_christoffelSecondKind_family
    (hg.contMDiffAt (hU.mem_nhds hq)) hnm (hnd q hq)).contMDiffWithinAt

/-- A globally `C^m` nondegenerate metric family has globally joint `C^n` Christoffel symbols,
for `n + 1 ≤ m`. In particular, a smooth family has smooth Christoffel symbols. -/
theorem contMDiff_christoffelSecondKind_family
    (hg : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g))
    (hnm : n + 1 ≤ m) (hnd : ∀ p x, (g p x).toBilinForm.Nondegenerate) :
    ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) :=
  fun q ↦ contMDiffAt_christoffelSecondKind_family (hg q) hnm (hnd q.1 q.2)

end TauCeti.Manifold
