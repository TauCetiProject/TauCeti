/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
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
Invertibility is needed at the point in the local theorem and throughout the domain in the
setwise theorem; finite-dimensional nondegeneracy supplies it in the companion forms.
Symmetry is unnecessary for regularity; no signature or positivity is assumed.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J 1 P]
  {g : P → E → E →L[ℝ] E →L[ℝ] ℝ} {m n : ℕ∞ω} {z : P × E}

section Complete

variable [CompleteSpace E]

/-- The Christoffel symbols of a `C^m` family of invertible bilinear forms are jointly `C^n`
in parameter and base point at every invertible point, for `n + 1 ≤ m`. -/
theorem _root_.ContMDiffAt.christoffelSecondKind_family
    (hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) (hinv : (g z.1 z.2).IsInvertible) :
    ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) z := by
  -- Fix the canonical target-space instances before synthesizing the derivative-space layer.
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  simpa only [christoffelSecondKind_def, Function.comp_def] using
    (ContinuousLinearMap.IsInvertible.contDiffAt_christoffelSecondKindOfJet
      (j := (g z.1 z.2, fderiv ℝ (g z.1) z.2))
      hinv).comp_contMDiffAt
      (f := fun q : P × E ↦ (g q.1 q.2, fderiv ℝ (g q.1) q.2))
      ((hg.of_le (le_self_add.trans hnm)).prodMk_space (hg.fderiv_right hnm))

/-- On an open parameter/base domain, the Christoffel symbols of a `C^m` invertible family
are jointly `C^n`, for `n + 1 ≤ m`. No product decomposition of the domain is required. -/
theorem _root_.ContMDiffOn.christoffelSecondKind_family {U : Set (P × E)}
    (hg : ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) U) (hU : IsOpen U)
    (hnm : n + 1 ≤ m) (hinv : ∀ q ∈ U, (g q.1 q.2).IsInvertible) :
    ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) U :=
  fun q hq ↦ ((hg.contMDiffAt (hU.mem_nhds hq)).christoffelSecondKind_family hnm
    (hinv q hq)).contMDiffWithinAt

/-- A globally `C^m` family of invertible bilinear forms has jointly `C^n` Christoffel symbols,
for `n + 1 ≤ m`. In particular, a smooth family has smooth Christoffel symbols. -/
theorem _root_.ContMDiff.christoffelSecondKind_family
    (hg : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g))
    (hnm : n + 1 ≤ m) (hinv : ∀ p x, (g p x).IsInvertible) :
    ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) :=
  fun q ↦ (hg q).christoffelSecondKind_family hnm (hinv q.1 q.2)

end Complete

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- In finite dimension, nondegeneracy suffices for joint Christoffel regularity at a point. -/
theorem _root_.ContMDiffAt.christoffelSecondKind_family_of_nondegenerate
    (hg : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) z)
    (hnm : n + 1 ≤ m) (hnd : (g z.1 z.2).toBilinForm.Nondegenerate) :
    ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) z :=
  hg.christoffelSecondKind_family hnm (isInvertible_of_separatingLeft hnd.1)

/-- A finite-dimensional nondegenerate family has joint Christoffel regularity on its open
parameter/base domain. -/
theorem _root_.ContMDiffOn.christoffelSecondKind_family_of_nondegenerate {U : Set (P × E)}
    (hg : ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g) U) (hU : IsOpen U)
    (hnm : n + 1 ≤ m) (hnd : ∀ q ∈ U, (g q.1 q.2).toBilinForm.Nondegenerate) :
    ContMDiffOn (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) U :=
  hg.christoffelSecondKind_family hU hnm fun q hq ↦ isInvertible_of_separatingLeft (hnd q hq).1

/-- A finite-dimensional globally nondegenerate family has globally joint Christoffel regularity.
-/
theorem _root_.ContMDiff.christoffelSecondKind_family_of_nondegenerate
    (hg : ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) m
      (Function.uncurry g))
    (hnm : n + 1 ≤ m) (hnd : ∀ p x, (g p x).toBilinForm.Nondegenerate) :
    ContMDiff (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) n
      (fun q : P × E ↦ christoffelSecondKind (g q.1) q.2) :=
  hg.christoffelSecondKind_family hnm fun p x ↦ isInvertible_of_separatingLeft (hnd p x).1

end FiniteDimensional

end TauCeti.Manifold
