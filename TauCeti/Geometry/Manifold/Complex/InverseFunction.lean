/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The holomorphic inverse function theorem on complex manifolds

A map between finite-dimensional complex manifolds which is holomorphic near a point and whose
complex differential there is invertible is a local biholomorphism at that point: a local
diffeomorphism of class `C^n` for every `n`, including complex analytic regularity `ω`. The
complex manifolds need only be of class `C¹`, since their atlases are then complex analytic.

The conclusion is Mathlib's `IsLocalDiffeomorphAt`, so its local inverse
`IsLocalDiffeomorphAt.localInverse` is holomorphic, the differential of that inverse is the
inverse of the differential (`IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`), and local
biholomorphisms compose (`IsLocalDiffeomorphAt.comp`). A holomorphic bijection with invertible
differentials is a biholomorphism through `IsLocalDiffeomorph.diffeomorphOfBijective`.

## Main declarations

* `MDifferentiableOn.isLocalDiffeomorphAt_of_mfderiv_eq` and
  `MDifferentiableOn.isLocalDiffeomorphAt_of_bijective_mfderiv`: the holomorphic inverse function
  theorem at a point.
* `MDifferentiableOn.isLocalDiffeomorphAt_iff_bijective_mfderiv`: at an interior point of a
  holomorphy domain, being a local biholomorphism is bijectivity of the differential.
* `MDifferentiable.isLocalDiffeomorph_of_bijective_mfderiv`: the global form.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I, §B (the holomorphic inverse function theorem).
-/

public section

open Function Set
open scoped ContDiff Manifold Topology

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {f : M → N} {s : Set M} {x : M} {n : ℕ∞ω}

namespace MDifferentiableOn

/-- **The holomorphic inverse function theorem on complex manifolds.** A map holomorphic on a
neighbourhood of a point, whose complex differential there is a continuous linear equivalence,
is a local biholomorphism there, of class `C^n` for every `n`, including `n = ω`. The target model
is finite-dimensional because the differential is an equivalence. -/
theorem isLocalDiffeomorphAt_of_mfderiv_eq (hf : MDifferentiableOn I J f s) (hs : s ∈ 𝓝 x)
    {e : TangentSpace I x ≃L[ℂ] TangentSpace J (f x)}
    (he : (e : TangentSpace I x →L[ℂ] TangentSpace J (f x)) = mfderiv I J f x) :
    IsLocalDiffeomorphAt I J n f x := by
  have : FiniteDimensional ℂ F :=
    ((e.symm.trans (tangentSpaceCastModel I x)).symm.trans
      (tangentSpaceCastModel J (f x))).toLinearEquiv.finiteDimensional
  have := FiniteDimensional.completeSpace ℂ E
  have := FiniteDimensional.completeSpace ℂ F
  have : IsManifold I ω M := .of_ne_zero ω one_ne_zero inferInstance
  have : IsManifold J ω N := .of_ne_zero ω one_ne_zero inferInstance
  -- work on the open interior of `s`, which contains `x`
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω)
    ((hf.mono interior_subset).contMDiffOn isOpen_interior) isOpen_interior
    (mem_interior_iff_mem_nhds.2 hs) BoundarylessManifold.isInteriorPoint le_top he).of_le le_top

/-- **The holomorphic inverse function theorem on complex manifolds**, with a bijective
differential. A map holomorphic on a neighbourhood of a point, whose complex differential there is
bijective, is a local biholomorphism there, of class `C^n` for every `n`. -/
theorem isLocalDiffeomorphAt_of_bijective_mfderiv (hf : MDifferentiableOn I J f s)
    (hs : s ∈ 𝓝 x) (hb : Bijective (mfderiv I J f x)) : IsLocalDiffeomorphAt I J n f x :=
  hf.isLocalDiffeomorphAt_of_mfderiv_eq hs
    (e := (LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap hb).toContinuousLinearEquiv)
    (by ext; simp)

/-- At a point with a neighbourhood on which a map between complex manifolds is holomorphic, the
map is a local diffeomorphism of class `C^n`, for any `n ≠ 0`, exactly when its complex
differential there is bijective. -/
theorem isLocalDiffeomorphAt_iff_bijective_mfderiv (hf : MDifferentiableOn I J f s)
    (hs : s ∈ 𝓝 x) (hn : n ≠ 0) :
    IsLocalDiffeomorphAt I J n f x ↔ Bijective (mfderiv I J f x) :=
  ⟨fun h ↦ (h.mfderivToContinuousLinearEquiv hn).bijective,
    hf.isLocalDiffeomorphAt_of_bijective_mfderiv hs⟩

end MDifferentiableOn

/-- **The global holomorphic inverse function theorem.** A holomorphic map between complex
manifolds all of whose complex differentials are bijective is a local biholomorphism, of class
`C^n` for every `n`, including `n = ω`. -/
theorem MDifferentiable.isLocalDiffeomorph_of_bijective_mfderiv
    (hf : MDifferentiable I J f) (hb : ∀ x, Bijective (mfderiv I J f x)) :
    IsLocalDiffeomorph I J n f := fun x ↦
  hf.mdifferentiableOn.isLocalDiffeomorphAt_of_bijective_mfderiv Filter.univ_mem (hb x)
