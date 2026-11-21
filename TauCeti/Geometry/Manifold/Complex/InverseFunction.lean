/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
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

* `MDifferentiableOn.isLocalDiffeomorphAt_of_mfderiv_eq`: the holomorphic inverse function
  theorem at a point.
* `TauCeti.isLocalDiffeomorphAt_iff_bijective_mfderiv_of_mdifferentiableOn`: at a point of an
  open holomorphy domain, being a local biholomorphism is bijectivity of the differential.
* `MDifferentiable.isLocalDiffeomorph_of_bijective_mfderiv`: the global form.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I, §B (the holomorphic inverse function theorem).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {f : M → N} {s : Set M} {x : M} {n : ℕ∞ω}

/-- **The holomorphic inverse function theorem on complex manifolds.** A map holomorphic on an
open set, whose complex differential at a point of that set is a continuous linear equivalence,
is a local biholomorphism there, of class `C^n` for every `n`, including `n = ω`. The target model
is finite-dimensional because the differential is an equivalence. -/
theorem _root_.MDifferentiableOn.isLocalDiffeomorphAt_of_mfderiv_eq
    (hf : MDifferentiableOn I J f s) (hs : IsOpen s) (hx : x ∈ s)
    {e : TangentSpace I x ≃L[ℂ] TangentSpace J (f x)}
    (he : (e : TangentSpace I x →L[ℂ] TangentSpace J (f x)) = mfderiv I J f x) :
    IsLocalDiffeomorphAt I J n f x := by
  have : FiniteDimensional ℂ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℂ E)
  have : FiniteDimensional ℂ F :=
    (e.toLinearEquiv.finiteDimensional : FiniteDimensional ℂ (TangentSpace J (f x)))
  have := FiniteDimensional.completeSpace ℂ E
  have := FiniteDimensional.completeSpace ℂ F
  have : IsManifold I ω M := .of_ne_zero ω one_ne_zero inferInstance
  have : IsManifold J ω N := .of_ne_zero ω one_ne_zero inferInstance
  exact (TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq (n := ω) (hf.contMDiffOn hs) hs hx
    BoundarylessManifold.isInteriorPoint le_top he).of_le le_top

/-- At a point of an open holomorphy domain, a map between complex manifolds is a local
diffeomorphism of class `C^n`, for any `n ≠ 0`, exactly when its complex differential there is
bijective. -/
theorem isLocalDiffeomorphAt_iff_bijective_mfderiv_of_mdifferentiableOn
    (hf : MDifferentiableOn I J f s) (hs : IsOpen s) (hx : x ∈ s) (hn : n ≠ 0) :
    IsLocalDiffeomorphAt I J n f x ↔ Bijective (mfderiv I J f x) := by
  refine ⟨fun h ↦ (h.mfderivToContinuousLinearEquiv hn).bijective, fun hb ↦ ?_⟩
  have : FiniteDimensional ℂ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℂ E)
  exact hf.isLocalDiffeomorphAt_of_mfderiv_eq hs hx
    (e := (LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap hb).toContinuousLinearEquiv) rfl

/-- **The global holomorphic inverse function theorem.** A holomorphic map between complex
manifolds all of whose complex differentials are bijective is a local biholomorphism, of class
`C^n` for every `n`, including `n = ω`. -/
theorem _root_.MDifferentiable.isLocalDiffeomorph_of_bijective_mfderiv
    (hf : MDifferentiable I J f) (hb : ∀ x, Bijective (mfderiv I J f x)) :
    IsLocalDiffeomorph I J n f := fun x ↦
  (isLocalDiffeomorphAt_iff_bijective_mfderiv_of_mdifferentiableOn (n := ω) hf.mdifferentiableOn
    isOpen_univ (mem_univ x) (by simp)).2 (hb x) |>.of_le le_top

end TauCeti
