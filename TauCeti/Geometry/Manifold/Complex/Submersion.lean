/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Holomorphic submersion normal forms

A holomorphic map between finite-dimensional complex manifolds is locally a coordinate
projection exactly where its complex differential is surjective. The complement has complex
dimension equal to the difference of the model dimensions. The coordinate changes can be taken
complex analytic, even when the given manifold structures are only of class `C¹`.

The conclusions use Mathlib's `Manifold.IsSubmersionAtOfComplement` and `Manifold.IsSubmersionAt`:
they provide actual charts in the maximal complex atlas, not just a condition on the derivative.
These charts give the local description of regular holomorphic level sets in arbitrary
codimension. The existing `Manifold.IsSubmersionAt.exists_contMDiffOn_section` then supplies
holomorphic local sections through every regular point, without another section construction.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I,
  the holomorphic implicit function theorem.
-/

public section

open Function Set Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {f : M → N} {U : Set M} {x : M} {n : ℕ∞ω}

/-- A holomorphic map near a point with surjective complex differential has a holomorphic
submersion normal form with the standard complement of dimension `dim E - dim F`.
This holds at every nonzero regularity, including complex analytic regularity `ω`. -/
theorem _root_.MDifferentiableOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    (hf : MDifferentiableOn I J f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n)
    (hs : Surjective (mfderiv I J f x)) :
    IsSubmersionAtOfComplement (Fin (Module.finrank ℂ E - Module.finrank ℂ F) → ℂ)
      I J n f x := by
  let : IsManifold I n M := IsManifold.of_ne_zero n one_ne_zero inferInstance
  let : IsManifold J n N := IsManifold.of_ne_zero n one_ne_zero inferInstance
  have := FiniteDimensional.complete ℂ F
  exact (hf.contMDiffOn hU).isSubmersionAtOfComplement_of_surjective_mfderiv hU hx hn hs

/-- At a point of an open holomorphy domain, the existence of holomorphic projection charts
is equivalent to surjectivity of the complex differential. -/
theorem isSubmersionAt_iff_surjective_mfderiv_of_mdifferentiableOn
    (hf : MDifferentiableOn I J f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n) :
    IsSubmersionAt I J n f x ↔ Surjective (mfderiv I J f x) := by
  refine ⟨fun h ↦ h.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)), fun hs ↦ ?_⟩
  exact (hf.isSubmersionAtOfComplement_of_surjective_mfderiv hU hx hn hs).isSubmersionAt

/-- A holomorphic map with surjective complex differentials is a holomorphic submersion
with one fixed standard complement, including when its source is empty. -/
theorem _root_.MDifferentiable.isSubmersionOfComplement_of_surjective_mfderiv
    (hf : MDifferentiable I J f) (hn : 1 ≤ n)
    (hs : ∀ x, Surjective (mfderiv I J f x)) :
    IsSubmersionOfComplement (Fin (Module.finrank ℂ E - Module.finrank ℂ F) → ℂ)
      I J n f := by
  rw [Manifold.isSubmersionOfComplement_iff]
  exact fun x ↦ hf.mdifferentiableOn.isSubmersionAtOfComplement_of_surjective_mfderiv
    isOpen_univ (mem_univ x) hn (hs x)

end TauCeti
