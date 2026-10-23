/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import TauCeti.Algebra.Module.GradedModule.HomogeneousPart

/-!
# Homogeneous splittings of surjective linear maps

A surjective homogeneous linear map between internally graded modules admits a homogeneous
linear right inverse when its target is projective. Starting with an ordinary linear section,
retain the appropriate homogeneous component on each target piece and assemble these maps through
the internal direct-sum decomposition. Over a division ring the target is automatically projective,
so every surjective homogeneous map of vector spaces splits.

The degree of the section is the negative of the degree of the original map. For vector spaces,
a degree-zero quotient map admits homogeneous representatives, while a degree-one differential
admits a degree-minus-one choice of preimages on its range. Those are the two splittings used to
contract a complex of vector spaces onto its cohomology.

## Main result

* `TauCeti.LinearMap.IsHomogeneous.exists_rightInverse`: a surjective homogeneous map of degree
  `r` onto a projective module has a homogeneous right inverse of degree `-r`.
-/

public section

namespace TauCeti.LinearMap.IsHomogeneous

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {G : InternalGrading R M} {H : InternalGrading R N} {f : M →ₗ[R] N} {r : ℤ}

/-- A surjective homogeneous linear map of degree `r` between internally graded modules has a
homogeneous right inverse of degree `-r` if its target is projective. -/
theorem exists_rightInverse [Module.Projective R N] (hf : IsHomogeneous f G.piece H.piece r)
    (hsurj : Function.Surjective f) :
    ∃ g : N →ₗ[R] M, f ∘ₗ g = LinearMap.id ∧ IsHomogeneous g H.piece G.piece (-r) := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨H.homogeneousPart G s (-r), ?_, H.isHomogeneous_homogeneousPart G s (-r)⟩
  simpa [hs] using H.comp_homogeneousPart G H s (-r) hf

end TauCeti.LinearMap.IsHomogeneous
