/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension at most one and subobjects of projectives

In an abelian category with enough projectives, every object has projective dimension at most one
if and only if every subobject of a projective object is projective. This is the hereditary
condition, expressed using Mathlib's existing projective-dimension predicate.

When every object has projective dimension at most one, the criterion shows that the cycles and
boundaries of a complex of projective objects are projective. Surjections onto these boundaries
then split, so the cycles split off the terms.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.2 (hereditary rings).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- A subobject of a projective object is projective if its quotient has projective dimension
at most one. -/
theorem projective_of_mono_of_hasProjectiveDimensionLE_one {X Y : C} (f : X ⟶ Y)
    [Mono f] [Projective Y] [HasProjectiveDimensionLE (cokernel f) 1] : Projective X := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS.hasProjectiveDimensionLT_X₁ 1 inferInstance inferInstance)

variable (C) [EnoughProjectives C]

/-- Every object has projective dimension at most one precisely when every monomorphism into a
projective object has projective source. -/
theorem forall_hasProjectiveDimensionLE_one_iff_projective_of_mono :
    (∀ X : C, HasProjectiveDimensionLE X 1) ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f] [Projective Y], Projective X := by
  constructor
  · intro h X Y f _ _
    have := h (cokernel f)
    exact projective_of_mono_of_hasProjectiveDimensionLE_one f
  · intro h X
    obtain ⟨P⟩ := EnoughProjectives.presentation X
    have : Projective P.p := P.projective
    have : Epi P.f := P.epi
    have : Projective (kernel P.f) := h (kernel.ι P.f)
    have hS : (ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel P.f) }
    exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

end CategoryTheory
