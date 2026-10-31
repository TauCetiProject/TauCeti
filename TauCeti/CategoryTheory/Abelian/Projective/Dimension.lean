/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Comparing projective dimensions, and subobjects of projectives

If every bound `HasProjectiveDimensionLT X n` on one object implies the same bound on another
object `Y`, possibly in a different abelian category, then the projective dimension of `Y` is at
most that of `X`. This compares projective dimensions degree by degree without unfolding their
definition as an infimum.

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

/-- If every bound on the projective dimension of `X` is also a bound for `Y`, then the projective
dimension of `Y` is at most that of `X`. The objects may lie in different abelian categories. -/
theorem projectiveDimension_le_of_hasProjectiveDimensionLT {D : Type*} [Category* D] [Abelian D]
    {X : C} {Y : D}
    (h : ∀ n : ℕ, HasProjectiveDimensionLT X n → HasProjectiveDimensionLT Y n) :
    projectiveDimension Y ≤ projectiveDimension X :=
  sInf_le_sInf fun _ hd i hi ↦ h i (hd i hi)

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
