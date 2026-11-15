/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Split
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective cycles over a category of projective dimension at most one

Suppose every object of an abelian category has projective dimension at most one. Then subobjects
of projective objects are projective. For a homological complex, this makes the cycles and
boundaries of a projective term projective. When the incoming differential into a projective term
vanishes, its homology coincides with its cycles and is therefore projective as well. The quotient
of a term by its cycles embeds into the next term, so it too is projective when that next term is
projective.

These instances supply the projectivity hypotheses in the Künneth and universal coefficient
sequences. The instance `HomologicalComplex.isSplitMono_iCycles_of_projective` then splits the
inclusion of the cycles, supplying the splittings used by these sequences. No projectivity of
homology is required, and the complex can have any shape.

The condition is expressed using Mathlib's `CategoryTheory.HasProjectiveDimensionLE`, without
assuming the category has enough projectives. It holds for modules over a principal ideal domain
by `ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing`.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Sections 3.6 and 4.2.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]
  [∀ X : C, HasProjectiveDimensionLE X 1] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i : ι)

/-- If every object has projective dimension at most one, the cycles of a projective term are
projective. -/
instance projective_cycles_of_hasProjectiveDimensionLE_one [Projective (K.X i)] :
    Projective (K.cycles i) :=
  projective_of_mono_of_hasProjectiveDimensionLE_one (K.iCycles i)

/-- If every object has projective dimension at most one, the boundaries in a projective term are
projective. -/
instance projective_kernel_homologyπ_of_hasProjectiveDimensionLE_one [Projective (K.X i)] :
    Projective (kernel (K.homologyπ i)) :=
  projective_of_mono_of_hasProjectiveDimensionLE_one (kernel.ι _ ≫ K.iCycles i)

/-- If every object has projective dimension at most one, the quotient of a term by its cycles is
projective when the next term is projective. Consequently the cycles split off the term. -/
instance projective_cokernel_iCycles_of_hasProjectiveDimensionLE_one
    [Projective (K.X (c.next i))] : Projective (cokernel (K.iCycles i)) :=
  projective_of_mono_of_hasProjectiveDimensionLE_one
    (cokernel.desc (K.iCycles i) (K.d i (c.next i)) (K.iCycles_d _ _))

/-- If every object has projective dimension at most one and every differential into `K.X i`
vanishes, the homology at `i` of a projective term is projective: with no incoming boundaries,
`K.homologyπ i` identifies `K.cycles i` with `K.homology i`. -/
theorem projective_homology_of_d_eq_zero_of_hasProjectiveDimensionLE_one [Projective (K.X i)]
    (h : ∀ j, c.Rel j i → K.d j i = 0) : Projective (K.homology i) := by
  have hd : K.d (c.prev i) i = 0 := by
    by_cases hrel : c.Rel (c.prev i) i
    · exact h _ hrel
    · exact K.shape _ _ hrel
  exact Projective.of_iso (K.isoHomologyπ (c.prev i) i rfl hd) inferInstance

/-- If every object has projective dimension at most one and every term with a differential into
`K.X i` is zero, the homology at `i` of a projective term is projective. -/
theorem projective_homology_of_isZero_X_of_hasProjectiveDimensionLE_one [Projective (K.X i)]
    (h : ∀ j, c.Rel j i → IsZero (K.X j)) : Projective (K.homology i) :=
  K.projective_homology_of_d_eq_zero_of_hasProjectiveDimensionLE_one i fun j hj ↦
    (h j hj).eq_of_src _ _

end HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [∀ X : C, HasProjectiveDimensionLE X 1]
  {α : Type*} [AddRightCancelSemigroup α] [One α] (K : ChainComplex C α) (n : α)

/-- In an abelian category of projective dimension at most one, if the differential into degree `n`
of a chain complex vanishes and `K.X n` is projective, then `K.homology n` is projective. -/
theorem projective_homology_of_d_eq_zero_of_hasProjectiveDimensionLE_one [Projective (K.X n)]
    (h : K.d (n + 1) n = 0) : Projective (K.homology n) :=
  HomologicalComplex.projective_homology_of_d_eq_zero_of_hasProjectiveDimensionLE_one K n
    fun _ hj ↦ hj ▸ h

/-- In an abelian category of projective dimension at most one, if `K.X (n + 1)` is zero and
`K.X n` is projective, then `K.homology n` is projective. -/
theorem projective_homology_of_isZero_X_succ_of_hasProjectiveDimensionLE_one [Projective (K.X n)]
    (h : IsZero (K.X (n + 1))) : Projective (K.homology n) :=
  K.projective_homology_of_d_eq_zero_of_hasProjectiveDimensionLE_one n (h.eq_of_src _ _)

end ChainComplex
