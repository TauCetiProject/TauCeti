/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight

/-!
# The spin indices in the tripled type-D4 weight table

The last sixteen entries of `TauCeti.DynkinType.d4TripledWeight` are the weights of the two
half-spin representations of type `D₄`. This file identifies them precisely with the sign sets
that index the exterior spin basis.

The index `d4SpinIndex s` is characterized by having weight `typeDSpinWeight s`. Injectivity of
the two weight families makes this choice unique. Odd sign sets give the block `V(ϖ₃)`, numbered
`1` by `d4TripledSummand`, and even sign sets give `V(ϖ₄)`, numbered `2`. Consequently the
index map is an equivalence from all sixteen sign sets onto the complement of the natural
eight-dimensional block.

The equivalence also conjugates the simple reflections on sign sets to the restrictions of the
tripled simple reflections. Thus it fixes both the Bourbaki node numbering and the target basis
vector of every simple-root step. A comparison of representations can use this reindexing and
then treat the scalar signs of the root operators separately.

## Main declarations

* `TauCeti.DynkinType.d4SpinIndex`: the tripled-table index of a type-`D₄` spin sign set.
* `TauCeti.DynkinType.d4TripledSummand_d4SpinIndex`: the half-spin block is determined by the
  parity of the sign set.
* `TauCeti.DynkinType.d4SpinIndexEquiv`: the sixteen spin sign sets are equivalent to the
  non-natural entries of the tripled table.
* `TauCeti.DynkinType.d4SpinIndexEquiv_typeDSpinReflection`: this equivalence intertwines all
  four simple reflections.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

namespace TauCeti.DynkinType

/-! ## The spin index and its weight -/

/-- The unique entry of the tripled type-`D₄` table carrying the weight of a spin sign set.

Existence comes from `range_typeDSpinWeight_four_subset_range_d4TripledWeight`; uniqueness follows
from `d4TripledWeight_injective`. The map from sign sets is itself injective by
`d4SpinIndex_injective`. -/
noncomputable def d4SpinIndex (s : Finset (Fin 4)) : Fin 24 :=
  Classical.choose
    (range_typeDSpinWeight_four_subset_range_d4TripledWeight ⟨s, rfl⟩)

/-- The tripled weight at the spin index is the integral type-`D₄` spin weight. -/
@[simp]
theorem d4TripledWeight_d4SpinIndex (s : Finset (Fin 4)) :
    d4TripledWeight (d4SpinIndex s) = typeDSpinWeight s :=
  Classical.choose_spec
    (range_typeDSpinWeight_four_subset_range_d4TripledWeight ⟨s, rfl⟩)

/-- Distinct sign sets have distinct indices in the tripled table. -/
theorem d4SpinIndex_injective : Function.Injective d4SpinIndex := by
  intro s t h
  apply typeDSpinWeight_injective
  rw [← d4TripledWeight_d4SpinIndex s, ← d4TripledWeight_d4SpinIndex t, h]

/-- The spin index carries a simple reflection of sign sets to the corresponding reflection in
the tripled table, with the same Bourbaki node number. -/
@[simp]
theorem d4SpinIndex_typeDSpinReflection (i : Fin 4) (s : Finset (Fin 4)) :
    d4SpinIndex (typeDSpinReflection i s) = d4TripledReflection i (d4SpinIndex s) := by
  apply d4TripledWeight_injective
  rw [d4TripledWeight_d4SpinIndex, typeDSpinWeight_typeDSpinReflection (by omega),
    d4TripledWeight_reflection, d4TripledWeight_d4SpinIndex]

/-! ## The two half-spin blocks -/

/-- Odd spin sign sets index the `V(ϖ₃)` block and even sign sets index the `V(ϖ₄)` block. -/
@[simp]
theorem d4TripledSummand_d4SpinIndex (s : Finset (Fin 4)) :
    d4TripledSummand (d4SpinIndex s) = if Even s.card then 2 else 1 :=
  d4TripledSummand_eq_of_weight_eq_typeDSpinWeight _ _ (d4TripledWeight_d4SpinIndex s)

private theorem d4TripledSummand_d4SpinIndex_ne_zero (s : Finset (Fin 4)) :
    d4TripledSummand (d4SpinIndex s) ≠ 0 := by
  rw [d4TripledSummand_d4SpinIndex]
  split <;> norm_num

/-- The spin indices are exactly the last two, half-spin blocks of the tripled table. -/
theorem range_d4SpinIndex :
    Set.range d4SpinIndex = {a : Fin 24 | d4TripledSummand a ≠ 0} := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact d4TripledSummand_d4SpinIndex_ne_zero s
  · intro ha
    obtain ⟨s, hs⟩ := (exists_typeDSpinWeight_eq_d4TripledWeight_iff a).2 ha
    refine ⟨s, ?_⟩
    apply d4TripledWeight_injective
    rw [d4TripledWeight_d4SpinIndex, hs]

/-! ## Equivalence and reflection compatibility -/

private noncomputable def d4SpinIndexSubtype (s : Finset (Fin 4)) :
    {a : Fin 24 // d4TripledSummand a ≠ 0} :=
  ⟨d4SpinIndex s, d4TripledSummand_d4SpinIndex_ne_zero s⟩

private theorem d4SpinIndexSubtype_bijective : Function.Bijective d4SpinIndexSubtype := by
  constructor
  · intro s t h
    exact d4SpinIndex_injective (congrArg Subtype.val h)
  · intro a
    have ha : a.1 ∈ Set.range d4SpinIndex := by
      rw [range_d4SpinIndex]
      exact a.2
    obtain ⟨s, hs⟩ := ha
    exact ⟨s, Subtype.ext hs⟩

/-- The type-`D₄` spin sign sets are equivalent to the two half-spin blocks of the tripled
weight table. -/
noncomputable def d4SpinIndexEquiv :
    Finset (Fin 4) ≃ {a : Fin 24 // d4TripledSummand a ≠ 0} :=
  Equiv.ofBijective d4SpinIndexSubtype d4SpinIndexSubtype_bijective

/-- The underlying table index of `d4SpinIndexEquiv s` is `d4SpinIndex s`. -/
@[simp]
theorem coe_d4SpinIndexEquiv (s : Finset (Fin 4)) :
    (d4SpinIndexEquiv s : Fin 24) = d4SpinIndex s := by
  simp [d4SpinIndexEquiv, d4SpinIndexSubtype]

/-- A tripled simple reflection restricted to the two half-spin blocks. -/
def d4TripledHalfSpinReflection (i : Fin 4) :
    Equiv.Perm {a : Fin 24 // d4TripledSummand a ≠ 0} :=
  (d4TripledReflection i).subtypePerm fun a ↦ by
    rw [d4TripledSummand_d4TripledReflection]

/-- The underlying table index of the restricted reflection is the tripled reflection. -/
@[simp]
theorem coe_d4TripledHalfSpinReflection (i : Fin 4)
    (a : {a : Fin 24 // d4TripledSummand a ≠ 0}) :
    (d4TripledHalfSpinReflection i a : Fin 24) = d4TripledReflection i a := by
  rw [d4TripledHalfSpinReflection, Equiv.Perm.subtypePerm_apply]

/-- The spin-index equivalence conjugates every simple reflection on sign sets to the
corresponding restricted reflection of the tripled table. -/
@[simp]
theorem d4SpinIndexEquiv_typeDSpinReflection (i : Fin 4) (s : Finset (Fin 4)) :
    d4SpinIndexEquiv (typeDSpinReflection i s) =
      d4TripledHalfSpinReflection i (d4SpinIndexEquiv s) := by
  apply Subtype.ext
  simp

end TauCeti.DynkinType
