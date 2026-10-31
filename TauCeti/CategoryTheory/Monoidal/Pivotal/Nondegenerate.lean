/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Nondegeneracy of categorical traces

In a finite semisimple pivotal category with simple unit, the left and right dimensions of
a split simple object are nonzero. Indeed, its coevaluation splits, and Frobenius reciprocity
and Schur's lemma make every retraction a scalar multiple of its pivotal evaluation.

Consequently the trace pairings on morphism spaces are nondegenerate: every nonzero morphism
`f : X ⟶ Y` has a partner `g : Y ⟶ X` with nonzero trace of `f ≫ g`. This is the cancellation
principle needed to deduce identities of morphisms from identities of categorical traces.
No braiding, finiteness of the set of simple classes, or characteristic-zero assumption is
needed. The coefficient field is algebraically closed and the simple endomorphism spaces
are finite-dimensional; finite-dimensionality of arbitrary morphism spaces is not assumed.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 8.10
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti

variable (k : Type*) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C] [Abelian C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

include k in
/-- The right dimension of a split simple object in a finite semisimple pivotal category with
simple tensor unit is nonzero. -/
theorem rightDim_ne_zero_of_simple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    rightDim X ≠ 0 := by
  have : IsSplitMono (η_ X Xᘁ) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero (Simple.not_isZero X))
  let := pivotalExactPairing X
  obtain ⟨c, hc⟩ := hom_tensorUnit_eq_smul_evaluation_of_simple_right k
    (retraction (η_ X Xᘁ))
  have h : c • rightDim X = 𝟙 (𝟙_ C) := by
    rw [← rightTrace_id, rightTrace_def, id_whiskerRight, Category.id_comp,
      ← Linear.comp_smul, ← hc]
    exact IsSplitMono.id _
  intro hz
  rw [hz, smul_zero] at h
  exact id_nonzero (𝟙_ C) h.symm

include k in
/-- The left dimension of a split simple object in a finite semisimple pivotal category with
simple tensor unit is nonzero. -/
theorem leftDim_ne_zero_of_simple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    leftDim X ≠ 0 := by
  let := pivotalExactPairing X
  have : IsSplitMono (η_ Xᘁ X) :=
    isSplitMono_of_nonzero_from_simple (coevaluation_ne_zero (Simple.not_isZero Xᘁ))
  obtain ⟨c, hc⟩ := hom_tensorUnit_eq_smul_evaluation_of_simple_left k
    (retraction (η_ Xᘁ X))
  have h : c • leftDim X = 𝟙 (𝟙_ C) := by
    rw [← leftTrace_id, leftTrace_def, whiskerLeft_id, Category.id_comp,
      ← Linear.comp_smul, ← hc]
    exact IsSplitMono.id _
  intro hz
  rw [hz, smul_zero] at h
  exact id_nonzero (𝟙_ C) h.symm

section Pairing

variable [hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include hfin

include k in
/-- Every nonzero morphism has a partner with which its composite has nonzero right trace. -/
theorem exists_rightTrace_comp_ne_zero {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, rightTrace (f ≫ g) ≠ 0 := by
  obtain ⟨ι, hι, S, hS, hB, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  -- A nonzero component of `f` has simple source, so it admits a retraction.
  obtain ⟨i, hi⟩ : ∃ i, biproduct.ι S i ≫ e.inv ≫ f ≠ 0 := by
    by_contra! h
    exact hf <| (cancel_epi e.inv).1 <| biproduct.hom_ext' _ _ fun i ↦ by simpa using h i
  let a : S i ⟶ X := biproduct.ι S i ≫ e.inv
  have : IsSplitMono (a ≫ f) :=
    isSplitMono_of_nonzero_from_simple (by simpa only [a, Category.assoc] using hi)
  refine ⟨retraction (a ≫ f) ≫ a, ?_⟩
  -- Cyclicity moves the simple summand around the loop, leaving its nonzero dimension.
  rw [← Category.assoc, rightTrace_comm, ← Category.assoc, IsSplitMono.id, rightTrace_id]
  exact rightDim_ne_zero_of_simple k (S i)

include k in
/-- Every nonzero morphism has a partner with which its composite has nonzero left trace. -/
theorem exists_leftTrace_comp_ne_zero {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, leftTrace (f ≫ g) ≠ 0 := by
  -- Taking mates interchanges left and right traces and reverses composition.
  have hf' : fᘁ ≠ 0 := by
    intro h
    exact hf (rightAdjointMate_injective (h.trans rightAdjointMate_zero.symm))
  obtain ⟨g, hg⟩ := exists_rightTrace_comp_ne_zero k (hfin := hfin) hf'
  refine ⟨ᘁg, ?_⟩
  rw [← rightTrace_rightAdjointMate, comp_rightAdjointMate,
    rightAdjointMate_leftAdjointMate, rightTrace_comm]
  exact hg

include k in
/-- The right trace pairing detects zero morphisms. -/
theorem forall_rightTrace_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∀ g : Y ⟶ X, rightTrace (f ≫ g) = 0) ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    obtain ⟨g, hg⟩ := exists_rightTrace_comp_ne_zero k (hfin := hfin) hf
    exact hg (h g)
  · rintro rfl g
    simp

include k in
/-- The left trace pairing detects zero morphisms. -/
theorem forall_leftTrace_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∀ g : Y ⟶ X, leftTrace (f ≫ g) = 0) ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    obtain ⟨g, hg⟩ := exists_leftTrace_comp_ne_zero k (hfin := hfin) hf
    exact hg (h g)
  · rintro rfl g
    simp

end Pairing

end TauCeti
