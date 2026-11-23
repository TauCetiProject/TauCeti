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

Let `C` be a finite semisimple pivotal category, linear over a commutative semiring `R`. The left
and right dimensions of a nonzero object `X` with scalar endomorphisms over `R` (the structure map
`algebraMap R (End X)` is surjective) are nonzero. Indeed, the coevaluation of `X` is nonzero, so
it splits on some simple summand of the unit, and Frobenius reciprocity makes every retraction
there a scalar multiple of the pivotal evaluation.

Consequently, when every simple object has scalar endomorphisms, the trace pairings on morphism
spaces are nondegenerate: every nonzero morphism `f : X ⟶ Y` has a partner `g : Y ⟶ X` with
nonzero trace of `f ≫ g`. This is the cancellation principle needed to deduce identities of
morphisms from identities of categorical traces.

No braiding, simple unit, finiteness of the set of simple classes, or characteristic assumption is
needed. Over an algebraically closed field, a simple object with finite-dimensional endomorphisms
has scalar endomorphisms by Schur's lemma (`TauCeti.bijective_algebraMap_end_of_simple`).

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 8.10
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti

variable {R : Type*} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C] [Abelian C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C]
  [IsFiniteSemisimpleCategory C]

/-- In a finite semisimple pivotal category, the right dimension of a nonzero object with scalar
endomorphisms is nonzero. -/
theorem rightDim_ne_zero_of_surjective {X : C} (hX : ¬IsZero X)
    (hR : Function.Surjective (algebraMap R (End X))) : rightDim X ≠ 0 := by
  let := pivotalExactPairing X
  have := comp_evaluation_ne_zero_of_surjective_right (X := Xᘁ) hR
    (coevaluation_ne_zero (Y := Xᘁ) hX)
  rwa [← rightTrace_id, rightTrace_def, id_whiskerRight, Category.id_comp]

/-- In a finite semisimple pivotal category, the left dimension of a nonzero object with scalar
endomorphisms is nonzero. -/
theorem leftDim_ne_zero_of_surjective {X : C} (hX : ¬IsZero X)
    (hR : Function.Surjective (algebraMap R (End X))) : leftDim X ≠ 0 := by
  -- The dual of `X` is nonzero, since the coevaluation `𝟙_ C ⟶ X ⊗ Xᘁ` is.
  have hX' : ¬IsZero Xᘁ := fun h ↦ coevaluation_ne_zero (Y := Xᘁ) hX <| by
    simpa using η_ X Xᘁ ≫= congrArg (X ◁ ·) (h.eq_of_src (𝟙 _) 0)
  let := pivotalExactPairing X
  have := comp_evaluation_ne_zero_of_surjective_left (Y := Xᘁ) hR
    (coevaluation_ne_zero (Y := X) hX')
  rwa [← leftTrace_id, leftTrace_def, whiskerLeft_id, Category.id_comp]

section Pairing

variable (hR : ∀ (S : C) [Simple S], Function.Surjective (algebraMap R (End S)))
include hR

/-- If every simple object has scalar endomorphisms, every nonzero morphism has a partner with
which its composite has nonzero right trace. -/
theorem exists_rightTrace_comp_ne_zero {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, rightTrace (f ≫ g) ≠ 0 := by
  -- Some morphism `a` from a simple object makes `a ≫ f` admit a retraction.
  obtain ⟨S, _, a, -, _⟩ := exists_simple_isSplitMono_comp_of_ne_zero hf
  refine ⟨retraction (a ≫ f) ≫ a, ?_⟩
  -- Cyclicity moves the simple object around the loop, leaving its nonzero dimension.
  rw [← Category.assoc, rightTrace_comm, ← Category.assoc, IsSplitMono.id, rightTrace_id]
  exact rightDim_ne_zero_of_surjective (Simple.not_isZero S) (hR S)

/-- If every simple object has scalar endomorphisms, every nonzero morphism has a partner with
which its composite has nonzero left trace. -/
theorem exists_leftTrace_comp_ne_zero {X Y : C} {f : X ⟶ Y} (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, leftTrace (f ≫ g) ≠ 0 := by
  -- Taking mates interchanges left and right traces and reverses composition.
  have hf' : fᘁ ≠ 0 := by
    intro h
    exact hf (rightAdjointMate_injective (h.trans rightAdjointMate_zero.symm))
  obtain ⟨g, hg⟩ := exists_rightTrace_comp_ne_zero hR hf'
  refine ⟨ᘁg, ?_⟩
  rw [← rightTrace_rightAdjointMate, comp_rightAdjointMate,
    rightAdjointMate_leftAdjointMate, rightTrace_comm]
  exact hg

/-- If every simple object has scalar endomorphisms, the right trace pairing detects zero
morphisms. -/
theorem forall_rightTrace_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∀ g : Y ⟶ X, rightTrace (f ≫ g) = 0) ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    obtain ⟨g, hg⟩ := exists_rightTrace_comp_ne_zero hR hf
    exact hg (h g)
  · rintro rfl g
    simp

/-- If every simple object has scalar endomorphisms, the left trace pairing detects zero
morphisms. -/
theorem forall_leftTrace_comp_eq_zero_iff {X Y : C} (f : X ⟶ Y) :
    (∀ g : Y ⟶ X, leftTrace (f ≫ g) = 0) ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    obtain ⟨g, hg⟩ := exists_leftTrace_comp_ne_zero hR hf
    exact hg (h g)
  · rintro rfl g
    simp

end Pairing

end TauCeti
