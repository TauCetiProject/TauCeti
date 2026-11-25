/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Projective representations are retracts of free representations

The canonical morphism `Rep.freeLift id : free k G A ⟶ A`, sending the generator at `a : A` to
`a`, is an epimorphism (`Rep.epi_freeLift_id`). Splitting it gives, for a projective
representation `A`, a retraction of the free representation on the underlying type of `A` onto `A`
(`Rep.retractFree`), whose retraction is `freeLift id` (`Rep.retractFree_r`).
-/

public section

universe u v

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- The canonical morphism from the free representation on the underlying type of `A` to `A`,
sending the generator at `a` to `a`, is an epimorphism. -/
instance epi_freeLift_id (A : Rep.{max u v} k G) : Epi (freeLift k G A id) :=
  (epi_iff_surjective _).2 fun x ↦ ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by simp⟩

/-- A projective representation is a retract of the free representation on its underlying type,
by splitting the canonical epimorphism `freeLift id`. -/
noncomputable def retractFree (A : Rep.{max u v} k G) [Projective A] :
    Retract A (free k G A) where
  i := Projective.factorThru (𝟙 A) (freeLift k G A id)
  r := freeLift k G A id
  retract := Projective.factorThru_comp _ _

/-- The retraction of `retractFree A` is the canonical morphism `freeLift id`. -/
@[simp]
theorem retractFree_r (A : Rep.{max u v} k G) [Projective A] :
    (retractFree A).r = freeLift k G A id := by
  rw [retractFree]

end Rep
