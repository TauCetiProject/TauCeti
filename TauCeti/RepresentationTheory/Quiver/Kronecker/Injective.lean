/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Kronecker.Indecomposable

/-!
# The vertex injectives of the one-arrow quiver

For `1 → 2`, the source injective is the source simple `S₁ = (k → 0)`, and the target
injective is the source projective `P₁ = (k → k)`. These identifications distinguish the
injective indecomposables from the target simple, the value of Auslander–Reiten translation.
They hold over an arbitrary field.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras* (1995), IV.1.
-/

public section

open CategoryTheory

namespace TauCeti

open Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type) [Unique A]

/-- For the one-arrow quiver, the injective at the source is the source simple. -/
theorem nonempty_iso_indecInjRep_src_simpleRep_kronecker :
    Nonempty (indecInjRep k (Quiver.Kronecker A) src ≅
      simpleRep k (Quiver.Kronecker A) src) := by
  rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    (indecInjRep k (Quiver.Kronecker A) src)
    (indecomposable_indecInjRep_of_isAcyclic Quiver.Kronecker.isAcyclic src) with h | h | h
  · exact h
  · obtain ⟨e⟩ := h
    have h := congrFun (dimVector_eq_of_iso e) tgt
    rw [dimVector_indecInjRep, dimVector_simpleRep] at h
    simp at h
  · obtain ⟨e⟩ := h
    have h := congrFun (dimVector_eq_of_iso e) tgt
    rw [dimVector_indecInjRep, dimVector_indecProjRep] at h
    simp at h

/-- For the one-arrow quiver, the injective at the target is the source projective. -/
theorem nonempty_iso_indecInjRep_tgt_indecProjRep_kronecker :
    Nonempty (indecInjRep k (Quiver.Kronecker A) tgt ≅
      indecProjRep k (Quiver.Kronecker A) src) := by
  rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    (indecInjRep k (Quiver.Kronecker A) tgt)
    (indecomposable_indecInjRep_of_isAcyclic Quiver.Kronecker.isAcyclic tgt) with h | h | h
  · obtain ⟨e⟩ := h
    have h := congrFun (dimVector_eq_of_iso e) tgt
    rw [dimVector_indecInjRep, dimVector_simpleRep] at h
    simp at h
  · obtain ⟨e⟩ := h
    have h := congrFun (dimVector_eq_of_iso e) src
    rw [dimVector_indecInjRep, dimVector_simpleRep] at h
    simp at h
  · exact h

end TauCeti
