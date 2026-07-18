/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Elementary collapses of simplicial complexes

An elementary simplicial collapse deletes a free face together with its unique proper coface.
This file supplies that local move for `PreAbstractSimplicialComplex`, Mathlib's type of
downward-closed collections of nonempty finite faces.  This is the elementary substrate for the
collapse track in layer 11 of the geometric-topology roadmap.

Following Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3, the pair
`(σ, τ)` is free when `σ` is a proper face of `τ` and every face containing `σ` is either `σ` or
`τ`.  The usual codimension-one condition is recorded separately; uniqueness already suffices to
prove that deleting the pair leaves a simplicial complex.

`PreAbstractSimplicialComplex` is intentional here.  Mathlib's `AbstractSimplicialComplex ι`
contains every singleton of the fixed ambient vertex type `ι`, so deleting a free vertex would
leave that type.  A collapse changes the used vertex set and therefore naturally lives in the
pre-complex type.

## Main definitions

* `PreAbstractSimplicialComplex.IsFreePair`: a face and its unique proper coface.
* `PreAbstractSimplicialComplex.eraseFreePair`: the complex obtained by deleting a free pair.
* `PreAbstractSimplicialComplex.ElementaryCollapsesTo`: the relation of one elementary collapse.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} (K : _root_.PreAbstractSimplicialComplex ι)

/-- A pair `(σ, τ)` of faces is free when `σ` is a proper face of `τ` and `τ` is the only
face other than `σ` that contains `σ`.

This formulation includes maximality of `τ`: applying the last field to a face containing `τ`
forces that face to equal `τ`. -/
structure IsFreePair (σ τ : Finset ι) : Prop where
  /-- The lower face belongs to the complex. -/
  lower_mem : σ ∈ K
  /-- The upper face belongs to the complex. -/
  upper_mem : τ ∈ K
  /-- The lower face is properly contained in the upper face. -/
  lower_ssubset_upper : σ ⊂ τ
  /-- These are the only faces of the complex containing the lower face. -/
  eq_lower_or_eq_upper : ∀ ⦃ω : Finset ι⦄, ω ∈ K → σ ⊆ ω → ω = σ ∨ ω = τ

namespace IsFreePair

variable {K} {σ τ : Finset ι}

/-- The two members of a free pair are distinct. -/
theorem lower_ne_upper (h : IsFreePair K σ τ) : σ ≠ τ :=
  h.lower_ssubset_upper.ne

/-- The upper face of a free pair is maximal in the complex. -/
theorem upper_maximal (h : IsFreePair K σ τ) {ω : Finset ι} (hω : ω ∈ K) (hτω : τ ⊆ ω) :
    ω = τ := by
  rcases h.eq_lower_or_eq_upper hω (h.lower_ssubset_upper.subset.trans hτω) with rfl | h_eq
  · exact (h.lower_ssubset_upper.not_subset hτω).elim
  · exact h_eq

/-- A free pair in which the upper face has one additional vertex is a classical elementary
collapse pair. -/
def IsCodimensionOne (_h : IsFreePair K σ τ) : Prop :=
  τ.card = σ.card + 1

/-- A codimension-one free pair has a unique vertex in its upper-minus-lower difference. -/
theorem card_sdiff_eq_one [DecidableEq ι] (h : IsFreePair K σ τ) (hcodim : h.IsCodimensionOne) :
    (τ \ σ).card = 1 := by
  rw [Finset.card_sdiff_of_subset h.lower_ssubset_upper.subset, hcodim]
  omega

end IsFreePair

/-- Delete the two faces in a free pair.  Uniqueness of the coface ensures that the remaining
faces are still downward closed. -/
def eraseFreePair {σ τ : Finset ι} (h : IsFreePair K σ τ) :
    _root_.PreAbstractSimplicialComplex ι where
  faces := K.faces \ {σ, τ}
  isRelLowerSet_faces := by
    rintro ω ⟨hω, hω_ne⟩
    constructor
    · exact (K.isRelLowerSet_faces hω).1
    · intro υ hυω hυ
      refine ⟨(K.isRelLowerSet_faces hω).2 hυω hυ, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hυσ
        subst υ
        rcases h.eq_lower_or_eq_upper hω hυω with hωσ | hωτ
        · exact hω_ne (by simp [hωσ])
        · exact hω_ne (by simp [hωτ])
      · intro hυτ
        subst υ
        have hωτ := h.upper_maximal hω hυω
        exact hω_ne (by simp [hωτ])

@[simp]
theorem mem_eraseFreePair {σ τ ω : Finset ι} (h : IsFreePair K σ τ) :
    ω ∈ eraseFreePair K h ↔ ω ∈ K ∧ ω ≠ σ ∧ ω ≠ τ := by
  change ω ∈ K.faces \ {σ, τ} ↔ ω ∈ K.faces ∧ ω ≠ σ ∧ ω ≠ τ
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

/-- Deleting a free pair only removes faces. -/
theorem eraseFreePair_le {σ τ : Finset ι} (h : IsFreePair K σ τ) :
    eraseFreePair K h ≤ K := by
  intro ω hω
  exact (mem_eraseFreePair (K := K) h).mp hω |>.1

@[simp]
theorem lower_not_mem_eraseFreePair {σ τ : Finset ι} (h : IsFreePair K σ τ) :
    σ ∉ eraseFreePair K h := by
  simp

@[simp]
theorem upper_not_mem_eraseFreePair {σ τ : Finset ι} (h : IsFreePair K σ τ) :
    τ ∉ eraseFreePair K h := by
  simp

/-- One complex elementarily collapses to another when the latter is obtained by deleting a
codimension-one free pair. -/
def ElementaryCollapsesTo (L : _root_.PreAbstractSimplicialComplex ι) : Prop :=
  ∃ (σ τ : Finset ι) (h : IsFreePair K σ τ), h.IsCodimensionOne ∧ L = eraseFreePair K h

namespace ElementaryCollapsesTo

variable {K L : _root_.PreAbstractSimplicialComplex ι}

/-- An elementary collapse produces a subcomplex. -/
theorem le (h : ElementaryCollapsesTo K L) : L ≤ K := by
  obtain ⟨σ, τ, hfree, _, rfl⟩ := h
  exact eraseFreePair_le K hfree

/-- An elementary collapse is strict: its lower free face is lost. -/
theorem lt (h : ElementaryCollapsesTo K L) : L < K := by
  refine lt_of_le_of_ne h.le ?_
  obtain ⟨σ, τ, hfree, _, rfl⟩ := h
  intro h_eq
  have : σ ∈ eraseFreePair K hfree := h_eq.symm ▸ hfree.lower_mem
  exact (lower_not_mem_eraseFreePair K hfree) this

/-- Membership in the result of an elementary collapse is membership in the original complex
away from the selected free pair. -/
theorem exists_pair (h : ElementaryCollapsesTo K L) :
    ∃ (σ τ : Finset ι) (hfree : IsFreePair K σ τ), hfree.IsCodimensionOne ∧
      ∀ ω, ω ∈ L ↔ ω ∈ K ∧ ω ≠ σ ∧ ω ≠ τ := by
  obtain ⟨σ, τ, hfree, hcodim, rfl⟩ := h
  exact ⟨σ, τ, hfree, hcodim, fun ω => mem_eraseFreePair K hfree⟩

end ElementaryCollapsesTo

end PreAbstractSimplicialComplex

end TauCeti
