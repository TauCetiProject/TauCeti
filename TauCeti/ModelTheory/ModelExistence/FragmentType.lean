/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.AElementary
public import TauCeti.ModelTheory.ModelExistence.Types

/-!
# Types and truth assignments relative to a fragment

The fragment type of a tuple consists of the formulas in a fragment's arity slice that hold of
that tuple. Equivalently, the tuple determines a truth assignment on the slice. These two views
carry the same information, including for fragments that are not closed under negation.

Restriction to a smaller fragment intersects the type with its slice, or precomposes the truth
assignment with the slice inclusion. Fragment-elementary embeddings preserve both descriptions;
conversely, preservation of the fragment types characterizes fragment elementarity. In particular,
isomorphisms preserve these types and truth assignments. No countability, formation closure, or
nonemptiness assumption is needed.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1
  (fragments and elementarity relative to a fragment).
-/

public section

universe u v w w'

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {A B : Fragment L} {n : ℕ}

/-- The type of a tuple relative to a fragment: the members of its arity slice true of the tuple.
It need not decide formulas outside the fragment, or contain their negations. -/
def fragmentType (A : Fragment L) (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    Set (L.BoundedFormulaω Empty n) :=
  A.slice n ∩ infinitaryType M a

/-- A formula belongs to the fragment type exactly when it belongs to the fragment and is true
of the tuple. -/
@[simp]
theorem mem_fragmentType {a : Fin n → M} {φ : L.BoundedFormulaω Empty n} :
    φ ∈ fragmentType A M a ↔ (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
      φ.Realize Empty.elim a := by
  simp only [fragmentType, Set.mem_inter_iff, Fragment.mem_slice, mem_infinitaryType]

/-- A fragment type is the restriction of the complete infinitary type to the arity slice. -/
theorem fragmentType_eq_inter (A : Fragment L) (a : Fin n → M) :
    fragmentType A M a = A.slice n ∩ infinitaryType M a := (rfl)

/-- Restricting a fragment restricts the fragment type by intersection with its arity slice. -/
theorem fragmentType_eq_inter_of_le (hAB : A ≤ B) (a : Fin n → M) :
    fragmentType A M a = A.slice n ∩ fragmentType B M a := by
  simpa only [fragmentType_eq_inter, Set.inter_def] using
    (Set.sep_eq_inter_sep (p := fun φ => φ ∈ infinitaryType M a) (Fragment.slice_mono hAB n))

/-- Fragment types are monotone in the fragment. -/
theorem fragmentType_mono (hAB : A ≤ B) (a : Fin n → M) :
    fragmentType A M a ⊆ fragmentType B M a :=
  Set.inter_subset_inter_left _ (Fragment.slice_mono hAB n)

/-- Equality of fragment types means agreement on realization of every formula in the slice. -/
theorem fragmentType_eq_iff {a : Fin n → M} {b : Fin n → N} :
    fragmentType A M a = fragmentType A N b ↔
      ∀ φ ∈ A.slice n, φ.Realize Empty.elim a ↔ φ.Realize Empty.elim b := by
  simpa only [fragmentType, Set.inter_def, mem_infinitaryType] using
    (Set.sep_ext_iff (s := A.slice n) (p := fun φ => φ ∈ infinitaryType M a)
      (q := fun φ => φ ∈ infinitaryType N b))

/-- An `A`-elementary embedding preserves the type of every tuple relative to `A`. -/
@[simp]
theorem AElementary.fragmentType_comp {f : N ↪[L] M} (hf : AElementary A f)
    (a : Fin n → N) : fragmentType A M (f ∘ a) = fragmentType A N a :=
  fragmentType_eq_iff.2 fun _ hφ => hf.realize_iff (Fragment.mem_slice.1 hφ) a

/-- An embedding is fragment-elementary exactly when it preserves every fragment type. -/
theorem aElementary_iff_fragmentType_comp {f : N ↪[L] M} :
    AElementary A f ↔ ∀ (n : ℕ) (a : Fin n → N),
      fragmentType A M (f ∘ a) = fragmentType A N a := by
  refine ⟨fun h _ a => h.fragmentType_comp a, fun h => aElementary_iff.2 ?_⟩
  intro n φ hφ a
  exact fragmentType_eq_iff.1 (h n a) φ (Fragment.mem_slice.2 hφ)

namespace Fragment

/-- The realized truth assignment of a tuple on the arity slice of a fragment. -/
def truthAssignment (A : Fragment L) (M : Type w) [L.Structure M] {n : ℕ} (a : Fin n → M) :
    A.slice n → Prop :=
  fun φ => φ.1.Realize Empty.elim a

/-- Evaluation of a realized truth assignment is realization of the formula. -/
@[simp]
theorem truthAssignment_apply (A : Fragment L) (a : Fin n → M) (φ : A.slice n) :
    A.truthAssignment M a φ ↔ φ.1.Realize Empty.elim a :=
  Iff.rfl

/-- On the slice, the truth assignment records membership in the fragment type. -/
theorem truthAssignment_iff_mem_fragmentType (A : Fragment L) (a : Fin n → M) (φ : A.slice n) :
    A.truthAssignment M a φ ↔ φ.1 ∈ fragmentType A M a := by
  simp only [truthAssignment_apply, mem_fragmentType, mem_slice.1 φ.2, true_and]

/-- The truth assignment restricts along fragment inclusion by precomposition with the slice map.
The slice map is Mathlib's `Set.inclusion`, so its identity and composition laws apply directly. -/
theorem truthAssignment_restrict (hAB : A ≤ B) (a : Fin n → M) :
    A.truthAssignment M a = B.truthAssignment M a ∘ Set.inclusion (slice_mono hAB n) := (rfl)

/-- Equality of realized truth assignments is equivalent to equality of fragment types. -/
theorem truthAssignment_eq_iff {a : Fin n → M} {b : Fin n → N} :
    A.truthAssignment M a = A.truthAssignment N b ↔ fragmentType A M a = fragmentType A N b := by
  rw [fragmentType_eq_iff, funext_iff]
  simp only [truthAssignment_apply, Subtype.forall, propext_iff]

end Fragment

/-- An `A`-elementary embedding preserves the realized truth assignment on every arity slice. -/
@[simp]
theorem AElementary.truthAssignment_comp {f : N ↪[L] M} (hf : AElementary A f)
    (a : Fin n → N) : A.truthAssignment M (f ∘ a) = A.truthAssignment N a :=
  Fragment.truthAssignment_eq_iff.2 (hf.fragmentType_comp a)

/-- An isomorphism preserves every fragment type. -/
@[simp]
theorem Equiv.fragmentType_comp (e : N ≃[L] M) (A : Fragment L) (a : Fin n → N) :
    fragmentType A M (e ∘ a) = fragmentType A N a :=
  (e.aElementary A).fragmentType_comp a

/-- An isomorphism preserves every realized truth assignment. -/
@[simp]
theorem Equiv.truthAssignment_comp (e : N ≃[L] M) (A : Fragment L) (a : Fin n → N) :
    A.truthAssignment M (e ∘ a) = A.truthAssignment N a :=
  (e.aElementary A).truthAssignment_comp a

end FirstOrder.Language
