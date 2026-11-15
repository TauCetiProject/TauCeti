/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.JointEigenvalueSearch.Basic
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Successive refinement of common eigenspaces

Search for simultaneous eigenvalue tuples over a finite field, adding one matrix at a time.
Each surviving tuple represents a nonzero common eigenspace of the matrices processed so far.
Extend it by the eigenvalues of the next matrix and compute the kernel of the extended system;
keep exactly the extensions whose common eigenspace is nonzero. Empty intersections are discarded
before any further extensions are formed.

The output is precisely the tuples admitting a nonzero common eigenvector. No commutativity or
splitting hypothesis is required for this characterization: when simultaneous diagonalization
fails, the search still returns all common eigenvalue tuples that exist over the given field.
In dimension zero it returns nothing, including for an empty family. For an empty family in
positive dimension it returns the unique empty tuple.

The search uses `TauCeti.eigenvalueSearch` and `TauCeti.jointEigenspaceBasis`; it recomputes the
stacked kernel at each extension, without restricting the next matrix to a basis of a
surviving eigenspace or stopping refinement early at a one-dimensional block.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446–450.
* G. J. A. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601–606: successive splitting of common eigenspaces.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {m n : ℕ}

/-- Search for common eigenvalue tuples by successively intersecting eigenspaces.
Only prefixes with nonzero common eigenspace are extended to the next matrix. -/
def jointEigenvalueSearch : {m : ℕ} →
    (Fin m → Matrix (Fin n) (Fin n) F) → Finset (Fin m → F)
  | 0, _ => if n = 0 then ∅ else {Fin.elim0}
  | m + 1, A =>
    let spectrum := eigenvalueSearch (A (Fin.last m))
    (jointEigenvalueSearch (fun i : Fin m => A i.castSucc)).biUnion fun a =>
      (spectrum.image (Fin.snoc a)).filter fun b => jointEigenspaceBasis A b ≠ []

/-- An empty family has the unique empty eigenvalue tuple exactly in positive dimension. -/
@[simp] theorem jointEigenvalueSearch_empty (A : Fin 0 → Matrix (Fin n) (Fin n) F) :
    jointEigenvalueSearch A = if n = 0 then ∅ else {Fin.elim0} := (rfl)

/-- One refinement step extends only the surviving prefixes and discards empty intersections. -/
theorem jointEigenvalueSearch_succ (A : Fin (m + 1) → Matrix (Fin n) (Fin n) F) :
    jointEigenvalueSearch A =
      (jointEigenvalueSearch (fun i : Fin m => A i.castSucc)).biUnion fun a =>
        ((eigenvalueSearch (A (Fin.last m))).image (Fin.snoc a)).filter fun b =>
          jointEigenspaceBasis A b ≠ [] := (rfl)

/-- The search returns exactly the tuples admitting a nonzero common eigenvector. -/
@[simp] theorem mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ jointEigenvalueSearch A ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  induction m with
  | zero =>
    by_cases hn : n = 0
    · subst n
      simp
    · have ha : a = Fin.elim0 := Subsingleton.elim _ _
      simp only [jointEigenvalueSearch_empty, ite_eq_right hn, Finset.mem_singleton, ha, true_iff]
      refine ⟨Pi.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1, ?_, fun i => i.elim0⟩
      intro h
      have := congrFun h ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at this
  | succ m ih =>
    rw [jointEigenvalueSearch_succ]
    constructor
    · intro h
      obtain ⟨b, _, ha⟩ := Finset.mem_biUnion.mp h
      exact (jointEigenspaceBasis_ne_nil_iff A a).mp (Finset.mem_filter.mp ha).2
    · rintro ⟨v, hv, heig⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨Fin.init a, ih.mpr ⟨v, hv, fun i => heig i.castSucc⟩, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨a (Fin.last m), ?_, Fin.snoc_init_self a⟩,
        (jointEigenspaceBasis_ne_nil_iff A a).mpr ⟨v, hv, heig⟩⟩
      exact mem_eigenvalueSearch_iff_exists_mulVec.mpr ⟨v, hv, heig (Fin.last m)⟩

/-- At most `n` nonzero common eigenspaces survive any refinement stage on `Fⁿ`.
Consequently the number of retained prefixes is bounded by the ambient dimension. -/
theorem card_jointEigenvalueSearch_le (A : Fin m → Matrix (Fin n) (Fin n) F) :
    (jointEigenvalueSearch A).card ≤ n := by
  let p (a : Fin m → F) : Submodule F (Fin n → F) :=
    ⨅ i, Module.End.eigenspace (Matrix.toLin' (A i)) (a i)
  have hp : iSupIndep p :=
    iSupIndep_iInf_eigenspace (fun i => Matrix.toLin' (A i))
  have hmem (a : Fin m → F) : a ∈ jointEigenvalueSearch A ↔ p a ≠ ⊥ := by
    rw [mem_jointEigenvalueSearch, Submodule.ne_bot_iff]
    simp only [p, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact ⟨fun ⟨v, hv, h⟩ => ⟨v, h, hv⟩, fun ⟨v, h, hv⟩ => ⟨v, hv, h⟩⟩
  calc
    (jointEigenvalueSearch A).card = Fintype.card {a // p a ≠ ⊥} := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr (Equiv.subtypeEquivRight hmem)
    _ ≤ Module.finrank F (Fin n → F) := hp.subtype_ne_bot_le_finrank
    _ = n := by simp

/-- Each component of a returned tuple is an eigenvalue of the corresponding matrix. -/
theorem apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  obtain ⟨v, hv, heig⟩ := mem_jointEigenvalueSearch.mp ha
  exact mem_eigenvalueSearch_iff_exists_mulVec.mpr ⟨v, hv, heig i⟩

/-- The common-eigenspace basis associated to a returned tuple is nonempty. -/
theorem jointEigenspaceBasis_ne_nil_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) : jointEigenspaceBasis A a ≠ [] :=
  (jointEigenspaceBasis_ne_nil_iff A a).mpr (mem_jointEigenvalueSearch.mp ha)

/-- **Correctness of the common eigenrow search**: searching the transposed family returns exactly
the tuples admitting a nonzero common left eigenvector. -/
theorem mem_jointEigenvalueSearch_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ jointEigenvalueSearch (fun i => (A i)ᵀ) ↔
      ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  simp [Matrix.mulVec_transpose]

/-- Every component of a tuple returned by searching the transposed family is an eigenvalue of
the corresponding original matrix. -/
theorem apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch (fun i => (A i)ᵀ)) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  rw [← eigenvalueSearch_transpose]
  exact apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch ha i

end TauCeti
