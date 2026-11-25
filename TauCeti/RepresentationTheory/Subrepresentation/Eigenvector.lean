/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Common eigenvectors and semisimplicity

A representation spanned by common eigenvectors of all the operators `ρ g` is semisimple: it is
the sum of the lines through those eigenvectors, which are irreducible subrepresentations
(`Representation.isSemisimpleRepresentation_of_span_eq_top`). Conversely, a finite-dimensional
semisimple representation of a commutative monoid over an algebraically closed field has a basis
of common eigenvectors (`Representation.exists_basis_forall_apply_eq_smul`), because its
irreducible subrepresentations are lines
(`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`).

## Main definitions

* `Representation.lineSubrepresentation`: the line through a common eigenvector, as a
  subrepresentation.

## Main results

* `Representation.isSemisimpleRepresentation_of_span_eq_top`: a representation spanned by common
  eigenvectors is semisimple.
* `Representation.span_setOf_forall_apply_eq_smul_eq_top`: a finite-dimensional semisimple
  representation of a commutative monoid over an algebraically closed field is spanned by common
  eigenvectors.
* `Representation.exists_basis_forall_apply_eq_smul`: such a representation has a basis of
  common eigenvectors.
-/

public section

namespace Representation

open Module

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-! ### Lines through common eigenvectors -/

/-- The line through a common eigenvector `v` of the operators `ρ g`, as a subrepresentation. -/
def lineSubrepresentation (v : V) (hv : ∀ g, ∃ c : k, ρ g v = c • v) : Subrepresentation ρ where
  toSubmodule := k ∙ v
  apply_mem_toSubmodule g w hw := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨c, hc⟩ := hv g
    rw [map_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

/-- The subspace carried by the line through `v` is the span of `v`. -/
@[simp]
theorem toSubmodule_lineSubrepresentation (v : V) (hv : ∀ g, ∃ c : k, ρ g v = c • v) :
    (lineSubrepresentation ρ v hv).toSubmodule = k ∙ v :=
  (rfl)

/-- A vector lies in the line through `v` exactly when it is a multiple of `v`. -/
@[simp]
theorem mem_lineSubrepresentation {v : V} {hv : ∀ g, ∃ c : k, ρ g v = c • v} {w : V} :
    w ∈ lineSubrepresentation ρ v hv ↔ w ∈ k ∙ v := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_lineSubrepresentation]

/-- The line through a nonzero common eigenvector is a minimal nonzero subrepresentation. -/
theorem isAtom_lineSubrepresentation {v : V} (hv : ∀ g, ∃ c : k, ρ g v = c • v) (hv0 : v ≠ 0) :
    IsAtom (lineSubrepresentation ρ v hv) := by
  have hline : IsAtom (k ∙ v) :=
    Submodule.isAtom_iff_finrank_eq_one.2 (finrank_span_singleton hv0)
  refine ⟨fun h ↦ hline.1 ?_, fun τ hτ ↦ ?_⟩
  · rw [← toSubmodule_lineSubrepresentation ρ v hv, h, Subrepresentation.toSubmodule_bot]
  · have hlt : τ.toSubmodule < k ∙ v := by
      rw [← toSubmodule_lineSubrepresentation ρ v hv]
      exact Subrepresentation.toSubmodule_lt_toSubmodule.2 hτ
    exact Subrepresentation.toSubmodule_injective (hline.2 _ hlt)

/-- **A representation spanned by common eigenvectors is semisimple**: it is the sum of the lines
through them, which are irreducible subrepresentations. -/
theorem isSemisimpleRepresentation_of_span_eq_top {S : Set V}
    (hS : ∀ v ∈ S, ∀ g, ∃ c : k, ρ g v = c • v) (hspan : Submodule.span k S = ⊤) :
    ρ.IsSemisimpleRepresentation := by
  refine isSemisimpleRepresentation_iff_iSup_atoms_eq_top.2 (eq_top_iff.2 ?_)
  rw [← hspan, Submodule.span_le]
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  refine Submodule.mem_iSup_of_mem ⟨_, isAtom_lineSubrepresentation ρ (hS v hv) hv0⟩ ?_
  rw [toSubmodule_lineSubrepresentation]
  exact Submodule.mem_span_singleton_self v

/-! ### Eigenbases of semisimple representations of commutative monoids -/

variable [IsMulCommutative G] [IsAlgClosed k] [FiniteDimensional k V]

/-- **A semisimple representation of a commutative monoid is spanned by common eigenvectors**,
over an algebraically closed field and in finite dimension: its irreducible subrepresentations are
lines. -/
theorem span_setOf_forall_apply_eq_smul_eq_top [ρ.IsSemisimpleRepresentation] :
    Submodule.span k {v : V | ∀ g, ∃ c : k, ρ g v = c • v} = ⊤ := by
  -- Every irreducible subrepresentation is a line, so every vector of it is a common eigenvector.
  refine eq_top_iff.2 ((isSemisimpleRepresentation_iff_iSup_atoms_eq_top.1 ‹_›).ge.trans
    (iSup_le fun σ w hw ↦ Submodule.subset_span fun g ↦ ?_))
  have := isIrreducible_toRepresentation_of_isAtom σ.property
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (IsIrreducible.finrank_eq_one_of_isMulCommutative σ.val.toRepresentation)
    (σ.val.toRepresentation g)
  have h := LinearMap.congr_fun hc ⟨w, hw⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, Subrepresentation.toRepresentation_apply_coe,
    Submodule.coe_smul] at h
  exact ⟨c, h⟩

/-- **An eigenbasis of a semisimple representation of a commutative monoid**, over an
algebraically closed field and in finite dimension: a basis of common eigenvectors of the
operators `ρ g`. -/
theorem exists_basis_forall_apply_eq_smul [ρ.IsSemisimpleRepresentation] :
    ∃ (s : Set V) (b : Basis s k V), ∀ i g, ∃ c : k, ρ g (b i) = c • b i :=
  ⟨_, Basis.ofSpan (span_setOf_forall_apply_eq_smul_eq_top ρ).ge,
    fun i ↦ Basis.ofSpan_subset _ ⟨i, rfl⟩⟩

end Representation
