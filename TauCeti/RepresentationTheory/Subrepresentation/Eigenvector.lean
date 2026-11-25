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
* `Representation.span_setOf_forall_apply_eq_smul`: a finite-dimensional semisimple
  representation of a commutative monoid over an algebraically closed field is spanned by common
  eigenvectors.
* `Representation.exists_basis_forall_apply_eq_smul`: such a representation has a basis of
  common eigenvectors.
-/

public section

namespace Representation

open Module

variable {k : Type} {G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
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
  refine isSemisimpleRepresentation_iff_eq_top_of_forall_atom_le.2 fun σ hσ ↦ ?_
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 ?_)
  rw [← hspan, Submodule.span_le]
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  exact hσ _ (isAtom_lineSubrepresentation ρ (hS v hv) hv0)
    ((mem_lineSubrepresentation ρ).2 (Submodule.mem_span_singleton_self v))

/-! ### Eigenbases of semisimple representations of commutative monoids -/

variable [IsMulCommutative G] [IsAlgClosed k] [FiniteDimensional k V]

/-- **A semisimple representation of a commutative monoid is spanned by common eigenvectors**,
over an algebraically closed field and in finite dimension: its irreducible subrepresentations are
lines. -/
theorem span_setOf_forall_apply_eq_smul [ρ.IsSemisimpleRepresentation] :
    Submodule.span k {v : V | ∀ g, ∃ c : k, ρ g v = c • v} = ⊤ := by
  set T := Submodule.span k {v : V | ∀ g, ∃ c : k, ρ g v = c • v}
  -- The span of the common eigenvectors is stable: `ρ g` maps eigenvectors to eigenvectors.
  have hstable : ∀ (g : G) ⦃w : V⦄, w ∈ T → ρ g w ∈ T := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      refine Submodule.subset_span fun h ↦ ?_
      obtain ⟨c, hc⟩ := hv h
      refine ⟨c, ?_⟩
      rw [← mul_apply_eq_comp, ← map_mul, IsMulCommutative.is_comm.comm h g, map_mul,
        mul_apply_eq_comp, hc, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  let τ : Subrepresentation ρ := ⟨T, hstable⟩
  -- Every irreducible subrepresentation is a line, so every vector of it is a common eigenvector.
  have hatoms : ∀ σ : Subrepresentation ρ, IsAtom σ → σ ≤ τ := by
    intro σ hσ w hw
    have := isIrreducible_toRepresentation_of_isAtom hσ
    refine Submodule.subset_span fun g ↦ ?_
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (IsIrreducible.finrank_eq_one_of_isMulCommutative σ.toRepresentation)
      (σ.toRepresentation g)
    exact ⟨c, congrArg Subtype.val (LinearMap.congr_fun hc ⟨w, hw⟩)⟩
  have hτ : τ = ⊤ := isSemisimpleRepresentation_iff_eq_top_of_forall_atom_le.1 ‹_› τ hatoms
  rw [← Subrepresentation.toSubmodule_top (ρ := ρ), ← hτ]

/-- **An eigenbasis of a semisimple representation of a commutative monoid**, over an
algebraically closed field and in finite dimension: a basis of common eigenvectors of the
operators `ρ g`. -/
theorem exists_basis_forall_apply_eq_smul [ρ.IsSemisimpleRepresentation] :
    ∃ (s : Set V) (b : Basis s k V), ∀ i g, ∃ c : k, ρ g (b i) = c • b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent k {v : V | ∀ g, ∃ c : k, ρ g v = c • v}
  refine ⟨s, Basis.mk hli ?_, fun i g ↦ ?_⟩
  · rw [Subtype.range_coe, hspan, span_setOf_forall_apply_eq_smul]
  · rw [Basis.mk_apply]
    exact hs i.property g

end Representation
