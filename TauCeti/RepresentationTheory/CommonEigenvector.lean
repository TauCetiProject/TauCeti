/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Common eigenvectors of commutative monoid representations

A nonzero finite-dimensional representation of a commutative monoid over an algebraically closed
field has a nonzero vector that is an eigenvector of every element
(`Representation.exists_ne_zero_forall_exists_apply_eq_smul`). An irreducible subrepresentation
exists by finite-dimensionality, and it is a line by Schur's lemma for commutative monoids
(`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`).
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [IsMulCommutative G] [AddCommGroup V] [Module k V]

/-- **Common eigenvectors.** A nonzero finite-dimensional representation of a commutative monoid
over an algebraically closed field has a nonzero vector that is an eigenvector of every element:
an irreducible subrepresentation is a line by Schur's lemma. -/
theorem exists_ne_zero_forall_exists_apply_eq_smul [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (ρ : Representation k G V) : ∃ v ≠ 0, ∀ g, ∃ c : k, ρ g v = c • v := by
  obtain ⟨σ, hσ, hirr⟩ := exists_isIrreducible_subrepresentation ρ
  have hσ' : σ.toSubmodule ≠ ⊥ := fun h ↦
    hσ (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ'
  have h1 : Module.finrank k σ.toSubmodule = 1 :=
    IsIrreducible.finrank_eq_one_of_isMulCommutative σ.toRepresentation
  refine ⟨w, hw0, fun g ↦ ?_⟩
  have hgw : ρ g w ∈ σ.toSubmodule := σ.apply_mem_toSubmodule g hw
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨w, hw⟩ : σ.toSubmodule)
    (by simpa using hw0)).mp h1 ⟨ρ g w, hgw⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

end Representation
