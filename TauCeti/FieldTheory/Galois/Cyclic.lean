/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic Galois extensions

In a finite Galois extension `L/F` with cyclic Galois group, an intermediate field is determined
by its degree over `F`: a cyclic group has at most one subgroup of each index, and the Galois
correspondence identifies `[E : F]` with the index of the fixing subgroup of `E`.

## Main results

* `IntermediateField.eq_of_finrank_eq_of_isCyclic`: intermediate fields of a finite cyclic Galois
  extension with the same degree are equal.
* `TauCeti.exists_pow_lt_finrank_eq`: if `g` generates the Galois group of a finite extension, every
  automorphism is `g ^ p` for some `p` below the degree.
-/

public section

open Module

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- In a finite Galois extension with cyclic Galois group, two intermediate fields of the same
degree are equal. -/
theorem eq_of_finrank_eq_of_isCyclic [FiniteDimensional F L] [IsGalois F L]
    [IsCyclic Gal(L/F)] {E₁ E₂ : IntermediateField F L} (h : finrank F E₁ = finrank F E₂) :
    E₁ = E₂ := by
  rw [← IsGalois.fixedField_fixingSubgroup E₁, ← IsGalois.fixedField_fixingSubgroup E₂]
  refine congrArg fixedField (IsCyclic.subgroup_eq_iff_index_eq.mpr ?_)
  rwa [← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index]

end IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- If `g` generates the Galois group of a finite Galois extension `L / K`, then every element of
the group is `g ^ p` for some `p` below the degree. -/
theorem exists_pow_lt_finrank_eq {g : L ≃ₐ[K] L}
    (hg : ∀ σ, σ ∈ Subgroup.zpowers g) (hord : orderOf g = Module.finrank K L)
    (τ : L ≃ₐ[K] L) : ∃ p < Module.finrank K L, τ = g ^ p := by
  classical
  obtain ⟨p, hp, hpτ⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 (hg τ))
  exact ⟨p, hord ▸ Finset.mem_range.1 hp, hpτ.symm⟩

end TauCeti
