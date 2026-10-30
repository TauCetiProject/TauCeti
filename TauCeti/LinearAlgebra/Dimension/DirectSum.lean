/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of an internal direct sum

A module that is the internal direct sum of a finite family of finite free submodules has the sum
of their ranks, `TauCeti.finrank_eq_sum_finrank_of_isInternal`. Finiteness is asked of the
summands rather than of the ambient module: the former is the form available at a call site that
only knows its summands. Over a division ring every summand is free, so this is the familiar
dimension count for vector spaces.

`TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep` is the same count for an independent family
whose supremum need not be the whole module.

`TauCeti.finsum_finrank_eq_finrank_of_isInternal` is the same count for a decomposition indexed by
an arbitrary type in which all but finitely many summands vanish, written with `finsum`. A graded
decomposition is usually indexed by `ℤ` even when only finitely many degrees occur, so this is the
form such a decomposition meets.

Mathlib has `Module.finrank_directSum` for the *external* direct sum `⨁ i, M i` and
`DirectSum.IsInternal` for an internal decomposition, but not the rank count that combining
them gives; the bridge is the canonical map `DirectSum.coeLinearMap V`, an isomorphism onto `M`
for an internal decomposition and injective with range `⨆ i, V i` for an independent family.
-/

public section

namespace TauCeti

open Module (finrank)

variable {R M ι : Type*}

section Semiring

variable [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  {V : ι → Submodule R M} [∀ i, Module.Free R (V i)] [∀ i, Module.Finite R (V i)]

/-- **The ranks of the summands of an internal direct sum add up.** -/
theorem finrank_eq_sum_finrank_of_isInternal [Fintype ι] [DecidableEq ι]
    (h : DirectSum.IsInternal V) : finrank R M = ∑ i, finrank R (V i) := by
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap V) h).finrank_eq,
    Module.finrank_directSum]

end Semiring

section Ring

variable [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  {V : ι → Submodule R M} [∀ i, Module.Free R (V i)] [∀ i, Module.Finite R (V i)]

/-- **The rank of the supremum of an independent finite family of submodules is the sum of their
ranks.** Unlike `TauCeti.finrank_eq_sum_finrank_of_isInternal`, the ambient module here is the
supremum of the given family rather than an independently supplied module. -/
theorem finrank_iSup_eq_sum_finrank_of_iSupIndep [Fintype ι] (h : iSupIndep V) :
    finrank R ↥(⨆ i, V i) = ∑ i, finrank R (V i) := by
  classical
  -- `DirectSum.coeLinearMap V` is by definition `DFinsupp.lsum` of the inclusions, whose
  -- injectivity is `iSupIndep.dfinsupp_lsum_injective`; Mathlib's
  -- `DirectSum.IsInternal.submodule_iSupIndep` uses the same identification.
  rw [← DirectSum.range_coeLinearMap,
    LinearMap.finrank_range_of_inj (f := DirectSum.coeLinearMap V) h.dfinsupp_lsum_injective,
    Module.finrank_directSum]

/-- **The ranks of the summands of an internal direct sum add up**, for a decomposition indexed by
an arbitrary type in which only finitely many summands are nonzero. -/
theorem finsum_finrank_eq_finrank_of_isInternal [DecidableEq ι] (h : DirectSum.IsInternal V)
    (hV : {i | V i ≠ ⊥}.Finite) : ∑ᶠ i, finrank R (V i) = finrank R M := by
  obtain ⟨hindep, htop⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V).1 h
  have hbot : ∀ i ∉ hV.toFinset, V i = ⊥ := fun i hi ↦ by simpa using hi
  have hsub : DirectSum.IsInternal fun i : hV.toFinset ↦ V i := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (hindep.comp Subtype.val_injective) (top_unique (htop ▸ iSup_le fun i ↦ ?_))
    by_cases hi : i ∈ hV.toFinset
    · exact le_iSup (fun j : hV.toFinset ↦ V j) ⟨i, hi⟩
    · simp [hbot i hi]
  have hsupport : (Function.support fun i ↦ finrank R (V i)) ⊆ hV.toFinset :=
    Function.support_subset_iff'.2 fun i hi ↦
      have := Submodule.subsingleton_iff_eq_bot.2 (hbot i hi)
      Module.finrank_zero_of_subsingleton
  rw [finsum_eq_sum_of_support_subset _ hsupport, finrank_eq_sum_finrank_of_isInternal hsub]
  exact (Finset.sum_coe_sort _ _).symm

end Ring

end TauCeti
