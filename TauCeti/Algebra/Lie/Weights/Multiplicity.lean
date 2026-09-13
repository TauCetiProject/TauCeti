/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Basic
public import TauCeti.Algebra.Lie.Isotypic
public import TauCeti.Algebra.Lie.Multiplicity
-- Non-public: these declarations support the internal-decomposition proof.
import TauCeti.Algebra.Lie.Submodule.Decomposition
import TauCeti.Algebra.Lie.Submodule.Finrank
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# Weight-space multiplicities in isotypic Lie modules

This file connects the dimension of an honest weight space with the number of irreducible
summands in an isotypic Lie module. A Lie-module equivalence preserves every weight space, while
an internal direct sum of Lie submodules decomposes each weight space into the corresponding
weight spaces of the summands. Consequently, if a weight has multiplicity one in the irreducible
type of a completely reducible isotypic module, its multiplicity in the whole module is the
isotypic multiplicity.

The statements concern simultaneous eigenspaces `LieModule.weightSpace`, not generalized weight
spaces. They therefore require neither nilpotence of the acting Lie algebra nor triangularizability
of the module.

## Main results

* `TauCeti.finrank_weightSpace_congr`: equivalent Lie modules have weight spaces of equal
  dimension.
* `TauCeti.finrank_weightSpace_eq_sum_of_isInternal`: weight-space dimensions add over a finite
  internal decomposition by Lie submodules.
* `LieModule.IsIsotypicOfType.isotypicMultiplicity_eq_finrank_weightSpace`: a weight of
  multiplicity one in the irreducible type reads off the isotypic multiplicity.
-/

public section

open scoped BigOperators DirectSum

namespace TauCeti

open _root_.LieModule Module

/-- **Weight-space dimension is an isomorphism invariant.** An equivalence of Lie modules carries
the `χ`-weight space of one module onto the `χ`-weight space of the other. -/
theorem finrank_weightSpace_congr
    {K L M P : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [AddCommGroup P] [Module K P] [LieRingModule L P] [LieModule K L P]
    (e : M ≃ₗ⁅K,L⁆ P) (χ : L → K) :
    finrank K (weightSpace M χ) = finrank K (weightSpace P χ) := by
  have hequiv := (LieSubmodule.equivMapOfInjective
    (weightSpace M χ) e.injective).toLinearEquiv.finrank_eq
  rw [LieModule.map_weightSpace_eq e χ] at hequiv
  exact hequiv

section Internal

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {ι : Type*} {N : ι → LieSubmodule K L M}

omit [LieModule K L M] in
/-- The inclusion of a summand, restricted to a Lie subalgebra, is injective. -/
private theorem injective_incl_restrictLie (i : ι) :
    Function.Injective ((N i).incl.restrictLie H) :=
  fun _ _ hxy ↦ LieSubmodule.injective_incl (N i) hxy

/-- The image of a summand's weight space is its intersection with the ambient weight space. -/
private theorem toSubmodule_map_weightSpace_incl (i : ι) (χ : H → K) :
    ((weightSpace ↥(N i) χ).map ((N i).incl.restrictLie H)).toSubmodule
      = (weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule := by
  ext m
  simp only [LieSubmodule.mem_toSubmodule, Submodule.mem_inf]
  constructor
  · intro hm
    rw [LieSubmodule.mem_map] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    exact ⟨LieModule.map_weightSpace_le ((N i).incl.restrictLie H) χ
      (LieSubmodule.mem_map_of_mem hx), x.2⟩
  · rintro ⟨hm, hmi⟩
    rw [LieSubmodule.mem_map]
    refine ⟨⟨m, hmi⟩, ?_, rfl⟩
    rw [mem_weightSpace] at hm ⊢
    intro x
    exact Subtype.ext (hm x)

/-- The intersection carrying a summand's weight space has the expected dimension. -/
private theorem finrank_inf_weightSpace (i : ι) (χ : H → K) :
    finrank K ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule : Submodule K M)
      = finrank K (weightSpace ↥(N i) χ) := by
  have hequiv := (LieSubmodule.equivMapOfInjective
    (weightSpace ↥(N i) χ) (injective_incl_restrictLie i)).toLinearEquiv.finrank_eq
  rw [← toSubmodule_map_weightSpace_incl i χ, finrank_toSubmodule, ← hequiv]

/-- The intersections of an ambient weight space with the summands span that weight space. -/
private theorem iSup_inf_weightSpace_eq [Finite ι] [DecidableEq ι]
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule) (χ : H → K) :
    ⨆ i, ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule)
      = (weightSpace M χ).toSubmodule := by
  classical
  have _ := Fintype.ofFinite ι
  refine le_antisymm (iSup_le fun i ↦ inf_le_left) fun m hm ↦ ?_
  set e := DirectSum.lieModuleEquivOfIsInternal N h with he
  have hcomp : ∀ i, (e.symm m i : ↥(N i)) ∈ weightSpace ↥(N i) χ := fun i ↦
    LieModule.map_weightSpace_le
      ((((DirectSum.lieModuleComponent K ι L fun j ↦ ↥(N j)) i).comp
        (e.symm : M →ₗ⁅K,L⁆ ⨁ j, ↥(N j))).restrictLie H) χ ⟨m, hm, rfl⟩
  have hmem : ∀ i, ((e.symm m i : ↥(N i)) : M)
      ∈ (weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule := fun i ↦
    ⟨LieModule.map_weightSpace_le ((N i).incl.restrictLie H) χ ⟨_, hcomp i, rfl⟩,
      (e.symm m i).2⟩
  have hsum : m = ∑ i, ((e.symm m i : ↥(N i)) : M) := by
    conv_lhs => rw [← e.apply_symm_apply m, ← DirectSum.sum_univ_of (e.symm m)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [he]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.mem_iSup_of_mem i (hmem i)

/-- **Weight-space dimensions are additive over an internal decomposition.** If a finite family of
`L`-submodules is an internal direct sum of `M`, then the dimension of the `χ`-weight space for any
Lie subalgebra `H` is the sum of the dimensions of the summands' `χ`-weight spaces. -/
theorem finrank_weightSpace_eq_sum_of_isInternal [FiniteDimensional K M]
    [Fintype ι] [DecidableEq ι]
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule) (χ : H → K) :
    finrank K (weightSpace M χ) = ∑ i, finrank K (weightSpace ↥(N i) χ) := by
  have hindep : iSupIndep fun i ↦
      ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule) :=
    h.submodule_iSupIndep.mono fun i ↦ inf_le_right
  rw [← finrank_toSubmodule, ← iSup_inf_weightSpace_eq h χ,
    finrank_iSup_eq_sum_finrank_of_iSupIndep hindep]
  exact Finset.sum_congr rfl fun i _ ↦ finrank_inf_weightSpace i χ

end Internal

end TauCeti

namespace LieModule

open Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {S : Type*} [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]

/-- **A multiplicity-one weight reads off the isotypic multiplicity.** Suppose `M` is a
finite-dimensional completely reducible module, isotypic of an irreducible type `S`. If the
`χ`-weight space of `S` is one-dimensional, then the dimension of the `χ`-weight space of `M` is
the number of copies of `S` in `M`. -/
theorem IsIsotypicOfType.isotypicMultiplicity_eq_finrank_weightSpace
    [IsAlgClosed K] [FiniteDimensional K M] [FiniteDimensional K S]
    [IsIrreducible K L S] [ComplementedLattice (LieSubmodule K L M)]
    (h : IsIsotypicOfType K L M S) (χ : H → K)
    (hone : finrank K (weightSpace S χ) = 1) :
    isotypicMultiplicity K L M S = finrank K (weightSpace M χ) := by
  classical
  obtain ⟨k, N, hint, hirr⟩ := TauCeti.exists_isInternal_isIrreducible K L M
  have hequiv : ∀ i, Nonempty (↥(N i) ≃ₗ⁅K,L⁆ S) := fun i ↦
    (isIsotypicOfType_iff K L M S).mp h (N i)
  have hmul : isotypicMultiplicity K L M S = k := by
    rw [isotypicMultiplicity_eq_ncard_of_isInternal N hint hirr]
    have hset : {i | Nonempty (S ≃ₗ⁅K,L⁆ N i)} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨(hequiv i).some.symm⟩
    rw [hset, Set.ncard_univ, Nat.card_fin]
  have hsummand : ∀ i, finrank K (weightSpace ↥(N i) χ) = 1 := fun i ↦
    (TauCeti.finrank_weightSpace_congr
      (TauCeti.LieModuleEquiv.restrictLie (hequiv i).some H) χ).trans hone
  have hweight : finrank K (weightSpace M χ) = k := by
    rw [TauCeti.finrank_weightSpace_eq_sum_of_isInternal hint]
    simp only [hsummand, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  exact hmul.trans hweight.symm

end LieModule
