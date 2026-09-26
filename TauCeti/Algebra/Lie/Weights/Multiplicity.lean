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
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.Lie.Submodule.Decomposition
import TauCeti.Algebra.Lie.Submodule.Finrank
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# Weight-space multiplicities in isotypic Lie modules

This file connects the dimension of an honest weight space with the number of irreducible
summands in an isotypic Lie module. A Lie-module equivalence preserves every weight space, while
an internal direct sum of Lie submodules decomposes each weight space into the corresponding
weight spaces of the summands. Consequently, the dimension of each ambient weight space is the
isotypic multiplicity times its dimension in the irreducible type. In particular, a weight of
multiplicity one reads off the isotypic multiplicity.

The statements concern simultaneous eigenspaces `LieModule.weightSpace`, not generalized weight
spaces. They therefore require neither nilpotence of the acting Lie algebra nor triangularizability
of the module.

## Main results

* `DirectSum.IsInternal.finrank_weightSpace_eq_sum`: weight-space dimensions add over a finite
  internal decomposition by Lie submodules.
* `LieModule.IsIsotypicOfType.finrank_weightSpace_eq_isotypicMultiplicity_mul`: the dimension of
  an isotypic weight space is the number of summands times its dimension in the irreducible type.
* `LieModule.IsIsotypicOfType.isotypicMultiplicity_eq_finrank_weightSpace`: a weight of
  multiplicity one in the irreducible type reads off the isotypic multiplicity.
-/

public section

open scoped BigOperators DirectSum

namespace DirectSum.IsInternal

open LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {ι : Type*} {N : ι → LieSubmodule K L M}

/-- **Weight-space dimensions are additive over an internal decomposition.** If a finite family of
`L`-submodules is an internal direct sum of `M`, then the dimension of the `χ`-weight space for any
Lie subalgebra `H` is the sum of the dimensions of the summands' `χ`-weight spaces. -/
theorem finrank_weightSpace_eq_sum [Fintype ι] {dec_ι : DecidableEq ι}
    (h : @DirectSum.IsInternal ι M (Submodule K M) dec_ι _ _ _
      fun i ↦ (N i).toSubmodule) (χ : H → K)
    [∀ i, FiniteDimensional K (weightSpace ↥(N i) χ)] :
    finrank K (weightSpace M χ) = ∑ i, finrank K (weightSpace ↥(N i) χ) := by
  let _ := dec_ι
  classical
  have hfinite : ∀ i, FiniteDimensional K
      ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule : Submodule K M) := fun i ↦ by
    rw [← LieSubmodule.toSubmodule_map_weightSpace_incl (N i) χ]
    exact Module.Finite.equiv
      (LieSubmodule.equivMapOfInjective
        (f := (N i).incl.restrictLie H) (weightSpace ↥(N i) χ)
        (LieSubmodule.injective_incl (N i))).toLinearEquiv
  have hindep : iSupIndep fun i ↦
      ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule) :=
    h.submodule_iSupIndep.mono fun i ↦ inf_le_right
  -- This is the honest-weight analogue of the component argument in
  -- `TauCeti.Algebra.Lie.Weights.FormalCharacter`, through the shared canonical projection.
  have hcomponent : ∀ (m : M), m ∈ (weightSpace M χ).toSubmodule → ∀ i,
      (((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun j ↦ (N j).toSubmodule) h).symm m i : N i) : M)
        ∈ (weightSpace M χ).toSubmodule := fun m hm i ↦
    LieModule.map_weightSpace_le ((h.lieModuleProjection i).restrictLie H) χ
      ⟨m, hm, h.lieModuleProjection_apply i m⟩
  rw [← TauCeti.finrank_toSubmodule,
    ← h.iSup_inf_eq_of_component_mem (weightSpace M χ).toSubmodule hcomponent,
    @TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep K M ι _ _ _ _ _ hfinite hindep]
  exact Finset.sum_congr rfl fun i _ ↦ (N i).finrank_inf_weightSpace χ

end DirectSum.IsInternal

namespace LieModule

open Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}
  {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  {S : Type*} [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S]

/-- **Weight-space dimension in an isotypic module.** Suppose `M` is a finite-dimensional
completely reducible module, isotypic of an irreducible type `S`. The dimension of every weight
space of `M` is the number of copies of `S` times the dimension of the corresponding weight space
of `S`. -/
theorem IsIsotypicOfType.finrank_weightSpace_eq_isotypicMultiplicity_mul
    [IsAlgClosed K] [FiniteDimensional K M] [FiniteDimensional K S]
    [IsIrreducible K L S] [ComplementedLattice (LieSubmodule K L M)]
    (h : IsIsotypicOfType K L M S) (χ : H → K) :
    finrank K (weightSpace M χ) =
      isotypicMultiplicity K L M S * finrank K (weightSpace S χ) := by
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
  have hsummand : ∀ i, finrank K (weightSpace ↥(N i) χ) =
      finrank K (weightSpace S χ) := fun i ↦
    (TauCeti.LieModuleEquiv.restrictLie (hequiv i).some H).finrank_weightSpace_eq χ
  rw [hint.finrank_weightSpace_eq_sum (N := N) χ]
  simp only [hsummand]
  calc
    ∑ _ : Fin k, finrank K (weightSpace S χ) = k * finrank K (weightSpace S χ) := by
      simp
    _ = isotypicMultiplicity K L M S * finrank K (weightSpace S χ) := by rw [hmul]

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
  rw [h.finrank_weightSpace_eq_isotypicMultiplicity_mul χ, hone, mul_one]

end LieModule
