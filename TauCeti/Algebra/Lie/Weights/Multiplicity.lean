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
import TauCeti.Algebra.Lie.Submodule.DirectSum
import TauCeti.Algebra.Lie.Submodule.Finrank
import TauCeti.LinearAlgebra.Dimension.DirectSum
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

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

The internal-decomposition argument adapts the generalized-weight-space construction in
`TauCeti.Algebra.Lie.Weights.FormalCharacter`; the common component/reassembly step is factored
through `DirectSum.IsInternal.iSup_inf_eq_of_component_mem`.

## Main results

* `TauCeti.finrank_weightSpace_congr`: equivalent Lie modules have weight spaces of equal
  dimension.
* `TauCeti.finrank_weightSpace_eq_sum_of_isInternal`: weight-space dimensions add over a finite
  internal decomposition by Lie submodules.
* `LieModule.IsIsotypicOfType.finrank_weightSpace_eq_isotypicMultiplicity_mul`: the dimension of
  an isotypic weight space is the number of summands times its dimension in the irreducible type.
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

/-- The underlying submodule of a weight space is its simultaneous eigenspace. -/
private theorem weightSpace_toSubmodule_eq_iInf_eigenspace
    {P : Type*} [AddCommGroup P] [Module K P] [LieRingModule H P] [LieModule K H P]
    (χ : H → K) :
    (weightSpace P χ).toSubmodule =
      ⨅ x : H, (LieModule.toEnd K H P x).eigenspace (χ x) := rfl

/-- For a Lie submodule, the restricted action and inclusion underlying its weight space are the
restrictions and subtype map of the ambient action. -/
private theorem toSubmodule_map_weightSpace_incl_eq_restricted_iInf
    (i : ι) (χ : H → K)
    (hp : ∀ x : H, Set.MapsTo (LieModule.toEnd K H M x)
      (N i).toSubmodule (N i).toSubmodule) :
    ((weightSpace ↥(N i) χ).map ((N i).incl.restrictLie H)).toSubmodule =
      (⨅ x : H, Module.End.eigenspace ((LieModule.toEnd K H M x).restrict (hp x))
        (χ x)).map
        (N i).toSubmodule.subtype := rfl

/-- The image of a summand's weight space is its intersection with the ambient weight space. -/
private theorem toSubmodule_map_weightSpace_incl (i : ι) (χ : H → K) :
    ((weightSpace ↥(N i) χ).map ((N i).incl.restrictLie H)).toSubmodule
      = (weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule := by
  have hp : ∀ x : H, Set.MapsTo (LieModule.toEnd K H M x)
      (N i).toSubmodule (N i).toSubmodule := fun _ _ hm ↦ (N i).lie_mem hm
  have hbridge := Submodule.inf_iInf_eigenspace_of_forall_mapsTo
    (f := fun x : H ↦ LieModule.toEnd K H M x) (N i).toSubmodule hp χ
  rw [toSubmodule_map_weightSpace_incl_eq_restricted_iInf (hp := hp),
    weightSpace_toSubmodule_eq_iInf_eigenspace, ← hbridge, inf_comm]

/-- The intersection carrying a summand's weight space has the expected dimension. -/
private theorem finrank_inf_weightSpace (i : ι) (χ : H → K) :
    finrank K ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule : Submodule K M)
      = finrank K (weightSpace ↥(N i) χ) := by
  have hequiv := (LieSubmodule.equivMapOfInjective
    (weightSpace ↥(N i) χ) (injective_incl_restrictLie i)).toLinearEquiv.finrank_eq
  rw [← toSubmodule_map_weightSpace_incl i χ, finrank_toSubmodule, ← hequiv]

/-- **Weight-space dimensions are additive over an internal decomposition.** If a finite family of
`L`-submodules is an internal direct sum of `M`, then the dimension of the `χ`-weight space for any
Lie subalgebra `H` is the sum of the dimensions of the summands' `χ`-weight spaces. -/
theorem finrank_weightSpace_eq_sum_of_isInternal [FiniteDimensional K M]
    [Fintype ι] {dec_ι : DecidableEq ι}
    (h : @DirectSum.IsInternal ι M (Submodule K M) dec_ι _ _ _
      fun i ↦ (N i).toSubmodule) (χ : H → K) :
    finrank K (weightSpace M χ) = ∑ i, finrank K (weightSpace ↥(N i) χ) := by
  let _ := dec_ι
  classical
  have hindep : iSupIndep fun i ↦
      ((weightSpace M χ).toSubmodule ⊓ (N i).toSubmodule) :=
    h.submodule_iSupIndep.mono fun i ↦ inf_le_right
  have hcomponent : ∀ (m : M), m ∈ (weightSpace M χ).toSubmodule → ∀ i,
      (((DirectSum.lieModuleEquivOfIsInternal N h).symm m i : N i) : M)
        ∈ (weightSpace M χ).toSubmodule := fun m hm i ↦ by
    have hcomp : (DirectSum.lieModuleEquivOfIsInternal N h).symm m i
        ∈ weightSpace ↥(N i) χ :=
      LieModule.map_weightSpace_le
        ((((DirectSum.lieModuleComponent K ι L fun j ↦ ↥(N j)) i).comp
          ((DirectSum.lieModuleEquivOfIsInternal N h).symm :
            M →ₗ⁅K,L⁆ ⨁ j, ↥(N j))).restrictLie H) χ ⟨m, hm, rfl⟩
    exact LieModule.map_weightSpace_le ((N i).incl.restrictLie H) χ ⟨_, hcomp, rfl⟩
  rw [← finrank_toSubmodule,
    ← h.iSup_inf_eq_of_component_mem (weightSpace M χ).toSubmodule hcomponent,
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
    TauCeti.finrank_weightSpace_congr
      (TauCeti.LieModuleEquiv.restrictLie (hequiv i).some H) χ
  rw [TauCeti.finrank_weightSpace_eq_sum_of_isInternal (N := N) hint]
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
