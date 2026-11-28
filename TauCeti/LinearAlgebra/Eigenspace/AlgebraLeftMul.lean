/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Joint generalized eigenvectors of commuting left multiplications

Let `R` be a `K`-algebra over a field `K`, `S : Submodule K R` a finite-dimensional subspace, and
`G : ι → R` a pairwise-commuting family of elements preserving `S` under left multiplication. When
the restricted left multiplications `Algebra.lmul K R (G a)` are triangularizable on `S` (in
particular whenever `K` is algebraically closed), their joint generalized eigenspaces span `S`.
Hence for any proper submodule `U : Submodule K S` (or any nonzero linear map `τ : S →ₗ[K] W`),
there exists a joint generalized eigenvector `z ∈ S` outside `U` (resp. with `τ z ≠ 0`), meaning
`(G a - χ a • 1) ^ N * (z : R) = 0` for each `a` and some `N : ℕ`.

## Main results

* `Algebra.exists_notMem_and_pow_sub_smul_mul_eq_zero_of_commute`: joint generalized eigenvector in
  `S` outside a proper submodule `U ≠ ⊤`, assuming triangularizability on `S`.
* `Algebra.exists_notMem_and_pow_sub_smul_mul_eq_zero_of_isAlgClosed`: algebraically closed
  specialization.
* `Algebra.exists_apply_ne_zero_and_pow_sub_smul_mul_eq_zero_of_isAlgClosed`: form for a nonzero
  linear map `τ : S →ₗ[K] W`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/LinearAlgebra/Eigenvalues.lean` (`New.exists_pow_sub_smul_mul_eq_zero_of_commute`).
-/

@[expose] public section

open Module

namespace Algebra

/-- Let `G : ι → R` be pairwise-commuting elements of a `K`-algebra `R` preserving a
finite-dimensional subspace `S : Submodule K R` under left multiplication, such that each
restricted left multiplication is triangularizable on `S`. For any proper submodule `U ≠ ⊤` of `S`,
there exist `χ : ι → K` and `z : S` with `z ∉ U` such that for every `a`, `(G a - χ a • 1) ^ N`
annihilates `z` on the left for some `N : ℕ`. -/
theorem exists_notMem_and_pow_sub_smul_mul_eq_zero_of_commute {K R ι : Type*} [Field K]
    [Ring R] [Algebra K R] {S : Submodule K R} [FiniteDimensional K S] {G : ι → R}
    (hG_comm : Pairwise fun a a' ↦ Commute (G a) (G a'))
    (hG_maps : ∀ a : ι, ∀ z ∈ S, G a * z ∈ S)
    (htri : ∀ a : ι,
      ⨆ μ : K, End.maxGenEigenspace ((Algebra.lmul K R (G a)).restrict (hG_maps a)) μ = ⊤)
    {U : Submodule K S} (hU : U ≠ ⊤) :
    ∃ (χ : ι → K) (z : S), z ∉ U ∧ ∀ a : ι, ∃ N : ℕ, (G a - χ a • 1) ^ N * (z : R) = 0 := by
  let L (a : ι) : End K S := (Algebra.lmul K R (G a)).restrict (hG_maps a)
  have hL_comm : Pairwise fun a a' ↦ Commute (L a) (L a') := fun a a' hne ↦ by
    ext ⟨z, hz⟩
    simp [L, (hG_comm hne).left_comm z]
  have hspan : (⨆ χ : ι → K, ⨅ a : ι, (L a).maxGenEigenspace (χ a)) = ⊤ :=
    End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute L hL_comm htri
  have hnot : ∃ χ : ι → K, ¬⨅ a : ι, (L a).maxGenEigenspace (χ a) ≤ U := by
    by_contra! hle
    exact hU (top_le_iff.mp (hspan ▸ iSup_le hle))
  obtain ⟨χ, hχ⟩ := hnot
  obtain ⟨z, hz, hzU⟩ := IsConcreteLE.not_le_iff_exists.mp hχ
  refine ⟨χ, z, hzU, fun a ↦ ?_⟩
  have hmem : (z : R) ∈ (Algebra.lmul K R (G a)).maxGenEigenspace (χ a) :=
    (End.genEigenspace_restrict (Algebra.lmul K R (G a)) S ⊤ (χ a) (hG_maps a)).le
      ((Submodule.mem_iInf _).mp hz a)
  obtain ⟨N, hN⟩ := (End.mem_maxGenEigenspace _ _ _).mp hmem
  refine ⟨N, ?_⟩
  rwa [← map_one (Algebra.lmul K R), ← map_smul, ← map_sub, ← map_pow] at hN

/-- Over an algebraically closed field `K`, if `G : ι → R` are pairwise-commuting elements of a
`K`-algebra `R` preserving a finite-dimensional subspace `S : Submodule K R` under left
multiplication and `U ≠ ⊤` is a proper submodule of `S`, then there exist `χ : ι → K` and `z : S`
with `z ∉ U` such that each `G a - χ a • 1` has a power annihilating `z` on the left. -/
theorem exists_notMem_and_pow_sub_smul_mul_eq_zero_of_isAlgClosed {K R ι : Type*} [Field K]
    [IsAlgClosed K] [Ring R] [Algebra K R] {S : Submodule K R} [FiniteDimensional K S] {G : ι → R}
    (hG_comm : Pairwise fun a a' ↦ Commute (G a) (G a'))
    (hG_maps : ∀ a : ι, ∀ z ∈ S, G a * z ∈ S) {U : Submodule K S} (hU : U ≠ ⊤) :
    ∃ (χ : ι → K) (z : S), z ∉ U ∧ ∀ a : ι, ∃ N : ℕ, (G a - χ a • 1) ^ N * (z : R) = 0 :=
  exists_notMem_and_pow_sub_smul_mul_eq_zero_of_commute hG_comm hG_maps
    (fun _ ↦ End.iSup_maxGenEigenspace_eq_top _) hU

/-- Over an algebraically closed field `K`, if `G : ι → R` are pairwise-commuting elements of a
`K`-algebra `R` preserving a finite-dimensional subspace `S : Submodule K R` under left
multiplication and `τ : S →ₗ[K] W` is a nonzero linear map, then `τ z ≠ 0` for some joint
generalized eigenvector `z : S` of left multiplication by the `G a`. -/
theorem exists_apply_ne_zero_and_pow_sub_smul_mul_eq_zero_of_isAlgClosed {K R W ι : Type*}
    [Field K] [IsAlgClosed K] [Ring R] [Algebra K R] [AddCommMonoid W] [Module K W]
    {S : Submodule K R} [FiniteDimensional K S] {G : ι → R}
    (hG_comm : Pairwise fun a a' ↦ Commute (G a) (G a'))
    (hG_maps : ∀ a : ι, ∀ z ∈ S, G a * z ∈ S) {τ : S →ₗ[K] W} (hτ : τ ≠ 0) :
    ∃ (χ : ι → K) (z : S), τ z ≠ 0 ∧ ∀ a : ι, ∃ N : ℕ, (G a - χ a • 1) ^ N * (z : R) = 0 := by
  have hker : LinearMap.ker τ ≠ ⊤ := mt LinearMap.ker_eq_top.mp hτ
  simpa only [LinearMap.mem_ker] using
    exists_notMem_and_pow_sub_smul_mul_eq_zero_of_isAlgClosed hG_comm hG_maps hker

end Algebra
