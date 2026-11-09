/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Basic
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Global PBW symmetrization and its filtered surjectivity

For a Lie algebra over a commutative rational algebra, `pbwSymmetrizationMap` is
the linear map from the symmetric algebra to the enveloping algebra obtained
by averaging products over permutations. Every element of PBW filtration degree
at most `k` has a symmetric preimage of degree at most `k`. In particular the map
is surjective, without freeness or flatness assumptions on the Lie algebra.

The restriction to each homogeneous symmetric component is the existing
`pbwHomogeneousSymmetrization`. Thus the global map retains the permutation
formula while providing a single map for coalgebra comparisons.

The symmetrization construction is classical; see Dixmier, *Enveloping
Algebras*, §2.4. For its role over rational algebras without a freeness
hypothesis, see Petracci, *Universal representations of Lie algebras by
coderivations*, §8 (arXiv:math/0303020v1).

Adapted from [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
Modified for the Tau Ceti API.
-/

public noncomputable section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra
open scoped TensorProduct

universe v

variable (R : Type) (L : Type v) [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)
local notation "𝒮" => homogeneousSubmodule R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- The canonical linear symmetrization map, averaging each homogeneous
symmetric tensor over all orders of its Lie generators. -/
def pbwSymmetrizationMap : SymmetricAlgebra R L →ₗ[R] U :=
  (DirectSum.toModule R ℕ U (fun n => pbwHomogeneousSymmetrization R L n
    (IsUnit.natCast_factorial_of_algebra ℚ n))).comp
      (DirectSum.decomposeLinearEquiv 𝒮).toLinearMap

/-- On a homogeneous symmetric polynomial the global map is the existing
degreewise symmetrization. The degree is supplied by the membership hypothesis. -/
theorem pbwSymmetrizationMap_of_mem {n : ℕ} {p : SymmetricAlgebra R L} (hp : p ∈ 𝒮 n) :
    pbwSymmetrizationMap R L p = pbwHomogeneousSymmetrization R L n
      (IsUnit.natCast_factorial_of_algebra ℚ n) ⟨p, hp⟩ := by
  simp only [pbwSymmetrizationMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝒮 hp,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

/-- Multiplying a symmetric tensor and then applying the global map gives the
degreewise permutation average. -/
@[simp]
theorem pbwSymmetrizationMap_toSymmetricAlgebra (n : ℕ) (x : Sym[R]^n L) :
    pbwSymmetrizationMap R L (TauCeti.SymmetricPower.toSymmetricAlgebra R L n x) =
      TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization R L n
        (IsUnit.natCast_factorial_of_algebra ℚ n) x := by
  rw [← TauCeti.SymmetricPower.coe_equivHomogeneous_apply,
    pbwSymmetrizationMap_of_mem R L (TauCeti.SymmetricPower.equivHomogeneous n x).property,
    pbwHomogeneousSymmetrization_equivHomogeneous]

/-- Symmetrization sends a product of generators to the average of their
ordered products, with the usual rational factorial denominator. -/
theorem pbwSymmetrizationMap_prod_ι (n : ℕ) (x : Fin n → L) :
    pbwSymmetrizationMap R L (∏ i, SymmetricAlgebra.ι R L (x i)) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i => ι (x (σ i))).prod := by
  have hp : ∏ i, SymmetricAlgebra.ι R L (x i) ∈ 𝒮 n := by
    simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn, List.length_ofFn] using
      prod_map_ι_mem_homogeneousSubmodule R L (List.ofFn x)
  rw [pbwSymmetrizationMap_of_mem R L hp, pbwHomogeneousSymmetrization_apply,
    TauCeti.SymmetricPower.equivHomogeneous_symm_prod_ι]
  exact TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_tprod_rat R L n _ x

/-- Pure powers are unchanged by averaging their identical factors. -/
@[simp]
theorem pbwSymmetrizationMap_ι_pow (x : L) (n : ℕ) :
    pbwSymmetrizationMap R L (SymmetricAlgebra.ι R L x ^ n) = ι x ^ n := by
  have hp : SymmetricAlgebra.ι R L x ^ n ∈ 𝒮 n := by
    simpa using prod_map_ι_mem_homogeneousSubmodule R L (List.replicate n x)
  rw [pbwSymmetrizationMap_of_mem R L hp]
  exact pbwHomogeneousSymmetrization_ι_pow R L n _ x hp

/-- The global map preserves the unit. -/
@[simp]
theorem pbwSymmetrizationMap_one : pbwSymmetrizationMap R L 1 = 1 := by
  simpa using pbwSymmetrizationMap_ι_pow R L (0 : L) 0

/-- The global map extends the canonical Lie map on generators. -/
@[simp]
theorem pbwSymmetrizationMap_ι (x : L) :
    pbwSymmetrizationMap R L (SymmetricAlgebra.ι R L x) = ι x := by
  simpa using pbwSymmetrizationMap_ι_pow R L x 1

/-- Symmetrization fixes scalars. -/
@[simp]
theorem pbwSymmetrizationMap_algebraMap (r : R) :
    pbwSymmetrizationMap R L (algebraMap R (SymmetricAlgebra R L) r) = algebraMap R U r := by
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, pbwSymmetrizationMap_one]

/-- Symmetrization does not increase word degree. -/
theorem pbwSymmetrizationMap_mem_pbwFiltration {k : ℕ} {p : SymmetricAlgebra R L}
    (hp : p ∈ F k) : pbwSymmetrizationMap R L p ∈ pbwFiltration R L k := by
  have hle : F k ≤ (pbwFiltration R L k).comap (pbwSymmetrizationMap R L) := by
    rw [TauCeti.Algebra.wordFiltration_eq_iSup_pow]
    refine iSup_le fun n => ?_
    intro p hp
    rw [Submodule.mem_comap, pbwSymmetrizationMap_of_mem R L hp]
    exact pbwFiltration_mono R L n.property
      (pbwHomogeneousSymmetrization_mem_pbwFiltration R L n _ _)
  exact hle hp

/-- Every leading PBW symbol can be lifted by a homogeneous symmetric element.
The error has strictly smaller word degree. -/
theorem exists_sub_pbwSymmetrizationMap_mem_previous {k : ℕ} {a : U}
    (ha : a ∈ pbwFiltration R L k) :
    ∃ p : 𝒮 k, a - pbwSymmetrizationMap R L p ∈ pbwFiltrationPrevious R L k := by
  obtain ⟨p, hp⟩ := pbwHomogeneousComponentMap_surjective R L k
    (Submodule.Quotient.mk (⟨a, by simpa only [pbwFiltration_def] using ha⟩ :
      TauCeti.Algebra.wordFiltration (ι).toLinearMap k))
  refine ⟨p, ?_⟩
  rw [← mk_pbwHomogeneousSymmetrization R L k
    (IsUnit.natCast_factorial_of_algebra ℚ k)] at hp
  have hsub := (Submodule.Quotient.eq _).mp hp.symm
  rw [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff] at hsub
  simpa only [Submodule.coe_sub, pbwSymmetrizationMap_of_mem R L p.property,
    pbwFiltrationPrevious_def] using hsub

/-- Every element in PBW filtration degree `k` has a symmetric preimage of
word degree at most `k`, without a freeness assumption. -/
theorem exists_pbwSymmetrizationMap_eq_of_mem {k : ℕ} {a : U}
    (ha : a ∈ pbwFiltration R L k) :
    ∃ p ∈ F k, pbwSymmetrizationMap R L p = a := by
  induction k generalizing a with
  | zero =>
    obtain ⟨p, hp⟩ := exists_sub_pbwSymmetrizationMap_mem_previous R L ha
    have he : a = pbwSymmetrizationMap R L p := by
      simpa only [pbwFiltrationPrevious_zero, Submodule.mem_bot, sub_eq_zero] using hp
    exact ⟨p, TauCeti.Algebra.range_pow_le_wordFiltration _ 0 p.property, he.symm⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := exists_sub_pbwSymmetrizationMap_mem_previous R L ha
    rw [pbwFiltrationPrevious_succ] at hp
    obtain ⟨q, hq, he⟩ := ih hp
    refine ⟨q + p, (F (k + 1)).add_mem
      (TauCeti.Algebra.wordFiltration_mono _ (Nat.le_succ k) hq)
      (TauCeti.Algebra.range_pow_le_wordFiltration _ (k + 1) p.property), ?_⟩
    rw [map_add, he, sub_add_cancel]

/-- Symmetrization maps each symmetric word-filtration step onto precisely
the corresponding PBW step. -/
@[simp]
theorem map_wordFiltration_pbwSymmetrizationMap (k : ℕ) :
    (F k).map (pbwSymmetrizationMap R L) = pbwFiltration R L k := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact pbwSymmetrizationMap_mem_pbwFiltration R L hp
  · intro a ha
    obtain ⟨p, hp, he⟩ := exists_pbwSymmetrizationMap_eq_of_mem R L ha
    exact ⟨p, hp, he⟩

/-- Global symmetrization is surjective over every commutative rational algebra. -/
theorem pbwSymmetrizationMap_surjective : Function.Surjective (pbwSymmetrizationMap R L) := by
  intro a
  obtain ⟨k, hk⟩ := exists_mem_pbwFiltration R L a
  obtain ⟨p, _, hp⟩ := exists_pbwSymmetrizationMap_eq_of_mem R L hk
  exact ⟨p, hp⟩

end TauCeti.UniversalEnvelopingAlgebra
