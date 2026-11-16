/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Folding.BlockReflection
public import TauCeti.LinearAlgebra.RootSystem.Folding.Realization
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Orthogonal folding of simply laced root systems

Let `P` be a finite reduced crystallographic root system over a linearly ordered field `K`, with
simply laced base `b`, and let `σ` be a based automorphism of `P` whose simple-root orbits are
pairwise orthogonal: no two distinct simple roots in the same `σ`-orbit are joined by an edge.

By `RootPairing.pairwise_isOrthogonal_orbitIndices`, every root orbit of `σ` is pairwise orthogonal
and its orbit sum has squared length `2 |O|` under `b.simplyLacedInvariantForm hsl`. Using the
duality induced by this form on `E^σ = LinearMap.fixedSubmodule σ.weightMap`, the distinct orbit
sums `P.foldedIndices σ` form a reduced crystallographic root system on `E^σ` and its linear dual
(`RootPairing.OrbitSumRealization.ofOrthogonal`).

By uniqueness of orbit-sum realizations (`Subsingleton (P.OrbitSumRealization b σ)`), every
realization in the orthogonal case satisfies explicit formulas for coroots, pairings, Cartan
integers (including `-N_{O,T} / |T|` on distinct simple orbits), and reflections.

## Main definitions

* `RootPairing.OrbitSumRealization.ofOrthogonal`: the orbit-sum realization constructed from an
  orthogonal based automorphism of a simply laced root system over a linearly ordered field.

## Main results

* `RootPairing.OrbitSumRealization.coroot_orbitSum_apply`: explicit coroot evaluation on `E^σ`.
* `RootPairing.OrbitSumRealization.pairing_orbitSum` and
  `RootPairing.OrbitSumRealization.pairingIn_orbitSum`: explicit pairings and Cartan integers.
* `RootPairing.OrbitSumRealization.card_mul_pairingIn_orbitSum_eq_neg_card_edges`: edge-count
  formula for folded Cartan entries between distinct simple orbits.
* `RootPairing.OrbitSumRealization.coe_reflection_orbitSum` and
  `RootPairing.OrbitSumRealization.coe_ofIdx_smul_orbitSum`: identification of folded reflections
  with ambient block reflections on `E^σ`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claim 5.
-/

public section

namespace RootPairing

open Finset TauCeti

namespace OrbitSumRealization

section OrthogonalConstruction

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  {b : P.Base} {σ : P.Aut}

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite ι] [P.IsReduced] [P.IsCrystallographic] in
private theorem coord_root_self (j : b.support) :
    b.toWeightBasis.coord j (P.root j.1) = 1 := by
  rw [show P.root j.1 = b.toWeightBasis j from (b.toWeightBasis_apply j).symm,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite ι] [P.IsReduced] [P.IsCrystallographic] in
private theorem coord_root_ne (j : b.support) {a : ι} (ha : a ∈ b.support) (h : a ≠ j.1) :
    b.toWeightBasis.coord j (P.root a) = 0 := by
  classical
  rw [show P.root a = b.toWeightBasis ⟨a, ha⟩ from (b.toWeightBasis_apply ⟨a, ha⟩).symm,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff.mpr fun heq ↦ absurd (congrArg Subtype.val heq) h]

omit [P.IsReduced] [P.IsCrystallographic] in
private theorem orbitSum_eq_orbitSum_iff_of_mem_support
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.orbitSum σ i = P.orbitSum σ j ↔ j ∈ P.orbitIndices σ i := by
  classical
  refine ⟨fun heq ↦ ?_, fun h ↦ (orbitSum_eq_of_mem h).symm⟩
  have hrepr : ∀ x ∈ b.support,
      b.toWeightBasis.coord ⟨j, hj⟩ (P.orbitSum σ x) =
        if j ∈ P.orbitIndices σ x then (1 : K) else 0 := by
    intro x hx
    rw [orbitSum_def, map_sum, ← Finset.sum_ite_eq (P.orbitIndices σ x) j (fun _ ↦ (1 : K))]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    by_cases haj : a = j
    · subst haj; simp [coord_root_self ⟨a, hj⟩]
    · simp [coord_root_ne ⟨j, hj⟩ (P.mem_support_of_mem_orbitIndices σ hσ hx ha) haj, Ne.symm haj]
  have h1 := hrepr i hi
  rw [heq, hrepr j hj, ite_eq_left_iff.mpr fun h ↦ absurd (P.self_mem_orbitIndices σ j) h] at h1
  by_contra hnot
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h hnot] at h1
  exact one_ne_zero h1

omit [P.IsReduced] [P.IsCrystallographic] in
private theorem simple_fiber_eq_orbitIndices [DecidableEq M]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i : ι} (hi : i ∈ b.support) :
    b.support.filter (fun j ↦
      (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ : P.foldedIndices σ) =
        ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩) =
      P.orbitIndices σ i := by
  ext j
  simp only [Finset.mem_filter, Subtype.mk.injEq]
  exact ⟨fun ⟨hj, heq⟩ ↦ (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi hj).mp heq.symm,
    fun hj ↦ ⟨P.mem_support_of_mem_orbitIndices σ hσ hi hj, orbitSum_eq_of_mem hj⟩⟩

omit [LinearOrder K] [IsStrictOrderedRing K] [Finite ι] [P.IsReduced] [P.IsCrystallographic] in
private theorem repr_indexEquiv_of_mem_fixedSubmodule
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {v : M} (hv : v ∈ LinearMap.fixedSubmodule σ.weightMap) {j : ι} (hj : j ∈ b.support) :
    b.toWeightBasis.repr v ⟨σ.indexEquiv j, hσ j hj⟩ = b.toWeightBasis.repr v ⟨j, hj⟩ := by
  have hvfix : σ.weightMap v = v := LinearMap.mem_fixedSubmodule_iff.mp hv
  conv_lhs => rw [← Module.Basis.coord_apply, ← hvfix, ← b.toWeightBasis.sum_repr v]
  rw [map_sum, map_sum, Finset.sum_eq_single ⟨j, hj⟩]
  · rw [map_smul, b.toWeightBasis_apply, Hom.root_weightMap_apply, map_smul,
      coord_root_self ⟨σ.indexEquiv j, hσ j hj⟩, smul_eq_mul, mul_one]
  · intro a _ haj
    rw [map_smul, b.toWeightBasis_apply, Hom.root_weightMap_apply, map_smul,
      coord_root_ne ⟨σ.indexEquiv j, hσ j hj⟩ (hσ a.1 a.2)
        (fun h ↦ haj (Subtype.ext (σ.indexEquiv.injective h))),
      smul_zero]
  · exact fun hnot ↦ absurd (Finset.mem_univ _) hnot

omit [LinearOrder K] [IsStrictOrderedRing K] [P.IsReduced] [P.IsCrystallographic] in
private theorem repr_eq_of_mem_orbitIndices
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {v : M} (hv : v ∈ LinearMap.fixedSubmodule σ.weightMap)
    {i j : ι} (hi : i ∈ b.support) (hji : j ∈ P.orbitIndices σ i) :
    b.toWeightBasis.repr v ⟨j, P.mem_support_of_mem_orbitIndices σ hσ hi hji⟩ =
      b.toWeightBasis.repr v ⟨i, hi⟩ := by
  have hmem (m : ℕ) : (σ.indexEquiv ^ m) i ∈ b.support :=
    P.mem_support_of_mem_orbitIndices σ hσ hi (mem_orbitIndices_iff_exists_pow.mpr ⟨m, rfl⟩)
  have hpow : ∀ n : ℕ, b.toWeightBasis.repr v ⟨(σ.indexEquiv ^ n) i, hmem n⟩ =
      b.toWeightBasis.repr v ⟨i, hi⟩ := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      have hsub : (⟨(σ.indexEquiv ^ (m + 1)) i, hmem (m + 1)⟩ : b.support) =
          ⟨σ.indexEquiv ((σ.indexEquiv ^ m) i), hσ _ (hmem m)⟩ :=
        Subtype.ext (by dsimp only; rw [pow_succ', Equiv.Perm.mul_apply])
      rw [hsub, repr_indexEquiv_of_mem_fixedSubmodule hσ hv (hmem m), ih]
  obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hji
  exact hpow n

omit [P.IsReduced] [P.IsCrystallographic] in
private theorem sum_support_smul_eq_sum_simpleOrbits {A : Type*} [Semiring A] [Module A M]
    [DecidableEq M] (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (c : ι → A) (hc : ∀ {i j}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i)
    (f : P.foldedIndices σ → A)
    (hf : ∀ i ∈ b.support, f ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ = c i) :
    ∑ j ∈ b.support, c j • P.root j =
      ∑ s ∈ b.support.image (fun j ↦ (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ :
        P.foldedIndices σ)), f s • (s : M) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := b.support)
    (g := fun j ↦ (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ : P.foldedIndices σ))
    (fun j hj ↦ Finset.mem_image_of_mem _ hj)]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
  rw [simple_fiber_eq_orbitIndices hσ hi, hf i hi]
  dsimp only
  rw [orbitSum_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [hc hi hj]

omit [P.IsReduced] [P.IsCrystallographic] in
private theorem exists_sum_simpleOrbits_eq {A : Type*} [Semiring A] [Module A M] [DecidableEq M]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (c : ι → A) (hc : ∀ {i j}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i) :
    ∃ f : P.foldedIndices σ → A,
      ∑ j ∈ b.support, c j • P.root j =
        ∑ s ∈ b.support.image (fun j ↦ (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ :
          P.foldedIndices σ)), f s • (s : M) := by
  classical
  set S : Finset (P.foldedIndices σ) :=
    b.support.image fun j ↦ ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
  refine ⟨fun s ↦ if hs : s ∈ S then c (Finset.mem_image.mp hs).choose else 0,
    sum_support_smul_eq_sum_simpleOrbits hσ c hc _ fun i hi ↦ ?_⟩
  have his : (⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ : P.foldedIndices σ) ∈ S :=
    Finset.mem_image_of_mem _ hi
  rw [dite_eq_left_of_eq_true (eq_true his)]
  set j := (Finset.mem_image.mp his).choose
  have hj : j ∈ b.support := (Finset.mem_image.mp his).choose_spec.1
  have hji : P.orbitSum σ j = P.orbitSum σ i :=
    congrArg Subtype.val (Finset.mem_image.mp his).choose_spec.2
  exact (hc hj ((orbitSum_eq_orbitSum_iff_of_mem_support hσ hj hi).mp hji)).symm

private noncomputable def foldedRoot (P : RootPairing ι K M N) (σ : P.Aut) :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap where
  toFun x := ⟨x.1, by
    obtain ⟨k, hk⟩ := mem_foldedIndices.mp x.2
    exact hk ▸ P.orbitSum_mem_fixedSubmodule σ k⟩
  inj' _ _ h := Subtype.ext (congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) h)

omit [LinearOrder K] [IsStrictOrderedRing K] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  in
@[simp]
private theorem coe_foldedRoot (x : P.foldedIndices σ) : (foldedRoot P σ x : M) = (x : M) :=
  rfl

private noncomputable def foldedCorootFun (hsl : b.cartanMatrix.IsSimplyLaced)
    (x : P.foldedIndices σ) : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
  (2 / (b.simplyLacedInvariantForm hsl).form x.1 x.1) •
    ((b.simplyLacedInvariantForm hsl).form.flip x.1).comp
      (LinearMap.fixedSubmodule σ.weightMap).subtype

omit [P.IsReduced] in
private theorem foldedCorootFun_self
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced) (x : P.foldedIndices σ) :
    foldedCorootFun hsl x (foldedRoot P σ x) = 2 := by
  have hx0 : (x : M) ≠ 0 := fun h ↦ zero_notMem_foldedIndices hσ (h ▸ x.2)
  have hpos : (b.simplyLacedInvariantForm hsl).form x.1 x.1 ≠ 0 :=
    (b.posDef_simplyLacedInvariantForm hsl x.1 hx0).ne'
  have hfl : (b.simplyLacedInvariantForm hsl).form.flip x.1 x.1 =
      (b.simplyLacedInvariantForm hsl).form x.1 x.1 := rfl
  simp only [foldedCorootFun, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, coe_foldedRoot, smul_eq_mul, hfl]
  exact div_mul_cancel₀ (2 : K) hpos

private theorem foldedCorootFun_orbitSum
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) (v : LinearMap.fixedSubmodule σ.weightMap) :
    foldedCorootFun hsl ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ v =
      P.coroot' k (v : M) := by
  have hform : (b.simplyLacedInvariantForm hsl).form (v : M) (P.orbitSum σ k) =
      (#(P.orbitIndices σ k) : K) * P.coroot' k (v : M) := by
    rw [orbitSum_def, map_sum]
    trans ∑ _a ∈ P.orbitIndices σ k, P.coroot' k (v : M)
    · refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [b.simplyLacedInvariantForm_apply_root hsl]
      exact P.coroot'_eq_of_mem_orbitIndices_of_mem_fixedSubmodule σ ha v.2
    · rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (#(P.orbitIndices σ k) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.card_orbitIndices_pos σ k).ne'
  have hflip : (b.simplyLacedInvariantForm hsl).form.flip (P.orbitSum σ k) (v : M) =
      (b.simplyLacedInvariantForm hsl).form (v : M) (P.orbitSum σ k) := rfl
  simp only [foldedCorootFun, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    smul_eq_mul, hflip, b.simplyLacedInvariantForm_orbitSum_self hσ hsl horth k, hform]
  field_simp [hcard]

private theorem foldedRoot_reduced
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (x y : P.foldedIndices σ)
    (hdep : ¬ LinearIndependent K ![foldedRoot P σ x, foldedRoot P σ y]) :
    (x : M) = (y : M) ∨ (x : M) = -(y : M) := by
  classical
  have hpos_case : ∀ (i k : ι), i ∈ b.support → b.IsPos k → ∀ c : K,
      P.orbitSum σ k = c • P.orbitSum σ i → P.orbitSum σ k = P.orbitSum σ i := by
    intro i k hi hk c hck
    obtain ⟨f, -, hf⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b k).mpr hk)
    obtain ⟨g, hg⟩ := (mem_posRootCone P b).mp (sum_mem fun a ha ↦
      root_mem_posRootCone_of_mem_posRoots P b ((mem_posRoots P b a).mpr
        ((isPos_iff_of_mem_orbitIndices hσ (Finset.mem_of_mem_erase ha)).mpr hk)) :
      ∑ a ∈ (P.orbitIndices σ k).erase k, P.root a ∈ posRootCone P b)
    have hsum_k : P.orbitSum σ k = ∑ j ∈ b.support, (f j + g j) • P.root j := by
      rw [orbitSum_def, ← Finset.add_sum_erase _ _ (P.self_mem_orbitIndices σ k), hf, hg,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ (add_nsmul _ _ _).symm
    have hzero_out : ∀ j ∈ b.support, j ∉ P.orbitIndices σ i → f j = 0 := by
      intro j hj hjnot
      have hrepr_l : b.toWeightBasis.coord ⟨j, hj⟩ (P.orbitSum σ k) = ((f j + g j : ℕ) : K) := by
        rw [hsum_k, map_sum, Finset.sum_eq_single_of_mem j hj]
        · rw [map_nsmul, coord_root_self ⟨j, hj⟩, nsmul_eq_mul, mul_one]
        · exact fun a ha haj ↦ by rw [map_nsmul, coord_root_ne ⟨j, hj⟩ ha haj, smul_zero]
      have hrepr_r : b.toWeightBasis.coord ⟨j, hj⟩ (c • P.orbitSum σ i) = 0 := by
        rw [orbitSum_def, Finset.smul_sum, map_sum]
        refine Finset.sum_eq_zero fun a ha ↦ ?_
        have haj : a ≠ j := fun h ↦ hjnot (h ▸ ha)
        rw [map_smul, coord_root_ne ⟨j, hj⟩ (P.mem_support_of_mem_orbitIndices σ hσ hi ha) haj,
          smul_zero]
      have hfg0' : f j + g j = 0 := Nat.cast_eq_zero.mp (by rw [← hrepr_l, hck, hrepr_r])
      omega
    have hfk : P.root k = ∑ a ∈ P.orbitIndices σ i, f a • P.root a := by
      rw [hf]
      exact (Finset.sum_subset (fun a ha ↦ P.mem_support_of_mem_orbitIndices σ hσ hi ha)
        fun j hj hjnot ↦ by rw [hzero_out j hj hjnot, zero_smul]).symm
    set B := b.simplyLacedInvariantForm hsl
    have horth_i := P.pairwise_isOrthogonal_orbitIndices_of_mem_support σ hσ horth hi
    have hnorm : B.form (P.root k) (P.root k) =
        2 * ((∑ a ∈ P.orbitIndices σ i, f a * f a : ℕ) : K) := by
      rw [hfk, map_sum, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [map_sum, LinearMap.sum_apply,
        Finset.sum_eq_single_of_mem a ha (fun a' ha' hne ↦ by
          rw [map_nsmul, map_nsmul, LinearMap.smul_apply,
            b.simplyLacedInvariantForm_root_root hsl, (horth_i ha' ha hne).1,
            smul_zero, smul_zero]),
        map_nsmul, map_nsmul, LinearMap.smul_apply,
        b.simplyLacedInvariantForm_root_self hsl, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [b.simplyLacedInvariantForm_root_self hsl] at hnorm
    have hsq1 : ∑ a ∈ P.orbitIndices σ i, f a * f a = 1 := by
      have h1 : ((∑ a ∈ P.orbitIndices σ i, f a * f a : ℕ) : K) = 1 :=
        mul_left_cancel₀ (two_ne_zero (α := K)) (by linear_combination -hnorm)
      exact_mod_cast h1
    obtain ⟨a, ha, hfa_ne⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (hsq1.trans_ne one_ne_zero)
    have hle1 : f a * f a ≤ 1 :=
      hsq1 ▸ Finset.single_le_sum (f := fun a ↦ f a * f a) (fun _ _ ↦ Nat.zero_le _) ha
    have hfa_pos : 1 ≤ f a := Nat.pos_of_ne_zero fun h ↦ hfa_ne (by simp [h])
    have hfa1 : f a = 1 := by nlinarith
    have hother : ∀ a' ∈ P.orbitIndices σ i, a' ≠ a → f a' = 0 := by
      intro a' ha' hne
      rw [← Finset.add_sum_erase _ _ ha, hfa1, mul_one, add_eq_left,
        Finset.sum_eq_zero_iff] at hsq1
      exact mul_self_eq_zero.mp (hsq1 a' (Finset.mem_erase.mpr ⟨hne, ha'⟩))
    have hka : k = a := P.root.injective (by
      rw [hfk, Finset.sum_eq_single_of_mem a ha (fun a' ha' hne ↦ by rw [hother a' ha' hne,
        zero_smul]), hfa1, one_smul])
    rw [hka]
    exact orbitSum_eq_of_mem ha
  have hxy_dep : ¬ LinearIndependent K ![(x : M), (y : M)] := fun hli ↦ by
    have hcomp : ![(x : M), (y : M)] =
        (LinearMap.fixedSubmodule σ.weightMap).subtype ∘ ![foldedRoot P σ x, foldedRoot P σ y] := by
      ext t; fin_cases t <;> rfl
    exact hdep (LinearIndependent.of_comp (LinearMap.fixedSubmodule σ.weightMap).subtype
      (hcomp ▸ hli))
  rw [LinearIndependent.pair_iff] at hxy_dep
  push Not at hxy_dep
  obtain ⟨r, s, hrs, hne⟩ := hxy_dep
  have hs0 : s ≠ 0 := fun hs0 ↦ by
    rw [hs0, zero_smul, add_zero] at hrs
    exact (fun h ↦ zero_notMem_foldedIndices hσ (h ▸ x.2))
      ((smul_eq_zero.mp hrs).resolve_left fun hr ↦ hne hr hs0)
  have hy_eq : (y : M) = (-r / s) • (x : M) := by
    have h1 : s • (y : M) = (-r) • (x : M) := by
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hrs
    rw [div_eq_inv_mul, mul_smul, ← h1, inv_smul_smul₀ hs0]
  obtain ⟨k₁, hk₁⟩ := mem_foldedIndices.mp x.2
  obtain ⟨k₂, hk₂⟩ := mem_foldedIndices.mp y.2
  obtain ⟨w, hw, hwi⟩ := exists_mem_closure_blockReflection_mem_support hσ hsl horth k₁
  have hcomm := P.commute_of_mem_closure_blockReflection σ hσ horth hw
  have hmap_sum (j : ι) : w • P.orbitSum σ j = P.orbitSum σ (P.weylGroupToPerm w j) :=
    P.weightMap_orbitSum (w : P.Aut)
      (fun a ↦ congrArg (fun g : P.Aut ↦ g.indexEquiv a) hcomm) j
  have hw_eq : P.orbitSum σ (P.weylGroupToPerm w k₂) =
      (-r / s) • P.orbitSum σ (P.weylGroupToPerm w k₁) := by
    rw [← hmap_sum k₂, ← hmap_sum k₁, hk₁, hk₂, hy_eq, smul_comm]
  by_cases hpos : b.IsPos (P.weylGroupToPerm w k₂)
  · have heq := hpos_case _ _ hwi hpos (-r / s) hw_eq
    rw [← hmap_sum k₂, ← hmap_sum k₁] at heq
    exact Or.inl (hk₁.symm.trans ((by simpa using congrArg (w⁻¹ • ·) heq :
      P.orbitSum σ k₂ = P.orbitSum σ k₁).symm.trans hk₂))
  · have hpos' : b.IsPos (P.reflectionPerm (P.weylGroupToPerm w k₂) (P.weylGroupToPerm w k₂)) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b _).mpr ((mem_negRoots P b _).mpr hpos)
    have heq := hpos_case _ _ hwi hpos' (-(-r / s)) (by
      rw [orbitSum_reflectionPerm_self, hw_eq, neg_smul])
    rw [orbitSum_reflectionPerm_self, ← hmap_sum k₂, ← hmap_sum k₁] at heq
    exact Or.inr (hk₁.symm.trans ((by simpa [smul_neg] using congrArg (w⁻¹ • ·) heq :
      -(P.orbitSum σ k₂) = P.orbitSum σ k₁).symm.trans (congrArg Neg.neg hk₂)))

private noncomputable def foldedCoroot
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.foldedIndices σ ↪ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) where
  toFun := foldedCorootFun hsl
  inj' x y hxy := by
    set B := b.simplyLacedInvariantForm hsl
    set cx : K := 2 / B.form x.1 x.1
    set cy : K := 2 / B.form y.1 y.1
    have hdiff_zero : cx • foldedRoot P σ x - cy • foldedRoot P σ y = 0 := by
      set u := cx • foldedRoot P σ x - cy • foldedRoot P σ y
      have hu : B.form u.1 u.1 = 0 := by
        have heval := congrArg (fun f : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) ↦ f u)
          hxy
        simp only [foldedCorootFun, LinearMap.smul_apply, LinearMap.comp_apply,
          Submodule.coe_subtype, smul_eq_mul] at heval
        have hbu : B.form u.1 u.1 = cx * B.form u.1 x.1 - cy * B.form u.1 y.1 := by
          simp [u, map_sub, map_smul, smul_eq_mul]
        rw [hbu, show cx * B.form u.1 x.1 = cy * B.form u.1 y.1 from heval, sub_self]
      by_contra hne
      exact (b.posDef_simplyLacedInvariantForm hsl u.1 fun h ↦ hne (Subtype.ext h)).ne' hu
    have hcx : cx ≠ 0 := div_ne_zero two_ne_zero
      (b.posDef_simplyLacedInvariantForm hsl x.1 fun h ↦ zero_notMem_foldedIndices hσ (h ▸ x.2)).ne'
    have hdep : ¬ LinearIndependent K ![foldedRoot P σ x, foldedRoot P σ y] := by
      rw [LinearIndependent.pair_iff]
      push Not
      exact ⟨cx, -cy, by simpa [sub_eq_add_neg, neg_smul] using hdiff_zero, fun h ↦ absurd h hcx⟩
    rcases foldedRoot_reduced hσ hsl horth x y hdep with h | h
    · exact Subtype.ext h
    · exfalso
      have h1 := foldedCorootFun_self hσ hsl x
      have h2 : foldedCorootFun hsl y (foldedRoot P σ x) = -2 := by
        rw [show foldedRoot P σ x = -foldedRoot P σ y from Subtype.ext h, map_neg,
          foldedCorootFun_self hσ hsl y]
      rw [hxy, h2] at h1
      linarith

omit [P.IsReduced] [P.IsCrystallographic] in
private theorem span_foldedRoot_eq_top
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Submodule.span K (Set.range (foldedRoot P σ)) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun v _ ↦ ?_
  let c : ι → K := fun j ↦ if hj : j ∈ b.support then b.toWeightBasis.repr (v : M) ⟨j, hj⟩ else 0
  have hc : ∀ {i j}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i := fun hi hji ↦ by
    have hj := P.mem_support_of_mem_orbitIndices σ hσ hi hji
    simp only [c, dite_eq_left_of_eq_true (eq_true hj), dite_eq_left_of_eq_true (eq_true hi)]
    exact repr_eq_of_mem_orbitIndices hσ v.2 hi hji
  obtain ⟨f, hf⟩ := exists_sum_simpleOrbits_eq hσ c hc
  have hv_exp : (v : M) = ∑ j ∈ b.support, c j • P.root j := by
    conv_lhs => rw [← b.toWeightBasis.sum_repr (v : M)]
    rw [← Finset.sum_attach b.support]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [c, j.2, b.toWeightBasis_apply]
  have hsum_v : v = ∑ s ∈ b.support.image
      (fun j ↦ (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ : P.foldedIndices σ)),
      f s • foldedRoot P σ s := Subtype.ext (by
    rw [hv_exp, hf, Submodule.coe_sum]; exact Finset.sum_congr rfl fun _ _ ↦ rfl)
  rw [hsum_v]
  exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

private noncomputable def orthogonalPairing
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  haveI : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  haveI : Module.IsReflexive K (LinearMap.fixedSubmodule σ.weightMap) :=
    Module.IsReflexive.of_finite_of_free K (LinearMap.fixedSubmodule σ.weightMap)
  RootPairing.mk'' (Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap))
    (foldedRoot P σ) (foldedCoroot hσ hsl horth)
    (fun x ↦ foldedCorootFun_self hσ hsl x)
    (fun x ↦ by
      rintro _ ⟨y, rfl⟩
      obtain ⟨k, hk⟩ := mem_foldedIndices.mp x.2
      obtain ⟨j, hj⟩ := mem_foldedIndices.mp y.2
      have hx : x = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := Subtype.ext hk.symm
      have hy : y = ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ := Subtype.ext hj.symm
      set w := P.blockReflection σ k (pairwise_isOrthogonal_orbitIndices hσ hsl horth k)
      have hcomm : Commute (w : P.Aut) σ := P.commute_blockReflection_coe σ k _
      refine ⟨⟨P.orbitSum σ (P.weylGroupToPerm w j), P.orbitSum_mem_foldedIndices σ _⟩, ?_⟩
      apply Subtype.ext
      rw [hx, hy]
      -- Coerce the `preReflection` identity to the ambient space `M`.
      change P.orbitSum σ (P.weylGroupToPerm w j) =
        P.orbitSum σ j -
          foldedCorootFun hsl ⟨P.orbitSum σ k, _⟩ (foldedRoot P σ ⟨P.orbitSum σ j, _⟩) •
            P.orbitSum σ k
      rw [foldedCorootFun_orbitSum hσ hsl horth k, coe_foldedRoot, Subtype.coe_mk,
        ← P.blockReflection_smul_of_mem_fixedSubmodule σ k _ (P.orbitSum_mem_fixedSubmodule σ j),
        weylGroupToPerm_apply,
        ← P.weightMap_orbitSum (w : P.Aut)
          (fun a ↦ congrArg (fun g : P.Aut ↦ g.indexEquiv a) hcomm) j]
      rfl)
    (span_foldedRoot_eq_top hσ)

/-- **Existence of the orthogonal orbit-sum realization**: for a simply laced finite reduced
crystallographic root system over a linearly ordered field and a based automorphism `σ` whose
simple-root orbits are pairwise orthogonal, the distinct orbit sums form a reduced crystallographic
root system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual. -/
noncomputable def ofOrthogonal
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.OrbitSumRealization b σ := by
  classical
  haveI : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  haveI : Module.IsReflexive K (LinearMap.fixedSubmodule σ.weightMap) :=
    Module.IsReflexive.of_finite_of_free K (LinearMap.fixedSubmodule σ.weightMap)
  letI : Fintype (P.foldedIndices σ) := Fintype.ofFinite (P.foldedIndices σ)
  set Q := orthogonalPairing hσ hsl horth
  have hQroot (u : P.foldedIndices σ) : (Q.root u : M) = (u : M) := rfl
  have hQ_int : ∀ x y : P.foldedIndices σ, ∃ z : ℤ,
      (z : K) = Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
        (foldedRoot P σ x) (foldedCoroot hσ hsl horth y) := fun x y ↦ by
    obtain ⟨j, hj⟩ := mem_foldedIndices.mp x.2
    obtain ⟨k, hk⟩ := mem_foldedIndices.mp y.2
    have hy : y = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := Subtype.ext hk.symm
    refine ⟨∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k, ?_⟩
    rw [hy]
    -- Unfold `Module.Dual.eval` to the coroot functional `foldedCorootFun`.
    change ((∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k : ℤ) : K) =
      foldedCorootFun hsl ⟨P.orbitSum σ k, _⟩ (foldedRoot P σ x)
    rw [foldedCorootFun_orbitSum hσ hsl horth k, coe_foldedRoot, ← hj, orbitSum_def, map_sum,
      Int.cast_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by
      rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ]; rfl
  haveI hQ_rs : Q.IsRootSystem := RootPairing.isRootSystem_mk'' hQ_int
  haveI hQ_cry : Q.IsCrystallographic := ⟨hQ_int⟩
  haveI hQ_red : Q.IsReduced := ⟨fun x y hdep ↦
    (foldedRoot_reduced hσ hsl horth x y hdep).imp Subtype.ext Subtype.ext⟩
  set S : Finset (P.foldedIndices σ) :=
    b.support.image fun j ↦ ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
  have hS_li : LinearIndepOn K Q.root (S : Set (P.foldedIndices σ)) := by
    rw [linearIndepOn_iff']
    intro t g hts hsum s hs
    let f : P.foldedIndices σ → K := fun u ↦ if u ∈ t then g u else 0
    have hsumM : ∑ a ∈ b.support,
        f ⟨P.orbitSum σ a, P.orbitSum_mem_foldedIndices σ a⟩ • P.root a = 0 := by
      rw [sum_support_smul_eq_sum_simpleOrbits hσ _
        (fun {_ _} _ hji ↦ by
          rw [show (⟨P.orbitSum σ _, _⟩ : P.foldedIndices σ) = ⟨P.orbitSum σ _, _⟩ from
            Subtype.ext (orbitSum_eq_of_mem hji)])
        f (fun _ _ ↦ rfl)]
      have hfilt : S.filter (· ∈ t) = t := Finset.filter_mem_eq_inter.trans
        (Finset.inter_eq_right.mpr fun u hu ↦ hts hu)
      rw [show (∑ u ∈ S, f u • (u : M)) = ∑ u ∈ S.filter (· ∈ t), g u • (u : M) by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun _ _ ↦ by simp [f], hfilt]
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hQroot] using
        congrArg Subtype.val hsum
    have hcoeff0 := (linearIndepOn_iff'.mp b.linearIndepOn_root) b.support _ Set.Subset.rfl hsumM
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hs)
    simpa [f, hs] using hcoeff0 i hi
  have hQ_root_mem : ∀ x : P.foldedIndices σ,
      Q.root x ∈ AddSubmonoid.closure (Q.root '' (S : Set (P.foldedIndices σ))) ∨
        -Q.root x ∈ AddSubmonoid.closure (Q.root '' (S : Set (P.foldedIndices σ))) := by
    have hpos_mem : ∀ k : ι, b.IsPos k →
        Q.root ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ ∈
          AddSubmonoid.closure (Q.root '' (S : Set (P.foldedIndices σ))) := fun k hk ↦ by
      obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hk)
      have hf_repr : ∀ j (hj : j ∈ b.support),
          b.toWeightBasis.repr (P.orbitSum σ k) ⟨j, hj⟩ = (f j : K) := fun j hj ↦ by
        rw [← Module.Basis.coord_apply, hf, map_sum, Finset.sum_eq_single_of_mem j hj]
        · rw [map_nsmul, coord_root_self ⟨j, hj⟩, nsmul_eq_mul, mul_one]
        · exact fun a ha haj ↦ by rw [map_nsmul, coord_root_ne ⟨j, hj⟩ ha haj, smul_zero]
      have hf_orbit : ∀ {i j : ι}, i ∈ b.support → j ∈ P.orbitIndices σ i → f j = f i :=
        fun hi hji ↦ by
          have hstep := repr_eq_of_mem_orbitIndices hσ (P.orbitSum_mem_fixedSubmodule σ k) hi hji
          rw [hf_repr _ (P.mem_support_of_mem_orbitIndices σ hσ hi hji), hf_repr _ hi] at hstep
          exact Nat.cast_injective hstep
      obtain ⟨f', hf'⟩ := exists_sum_simpleOrbits_eq hσ f hf_orbit
      have hdecomp : Q.root ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ =
          ∑ s ∈ S, f' s • Q.root s := Subtype.ext (by
        rw [Submodule.coe_sum, hQroot, Subtype.coe_mk, hf, hf']
        exact Finset.sum_congr rfl fun _ _ ↦ rfl)
      rw [hdecomp]
      exact sum_mem fun s hs ↦
        nsmul_mem (AddSubmonoid.subset_closure (Set.mem_image_of_mem Q.root hs)) _
    intro x
    obtain ⟨k, hk⟩ := mem_foldedIndices.mp x.2
    rw [show x = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ from Subtype.ext hk.symm]
    by_cases hpos : b.IsPos k
    · exact Or.inl (hpos_mem k hpos)
    · right
      have hneg : -Q.root ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ =
          Q.root ⟨P.orbitSum σ (P.reflectionPerm k k), P.orbitSum_mem_foldedIndices σ _⟩ :=
        Subtype.ext (by
          rw [Submodule.coe_neg, hQroot, hQroot]; exact (P.orbitSum_reflectionPerm_self σ k).symm)
      rw [hneg]
      exact hpos_mem (P.reflectionPerm k k)
        ((isPos_reflectionPerm_self_iff_mem_negRoots P b k).mpr ((mem_negRoots P b k).mpr hpos))
  have hQ_coroot_mem : ∀ x : P.foldedIndices σ,
      Q.coroot x ∈ AddSubmonoid.closure (Q.coroot '' (S : Set (P.foldedIndices σ))) ∨
        -Q.coroot x ∈ AddSubmonoid.closure (Q.coroot '' (S : Set (P.foldedIndices σ))) := by
    let φ : N →+ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
      { toFun := fun y ↦ (P.toLinearMap.flip y).comp (LinearMap.fixedSubmodule σ.weightMap).subtype
        map_zero' := by ext v; simp
        map_add' := fun y₁ y₂ ↦ by ext v; simp }
    have hφ_coroot (j : ι) : φ (P.coroot j) =
        Q.coroot ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ :=
      LinearMap.ext fun v ↦ (foldedCorootFun_orbitSum hσ hsl horth j v).symm
    have hφ_maps : ∀ y ∈ AddSubmonoid.closure (P.coroot '' (b.support : Set ι)),
        φ y ∈ AddSubmonoid.closure (Q.coroot '' (S : Set (P.foldedIndices σ))) := fun y hy ↦ by
      induction hy using AddSubmonoid.closure_induction with
      | mem z hz =>
        obtain ⟨j, hj, rfl⟩ := hz
        rw [hφ_coroot j]
        exact AddSubmonoid.subset_closure ⟨_, Finset.mem_image_of_mem _ hj, rfl⟩
      | zero => simp
      | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
    intro x
    obtain ⟨k, hk⟩ := mem_foldedIndices.mp x.2
    rw [show x = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ from Subtype.ext hk.symm,
      ← hφ_coroot k]
    rcases b.coroot_mem_or_neg_mem k with h | h
    · exact Or.inl (hφ_maps _ h)
    · exact Or.inr (by simpa [map_neg] using hφ_maps _ h)
  exact
    { pairing := Q
      base :=
        { support := S
          linearIndepOn_root := hS_li
          linearIndepOn_coroot := Q.linearIndepOn_coroot_iff.mpr hS_li
          root_mem_or_neg_mem := hQ_root_mem
          coroot_mem_or_neg_mem := hQ_coroot_mem }
      rootSystem := hQ_rs
      reduced := hQ_red
      crystallographic := hQ_cry
      evaluation := fun _ _ ↦ rfl
      root_eq := fun _ ↦ rfl
      base_eq := fun x ↦ by
        simp only [S, Finset.mem_image]
        exact ⟨fun ⟨j, hj, h⟩ ↦ ⟨j, hj, congrArg Subtype.val h⟩,
          fun ⟨j, hj, h⟩ ↦ ⟨j, hj, Subtype.ext h⟩⟩ }

/-! ### Explicit formulas for any orthogonal orbit-sum realization -/

section ExplicitFormulas

variable (F : P.OrbitSumRealization b σ)
  (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
  (hsl : b.cartanMatrix.IsSimplyLaced)
  (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)

include hσ hsl horth

/-- **Coroots of an orthogonal orbit-sum realization**: each folded coroot evaluates on fixed
vectors as the ambient coroot functional of any representative root in the orbit. -/
theorem coroot_orbitSum_apply (k : ι) (v : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ v =
      P.coroot' k (v : M) := by
  obtain rfl : F = ofOrthogonal hσ hsl horth := Subsingleton.elim _ _
  exact foldedCorootFun_orbitSum hσ hsl horth k v

/-- **Pairings of an orthogonal orbit-sum realization**: the pairing of two folded roots is the
orbit sum of the ambient pairings against a representative of the second orbit. -/
theorem pairing_orbitSum (j k : ι) :
    F.pairing.pairing ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
      ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ =
      ∑ a ∈ P.orbitIndices σ j, P.pairing a k := by
  rw [← root_coroot'_eq_pairing, F.coroot'_apply, F.coroot_orbitSum_apply hσ hsl horth k,
    F.coe_root]
  dsimp only
  rw [orbitSum_def, map_sum]
  exact Finset.sum_congr rfl fun a _ ↦ root_coroot'_eq_pairing P k a

/-- **Cartan integers of an orthogonal orbit-sum realization**: the integral pairing of two folded
roots is the orbit sum of the ambient Cartan integers. -/
theorem pairingIn_orbitSum (j k : ι) :
    F.pairing.pairingIn ℤ ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
      ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ =
      ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [algebraMap_pairingIn, F.pairing_orbitSum hσ hsl horth j k, map_sum]
  exact Finset.sum_congr rfl fun a _ ↦ (P.algebraMap_pairingIn ℤ a k).symm

/-- **Edge-count formula for Cartan entries between distinct simple orbits**: multiplying the
folded Cartan integer `⟨β_O, β_T^∨⟩` by `|T|` gives minus the number of edges between `O` and `T`
in the simply laced diagram. -/
theorem card_mul_pairingIn_orbitSum_eq_neg_card_edges
    {j k : ι} (hj : j ∈ b.support) (hk : k ∈ b.support) (hjk : k ∉ P.orbitIndices σ j) :
    (#(P.orbitIndices σ k) : ℤ) *
        F.pairing.pairingIn ℤ ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
          ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ =
      -(#((P.orbitIndices σ j ×ˢ P.orbitIndices σ k).filter fun p ↦ P.pairingIn ℤ p.1 p.2 ≠ 0) :
        ℤ) := by
  rw [F.pairingIn_orbitSum hσ hsl horth j k]
  have hconst : ∀ c ∈ P.orbitIndices σ k,
      ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a c =
        ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k := fun c hc ↦ by
    have hstep (x : ι) :
        ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a (σ.indexEquiv x) =
          ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a x := by
      symm
      refine Finset.sum_equiv σ.indexEquiv (fun a ↦ indexEquiv_mem_orbitIndices_iff.symm)
        fun a _ ↦ FaithfulSMul.algebraMap_injective ℤ K ?_
      rw [algebraMap_pairingIn, algebraMap_pairingIn]
      exact (σ.toHom.pairing (i := a) (j := x)).symm
    exact (Equiv.Perm.SameCycle.apply_eq_of_apply_eq
      (f := fun x ↦ ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a x)
      (mem_orbitIndices.mp hc) hstep).symm
  have hdouble : (#(P.orbitIndices σ k) : ℤ) * ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k =
      ∑ p ∈ P.orbitIndices σ j ×ˢ P.orbitIndices σ k, P.pairingIn ℤ p.1 p.2 := by
    rw [Finset.sum_product_right]
    trans ∑ _c ∈ P.orbitIndices σ k, ∑ a ∈ P.orbitIndices σ j, P.pairingIn ℤ a k
    · rw [Finset.sum_const, nsmul_eq_mul]
    · exact Finset.sum_congr rfl fun c hc ↦ (hconst c hc).symm
  rw [hdouble, ← Finset.sum_filter_ne_zero]
  trans ∑ _p ∈ (P.orbitIndices σ j ×ˢ P.orbitIndices σ k).filter
      (fun p ↦ P.pairingIn ℤ p.1 p.2 ≠ 0), (-1 : ℤ)
  · refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨hp_mem, hne0⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp_mem
    have h1 : p.1 ∈ b.support := P.mem_support_of_mem_orbitIndices σ hσ hj hp1
    have h2 : p.2 ∈ b.support := P.mem_support_of_mem_orbitIndices σ hσ hk hp2
    have hne : (⟨p.1, h1⟩ : b.support) ≠ ⟨p.2, h2⟩ := fun heq ↦ by
      have h12 : p.1 = p.2 := congrArg Subtype.val heq
      have hp2j : p.2 ∈ P.orbitIndices σ j := h12 ▸ hp1
      exact hjk (by
        rw [← orbitIndices_eq_of_mem hp2j, orbitIndices_eq_of_mem hp2]
        exact P.self_mem_orbitIndices σ k)
    have hcart : b.cartanMatrix ⟨p.1, h1⟩ ⟨p.2, h2⟩ = P.pairingIn ℤ p.1 p.2 := by
      simp [Base.cartanMatrix, Base.cartanMatrixIn_def]
    rcases hsl hne with h0 | hm1
    · exact absurd (hcart.symm.trans h0) hne0
    · exact hcart.symm.trans hm1
  · simp

/-- **Reflection comparison**: on `LinearMap.fixedSubmodule σ.weightMap`, reflection in a folded
root agrees with the ambient block reflection of its orbit. -/
theorem coe_reflection_orbitSum (k : ι) (v : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.pairing.reflection ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ v :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.blockReflection σ k (pairwise_isOrthogonal_orbitIndices hσ hsl horth k) • (v : M) := by
  rw [P.blockReflection_smul_of_mem_fixedSubmodule σ k _ v.2, RootPairing.reflection_apply,
    Submodule.coe_sub, Submodule.coe_smul, F.coroot'_apply,
    F.coroot_orbitSum_apply hσ hsl horth k v, F.coe_root]

/-- **Weyl-generator comparison**: the action of a root reflection in `F.pairing.weylGroup` on
fixed vectors agrees with the ambient block reflection of the corresponding root orbit. -/
theorem coe_ofIdx_smul_orbitSum (k : ι) (v : LinearMap.fixedSubmodule σ.weightMap) :
    ((weylGroup.ofIdx F.pairing ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ • v :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.blockReflection σ k (pairwise_isOrthogonal_orbitIndices hσ hsl horth k) • (v : M) := by
  rw [weylGroup.ofIdx_smul, Equiv.reflection_smul, F.coe_reflection_orbitSum hσ hsl horth k v]

end ExplicitFormulas

end OrthogonalConstruction

end OrbitSumRealization

end RootPairing
