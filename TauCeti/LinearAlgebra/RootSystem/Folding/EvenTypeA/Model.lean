/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.B
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
public import TauCeti.LinearAlgebra.RootSystem.ZeroSumTypeA
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinate model for folding even type `A₂ₙ` under diagram reversal

This file develops the explicit coordinate model for folding `typeAZeroSumRootPairing K (2 * n)`
along its diagram reversal `typeAZeroSumRevAut K (2 * n)` and identifies it with the
`K`-base-changed type-`Bₙ` root system `typeBBaseChangeRootSystem K n` on `Fin n → K` via the
fixed basis `evenTypeAFixedBasis` and fundamental-weight equivalence `evenTypeAFixedCoordEquiv`.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--II.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace TauCeti.DynkinType

open Finset Function Submodule

/-- The `i`-th left coordinate index `i < n` inside `Fin (2 * n + 1)`. -/
def evenTypeALeftIdx (n : ℕ) (i : Fin n) : Fin (2 * n + 1) := ⟨i, by have := i.isLt; omega⟩

/-- The middle coordinate index `n` inside `Fin (2 * n + 1)`, fixed by `Fin.rev`. -/
def evenTypeAMidIdx (n : ℕ) : Fin (2 * n + 1) := ⟨n, by omega⟩

/-- Coercing `evenTypeALeftIdx n i` to `ℕ` gives `i`. -/
@[simp] theorem val_evenTypeALeftIdx (n : ℕ) (i : Fin n) : (evenTypeALeftIdx n i : ℕ) = i := (rfl)

/-- Coercing `evenTypeAMidIdx n` to `ℕ` gives `n`. -/
@[simp] theorem val_evenTypeAMidIdx (n : ℕ) : (evenTypeAMidIdx n : ℕ) = n := (rfl)

/-- Reversing `evenTypeAMidIdx n` fixes it. -/
@[simp] theorem rev_evenTypeAMidIdx (n : ℕ) : (evenTypeAMidIdx n).rev = evenTypeAMidIdx n := by
  ext; rw [Fin.val_rev, val_evenTypeAMidIdx]; omega

/-- Coercing `(evenTypeALeftIdx n i).rev` to `ℕ` gives `2 * n - i`. -/
theorem val_rev_evenTypeALeftIdx (n : ℕ) (i : Fin n) :
    ((evenTypeALeftIdx n i).rev : ℕ) = 2 * n - i := by
  have := i.isLt; rw [Fin.val_rev, val_evenTypeALeftIdx]; omega

/-- `a : Fin (2 * n + 1)` is fixed by `Fin.rev` if and only if `a = evenTypeAMidIdx n`. -/
theorem rev_eq_self_iff_eq_evenTypeAMidIdx {n : ℕ} {a : Fin (2 * n + 1)} :
    a.rev = a ↔ a = evenTypeAMidIdx n := by
  have := a.isLt; simp only [Fin.ext_iff, Fin.val_rev, val_evenTypeAMidIdx]; omega

private lemma castSucc_evenTypeAFin (n : ℕ) (k : Fin n) :
    (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (2 * n)).castSucc = evenTypeALeftIdx n k :=
  Fin.ext rfl

private lemma succ_evenTypeAFin_of_lt {n : ℕ} {k : Fin n} (h : (k : ℕ) + 1 < n) :
    (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (2 * n)).succ =
      evenTypeALeftIdx n ⟨(k : ℕ) + 1, h⟩ := Fin.ext rfl

private lemma succ_evenTypeAFin_of_eq {n : ℕ} {k : Fin n} (h : (k : ℕ) + 1 = n) :
    (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (2 * n)).succ = evenTypeAMidIdx n := Fin.ext h

/-- The `i`-th basis vector `fᵢ = eᵢ - e₂ₙ₋ᵢ` of the reversal-fixed subspace. -/
def evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    singleParityCheckCode R (Fin (2 * n + 1)) :=
  typeAZeroSumVec R (evenTypeALeftIdx n i) (evenTypeALeftIdx n i).rev

/-- `evenTypeABasisVec` is fixed by `typeAZeroSumNegRevEquiv`. -/
@[simp] theorem typeAZeroSumNegRevEquiv_evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ)
    (i : Fin n) :
    typeAZeroSumNegRevEquiv R (2 * n) (evenTypeABasisVec R n i) = evenTypeABasisVec R n i := by
  rw [evenTypeABasisVec, typeAZeroSumNegRevEquiv_vec, Fin.rev_rev]

/-- Evaluating `evenTypeABasisVec R n i` at a left index `evenTypeALeftIdx n j` gives `[i = j]`. -/
@[simp] theorem evenTypeABasisVec_apply_left (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) (evenTypeALeftIdx n j) =
      if i = j then 1 else 0 := by
  have := i.isLt; have := j.isLt; rw [evenTypeABasisVec, typeAZeroSumVec_apply]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- Evaluating `evenTypeABasisVec R n i` at the middle index `n` gives `0`. -/
@[simp] theorem evenTypeABasisVec_apply_mid (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) (evenTypeAMidIdx n) = 0 := by
  have := i.isLt; rw [evenTypeABasisVec, typeAZeroSumVec_apply]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx, val_evenTypeAMidIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- The vectors `evenTypeABasisVec R n i` are pairwise orthogonal of squared length `2`. -/
theorem evenTypeABasisVec_dotProduct_evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ)
    (i j : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) ⬝ᵥ
        (evenTypeABasisVec R n j : Fin (2 * n + 1) → R) = if i = j then 2 else 0 := by
  have := i.isLt; have := j.isLt
  rw [evenTypeABasisVec, evenTypeABasisVec, typeAZeroSumVec_dotProduct_typeAZeroSumVec]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

private def evenTypeAFoldAtom (R : Type*) [CommRing R] (n : ℕ) (a : Fin (2 * n + 1)) :
    singleParityCheckCode R (Fin (2 * n + 1)) := typeAZeroSumVec R a a.rev

private lemma evenTypeAFoldAtom_mid (R : Type*) [CommRing R] (n : ℕ) :
    evenTypeAFoldAtom R n (evenTypeAMidIdx n) = 0 := by
  rw [evenTypeAFoldAtom, rev_evenTypeAMidIdx, typeAZeroSumVec_self]

private lemma evenTypeAFoldAtom_left (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    evenTypeAFoldAtom R n (evenTypeALeftIdx n i) = evenTypeABasisVec R n i := rfl

private lemma add_rev_typeAZeroSumVec (R : Type*) [CommRing R] (n : ℕ) (a b : Fin (2 * n + 1)) :
    typeAZeroSumVec R a b + typeAZeroSumVec R b.rev a.rev =
      evenTypeAFoldAtom R n a - evenTypeAFoldAtom R n b := by
  ext; simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    evenTypeAFoldAtom, typeAZeroSumVec_apply]; ring

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- Every `evenTypeABasisVec` lies in the fixed submodule of `typeAZeroSumRevAut K (2 * n)`. -/
theorem evenTypeABasisVec_mem_fixedSubmodule (n : ℕ) (i : Fin n) :
    evenTypeABasisVec K n i ∈
      LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
    typeAZeroSumNegRevEquiv_evenTypeABasisVec]

private lemma fixedSubmodule_revAut_apply_rev {n : ℕ}
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap)
    (a : Fin (2 * n + 1)) :
    ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a.rev =
      -((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a := by
  have hx := congrArg (fun w : singleParityCheckCode K (Fin (2 * n + 1)) ↦
    (w : Fin (2 * n + 1) → K) a) (LinearMap.mem_fixedSubmodule_iff.mp x.property)
  simp only [weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe, coe_typeAZeroSumNegRevEquiv_apply,
    neg_eq_iff_eq_neg] at hx
  exact hx

private lemma fixedSubmodule_revAut_apply_mid {n : ℕ}
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
      (evenTypeAMidIdx n) = 0 := by
  have h := fixedSubmodule_revAut_apply_rev K x (evenTypeAMidIdx n)
  rw [rev_evenTypeAMidIdx] at h
  exact (mul_eq_zero.mp (by linear_combination h : (2 : K) * _ = 0)).resolve_left two_ne_zero

private noncomputable def evenTypeAFixedLeftEquiv (n : ℕ) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap ≃ₗ[K] (Fin n → K) where
  toFun x i := ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
    (evenTypeALeftIdx n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨∑ i : Fin n, y i • evenTypeABasisVec K n i,
    sum_mem fun i _ ↦ Submodule.smul_mem _ _ (evenTypeABasisVec_mem_fixedSubmodule K n i)⟩
  right_inv y := by ext j; simp [evenTypeABasisVec_apply_left]
  left_inv x := by
    let y : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap :=
      ⟨∑ i : Fin n, ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
          (evenTypeALeftIdx n i) • evenTypeABasisVec K n i,
        sum_mem fun i _ ↦ Submodule.smul_mem _ _ (evenTypeABasisVec_mem_fixedSubmodule K n i)⟩
    have hleft (j : Fin n) : ((y : singleParityCheckCode K (Fin (2 * n + 1))) : _ → K)
        (evenTypeALeftIdx n j) = ((x : singleParityCheckCode K (Fin (2 * n + 1))) : _ → K)
        (evenTypeALeftIdx n j) := by simp [y, evenTypeABasisVec_apply_left]
    apply Subtype.ext; apply Subtype.ext; ext a
    rcases lt_trichotomy (a : ℕ) n with hlt | heq | hgt
    · exact hleft ⟨a, hlt⟩
    · rw [(Fin.ext heq : a = evenTypeAMidIdx n),
        fixedSubmodule_revAut_apply_mid K y, fixedSubmodule_revAut_apply_mid K x]
    · let j : Fin n := ⟨2 * n - a, by have := a.isLt; omega⟩
      have ha : a = (evenTypeALeftIdx n j).rev :=
        Fin.ext (by rw [val_rev_evenTypeALeftIdx]; dsimp [j]; have := a.isLt; omega)
      rw [ha, fixedSubmodule_revAut_apply_rev K y, fixedSubmodule_revAut_apply_rev K x, hleft j]

private lemma evenTypeAFixedLeftEquiv_apply (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) (i : Fin n) :
    evenTypeAFixedLeftEquiv K n x i =
      ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
        (evenTypeALeftIdx n i) := rfl

private lemma evenTypeAFixedLeftEquiv_symm_apply (n : ℕ) (y : Fin n → K) :
    ((evenTypeAFixedLeftEquiv K n).symm y : singleParityCheckCode K (Fin (2 * n + 1))) =
      ∑ i : Fin n, y i • evenTypeABasisVec K n i := rfl

/-- The vectors `fᵢ = eᵢ - e₂ₙ₋ᵢ` (`i : Fin n`) form a `K`-basis of the fixed subspace. -/
noncomputable def evenTypeAFixedBasis (n : ℕ) :
    Module.Basis (Fin n) K (LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :=
  Module.Basis.ofRepr
    ((evenTypeAFixedLeftEquiv K n).trans (Finsupp.linearEquivFunOnFinite K K (Fin n)).symm)

/-- The `i`-th vector of `evenTypeAFixedBasis K n` coerces to `evenTypeABasisVec K n i`. -/
@[simp] theorem coe_evenTypeAFixedBasis_apply (n : ℕ) (i : Fin n) :
    (evenTypeAFixedBasis K n i : singleParityCheckCode K (Fin (2 * n + 1))) =
      evenTypeABasisVec K n i := by
  rw [evenTypeAFixedBasis, Module.Basis.coe_ofRepr]; dsimp only
  rw [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    evenTypeAFixedLeftEquiv_symm_apply]; simp [Finsupp.single_apply]

private lemma orbitSum_typeAZeroSumRevAut_eq (n : ℕ) (p : TypeAIndex (2 * n)) :
    (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p =
      if p.val.2 = p.val.1.rev then evenTypeAFoldAtom K n p.val.1
      else evenTypeAFoldAtom K n p.val.1 - evenTypeAFoldAtom K n p.val.2 := by
  rw [RootPairing.orbitSum_def, orbitIndices_typeAZeroSumRevAut]
  by_cases hfix : p.val.2 = p.val.1.rev
  · rw [ite_eq_left hfix, (finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev p).mpr hfix,
      pair_eq_singleton, sum_singleton, root_typeAZeroSumRootPairing, hfix, evenTypeAFoldAtom]
  · have hp : p ≠ finDistinctPairsRevSwap (2 * n + 1) p :=
      fun hc ↦ hfix ((finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev p).mp hc.symm)
    rw [ite_eq_right hfix, sum_pair hp, root_typeAZeroSumRootPairing, root_typeAZeroSumRootPairing,
      finDistinctPairsRevSwap_apply_val, add_rev_typeAZeroSumVec]

/-- On the `k`-th Bourbaki simple pair (`k < n`), the orbit sum is `f_k - f_{k+1}` for `k + 1 < n`
and `f_{n-1}` at the middle node `k + 1 = n`. -/
theorem orbitSum_typeAZeroSumRevAut_simplePair (n : ℕ) (k : Fin n) :
    (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩) =
      if h : (k : ℕ) + 1 < n then
        evenTypeABasisVec K n k - evenTypeABasisVec K n ⟨(k : ℕ) + 1, h⟩
      else evenTypeABasisVec K n k := by
  have hk := k.isLt
  have hne : (typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩).val.2 ≠
      (typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩).val.1.rev := by
    rw [typeAZeroSumSimplePair_val, castSucc_evenTypeAFin]
    simp only [ne_eq, Fin.ext_iff, Fin.val_succ, val_rev_evenTypeALeftIdx]; omega
  rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, typeAZeroSumSimplePair_val,
    castSucc_evenTypeAFin, evenTypeAFoldAtom_left]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [dite_eq_left hlt, succ_evenTypeAFin_of_lt hlt, evenTypeAFoldAtom_left]
  · rw [dite_eq_right hlt, succ_evenTypeAFin_of_eq (by omega), evenTypeAFoldAtom_mid, sub_zero]

/-- The fixed positive root pair `(i, 2 * n - i)` lifting the `i`-th short root `fᵢ`. -/
def evenTypeAFixedShortLift (n : ℕ) (i : Fin n) : TypeAIndex (2 * n) :=
  ⟨(evenTypeALeftIdx n i, (evenTypeALeftIdx n i).rev), by have := i.isLt; simp [Fin.ext_iff]; omega⟩

/-- Underlying pair of `evenTypeAFixedShortLift n i`. -/
@[simp] theorem evenTypeAFixedShortLift_val (n : ℕ) (i : Fin n) :
    (evenTypeAFixedShortLift n i).val = (evenTypeALeftIdx n i, (evenTypeALeftIdx n i).rev) := (rfl)

/-- The middle positive pair `(i, n)` whose size-`2` orbit sums to the `i`-th short root `fᵢ`. -/
def evenTypeAPairedShortLift (n : ℕ) (i : Fin n) : TypeAIndex (2 * n) :=
  ⟨(evenTypeALeftIdx n i, evenTypeAMidIdx n), by have := i.isLt; simp [Fin.ext_iff]; omega⟩

/-- Underlying pair of `evenTypeAPairedShortLift n i`. -/
@[simp] theorem evenTypeAPairedShortLift_val (n : ℕ) (i : Fin n) :
    (evenTypeAPairedShortLift n i).val = (evenTypeALeftIdx n i, evenTypeAMidIdx n) := (rfl)

/-- `evenTypeAFixedShortLift n i` is positive, has orbit size `1`, and has orbit sum `fᵢ`. -/
theorem evenTypeAFixedShortLift_spec (n : ℕ) (i : Fin n) :
    (typeAZeroSumBase K (2 * n)).IsPos (evenTypeAFixedShortLift n i) ∧
      #((typeAZeroSumRootPairing K (2 * n)).orbitIndices (typeAZeroSumRevAut K (2 * n))
        (evenTypeAFixedShortLift n i)) = 1 ∧
      (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (evenTypeAFixedShortLift n i) = evenTypeABasisVec K n i := by
  have hi := i.isLt
  have hfix : (evenTypeAFixedShortLift n i).val.2 = (evenTypeAFixedShortLift n i).val.1.rev := rfl
  refine ⟨by rw [isPos_typeAZeroSumBase_iff, evenTypeAFixedShortLift_val, Fin.lt_def,
      val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]; omega,
    by rw [orbitIndices_typeAZeroSumRevAut,
      (finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev _).mpr hfix,
      pair_eq_singleton, card_singleton],
    by rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_left hfix, evenTypeAFixedShortLift_val,
      evenTypeAFoldAtom_left]⟩

/-- `evenTypeAPairedShortLift n i` is positive, has orbit size `2`, and has orbit sum `fᵢ`. -/
theorem evenTypeAPairedShortLift_spec (n : ℕ) (i : Fin n) :
    (typeAZeroSumBase K (2 * n)).IsPos (evenTypeAPairedShortLift n i) ∧
      #((typeAZeroSumRootPairing K (2 * n)).orbitIndices (typeAZeroSumRevAut K (2 * n))
        (evenTypeAPairedShortLift n i)) = 2 ∧
      (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (evenTypeAPairedShortLift n i) = evenTypeABasisVec K n i := by
  have hi := i.isLt
  have hne : (evenTypeAPairedShortLift n i).val.2 ≠ (evenTypeAPairedShortLift n i).val.1.rev := by
    simp [Fin.ext_iff]; omega
  refine ⟨by rw [isPos_typeAZeroSumBase_iff, evenTypeAPairedShortLift_val, Fin.lt_def]; exact hi,
    by rw [orbitIndices_typeAZeroSumRevAut]
       exact card_pair fun hc ↦ hne ((finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev _).mp hc.symm),
    by rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, evenTypeAPairedShortLift_val,
      evenTypeAFoldAtom_left, evenTypeAFoldAtom_mid, sub_zero]⟩

private def typeBFundamentalCoordMap (n : ℕ) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun y k := if h : (k : ℕ) + 1 < n then y k - y ⟨(k : ℕ) + 1, h⟩ else 2 * y k
  map_add' _ _ := funext fun _ ↦ by simp; split_ifs <;> ring
  map_smul' _ _ := funext fun _ ↦ by simp; split_ifs <;> ring

omit [CharZero K] in
private lemma typeBFundamentalCoordMap_apply (n : ℕ) (y : Fin n → K) (k : Fin n) :
    typeBFundamentalCoordMap K n y k =
      if h : (k : ℕ) + 1 < n then y k - y ⟨(k : ℕ) + 1, h⟩ else 2 * y k := rfl

private lemma typeBFundamentalCoordMap_injective : ∀ n, Injective (typeBFundamentalCoordMap K n)
  | 0 => fun _ _ _ ↦ Subsingleton.elim _ _
  | m + 1 => (injective_iff_map_eq_zero _).mpr fun y hy ↦ funext <| Fin.reverseInduction
      (by have h := congrFun hy (Fin.last m)
          rw [typeBFundamentalCoordMap_apply, Pi.zero_apply, dite_eq_right (by simp)] at h
          exact (mul_eq_zero.mp h).resolve_left two_ne_zero)
      fun k ih ↦ by
        have h := congrFun hy k.castSucc
        rw [typeBFundamentalCoordMap_apply, Pi.zero_apply, dite_eq_left (by simp)] at h
        exact (sub_eq_zero.mp h).trans ih

private lemma typeBFundamentalCoordMap_bijective (n : ℕ) :
    Bijective (typeBFundamentalCoordMap K n) :=
  ⟨typeBFundamentalCoordMap_injective K n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (typeBFundamentalCoordMap_injective K n)⟩

/-- Fundamental-weight coordinate equivalence from the reversal-fixed subspace to `Fin n → K`. -/
noncomputable def evenTypeAFixedCoordEquiv (n : ℕ) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap ≃ₗ[K] (Fin n → K) :=
  (evenTypeAFixedLeftEquiv K n).trans <|
    LinearEquiv.ofBijective (typeBFundamentalCoordMap K n)
      (typeBFundamentalCoordMap_bijective K n)

/-- Coordinate formula for `evenTypeAFixedCoordEquiv K n`: scales the `k`-th simple coroot pairing
by `1` off the middle (`k + 1 < n`) and by `2` at the middle (`k + 1 = n`). -/
theorem evenTypeAFixedCoordEquiv_apply (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) (k : Fin n) :
    evenTypeAFixedCoordEquiv K n x k =
      (if (k : ℕ) + 1 = n then (2 : K) else 1) *
        (typeAZeroSumRootPairing K (2 * n)).coroot'
          (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩) (x : _) := by
  have hk := k.isLt
  rw [evenTypeAFixedCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    typeBFundamentalCoordMap_apply, coroot'_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val,
    castSucc_evenTypeAFin]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [dite_eq_left hlt, ite_eq_right (by omega), one_mul, succ_evenTypeAFin_of_lt hlt,
      evenTypeAFixedLeftEquiv_apply, evenTypeAFixedLeftEquiv_apply]
  · have hlast : (k : ℕ) + 1 = n := by omega
    rw [dite_eq_right hlt, ite_eq_left hlast, succ_evenTypeAFin_of_eq hlast,
      fixedSubmodule_revAut_apply_mid K x, sub_zero, evenTypeAFixedLeftEquiv_apply]

/-- `evenTypeAFixedCoordEquiv K n` sends the `i`-th fixed basis vector `fᵢ` to `TypeB.weight n i`.
-/
theorem evenTypeAFixedCoordEquiv_basisVec (n : ℕ) (i : Fin n) :
    evenTypeAFixedCoordEquiv K n
        ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩ =
      Pi.algebraMap (Fin n) ℤ K (TypeB.weight n i) := by
  ext k; have := i.isLt; have := k.isLt
  rw [evenTypeAFixedCoordEquiv_apply, piAlgebraMap_apply, TypeB.weight_apply,
    coroot'_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val, algebraMap_int_eq, eq_intCast]
  push_cast
  simp only [evenTypeABasisVec, typeAZeroSumVec_apply, Fin.ext_iff,
    val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (ring; done) | (exfalso; omega)

private def evenTypeASignedIdx (n : ℕ) (u : Fin (2 * n)) : Fin (2 * n + 1) :=
  if h : (u : ℕ) < n then evenTypeALeftIdx n ⟨u, h⟩
  else (evenTypeALeftIdx n ⟨(u : ℕ) - n, by have := u.isLt; omega⟩).rev

private lemma evenTypeASignedIdx_ne_mid (n : ℕ) (u : Fin (2 * n)) :
    evenTypeASignedIdx n u ≠ evenTypeAMidIdx n := by
  have := u.isLt; simp only [evenTypeASignedIdx, ne_eq, Fin.ext_iff, val_evenTypeAMidIdx]
  split_ifs <;> simp only [val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx] <;> omega

private lemma rev_evenTypeASignedIdx (n : ℕ) (u : Fin (2 * n)) :
    (evenTypeASignedIdx n u).rev = evenTypeASignedIdx n (TypeB.opp u) := by
  have := u.isLt; ext; simp only [evenTypeASignedIdx, TypeB.coe_opp, Fin.val_rev]
  split_ifs <;> simp only [val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx] <;> omega

private lemma evenTypeASignedIdx_injective (n : ℕ) : Injective (evenTypeASignedIdx n) := by
  intro u v huv; have := u.isLt; have := v.isLt; have hval := congrArg Fin.val huv
  simp only [evenTypeASignedIdx] at hval
  split_ifs at hval <;> simp only [val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx] at hval <;>
    exact Fin.ext (by omega)

private lemma exists_evenTypeASignedIdx {n : ℕ} {a : Fin (2 * n + 1)}
    (ha : a ≠ evenTypeAMidIdx n) : ∃ u : Fin (2 * n), evenTypeASignedIdx n u = a := by
  have := a.isLt; have hane : (a : ℕ) ≠ n := fun hc ↦ ha (Fin.ext hc)
  by_cases hlt : (a : ℕ) < n
  · exact ⟨⟨a, by omega⟩, by simp [evenTypeASignedIdx, hlt, evenTypeALeftIdx]⟩
  · exact ⟨⟨n + (2 * n - a), by omega⟩, Fin.ext <| by
      have hnot : ¬ (n + (2 * n - (a : ℕ)) < n) := by omega
      simp [evenTypeASignedIdx, hnot]; omega⟩

private def evenTypeAFoldAtomFixed (n : ℕ) (a : Fin (2 * n + 1)) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap :=
  ⟨evenTypeAFoldAtom K n a, by
    rw [LinearMap.mem_fixedSubmodule_iff, weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
      evenTypeAFoldAtom, typeAZeroSumNegRevEquiv_vec, Fin.rev_rev]⟩

@[simp] private lemma coe_evenTypeAFoldAtomFixed (n : ℕ) (a : Fin (2 * n + 1)) :
    (evenTypeAFoldAtomFixed K n a : singleParityCheckCode K (Fin (2 * n + 1))) =
      evenTypeAFoldAtom K n a := rfl

private lemma evenTypeAFoldAtomFixed_left (n : ℕ) (i : Fin n) :
    evenTypeAFoldAtomFixed K n (evenTypeALeftIdx n i) =
      ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩ :=
  Subtype.ext (by rw [coe_evenTypeAFoldAtomFixed, evenTypeAFoldAtom_left])

private lemma evenTypeAFixedCoordEquiv_foldAtom_rev (n : ℕ) (a : Fin (2 * n + 1)) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a.rev) =
      -evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a) := by
  rw [← map_neg (evenTypeAFixedCoordEquiv K n)]
  exact congrArg _ (Subtype.ext (by
    rw [Submodule.coe_neg, coe_evenTypeAFoldAtomFixed, coe_evenTypeAFoldAtomFixed,
      evenTypeAFoldAtom, Fin.rev_rev, evenTypeAFoldAtom, neg_typeAZeroSumVec]))

private lemma evenTypeAFixedCoordEquiv_foldAtom_mid (n : ℕ) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n (evenTypeAMidIdx n)) = 0 := by
  rw [← map_zero (evenTypeAFixedCoordEquiv K n)]
  exact congrArg _ (Subtype.ext (by
    rw [coe_evenTypeAFoldAtomFixed, evenTypeAFoldAtom_mid, Submodule.coe_zero]))

private lemma evenTypeAFixedCoordEquiv_signedIdx (n : ℕ) (u : Fin (2 * n)) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u)) =
      Pi.algebraMap (Fin n) ℤ K (TypeB.signedWeight u) := by
  have := u.isLt
  by_cases hlt : (u : ℕ) < n
  · rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_left hlt, ite_eq_left hlt,
      one_smul, ← evenTypeAFixedCoordEquiv_basisVec K n ⟨u, hlt⟩, evenTypeASignedIdx,
      dite_eq_left hlt, evenTypeAFoldAtomFixed_left]
  · rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_right hlt, ite_eq_right hlt,
      neg_one_smul, map_neg, ← evenTypeAFixedCoordEquiv_basisVec K n ⟨(u : ℕ) - n, by omega⟩,
      evenTypeASignedIdx, dite_eq_right hlt, evenTypeAFixedCoordEquiv_foldAtom_rev,
      evenTypeAFoldAtomFixed_left]

private lemma mem_foldedIndices_of_mem_range_typeB {n : ℕ}
    {x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap}
    (hx : evenTypeAFixedCoordEquiv K n x ∈ Set.range (typeBBaseChangeRootSystem K n).root) :
    (x : singleParityCheckCode K (Fin (2 * n + 1))) ∈
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  rw [RootPairing.mem_foldedIndices]
  obtain ⟨idx, hidx⟩ := hx; rw [root_typeBBaseChangeRootSystem] at hidx
  obtain ⟨u, v, huv, hr⟩ := mem_range_root_typeBSimplyConnectedRootDatum_iff.mp ⟨idx, rfl⟩
  have hroot : evenTypeAFixedCoordEquiv K n x =
      Pi.algebraMap (Fin n) ℤ K (TypeB.rootOfPair u v) := hidx.symm.trans (congrArg _ hr)
  rcases eq_or_ne u v with rfl | hne
  · refine ⟨⟨(evenTypeASignedIdx n u, (evenTypeASignedIdx n u).rev),
      fun hc ↦ evenTypeASignedIdx_ne_mid n u (rev_eq_self_iff_eq_evenTypeAMidIdx.mp hc.symm)⟩, ?_⟩
    have hx' : x = evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) :=
      (evenTypeAFixedCoordEquiv K n).injective (by
        rw [hroot, TypeB.rootOfPair_self, evenTypeAFixedCoordEquiv_signedIdx])
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_left rfl, coe_evenTypeAFoldAtomFixed]
  · let a := evenTypeASignedIdx n u; let b := (evenTypeASignedIdx n v).rev
    have hab : a ≠ b := fun hc ↦ huv.ne_opp (evenTypeASignedIdx_injective n (by
      simpa [a, b, rev_evenTypeASignedIdx] using hc))
    have hnotfix : b ≠ a.rev :=
      fun hc ↦ hne (evenTypeASignedIdx_injective n (Fin.rev_inj.mp hc).symm)
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    have hx' : x = evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b :=
      (evenTypeAFixedCoordEquiv K n).injective (by
        rw [hroot, TypeB.rootOfPair_of_ne hne, map_add, map_sub (evenTypeAFixedCoordEquiv K n),
          evenTypeAFixedCoordEquiv_foldAtom_rev, sub_neg_eq_add,
          evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx])
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hnotfix, Submodule.coe_sub,
      coe_evenTypeAFoldAtomFixed, coe_evenTypeAFoldAtomFixed]

private lemma evenTypeAFoldAtom_mem_range_typeB (n : ℕ) {a : Fin (2 * n + 1)}
    (ha : a ≠ evenTypeAMidIdx n) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a) ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  obtain ⟨u, rfl⟩ := exists_evenTypeASignedIdx ha
  rw [evenTypeAFixedCoordEquiv_signedIdx, ← TypeB.rootOfPair_self,
    piAlgebraMap_mem_range_root_typeBBaseChangeRootSystem_iff,
    mem_range_root_typeBSimplyConnectedRootDatum_iff]
  exact ⟨u, u, (TypeB.isPair_iff u u).mpr (Or.inl rfl), rfl⟩

private lemma evenTypeAFoldAtom_sub_mem_range_typeB (n : ℕ) {a b : Fin (2 * n + 1)}
    (hab : a ≠ b) (hnotfix : b ≠ a.rev) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b) ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  rw [map_sub (evenTypeAFixedCoordEquiv K n)]
  by_cases ha : a = evenTypeAMidIdx n
  · rw [ha, evenTypeAFixedCoordEquiv_foldAtom_mid, zero_sub,
      ← evenTypeAFixedCoordEquiv_foldAtom_rev]
    exact evenTypeAFoldAtom_mem_range_typeB K n fun hc ↦
      hab (ha.trans (by simpa [rev_evenTypeAMidIdx] using (congrArg Fin.rev hc).symm))
  · by_cases hb : b = evenTypeAMidIdx n
    · rw [hb, evenTypeAFixedCoordEquiv_foldAtom_mid, sub_zero]
      exact evenTypeAFoldAtom_mem_range_typeB K n ha
    · obtain ⟨u, hu⟩ := exists_evenTypeASignedIdx ha
      obtain ⟨v, hv⟩ := exists_evenTypeASignedIdx (a := b.rev)
        (fun hc ↦ hb (by simpa [rev_evenTypeAMidIdx] using congrArg Fin.rev hc))
      have huv_ne : u ≠ v := fun hc ↦ hnotfix (by rw [← hu, hc, hv, Fin.rev_rev])
      have huv_opp : u ≠ TypeB.opp v := fun hc ↦
        hab (by rw [← hu, hc, ← rev_evenTypeASignedIdx, hv, Fin.rev_rev])
      rw [← hu, ← Fin.rev_rev b, ← hv, evenTypeAFixedCoordEquiv_foldAtom_rev, sub_neg_eq_add,
        evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx, ← map_add,
        ← TypeB.rootOfPair_of_ne huv_ne, piAlgebraMap_mem_range_root_typeBBaseChangeRootSystem_iff,
        mem_range_root_typeBSimplyConnectedRootDatum_iff]
      exact ⟨u, v, (TypeB.isPair_iff u v).mpr (Or.inr fun hax ↦
        (TypeB.eq_or_eq_opp_of_axis_eq hax).elim huv_ne huv_opp), rfl⟩

/-- `evenTypeAFixedCoordEquiv K n` maps the folded roots of `typeAZeroSumRootPairing K (2 * n)`
bijectively onto the roots of `typeBBaseChangeRootSystem K n`. -/
theorem mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    evenTypeAFixedCoordEquiv K n x ∈ Set.range (typeBBaseChangeRootSystem K n).root ↔
      (x : singleParityCheckCode K (Fin (2 * n + 1))) ∈
        (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  refine ⟨mem_foldedIndices_of_mem_range_typeB K, fun hx ↦ ?_⟩
  obtain ⟨p, hp⟩ := RootPairing.mem_foldedIndices.mp hx
  by_cases hfix : p.val.2 = p.val.1.rev
  · have hx' : x = evenTypeAFoldAtomFixed K n p.val.1 :=
      Subtype.ext (by rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_left hfix,
        coe_evenTypeAFoldAtomFixed])
    exact hx' ▸ evenTypeAFoldAtom_mem_range_typeB K n
      (fun hc ↦ p.property (by rw [hfix, hc, rev_evenTypeAMidIdx]))
  · have hx' : x = evenTypeAFoldAtomFixed K n p.val.1 - evenTypeAFoldAtomFixed K n p.val.2 :=
      Subtype.ext (by rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hfix,
        Submodule.coe_sub, coe_evenTypeAFoldAtomFixed, coe_evenTypeAFoldAtomFixed])
    exact hx' ▸ evenTypeAFoldAtom_sub_mem_range_typeB K n p.property hfix

/-- Ambient characterization of `foldedIndices` for `typeAZeroSumRootPairing K (2 * n)` under
`typeAZeroSumRevAut K (2 * n)`: its elements are precisely `±fᵢ` (`i : Fin n`) and `±fᵢ ± fⱼ`
(`i ≠ j`). -/
theorem mem_foldedIndices_typeAZeroSumRevAut_iff (n : ℕ)
    (x : singleParityCheckCode K (Fin (2 * n + 1))) :
    x ∈ (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) ↔
      (∃ i : Fin n, x = evenTypeABasisVec K n i ∨ x = -evenTypeABasisVec K n i) ∨
        (∃ i j : Fin n, i ≠ j ∧
          (x = evenTypeABasisVec K n i + evenTypeABasisVec K n j ∨
           x = evenTypeABasisVec K n i - evenTypeABasisVec K n j ∨
           x = -evenTypeABasisVec K n i + evenTypeABasisVec K n j ∨
           x = -evenTypeABasisVec K n i - evenTypeABasisVec K n j)) := by
  have hmem_pair (y : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap)
      (u v : Fin (2 * n)) (huv : TypeB.IsPair u v)
      (hy : evenTypeAFixedCoordEquiv K n y = Pi.algebraMap (Fin n) ℤ K (TypeB.rootOfPair u v)) :
      (y : singleParityCheckCode K (Fin (2 * n + 1))) ∈
        (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
    rw [← mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices, hy,
      piAlgebraMap_mem_range_root_typeBBaseChangeRootSystem_iff,
      mem_range_root_typeBSimplyConnectedRootDatum_iff]
    exact ⟨u, v, huv, rfl⟩
  have hpos_signed (i : Fin n) :
      TypeB.axis (⟨i, by have := i.isLt; omega⟩ : Fin (2 * n)) = i ∧
        TypeB.signedWeight (⟨i, by have := i.isLt; omega⟩ : Fin (2 * n)) = TypeB.weight n i := by
    have hi := i.isLt
    simp [TypeB.axis_def, TypeB.signedWeight_def, TypeB.sgn_def, hi]
  have hneg_signed (i : Fin n) :
      TypeB.axis (⟨n + i, by have := i.isLt; omega⟩ : Fin (2 * n)) = i ∧
        TypeB.signedWeight (⟨n + i, by have := i.isLt; omega⟩ : Fin (2 * n)) =
          -TypeB.weight n i := by
    have hnot : ¬ n + (i : ℕ) < n := by omega
    simp [TypeB.axis_def, TypeB.signedWeight_def, TypeB.sgn_def, hnot]
  have hmem_pair_ne (y₁ y₂ : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap)
      (u v : Fin (2 * n)) (hax : TypeB.axis u ≠ TypeB.axis v)
      (hy₁ : evenTypeAFixedCoordEquiv K n y₁ = Pi.algebraMap (Fin n) ℤ K (TypeB.signedWeight u))
      (hy₂ : evenTypeAFixedCoordEquiv K n y₂ = Pi.algebraMap (Fin n) ℤ K (TypeB.signedWeight v)) :
      ((y₁ + y₂ : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
          singleParityCheckCode K (Fin (2 * n + 1))) ∈
        (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
    refine hmem_pair (y₁ + y₂) u v ((TypeB.isPair_iff u v).mpr (Or.inr hax)) ?_
    rw [map_add, hy₁, hy₂, TypeB.rootOfPair_of_ne (fun h ↦ hax (congrArg TypeB.axis h)), map_add]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨p, hp⟩ := RootPairing.mem_foldedIndices.mp hx
    let xf : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap :=
      ⟨x, hp ▸ RootPairing.orbitSum_mem_fixedSubmodule _ _ p⟩
    obtain ⟨idx, hidx⟩ :=
      (mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices K n xf).mpr hx
    rw [root_typeBBaseChangeRootSystem] at hidx
    obtain ⟨u, v, huv, hr⟩ := mem_range_root_typeBSimplyConnectedRootDatum_iff.mp ⟨idx, rfl⟩
    have hroot : evenTypeAFixedCoordEquiv K n xf =
        Pi.algebraMap (Fin n) ℤ K (TypeB.rootOfPair u v) := hidx.symm.trans (congrArg _ hr)
    rcases eq_or_ne u v with rfl | hne
    · left
      have hxf : xf = evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) :=
        (evenTypeAFixedCoordEquiv K n).injective (by
          rw [hroot, TypeB.rootOfPair_self, evenTypeAFixedCoordEquiv_signedIdx])
      have hu : x = (evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) :
          singleParityCheckCode K (Fin (2 * n + 1))) := congrArg Subtype.val hxf
      rw [hu, coe_evenTypeAFoldAtomFixed, evenTypeASignedIdx]
      split_ifs with hlt
      · exact ⟨⟨u, hlt⟩, Or.inl rfl⟩
      · refine ⟨⟨(u : ℕ) - n, by have := u.isLt; omega⟩, Or.inr ?_⟩
        rw [evenTypeAFoldAtom, ← neg_typeAZeroSumVec, Fin.rev_rev]; rfl
    · right
      have hax : TypeB.axis u ≠ TypeB.axis v := ((TypeB.isPair_iff u v).mp huv).resolve_left hne
      have hxf : xf = evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) +
          evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n v) :=
        (evenTypeAFixedCoordEquiv K n).injective (by
          rw [hroot, TypeB.rootOfPair_of_ne hne, map_add, map_add (evenTypeAFixedCoordEquiv K n),
            evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx])
      have hx' : x = (evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) +
          evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n v) :
          singleParityCheckCode K (Fin (2 * n + 1))) := congrArg Subtype.val hxf
      have hu := u.isLt; have hv := v.isLt
      by_cases hlu : (u : ℕ) < n <;> by_cases hlv : (v : ℕ) < n
      · refine ⟨⟨u, hlu⟩, ⟨v, hlv⟩, ?_, Or.inl ?_⟩
        · simpa [Fin.ext_iff, TypeB.axis_def, hlu, hlv] using hax
        · simpa [evenTypeASignedIdx, hlu, hlv, evenTypeAFoldAtom, evenTypeABasisVec] using hx'
      · refine ⟨⟨u, hlu⟩, ⟨(v : ℕ) - n, by omega⟩, ?_, Or.inr (Or.inl ?_)⟩
        · simpa [Fin.ext_iff, TypeB.axis_def, hlu, hlv] using hax
        · simpa [evenTypeASignedIdx, hlu, hlv, evenTypeAFoldAtom, evenTypeABasisVec, sub_eq_add_neg]
            using hx'
      · refine ⟨⟨(u : ℕ) - n, by omega⟩, ⟨v, hlv⟩, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
        · simpa [Fin.ext_iff, TypeB.axis_def, hlu, hlv] using hax
        · simpa [evenTypeASignedIdx, hlu, hlv, evenTypeAFoldAtom, evenTypeABasisVec] using hx'
      · refine ⟨⟨(u : ℕ) - n, by omega⟩, ⟨(v : ℕ) - n, by omega⟩, ?_, Or.inr (Or.inr (Or.inr ?_))⟩
        · simpa [Fin.ext_iff, TypeB.axis_def, hlu, hlv] using hax
        · simpa [evenTypeASignedIdx, hlu, hlv, evenTypeAFoldAtom, evenTypeABasisVec, sub_eq_add_neg]
            using hx'
  · rintro (⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl | rfl⟩)
    · refine hmem_pair ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩
        ⟨i, by have := i.isLt; omega⟩ ⟨i, by have := i.isLt; omega⟩
        ((TypeB.isPair_iff _ _).mpr (Or.inl rfl)) ?_
      rw [evenTypeAFixedCoordEquiv_basisVec, TypeB.rootOfPair_self, (hpos_signed i).2]
    · refine hmem_pair (-⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩)
        ⟨n + i, by have := i.isLt; omega⟩ ⟨n + i, by have := i.isLt; omega⟩
        ((TypeB.isPair_iff _ _).mpr (Or.inl rfl)) ?_
      rw [map_neg (evenTypeAFixedCoordEquiv K n), evenTypeAFixedCoordEquiv_basisVec,
        TypeB.rootOfPair_self, (hneg_signed i).2, map_neg]
    · exact hmem_pair_ne ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩
        ⟨evenTypeABasisVec K n j, evenTypeABasisVec_mem_fixedSubmodule K n j⟩
        ⟨i, by have := i.isLt; omega⟩ ⟨j, by have := j.isLt; omega⟩
        (by rw [(hpos_signed i).1, (hpos_signed j).1]; exact Fin.val_ne_of_ne hij)
        (by rw [evenTypeAFixedCoordEquiv_basisVec, (hpos_signed i).2])
        (by rw [evenTypeAFixedCoordEquiv_basisVec, (hpos_signed j).2])
    · simpa only [Submodule.coe_add, Submodule.coe_neg, ← sub_eq_add_neg] using
        hmem_pair_ne ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩
          (-⟨evenTypeABasisVec K n j, evenTypeABasisVec_mem_fixedSubmodule K n j⟩)
          ⟨i, by have := i.isLt; omega⟩ ⟨n + j, by have := j.isLt; omega⟩
          (by rw [(hpos_signed i).1, (hneg_signed j).1]; exact Fin.val_ne_of_ne hij)
          (by rw [evenTypeAFixedCoordEquiv_basisVec, (hpos_signed i).2])
          (by rw [map_neg (evenTypeAFixedCoordEquiv K n), evenTypeAFixedCoordEquiv_basisVec,
            (hneg_signed j).2, map_neg])
    · simpa only [Submodule.coe_add, Submodule.coe_neg] using
        hmem_pair_ne (-⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩)
          ⟨evenTypeABasisVec K n j, evenTypeABasisVec_mem_fixedSubmodule K n j⟩
          ⟨n + i, by have := i.isLt; omega⟩ ⟨j, by have := j.isLt; omega⟩
          (by rw [(hneg_signed i).1, (hpos_signed j).1]; exact Fin.val_ne_of_ne hij)
          (by rw [map_neg (evenTypeAFixedCoordEquiv K n), evenTypeAFixedCoordEquiv_basisVec,
            (hneg_signed i).2, map_neg])
          (by rw [evenTypeAFixedCoordEquiv_basisVec, (hpos_signed j).2])
    · simpa only [Submodule.coe_add, Submodule.coe_neg, ← sub_eq_add_neg] using
        hmem_pair_ne (-⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩)
          (-⟨evenTypeABasisVec K n j, evenTypeABasisVec_mem_fixedSubmodule K n j⟩)
          ⟨n + i, by have := i.isLt; omega⟩ ⟨n + j, by have := j.isLt; omega⟩
          (by rw [(hneg_signed i).1, (hneg_signed j).1]; exact Fin.val_ne_of_ne hij)
          (by rw [map_neg (evenTypeAFixedCoordEquiv K n), evenTypeAFixedCoordEquiv_basisVec,
            (hneg_signed i).2, map_neg])
          (by rw [map_neg (evenTypeAFixedCoordEquiv K n), evenTypeAFixedCoordEquiv_basisVec,
            (hneg_signed j).2, map_neg])

/-- `evenTypeAFixedCoordEquiv K n` sends the `k`-th simple orbit sum of `A₂ₙ` to the `k`-th
Bourbaki simple root of `typeBBaseChangeRootSystem K n`. -/
theorem evenTypeAFixedCoordEquiv_simpleOrbitSum (n : ℕ) (k : Fin n) :
    evenTypeAFixedCoordEquiv K n
        ⟨(typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
          (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩),
          RootPairing.orbitSum_mem_fixedSubmodule _ _ _⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
  have hk := k.isLt
  have hrhs : (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) =
      Pi.algebraMap (Fin n) ℤ K (TypeB.weight n k - TypeB.weight n ((k : ℕ) + 1)) := by
    ext j; have := j.isLt
    rw [root_typeBBaseChangeRootSystem, piAlgebraMap_apply, piAlgebraMap_apply,
      root_typeBSimpleIndex]
    congr 1
    simp only [CartanMatrix.B, Matrix.of_apply, Pi.sub_apply, TypeB.weight_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [hrhs]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [map_sub, ← evenTypeAFixedCoordEquiv_basisVec K n k,
      ← evenTypeAFixedCoordEquiv_basisVec K n ⟨(k : ℕ) + 1, hlt⟩, ← map_sub]
    exact congrArg _ (Subtype.ext (by simp [orbitSum_typeAZeroSumRevAut_simplePair, hlt]))
  · rw [TypeB.weight_eq_zero_of_le (by omega : n ≤ (k : ℕ) + 1), sub_zero,
      ← evenTypeAFixedCoordEquiv_basisVec K n k]
    exact congrArg _ (Subtype.ext (by simp [orbitSum_typeAZeroSumRevAut_simplePair, hlt]))

end Field

end TauCeti.DynkinType
