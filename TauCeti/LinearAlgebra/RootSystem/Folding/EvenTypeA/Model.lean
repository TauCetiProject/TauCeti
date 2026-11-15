/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
public import TauCeti.LinearAlgebra.RootSystem.ZeroSumTypeA
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NonSimplyLaced

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

/-- The `i`-th basis vector `fᵢ = eᵢ - e₂ₙ₋ᵢ` of the reversal-fixed subspace. -/
def evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    singleParityCheckCode R (Fin (2 * n + 1)) :=
  typeAZeroSumVec R (evenTypeALeftIdx n i) (evenTypeALeftIdx n i).rev

/-- `evenTypeABasisVec` is fixed by `typeAZeroSumRevEquiv`. -/
@[simp] theorem typeAZeroSumRevEquiv_evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ)
    (i : Fin n) :
    typeAZeroSumRevEquiv R (2 * n) (evenTypeABasisVec R n i) = evenTypeABasisVec R n i := by
  rw [evenTypeABasisVec, typeAZeroSumRevEquiv_vec, Fin.rev_rev]

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
theorem evenTypeABasisVec_dotProduct (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) ⬝ᵥ
        (evenTypeABasisVec R n j : Fin (2 * n + 1) → R) = if i = j then 2 else 0 := by
  have := i.isLt; have := j.isLt
  rw [evenTypeABasisVec, evenTypeABasisVec, typeAZeroSumVec_dotProduct]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

private def evenTypeAFoldAtom (R : Type*) [CommRing R] (n : ℕ) (a : Fin (2 * n + 1)) :
    singleParityCheckCode R (Fin (2 * n + 1)) := typeAZeroSumVec R a a.rev

private lemma evenTypeAFoldAtom_rev (R : Type*) [CommRing R] (n : ℕ) (a : Fin (2 * n + 1)) :
    evenTypeAFoldAtom R n a.rev = -evenTypeAFoldAtom R n a := by
  rw [evenTypeAFoldAtom, Fin.rev_rev, evenTypeAFoldAtom, neg_typeAZeroSumVec]

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

private lemma evenTypeAFoldAtom_dotProduct_basisVec (R : Type*) [CommRing R] (n : ℕ)
    (a : Fin (2 * n + 1)) (i : Fin n) :
    (evenTypeAFoldAtom R n a : Fin (2 * n + 1) → R) ⬝ᵥ
        (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) =
      if a = evenTypeALeftIdx n i then 2
      else if a = (evenTypeALeftIdx n i).rev then -2 else 0 := by
  have := a.isLt; have := i.isLt
  rw [evenTypeAFoldAtom, evenTypeABasisVec, typeAZeroSumVec_dotProduct]
  simp only [Fin.ext_iff, Fin.val_rev, val_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- Every `evenTypeABasisVec` lies in the fixed submodule of `typeAZeroSumRevAut K (2 * n)`. -/
theorem evenTypeABasisVec_mem_fixedSubmodule (n : ℕ) (i : Fin n) :
    evenTypeABasisVec K n i ∈
      LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
    typeAZeroSumRevEquiv_evenTypeABasisVec]

private lemma fixedSubmodule_revAut_apply_rev {n : ℕ}
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap)
    (a : Fin (2 * n + 1)) :
    ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a.rev =
      -((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a := by
  let v : singleParityCheckCode K (Fin (2 * n + 1)) := x
  have hx : (typeAZeroSumRevAut K (2 * n)).weightMap v = v :=
    LinearMap.mem_fixedSubmodule_iff.mp x.2
  rw [weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe] at hx
  have ha := congrArg (fun w : singleParityCheckCode K (Fin (2 * n + 1)) ↦
    (w : Fin (2 * n + 1) → K) a) hx
  rwa [coe_typeAZeroSumRevEquiv_apply, neg_eq_iff_eq_neg] at ha

private lemma fixedSubmodule_revAut_apply_mid {n : ℕ}
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
      (evenTypeAMidIdx n) = 0 := by
  have h := fixedSubmodule_revAut_apply_rev K x (evenTypeAMidIdx n)
  rw [rev_evenTypeAMidIdx] at h
  exact (mul_eq_zero.mp (show (2 : K) * _ = 0 by linear_combination h)).resolve_left two_ne_zero

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
    apply Subtype.ext; apply Subtype.ext; ext a
    let cx : Fin (2 * n + 1) → K := x.1
    have hsum : (((∑ i : Fin n, cx (evenTypeALeftIdx n i) • evenTypeABasisVec K n i :
        singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a) =
        ∑ i : Fin n, cx (evenTypeALeftIdx n i) * (evenTypeABasisVec K n i : _ → K) a := by simp
    dsimp only; rw [hsum]
    rcases lt_trichotomy (a : ℕ) n with hlt | heq | hgt
    · rw [show a = evenTypeALeftIdx n ⟨a, hlt⟩ from rfl]; simp [evenTypeABasisVec_apply_left, cx]
    · rw [show a = evenTypeAMidIdx n from Fin.ext heq, fixedSubmodule_revAut_apply_mid]
      simp [evenTypeABasisVec_apply_mid]
    · let j : Fin n := ⟨2 * n - a, by have := a.isLt; omega⟩
      rw [show a = (evenTypeALeftIdx n j).rev from
        Fin.ext (by rw [val_rev_evenTypeALeftIdx]; dsimp [j]; have := a.isLt; omega),
        fixedSubmodule_revAut_apply_rev]
      have hval (i : Fin n) :
          (evenTypeABasisVec K n i : Fin (2 * n + 1) → K) (evenTypeALeftIdx n j).rev =
            -(if i = j then (1 : K) else 0) := by
        have := i.isLt; rw [evenTypeABasisVec, typeAZeroSumVec_apply]
        simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
        split_ifs <;> first | (norm_num; done) | (exfalso; omega)
      simp [hval, cx]

/-- The vectors `fᵢ = eᵢ - e₂ₙ₋ᵢ` (`i : Fin n`) form a `K`-basis of the fixed subspace. -/
noncomputable def evenTypeAFixedBasis (n : ℕ) :
    Module.Basis (Fin n) K (LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :=
  Module.Basis.ofRepr
    ((evenTypeAFixedLeftEquiv K n).trans (Finsupp.linearEquivFunOnFinite K K (Fin n)).symm)

/-- The `i`-th vector of `evenTypeAFixedBasis K n` coerces to `evenTypeABasisVec K n i`. -/
@[simp] theorem coe_evenTypeAFixedBasis_apply (n : ℕ) (i : Fin n) :
    (evenTypeAFixedBasis K n i : singleParityCheckCode K (Fin (2 * n + 1))) =
      evenTypeABasisVec K n i := by
  rw [evenTypeAFixedBasis, Module.Basis.coe_ofRepr]
  dsimp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    evenTypeAFixedLeftEquiv, LinearEquiv.coe_mk]; simp

/-- The root orbit of `p : TypeAIndex m` under `typeAZeroSumRevAut K m` is
`{p, finDistinctPairsRevSwap (m + 1) p}`. -/
theorem orbitIndices_typeAZeroSumRevAut (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).orbitIndices (typeAZeroSumRevAut K m) p =
      {p, finDistinctPairsRevSwap (m + 1) p} := by
  have hpow (k : ℕ) : (finDistinctPairsRevSwap (m + 1) ^ k) p = p ∨
      (finDistinctPairsRevSwap (m + 1) ^ k) p = finDistinctPairsRevSwap (m + 1) p := by
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.elim (fun h ↦ Or.inr (by rw [h]))
        (fun h ↦ Or.inl (by rw [h, finDistinctPairsRevSwap_finDistinctPairsRevSwap]))
  ext q; rw [RootPairing.mem_orbitIndices_iff_exists_pow, indexEquiv_typeAZeroSumRevAut,
    mem_insert, mem_singleton]
  exact ⟨fun ⟨k, hk⟩ ↦ hk ▸ hpow k, by rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, by simp⟩]⟩

/-- A root pair `p` is fixed by `finDistinctPairsRevSwap (m + 1)` iff `p.val.2 = p.val.1.rev`. -/
theorem finDistinctPairsRevSwap_eq_self_iff {m : ℕ} {p : TypeAIndex m} :
    finDistinctPairsRevSwap (m + 1) p = p ↔ p.val.2 = p.val.1.rev := by
  rw [Subtype.ext_iff, finDistinctPairsRevSwap_apply_val, Prod.ext_iff, Fin.rev_eq_iff,
    eq_comm (a := p.val.1.rev), and_self]

private lemma orbitSum_typeAZeroSumRevAut_eq (n : ℕ) (p : TypeAIndex (2 * n)) :
    (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p =
      if p.val.2 = p.val.1.rev then evenTypeAFoldAtom K n p.val.1
      else evenTypeAFoldAtom K n p.val.1 - evenTypeAFoldAtom K n p.val.2 := by
  rw [RootPairing.orbitSum_def, orbitIndices_typeAZeroSumRevAut]
  by_cases hfix : p.val.2 = p.val.1.rev
  · rw [ite_eq_left hfix, finDistinctPairsRevSwap_eq_self_iff.mpr hfix, pair_eq_singleton,
      sum_singleton, root_typeAZeroSumRootPairing, hfix, evenTypeAFoldAtom]
  · have hp : p ≠ finDistinctPairsRevSwap (2 * n + 1) p :=
      fun hc ↦ hfix (finDistinctPairsRevSwap_eq_self_iff.mp hc.symm)
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
  let s := typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩
  have hs_val : s.val = (⟨k, by omega⟩, ⟨(k : ℕ) + 1, by omega⟩) :=
    typeAZeroSumSimplePair_val (2 * n) ⟨k, by omega⟩
  have hs1 : s.val.1 = evenTypeALeftIdx n k := (congrArg Prod.fst hs_val).trans rfl
  have hs2_val : (s.val.2 : ℕ) = (k : ℕ) + 1 := congrArg (Fin.val ∘ Prod.snd) hs_val
  have hne : s.val.2 ≠ s.val.1.rev := fun hc ↦ by
    have hval := congrArg Fin.val hc; rw [hs2_val, hs1, val_rev_evenTypeALeftIdx] at hval; omega
  change (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) s = _
  rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, hs1, evenTypeAFoldAtom_left]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [dite_eq_left hlt, show s.val.2 = evenTypeALeftIdx n ⟨(k : ℕ) + 1, hlt⟩ from Fin.ext hs2_val,
      evenTypeAFoldAtom_left]
  · rw [dite_eq_right hlt,
      show s.val.2 = evenTypeAMidIdx n from Fin.ext (by rw [hs2_val, val_evenTypeAMidIdx]; omega),
      evenTypeAFoldAtom_mid, sub_zero]

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
    by rw [orbitIndices_typeAZeroSumRevAut, finDistinctPairsRevSwap_eq_self_iff.mpr hfix,
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
    rw [evenTypeAPairedShortLift_val]
    simp only [ne_eq, Fin.ext_iff, val_evenTypeAMidIdx, val_rev_evenTypeALeftIdx]; omega
  refine ⟨by rw [isPos_typeAZeroSumBase_iff, evenTypeAPairedShortLift_val, Fin.lt_def,
      val_evenTypeALeftIdx, val_evenTypeAMidIdx]; exact hi,
    by rw [orbitIndices_typeAZeroSumRevAut]
       exact card_pair fun hc ↦ hne (finDistinctPairsRevSwap_eq_self_iff.mp hc.symm),
    by rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, evenTypeAPairedShortLift_val,
      evenTypeAFoldAtom_left, evenTypeAFoldAtom_mid, sub_zero]⟩

/-- Twice a short root `2 • fᵢ` is never an orbit sum of `typeAZeroSumRevAut K (2 * n)`. -/
theorem two_smul_evenTypeABasisVec_notMem_foldedIndices (n : ℕ) (i : Fin n) :
    (2 : K) • evenTypeABasisVec K n i ∉
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  rw [RootPairing.mem_foldedIndices]; rintro ⟨p, hp⟩
  have hdot := congrArg (fun v : singleParityCheckCode K (Fin (2 * n + 1)) ↦
    (v : Fin (2 * n + 1) → K) ⬝ᵥ (evenTypeABasisVec K n i : Fin (2 * n + 1) → K)) hp
  rw [SetLike.val_smul, smul_dotProduct, smul_eq_mul, evenTypeABasisVec_dotProduct,
    ite_eq_left rfl, orbitSum_typeAZeroSumRevAut_eq] at hdot
  by_cases hfix : p.val.2 = p.val.1.rev
  · rw [ite_eq_left hfix, evenTypeAFoldAtom_dotProduct_basisVec] at hdot
    split_ifs at hdot <;> norm_num at hdot
  · rw [ite_eq_right hfix, Submodule.coe_sub, sub_dotProduct,
      evenTypeAFoldAtom_dotProduct_basisVec, evenTypeAFoldAtom_dotProduct_basisVec] at hdot
    split_ifs at hdot <;> first | (norm_num at hdot; done) | exact hfix (by simp_all)

/-- Entrywise base-changed root system of type `Bₙ` on `Fin n → K`. -/
def typeBBaseChangeRootSystem (n : ℕ) :
    RootPairing (Fin (2 * n ^ 2)) K (Fin n → K) (Fin n → K) :=
  rootPairingBaseChange K (typeBSimplyConnectedRootDatum n)
    (fun x y ↦ toLinearMap_typeBSimplyConnectedRootDatum x y)

/-- The Bourbaki-numbered base of `typeBBaseChangeRootSystem K n`. -/
def typeBBaseChangeBase (n : ℕ) : (typeBBaseChangeRootSystem K n).Base :=
  rootPairingBaseChangeBase K (typeBSimplyConnectedRootDatum n)
    (fun x y ↦ toLinearMap_typeBSimplyConnectedRootDatum x y) (typeBSimplyConnectedBase n)

/-- `typeBBaseChangeRootSystem K n` is crystallographic. -/
instance instIsCrystallographicTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

/-- `typeBBaseChangeRootSystem K n` is reduced. -/
instance instIsReducedTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsReduced := isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeBBaseChangeRootSystem K n`
span `Fin n → K`. -/
instance instIsRootSystemTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsRootSystem where
  span_root_eq_top := top_le_iff.mp <| by
    have hcard : Fintype.card (typeBBaseChangeBase K n).support =
        Module.finrank K (Fin n → K) := by
      rw [Fintype.card_coe, Module.finrank_fin_fun, typeBBaseChangeBase,
        support_rootPairingBaseChangeBase,
        (hasCartanType_typeBSimplyConnectedRootDatum n).card_support, DynkinType.rank_B]
    rw [← (typeBBaseChangeBase K n).linearIndepOn_root.span_eq_top_of_card_eq_finrank' hcard]
    exact Submodule.span_mono <| by
      rintro - ⟨i, rfl⟩; exact Set.mem_range_self (i : Fin (2 * n ^ 2))
  span_coroot_eq_top := span_range_coroot_rootPairingBaseChange_eq_top K _ _
    (corootSpan_typeBSimplyConnectedRootDatum_eq_top n)

/-- `typeBBaseChangeBase K n` has Cartan type `B n`. -/
theorem hasCartanType_typeBBaseChangeBase (n : ℕ) :
    HasCartanType (typeBBaseChangeRootSystem K n) (typeBBaseChangeBase K n) (.B n) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).mp (hasCartanType_typeBSimplyConnectedRootDatum n)
  exact (hasCartanType_iff _ _).mpr ⟨(supportEquivRootPairingBaseChangeBase K _ _ _).trans e,
    fun i j ↦ (cartanMatrix_rootPairingBaseChangeBase K _ _ _ i j).trans (he _ _)⟩

/-- The bilinear pairing of `typeBBaseChangeRootSystem K n` is `dotProduct`. -/
@[simp] theorem toLinearMap_typeBBaseChangeRootSystem (n : ℕ) (x y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange K (typeBSimplyConnectedRootDatum n) _ x y

/-- `m ∈ (typeBBaseChangeBase K n).support` iff `(m : ℕ) < n`. -/
@[simp] theorem mem_support_typeBBaseChangeBase_iff (n : ℕ) (m : Fin (2 * n ^ 2)) :
    m ∈ (typeBBaseChangeBase K n).support ↔ (m : ℕ) < n := by
  rw [typeBBaseChangeBase, support_rootPairingBaseChangeBase, mem_typeBSimplyConnectedBase_support]

/-- Evaluating the `k`-th simple coroot of `typeBBaseChangeRootSystem K n` on `y` gives `y k`. -/
theorem coroot'_typeBBaseChangeRootSystem_simpleIndex (n : ℕ) (k : Fin n) (y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).coroot' (typeBSimpleIndex n k) y = y k := by
  rw [RootPairing.coroot', LinearMap.flip_apply, typeBBaseChangeRootSystem,
    toLinearMap_rootPairingBaseChange, coroot_rootPairingBaseChange, coroot_typeBSimpleIndex]
  have hsingle : Pi.algebraMap (Fin n) ℤ K (Pi.single k 1) = Pi.single k (1 : K) := by
    ext j; rcases eq_or_ne j k with rfl | hjk <;> simp [piAlgebraMap_apply, *]
  rw [hsingle, dotProduct_single, mul_one]

private def typeBFundamentalCoordMap (n : ℕ) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun y k := if h : (k : ℕ) + 1 < n then y k - y ⟨(k : ℕ) + 1, h⟩ else 2 * y k
  map_add' _ _ := funext fun _ ↦ by simp; split_ifs <;> ring
  map_smul' _ _ := funext fun _ ↦ by simp; split_ifs <;> ring

private lemma typeBFundamentalCoordMap_injective (n : ℕ) :
    Injective (typeBFundamentalCoordMap K n) := by
  intro y₁ y₂ hy₁₂; suffices hsub : y₁ - y₂ = 0 from sub_eq_zero.mp hsub
  have hy : typeBFundamentalCoordMap K n (y₁ - y₂) = 0 := by rw [map_sub, hy₁₂, sub_self]
  set y := y₁ - y₂
  have hzero (d : ℕ) (hd0 : 0 < d) (hd : d ≤ n) : y ⟨n - d, by omega⟩ = 0 := by
    induction d with
    | zero => omega
    | succ d ih =>
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · have hk := congrFun hy ⟨n - 1, by omega⟩
        dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hk
        rw [dite_eq_right (by omega)] at hk; exact (mul_eq_zero.mp hk).resolve_left two_ne_zero
      · have hk := congrFun hy ⟨n - (d + 1), by omega⟩
        dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hk
        rw [dite_eq_left (by omega)] at hk; have hstep := sub_eq_zero.mp hk
        rw [show (⟨n - (d + 1) + 1, by omega⟩ : Fin n) = ⟨n - d, by omega⟩ from
          Fin.ext (by dsimp; omega)] at hstep
        exact hstep.trans (ih hdpos (by omega))
  ext i; have := i.isLt
  rw [show i = ⟨n - (n - i), by omega⟩ from Fin.ext (by dsimp; omega), Pi.zero_apply]
  exact hzero (n - i) (by omega) (by omega)

private noncomputable def typeBFundamentalCoordEquiv (n : ℕ) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  have hinj := typeBFundamentalCoordMap_injective K n
  LinearEquiv.ofBijective (typeBFundamentalCoordMap K n)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

/-- Fundamental-weight coordinate equivalence from the reversal-fixed subspace to `Fin n → K`. -/
noncomputable def evenTypeAFixedCoordEquiv (n : ℕ) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap ≃ₗ[K] (Fin n → K) :=
  (evenTypeAFixedLeftEquiv K n).trans (typeBFundamentalCoordEquiv K n)

/-- Coordinate formula for `evenTypeAFixedCoordEquiv K n`: scales the `k`-th simple coroot pairing
by `1` off the middle (`k + 1 < n`) and by `2` at the middle (`k + 1 = n`). -/
theorem evenTypeAFixedCoordEquiv_apply (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) (k : Fin n) :
    evenTypeAFixedCoordEquiv K n x k =
      (if (k : ℕ) + 1 = n then (2 : K) else 1) *
        (typeAZeroSumRootPairing K (2 * n)).coroot'
          (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩) (x : _) := by
  have hk := k.isLt; rw [coroot'_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val]
  change typeBFundamentalCoordMap K n (evenTypeAFixedLeftEquiv K n x) k = _
  dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk,
    evenTypeAFixedLeftEquiv, LinearEquiv.coe_mk]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [dite_eq_left hlt, ite_eq_right (by omega), one_mul]; rfl
  · have hlast : (k : ℕ) + 1 = n := by omega
    rw [dite_eq_right hlt, ite_eq_left hlast,
      show (⟨(k : ℕ), by omega⟩ : Fin (2 * n)).succ = evenTypeAMidIdx n from
        Fin.ext (by rw [Fin.val_succ, val_evenTypeAMidIdx]; exact hlast),
      fixedSubmodule_revAut_apply_mid K x, sub_zero]; rfl

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
  split_ifs with h
  · rw [val_evenTypeALeftIdx]; omega
  · rw [val_rev_evenTypeALeftIdx]; dsimp; omega

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
  · exact ⟨⟨a, by omega⟩, by rw [evenTypeASignedIdx, dite_eq_left hlt]; rfl⟩
  · refine ⟨⟨n + (2 * n - a), by omega⟩, ?_⟩
    rw [evenTypeASignedIdx, dite_eq_right (show ¬ (n + (2 * n - (a : ℕ)) < n) by omega)]
    ext; rw [val_rev_evenTypeALeftIdx]; dsimp; omega

private def evenTypeAFoldAtomFixed (n : ℕ) (a : Fin (2 * n + 1)) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap :=
  ⟨evenTypeAFoldAtom K n a, by
    rw [LinearMap.mem_fixedSubmodule_iff, weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
      evenTypeAFoldAtom, typeAZeroSumRevEquiv_vec, Fin.rev_rev]⟩

private lemma evenTypeAFixedCoordEquiv_signedIdx (n : ℕ) (u : Fin (2 * n)) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u)) =
      Pi.algebraMap (Fin n) ℤ K (TypeB.signedWeight u) := by
  have := u.isLt
  by_cases hlt : (u : ℕ) < n
  · rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_left hlt, ite_eq_left hlt,
      one_smul, ← evenTypeAFixedCoordEquiv_basisVec K n ⟨u, hlt⟩]; congr 1
    exact Subtype.ext (by simp [evenTypeAFoldAtomFixed, evenTypeASignedIdx, hlt,
      evenTypeAFoldAtom_left])
  · rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_right hlt, ite_eq_right hlt,
      neg_one_smul, map_neg, ← evenTypeAFixedCoordEquiv_basisVec K n ⟨(u : ℕ) - n, by omega⟩,
      eq_neg_iff_add_eq_zero, ← map_add, show evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) +
        ⟨evenTypeABasisVec K n ⟨(u : ℕ) - n, by omega⟩,
          evenTypeABasisVec_mem_fixedSubmodule K n _⟩ = 0 from Subtype.ext (by
        rw [Submodule.coe_add, Submodule.coe_zero]; dsimp only [evenTypeAFoldAtomFixed]
        rw [evenTypeASignedIdx, dite_eq_right hlt, evenTypeAFoldAtom_rev, evenTypeAFoldAtom_left,
          neg_add_cancel]), map_zero]

private lemma mem_foldedIndices_of_mem_range_typeB {n : ℕ}
    {x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap}
    (hx : evenTypeAFixedCoordEquiv K n x ∈ Set.range (typeBBaseChangeRootSystem K n).root) :
    (x : singleParityCheckCode K (Fin (2 * n + 1))) ∈
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  rw [RootPairing.mem_foldedIndices]
  obtain ⟨u, v, huv, hroot⟩ : ∃ u v : Fin (2 * n), TypeB.IsPair u v ∧
      evenTypeAFixedCoordEquiv K n x = Pi.algebraMap (Fin n) ℤ K (TypeB.rootOfPair u v) := by
    obtain ⟨idx, hidx⟩ := hx; rw [typeBBaseChangeRootSystem, root_rootPairingBaseChange] at hidx
    obtain ⟨u, v, huv, hr⟩ := mem_range_root_typeBSimplyConnectedRootDatum_iff.mp ⟨idx, rfl⟩
    exact ⟨u, v, huv, hidx.symm.trans (congrArg _ hr)⟩
  rcases eq_or_ne u v with rfl | hne
  · refine ⟨⟨(evenTypeASignedIdx n u, (evenTypeASignedIdx n u).rev),
      fun hc ↦ evenTypeASignedIdx_ne_mid n u (rev_eq_self_iff_eq_evenTypeAMidIdx.mp hc.symm)⟩, ?_⟩
    have hx' : x = evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) :=
      (evenTypeAFixedCoordEquiv K n).injective
        (show evenTypeAFixedCoordEquiv K n x = _ by
          rw [hroot, TypeB.rootOfPair_self, evenTypeAFixedCoordEquiv_signedIdx])
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_left rfl]; rfl
  · let a := evenTypeASignedIdx n u; let b := (evenTypeASignedIdx n v).rev
    have hab : a ≠ b := by
      dsimp only [a, b]; rw [rev_evenTypeASignedIdx]
      exact fun hc ↦ huv.ne_opp (evenTypeASignedIdx_injective n hc)
    have hnotfix : b ≠ a.rev :=
      fun hc ↦ hne (evenTypeASignedIdx_injective n (Fin.rev_inj.mp hc).symm)
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    have hx' : x = evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b :=
      (evenTypeAFixedCoordEquiv K n).injective <| by
        have hsub : evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b =
            evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) +
              evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n v) :=
          Subtype.ext <| by
            simp [evenTypeAFoldAtomFixed, a, b, evenTypeAFoldAtom_rev, sub_neg_eq_add]
        rw [hroot, TypeB.rootOfPair_of_ne hne, map_add, hsub, map_add,
          evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx]
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hnotfix]; rfl

private lemma evenTypeAFoldAtom_mem_range_typeB (n : ℕ) {a : Fin (2 * n + 1)}
    (ha : a ≠ evenTypeAMidIdx n) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a) ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  obtain ⟨u, rfl⟩ := exists_evenTypeASignedIdx ha
  rw [evenTypeAFixedCoordEquiv_signedIdx, ← TypeB.rootOfPair_self, typeBBaseChangeRootSystem,
    piAlgebraMap_mem_range_root_rootPairingBaseChange_iff,
    mem_range_root_typeBSimplyConnectedRootDatum_iff]
  exact ⟨u, u, (TypeB.isPair_iff u u).mpr (Or.inl rfl), rfl⟩

private lemma evenTypeAFoldAtom_sub_mem_range_typeB (n : ℕ) {a b : Fin (2 * n + 1)}
    (hab : a ≠ b) (hnotfix : b ≠ a.rev) :
    evenTypeAFixedCoordEquiv K n (evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b) ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  by_cases ha : a = evenTypeAMidIdx n
  · rw [show evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b =
      evenTypeAFoldAtomFixed K n b.rev from Subtype.ext (by
        simp [evenTypeAFoldAtomFixed, ha, evenTypeAFoldAtom_mid, evenTypeAFoldAtom_rev])]
    exact evenTypeAFoldAtom_mem_range_typeB K n fun hc ↦
      hab (ha.trans (by simpa [rev_evenTypeAMidIdx] using (congrArg Fin.rev hc).symm))
  · by_cases hb : b = evenTypeAMidIdx n
    · rw [show evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b =
        evenTypeAFoldAtomFixed K n a from Subtype.ext (by
          simp [evenTypeAFoldAtomFixed, hb, evenTypeAFoldAtom_mid])]
      exact evenTypeAFoldAtom_mem_range_typeB K n ha
    · obtain ⟨u, hu⟩ := exists_evenTypeASignedIdx ha
      obtain ⟨v, hv⟩ := exists_evenTypeASignedIdx (a := b.rev)
        (fun hc ↦ hb (by simpa [rev_evenTypeAMidIdx] using congrArg Fin.rev hc))
      have huv_ne : u ≠ v := fun hc ↦ hnotfix (by
        have := hc ▸ hv; simpa [hu] using (congrArg Fin.rev this).symm)
      have huv_opp : u ≠ TypeB.opp v := fun hc ↦ hab (by
        rw [← hu, hc, ← rev_evenTypeASignedIdx, hv, Fin.rev_rev])
      rw [show evenTypeAFoldAtomFixed K n a - evenTypeAFoldAtomFixed K n b =
        evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n u) +
          evenTypeAFoldAtomFixed K n (evenTypeASignedIdx n v) from Subtype.ext (by
          simp [evenTypeAFoldAtomFixed, hu, hv, evenTypeAFoldAtom_rev, sub_eq_add_neg]),
        map_add, evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx,
        ← map_add, ← TypeB.rootOfPair_of_ne huv_ne, typeBBaseChangeRootSystem,
        piAlgebraMap_mem_range_root_rootPairingBaseChange_iff,
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
  · rw [show x = evenTypeAFoldAtomFixed K n p.val.1 from Subtype.ext <| by
      rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_left hfix]; rfl]
    exact evenTypeAFoldAtom_mem_range_typeB K n
      (fun hc ↦ p.2 (by rw [hfix, hc, rev_evenTypeAMidIdx]))
  · rw [show x = evenTypeAFoldAtomFixed K n p.val.1 - evenTypeAFoldAtomFixed K n p.val.2 from
      Subtype.ext <| by rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hfix]; rfl]
    exact evenTypeAFoldAtom_sub_mem_range_typeB K n p.2 hfix

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
    rw [typeBBaseChangeRootSystem, root_rootPairingBaseChange, piAlgebraMap_apply,
      piAlgebraMap_apply, root_typeBSimpleIndex]; congr 1
    simp only [CartanMatrix.B, Matrix.of_apply, Pi.sub_apply, TypeB.weight_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [hrhs]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [map_sub, ← evenTypeAFixedCoordEquiv_basisVec K n k,
      ← evenTypeAFixedCoordEquiv_basisVec K n ⟨(k : ℕ) + 1, hlt⟩, eq_sub_iff_add_eq, ← map_add]
    congr 1; apply Subtype.ext; rw [Submodule.coe_add]; dsimp only
    rw [orbitSum_typeAZeroSumRevAut_simplePair, dite_eq_left hlt, sub_add_cancel]
  · rw [TypeB.weight_eq_zero_of_le (show n ≤ (k : ℕ) + 1 by omega), sub_zero,
      ← evenTypeAFixedCoordEquiv_basisVec K n k]
    congr 1; exact Subtype.ext (by
      dsimp only; rw [orbitSum_typeAZeroSumRevAut_simplePair, dite_eq_right hlt])

end Field

end TauCeti.DynkinType
