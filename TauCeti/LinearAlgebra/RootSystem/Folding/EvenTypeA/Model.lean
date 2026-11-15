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

In rank `2 * n`, the diagram reversal `typeAZeroSumRevAut K (2 * n)` of the classical sum-zero
realization `typeAZeroSumRootPairing K (2 * n)` exchanges the two adjacent middle simple roots
`αₙ₋₁ = eₙ₋₁ - eₙ` and `αₙ = eₙ - eₙ₊₁`. This file develops the explicit coordinate model of the
resulting fold on `singleParityCheckCode K (Fin (2 * n + 1))` and identifies it with the
`K`-base-changed type-`Bₙ` root system `typeBBaseChangeRootSystem K n` on `Fin n → K`:

* The vectors `fᵢ = eᵢ - e₂ₙ₋ᵢ` (`0 ≤ i < n`) form a `K`-basis (`evenTypeAFixedBasis`) of the
  fixed hyperplane `LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap`.
* Each short root `fᵢ` lifts both to the fixed positive root `eᵢ - e₂ₙ₋ᵢ` of orbit size `1`
  (`evenTypeAFixedShortLift`) and to the positive middle root `eᵢ - eₙ` of orbit size `2`
  (`evenTypeAPairedShortLift`), while `2 • fᵢ` is never an orbit sum
  (`two_smul_evenTypeABasisVec_notMem_foldedIndices`).
* The linear equivalence `evenTypeAFixedCoordEquiv K n` sends a fixed vector `x` to its
  fundamental-weight coordinates `k ↦ (if k + 1 = n then 2 else 1) * ⟨αₖ^∨, x⟩` in `Fin n → K`,
  carrying the folded root set bijectively onto `Set.range (typeBBaseChangeRootSystem K n).root` and
  carrying the `k`-th simple orbit sum to the `k`-th Bourbaki simple root of `Bₙ`.

## Main definitions

* `TauCeti.DynkinType.evenTypeALeftIdx` and `TauCeti.DynkinType.evenTypeAMidIdx`: the left indices
  `i < n` and reversal-fixed middle index `n` inside `Fin (2 * n + 1)`.
* `TauCeti.DynkinType.evenTypeABasisVec` and `TauCeti.DynkinType.evenTypeAFixedBasis`: the vectors
  `fᵢ = eᵢ - e₂ₙ₋ᵢ` and the basis they form of the reversal-fixed subspace of `A₂ₙ`.
* `TauCeti.DynkinType.evenTypeAFixedShortLift` and `TauCeti.DynkinType.evenTypeAPairedShortLift`:
  explicit positive root pairs of orbit sizes `1` and `2` summing to `fᵢ`.
* `TauCeti.DynkinType.typeBBaseChangeRootSystem` and `TauCeti.DynkinType.typeBBaseChangeBase`: the
  `K`-base-changed root system and base of type `Bₙ`.
* `TauCeti.DynkinType.evenTypeAFixedCoordEquiv`: the fundamental-weight coordinate equivalence from
  the reversal-fixed subspace of `A₂ₙ` to `Fin n → K`.

## Main results

* `TauCeti.DynkinType.orbitIndices_typeAZeroSumRevAut` and
  `TauCeti.DynkinType.orbitSum_typeAZeroSumRevAut_simplePair`: explicit root orbits and simple
  orbit sums of `typeAZeroSumRevAut`.
* `TauCeti.DynkinType.evenTypeAFixedShortLift_spec`,
  `TauCeti.DynkinType.evenTypeAPairedShortLift_spec`, and
  `TauCeti.DynkinType.two_smul_evenTypeABasisVec_notMem_foldedIndices`: short-root lifts of sizes
  `1` and `2`, and absence of doubled short roots.
* `TauCeti.DynkinType.mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices` and
  `TauCeti.DynkinType.evenTypeAFixedCoordEquiv_simpleOrbitSum`: bijection between `A₂ₙ` orbit sums
  and `Bₙ` roots, matching Bourbaki simple roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--II.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace TauCeti.DynkinType

open Finset Function Submodule

/-! ### Classical `A₂ₙ` fixed basis, folding atoms, and orbit sums -/

/-- The `i`-th left coordinate index `i < n` inside `Fin (2 * n + 1)`. -/
def evenTypeALeftIdx (n : ℕ) (i : Fin n) : Fin (2 * n + 1) :=
  ⟨i, by have := i.isLt; omega⟩

/-- The middle coordinate index `n` inside `Fin (2 * n + 1)`, fixed by `Fin.rev`. -/
def evenTypeAMidIdx (n : ℕ) : Fin (2 * n + 1) :=
  ⟨n, by omega⟩

/-- Coercing `evenTypeALeftIdx n i` to `ℕ` gives `i`. -/
@[simp]
theorem val_evenTypeALeftIdx (n : ℕ) (i : Fin n) : (evenTypeALeftIdx n i : ℕ) = i :=
  (rfl)

/-- Coercing `evenTypeAMidIdx n` to `ℕ` gives `n`. -/
@[simp]
theorem val_evenTypeAMidIdx (n : ℕ) : (evenTypeAMidIdx n : ℕ) = n :=
  (rfl)

/-- Reversing `evenTypeAMidIdx n` fixes it. -/
@[simp]
theorem rev_evenTypeAMidIdx (n : ℕ) : (evenTypeAMidIdx n).rev = evenTypeAMidIdx n := by
  ext
  rw [Fin.val_rev, val_evenTypeAMidIdx]
  omega

/-- Coercing `(evenTypeALeftIdx n i).rev` to `ℕ` gives `2 * n - i`. -/
theorem val_rev_evenTypeALeftIdx (n : ℕ) (i : Fin n) :
    ((evenTypeALeftIdx n i).rev : ℕ) = 2 * n - i := by
  have := i.isLt
  rw [Fin.val_rev, val_evenTypeALeftIdx]
  omega

/-- `a : Fin (2 * n + 1)` is fixed by `Fin.rev` if and only if `a = evenTypeAMidIdx n`. -/
theorem rev_eq_self_iff_eq_evenTypeAMidIdx {n : ℕ} {a : Fin (2 * n + 1)} :
    a.rev = a ↔ a = evenTypeAMidIdx n := by
  have := a.isLt
  simp only [Fin.ext_iff, Fin.val_rev, val_evenTypeAMidIdx]
  omega

/-- The `i`-th basis vector `fᵢ = eᵢ - e₂ₙ₋ᵢ` of the reversal-fixed subspace in
`singleParityCheckCode R (Fin (2 * n + 1))`. -/
def evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    singleParityCheckCode R (Fin (2 * n + 1)) :=
  typeAZeroSumVec R (evenTypeALeftIdx n i) (evenTypeALeftIdx n i).rev

/-- `evenTypeABasisVec` is fixed by `typeAZeroSumRevEquiv`. -/
@[simp]
theorem typeAZeroSumRevEquiv_evenTypeABasisVec (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    typeAZeroSumRevEquiv R (2 * n) (evenTypeABasisVec R n i) = evenTypeABasisVec R n i := by
  rw [evenTypeABasisVec, typeAZeroSumRevEquiv_vec, Fin.rev_rev]

/-- Evaluating `evenTypeABasisVec R n i` at a left index `evenTypeALeftIdx n j` gives `[i = j]`. -/
@[simp]
theorem evenTypeABasisVec_apply_left (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) (evenTypeALeftIdx n j) =
      if i = j then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  rw [evenTypeABasisVec, typeAZeroSumVec_apply]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- Evaluating `evenTypeABasisVec R n i` at the middle index `n` gives `0`. -/
@[simp]
theorem evenTypeABasisVec_apply_mid (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) (evenTypeAMidIdx n) = 0 := by
  have hi := i.isLt
  rw [evenTypeABasisVec, typeAZeroSumVec_apply]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx, val_evenTypeAMidIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- The vectors `evenTypeABasisVec R n i` are pairwise orthogonal of squared length `2`. -/
theorem evenTypeABasisVec_dotProduct (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) ⬝ᵥ
        (evenTypeABasisVec R n j : Fin (2 * n + 1) → R) =
      if i = j then 2 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  rw [evenTypeABasisVec, evenTypeABasisVec, typeAZeroSumVec_dotProduct]
  simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

/-- The folding atom `ψ(a) = eₐ - e_{rev a}` in `singleParityCheckCode R (Fin (2 * n + 1))`. -/
private def evenTypeAFoldAtom (R : Type*) [CommRing R] (n : ℕ) (a : Fin (2 * n + 1)) :
    singleParityCheckCode R (Fin (2 * n + 1)) :=
  typeAZeroSumVec R a a.rev

private lemma evenTypeAFoldAtom_rev (R : Type*) [CommRing R] (n : ℕ) (a : Fin (2 * n + 1)) :
    evenTypeAFoldAtom R n a.rev = -evenTypeAFoldAtom R n a := by
  rw [evenTypeAFoldAtom, Fin.rev_rev, evenTypeAFoldAtom, neg_typeAZeroSumVec]

private lemma evenTypeAFoldAtom_mid (R : Type*) [CommRing R] (n : ℕ) :
    evenTypeAFoldAtom R n (evenTypeAMidIdx n) = 0 := by
  rw [evenTypeAFoldAtom, rev_evenTypeAMidIdx, typeAZeroSumVec_self]

private lemma evenTypeAFoldAtom_left (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    evenTypeAFoldAtom R n (evenTypeALeftIdx n i) = evenTypeABasisVec R n i :=
  rfl

private lemma add_rev_typeAZeroSumVec (R : Type*) [CommRing R] (n : ℕ) (a b : Fin (2 * n + 1)) :
    typeAZeroSumVec R a b + typeAZeroSumVec R b.rev a.rev =
      evenTypeAFoldAtom R n a - evenTypeAFoldAtom R n b := by
  ext k
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    evenTypeAFoldAtom, typeAZeroSumVec_apply]
  ring

private lemma evenTypeAFoldAtom_dotProduct_basisVec (R : Type*) [CommRing R] (n : ℕ)
    (a : Fin (2 * n + 1)) (i : Fin n) :
    (evenTypeAFoldAtom R n a : Fin (2 * n + 1) → R) ⬝ᵥ
        (evenTypeABasisVec R n i : Fin (2 * n + 1) → R) =
      if a = evenTypeALeftIdx n i then 2
      else if a = (evenTypeALeftIdx n i).rev then -2 else 0 := by
  have ha := a.isLt
  have hi := i.isLt
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
  rw [coe_typeAZeroSumRevEquiv_apply, neg_eq_iff_eq_neg] at ha
  exact ha

private lemma fixedSubmodule_revAut_apply_mid {n : ℕ}
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
      (evenTypeAMidIdx n) = 0 := by
  have h := fixedSubmodule_revAut_apply_rev K x (evenTypeAMidIdx n)
  rw [rev_evenTypeAMidIdx] at h
  have h2 : (2 : K) *
      ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
        (evenTypeAMidIdx n) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Linear equivalence identifying the reversal-fixed subspace of `A₂ₙ` with `Fin n → K` by reading
the first `n` coordinates. -/
private noncomputable def evenTypeAFixedLeftEquiv (n : ℕ) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap ≃ₗ[K] (Fin n → K) where
  toFun x i := ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
    (evenTypeALeftIdx n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨∑ i : Fin n, y i • evenTypeABasisVec K n i,
    sum_mem fun i _ ↦ Submodule.smul_mem _ _ (evenTypeABasisVec_mem_fixedSubmodule K n i)⟩
  right_inv y := by
    ext j
    simp [evenTypeABasisVec_apply_left]
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    ext a
    have hsum : (((∑ i : Fin n,
          ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
            (evenTypeALeftIdx n i) • evenTypeABasisVec K n i :
          singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) a) =
        ∑ i : Fin n, ((x : singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K)
          (evenTypeALeftIdx n i) * (evenTypeABasisVec K n i : Fin (2 * n + 1) → K) a := by
      simp
    dsimp only
    rw [hsum]
    rcases lt_trichotomy (a : ℕ) n with hlt | heq | hgt
    · have ha : a = evenTypeALeftIdx n ⟨a, hlt⟩ := rfl
      rw [ha]
      simp [evenTypeABasisVec_apply_left]
    · have ha : a = evenTypeAMidIdx n := Fin.ext heq
      rw [ha, fixedSubmodule_revAut_apply_mid]
      simp [evenTypeABasisVec_apply_mid]
    · have hjlt : 2 * n - (a : ℕ) < n := by have := a.isLt; omega
      let j : Fin n := ⟨2 * n - a, hjlt⟩
      have ha : a = (evenTypeALeftIdx n j).rev :=
        Fin.ext (by rw [val_rev_evenTypeALeftIdx]; dsimp [j]; have := a.isLt; omega)
      rw [ha, fixedSubmodule_revAut_apply_rev]
      have hval : ∀ i : Fin n,
          (evenTypeABasisVec K n i : Fin (2 * n + 1) → K) (evenTypeALeftIdx n j).rev =
            -(if i = j then (1 : K) else 0) := by
        intro i
        have := i.isLt
        rw [evenTypeABasisVec, typeAZeroSumVec_apply]
        simp only [Fin.ext_iff, val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
        split_ifs <;> first | (norm_num; done) | (exfalso; omega)
      simp [hval]

/-- The vectors `fᵢ = eᵢ - e₂ₙ₋ᵢ` (`i : Fin n`) form a `K`-basis of the fixed subspace of
`typeAZeroSumRevAut K (2 * n)`. -/
noncomputable def evenTypeAFixedBasis (n : ℕ) :
    Module.Basis (Fin n) K (LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :=
  Module.Basis.ofRepr
    ((evenTypeAFixedLeftEquiv K n).trans (Finsupp.linearEquivFunOnFinite K K (Fin n)).symm)

/-- The `i`-th vector of `evenTypeAFixedBasis K n` coerces to `evenTypeABasisVec K n i`. -/
@[simp]
theorem coe_evenTypeAFixedBasis_apply (n : ℕ) (i : Fin n) :
    (evenTypeAFixedBasis K n i : singleParityCheckCode K (Fin (2 * n + 1))) =
      evenTypeABasisVec K n i := by
  rw [evenTypeAFixedBasis, Module.Basis.coe_ofRepr]
  dsimp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    evenTypeAFixedLeftEquiv, LinearEquiv.coe_mk]
  simp

/-- The root orbit of `p : TypeAIndex m` under `typeAZeroSumRevAut K m` is the pair
`{p, finDistinctPairsRevSwap (m + 1) p}` (which collapses to `{p}` when `p` is fixed). -/
theorem orbitIndices_typeAZeroSumRevAut (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).orbitIndices (typeAZeroSumRevAut K m) p =
      {p, finDistinctPairsRevSwap (m + 1) p} := by
  have hpow : ∀ k : ℕ,
      (finDistinctPairsRevSwap (m + 1) ^ k) p = p ∨
        (finDistinctPairsRevSwap (m + 1) ^ k) p = finDistinctPairsRevSwap (m + 1) p := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · rw [h]
        exact Or.inr rfl
      · rw [h, finDistinctPairsRevSwap_finDistinctPairsRevSwap]
        exact Or.inl rfl
  ext q
  rw [RootPairing.mem_orbitIndices_iff_exists_pow, indexEquiv_typeAZeroSumRevAut,
    mem_insert, mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨k, rfl⟩
    exact hpow k
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, by simp⟩

/-- A root pair `p : TypeAIndex m` is fixed by `finDistinctPairsRevSwap (m + 1)` if and only if
`p.val.2 = p.val.1.rev`. -/
theorem finDistinctPairsRevSwap_eq_self_iff {m : ℕ} {p : TypeAIndex m} :
    finDistinctPairsRevSwap (m + 1) p = p ↔ p.val.2 = p.val.1.rev := by
  rw [Subtype.ext_iff, finDistinctPairsRevSwap_apply_val, Prod.ext_iff, Fin.rev_eq_iff,
    eq_comm (a := p.val.1.rev), and_self]

/-- Explicit formula for the orbit sum of `p : TypeAIndex (2 * n)` under `typeAZeroSumRevAut`:
`e_{p.1} - e_{rev p.1}` when `p.2 = rev p.1`, and
`(e_{p.1} - e_{rev p.1}) - (e_{p.2} - e_{rev p.2})` otherwise. -/
private lemma orbitSum_typeAZeroSumRevAut_eq (n : ℕ) (p : TypeAIndex (2 * n)) :
    (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p =
      if p.val.2 = p.val.1.rev then evenTypeAFoldAtom K n p.val.1
      else evenTypeAFoldAtom K n p.val.1 - evenTypeAFoldAtom K n p.val.2 := by
  rw [RootPairing.orbitSum_def, orbitIndices_typeAZeroSumRevAut]
  by_cases hfix : p.val.2 = p.val.1.rev
  · have hp : finDistinctPairsRevSwap (2 * n + 1) p = p :=
      finDistinctPairsRevSwap_eq_self_iff.mpr hfix
    rw [ite_eq_left hfix, hp, pair_eq_singleton, sum_singleton, root_typeAZeroSumRootPairing, hfix,
      evenTypeAFoldAtom]
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
  have hs1 : s.val.1 = evenTypeALeftIdx n k :=
    (congrArg Prod.fst hs_val).trans rfl
  have hs2_val : (s.val.2 : ℕ) = (k : ℕ) + 1 :=
    congrArg (fun x : Fin (2 * n + 1) ↦ (x : ℕ)) (congrArg Prod.snd hs_val)
  have hne : s.val.2 ≠ s.val.1.rev := by
    intro hc
    have hval := congrArg Fin.val hc
    rw [hs2_val, hs1, val_rev_evenTypeALeftIdx] at hval
    omega
  -- Fold the explicit simple pair into `s` so `hs1` and `hs2_val` rewrite directly.
  change (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) s = _
  rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, hs1, evenTypeAFoldAtom_left]
  by_cases hlt : (k : ℕ) + 1 < n
  · have hs2 : s.val.2 = evenTypeALeftIdx n ⟨(k : ℕ) + 1, hlt⟩ := Fin.ext hs2_val
    rw [dite_eq_left hlt, hs2, evenTypeAFoldAtom_left]
  · have hs2 : s.val.2 = evenTypeAMidIdx n := Fin.ext (by rw [hs2_val, val_evenTypeAMidIdx]; omega)
    rw [dite_eq_right hlt, hs2, evenTypeAFoldAtom_mid, sub_zero]

/-- The fixed positive root pair `(i, 2 * n - i)` lifting the `i`-th short root `fᵢ`. -/
def evenTypeAFixedShortLift (n : ℕ) (i : Fin n) : TypeAIndex (2 * n) :=
  ⟨(evenTypeALeftIdx n i, (evenTypeALeftIdx n i).rev), by
    have := i.isLt; simp [Fin.ext_iff]; omega⟩

/-- Underlying pair of `evenTypeAFixedShortLift n i`. -/
@[simp]
theorem evenTypeAFixedShortLift_val (n : ℕ) (i : Fin n) :
    (evenTypeAFixedShortLift n i).val = (evenTypeALeftIdx n i, (evenTypeALeftIdx n i).rev) :=
  (rfl)

/-- The middle positive pair `(i, n)` whose size-`2` orbit sums to the `i`-th short root `fᵢ`. -/
def evenTypeAPairedShortLift (n : ℕ) (i : Fin n) : TypeAIndex (2 * n) :=
  ⟨(evenTypeALeftIdx n i, evenTypeAMidIdx n), by
    have := i.isLt; simp [Fin.ext_iff]; omega⟩

/-- Underlying pair of `evenTypeAPairedShortLift n i`. -/
@[simp]
theorem evenTypeAPairedShortLift_val (n : ℕ) (i : Fin n) :
    (evenTypeAPairedShortLift n i).val = (evenTypeALeftIdx n i, evenTypeAMidIdx n) :=
  (rfl)

/-- `evenTypeAFixedShortLift n i` is positive, has orbit size `1`, and has orbit sum `fᵢ`. -/
theorem evenTypeAFixedShortLift_spec (n : ℕ) (i : Fin n) :
    (typeAZeroSumBase K (2 * n)).IsPos (evenTypeAFixedShortLift n i) ∧
      #((typeAZeroSumRootPairing K (2 * n)).orbitIndices (typeAZeroSumRevAut K (2 * n))
        (evenTypeAFixedShortLift n i)) = 1 ∧
      (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (evenTypeAFixedShortLift n i) = evenTypeABasisVec K n i := by
  have hi := i.isLt
  have hfix : (evenTypeAFixedShortLift n i).val.2 = (evenTypeAFixedShortLift n i).val.1.rev := by
    rw [evenTypeAFixedShortLift_val]
  refine ⟨?_, ?_, ?_⟩
  · rw [isPos_typeAZeroSumBase_iff, evenTypeAFixedShortLift_val, Fin.lt_def,
      val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx]
    omega
  · rw [orbitIndices_typeAZeroSumRevAut,
      finDistinctPairsRevSwap_eq_self_iff.mpr hfix, pair_eq_singleton, card_singleton]
  · rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_left hfix, evenTypeAFixedShortLift_val,
      evenTypeAFoldAtom_left]

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
    simp only [ne_eq, Fin.ext_iff, val_evenTypeAMidIdx, val_rev_evenTypeALeftIdx]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [isPos_typeAZeroSumBase_iff, evenTypeAPairedShortLift_val, Fin.lt_def,
      val_evenTypeALeftIdx, val_evenTypeAMidIdx]
    exact hi
  · rw [orbitIndices_typeAZeroSumRevAut]
    exact card_pair fun hc ↦ hne (finDistinctPairsRevSwap_eq_self_iff.mp hc.symm)
  · rw [orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hne, evenTypeAPairedShortLift_val,
      evenTypeAFoldAtom_left, evenTypeAFoldAtom_mid, sub_zero]

/-- Twice a short root `2 • fᵢ` is never an orbit sum of `typeAZeroSumRevAut K (2 * n)`. -/
theorem two_smul_evenTypeABasisVec_notMem_foldedIndices (n : ℕ) (i : Fin n) :
    (2 : K) • evenTypeABasisVec K n i ∉
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  rw [RootPairing.mem_foldedIndices]
  rintro ⟨p, hp⟩
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

/-! ### Base-changed type-`Bₙ` system and coordinate identification -/

/-- The root system of type `Bₙ` on `Fin n → K` obtained by entrywise base change from
`typeBSimplyConnectedRootDatum n`. -/
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
    (typeBBaseChangeRootSystem K n).IsReduced :=
  isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeBBaseChangeRootSystem K n`
span `Fin n → K`. -/
instance instIsRootSystemTypeBBaseChangeRootSystem (n : ℕ) :
    (typeBBaseChangeRootSystem K n).IsRootSystem where
  span_root_eq_top := by
    have hli : LinearIndependent K fun i : (typeBBaseChangeBase K n).support ↦
        (typeBBaseChangeRootSystem K n).root i := (typeBBaseChangeBase K n).linearIndepOn_root
    have hcard : Fintype.card (typeBBaseChangeBase K n).support =
        Module.finrank K (Fin n → K) := by
      rw [Fintype.card_coe, Module.finrank_fin_fun, typeBBaseChangeBase,
        support_rootPairingBaseChangeBase,
        (hasCartanType_typeBSimplyConnectedRootDatum n).card_support, DynkinType.rank_B]
    refine top_le_iff.mp ?_
    rw [← hli.span_eq_top_of_card_eq_finrank' hcard]
    exact Submodule.span_mono
      (by rintro - ⟨i, rfl⟩; exact Set.mem_range_self (i : Fin (2 * n ^ 2)))
  span_coroot_eq_top :=
    span_range_coroot_rootPairingBaseChange_eq_top K _ _
      (corootSpan_typeBSimplyConnectedRootDatum_eq_top n)

/-- `typeBBaseChangeBase K n` has Cartan type `B n`. -/
theorem hasCartanType_typeBBaseChangeBase (n : ℕ) :
    HasCartanType (typeBBaseChangeRootSystem K n) (typeBBaseChangeBase K n) (.B n) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).mp (hasCartanType_typeBSimplyConnectedRootDatum n)
  refine (hasCartanType_iff _ _).mpr
    ⟨(supportEquivRootPairingBaseChangeBase K _ _ _).trans e, fun i j ↦ ?_⟩
  exact (cartanMatrix_rootPairingBaseChangeBase K _ _ _ i j).trans (he _ _)

/-- The bilinear pairing of `typeBBaseChangeRootSystem K n` is `dotProduct`. -/
@[simp]
theorem toLinearMap_typeBBaseChangeRootSystem (n : ℕ) (x y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).toLinearMap x y = x ⬝ᵥ y :=
  toLinearMap_rootPairingBaseChange K (typeBSimplyConnectedRootDatum n) _ x y

/-- An index `m : Fin (2 * n ^ 2)` belongs to `(typeBBaseChangeBase K n).support` if and only if
`(m : ℕ) < n`. -/
@[simp]
theorem mem_support_typeBBaseChangeBase_iff (n : ℕ) (m : Fin (2 * n ^ 2)) :
    m ∈ (typeBBaseChangeBase K n).support ↔ (m : ℕ) < n := by
  rw [typeBBaseChangeBase, support_rootPairingBaseChangeBase, mem_typeBSimplyConnectedBase_support]

/-- Evaluating the `k`-th simple coroot of `typeBBaseChangeRootSystem K n` on `y : Fin n → K` reads
its `k`-th coordinate `y k`. -/
theorem coroot'_typeBBaseChangeRootSystem_simpleIndex (n : ℕ) (k : Fin n) (y : Fin n → K) :
    (typeBBaseChangeRootSystem K n).coroot' (typeBSimpleIndex n k) y = y k := by
  rw [RootPairing.coroot', LinearMap.flip_apply, typeBBaseChangeRootSystem,
    toLinearMap_rootPairingBaseChange, coroot_rootPairingBaseChange, coroot_typeBSimpleIndex]
  have hsingle : Pi.algebraMap (Fin n) ℤ K (Pi.single k 1) = Pi.single k (1 : K) := by
    ext j
    rcases eq_or_ne j k with rfl | hjk <;> simp [piAlgebraMap_apply, *]
  rw [hsingle, dotProduct_single, mul_one]

/-- Change-of-basis map on `Fin n → K` from classical basis coordinates `y` to type-`Bₙ`
fundamental-weight coordinates `k ↦ (y_k - y_{k+1})` (`k + 1 < n`), `n - 1 ↦ 2 * y_{n-1}`. -/
private def typeBFundamentalCoordMap (n : ℕ) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun y k := if h : (k : ℕ) + 1 < n then y k - y ⟨(k : ℕ) + 1, h⟩ else 2 * y k
  map_add' y₁ y₂ := funext fun k ↦ by simp; split_ifs <;> ring
  map_smul' c y := funext fun k ↦ by simp; split_ifs <;> ring

private lemma typeBFundamentalCoordMap_injective (n : ℕ) :
    Injective (typeBFundamentalCoordMap K n) := by
  intro y₁ y₂ hy₁₂
  suffices hsub : y₁ - y₂ = 0 from sub_eq_zero.mp hsub
  have hy : typeBFundamentalCoordMap K n (y₁ - y₂) = 0 := by rw [map_sub, hy₁₂, sub_self]
  set y := y₁ - y₂
  have hzero : ∀ d : ℕ, (hd0 : 0 < d) → (hd : d ≤ n) → y ⟨n - d, by omega⟩ = 0 := by
    intro d
    induction d with
    | zero => intro hd0; omega
    | succ d ih =>
      intro _ hd
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · have hk := congrFun hy ⟨n - 1, by omega⟩
        dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hk
        rw [dite_eq_right (by omega)] at hk
        exact (mul_eq_zero.mp hk).resolve_left two_ne_zero
      · have hk := congrFun hy ⟨n - (d + 1), by omega⟩
        dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hk
        have hlt : (n - (d + 1)) + 1 < n := by omega
        rw [dite_eq_left hlt] at hk
        have hstep := sub_eq_zero.mp hk
        have heq : (⟨n - (d + 1) + 1, by omega⟩ : Fin n) = ⟨n - d, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [heq] at hstep
        exact hstep.trans (ih hdpos (by omega))
  ext i
  have hi := i.isLt
  have hid : i = ⟨n - (n - i), by omega⟩ := Fin.ext (by dsimp; omega)
  rw [hid, Pi.zero_apply]
  exact hzero (n - i) (by omega) (by omega)

private noncomputable def typeBFundamentalCoordEquiv (n : ℕ) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  have hinj := typeBFundamentalCoordMap_injective K n
  LinearEquiv.ofBijective (typeBFundamentalCoordMap K n)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

/-- Linear equivalence from the reversal-fixed subspace of `A₂ₙ` to the weight space `Fin n → K` of
`typeBBaseChangeRootSystem K n`, reading fundamental-weight coordinates. -/
noncomputable def evenTypeAFixedCoordEquiv (n : ℕ) :
    LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap ≃ₗ[K] (Fin n → K) :=
  (evenTypeAFixedLeftEquiv K n).trans (typeBFundamentalCoordEquiv K n)

/-- Coordinate formula for `evenTypeAFixedCoordEquiv K n`: the `k`-th coordinate scales the `k`-th
simple coroot pairing of `A₂ₙ` by `1` off the middle (`k + 1 < n`) and by `2` at the middle
(`k + 1 = n`). -/
theorem evenTypeAFixedCoordEquiv_apply (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) (k : Fin n) :
    evenTypeAFixedCoordEquiv K n x k =
      (if (k : ℕ) + 1 = n then (2 : K) else 1) *
        (typeAZeroSumRootPairing K (2 * n)).coroot'
          (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩) (x : _) := by
  have hk := k.isLt
  rw [coroot'_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val]
  -- Unfold `evenTypeAFixedCoordEquiv` to the `k`-th coordinate of `typeBFundamentalCoordMap`.
  change typeBFundamentalCoordMap K n (evenTypeAFixedLeftEquiv K n x) k = _
  dsimp only [typeBFundamentalCoordMap, LinearMap.coe_mk, AddHom.coe_mk,
    evenTypeAFixedLeftEquiv, LinearEquiv.coe_mk]
  by_cases hlt : (k : ℕ) + 1 < n
  · rw [dite_eq_left hlt, ite_eq_right (by omega), one_mul]
    rfl
  · have hlast : (k : ℕ) + 1 = n := by omega
    have hsucc : (⟨(k : ℕ), by omega⟩ : Fin (2 * n)).succ = evenTypeAMidIdx n :=
      Fin.ext (by rw [Fin.val_succ, val_evenTypeAMidIdx]; exact hlast)
    rw [dite_eq_right hlt, ite_eq_left hlast, hsucc, fixedSubmodule_revAut_apply_mid K x, sub_zero]
    rfl

private lemma evenTypeAFixedCoordEquiv_neg (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    evenTypeAFixedCoordEquiv K n (-x) = -evenTypeAFixedCoordEquiv K n x := by
  ext k
  rw [Pi.neg_apply, evenTypeAFixedCoordEquiv_apply, evenTypeAFixedCoordEquiv_apply,
    coroot'_typeAZeroSumRootPairing, coroot'_typeAZeroSumRootPairing]
  simp only [Submodule.coe_neg, Pi.neg_apply]
  ring

private lemma evenTypeAFixedCoordEquiv_sub (n : ℕ)
    (x y : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    evenTypeAFixedCoordEquiv K n (x - y) =
      evenTypeAFixedCoordEquiv K n x - evenTypeAFixedCoordEquiv K n y := by
  ext k
  rw [Pi.sub_apply, evenTypeAFixedCoordEquiv_apply, evenTypeAFixedCoordEquiv_apply,
    evenTypeAFixedCoordEquiv_apply, coroot'_typeAZeroSumRootPairing,
    coroot'_typeAZeroSumRootPairing, coroot'_typeAZeroSumRootPairing]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  ring

/-- `evenTypeAFixedCoordEquiv K n` sends the `i`-th fixed basis vector `fᵢ` to `TypeB.weight n i`.
-/
theorem evenTypeAFixedCoordEquiv_basisVec (n : ℕ) (i : Fin n) :
    evenTypeAFixedCoordEquiv K n
        ⟨evenTypeABasisVec K n i, evenTypeABasisVec_mem_fixedSubmodule K n i⟩ =
      Pi.algebraMap (Fin n) ℤ K (TypeB.weight n i) := by
  ext k
  have hi := i.isLt
  have hk := k.isLt
  rw [evenTypeAFixedCoordEquiv_apply, piAlgebraMap_apply, TypeB.weight_apply,
    coroot'_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val, algebraMap_int_eq, eq_intCast]
  push_cast
  simp only [evenTypeABasisVec, typeAZeroSumVec_apply, Fin.ext_iff,
    val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (ring; done) | (exfalso; omega)

/-- Bijection between signed basis indices `u : Fin (2 * n)` of type `Bₙ` and non-middle indices
`a ≠ evenTypeAMidIdx n` in `Fin (2 * n + 1)`. -/
private def evenTypeASignedIdx (n : ℕ) (u : Fin (2 * n)) : Fin (2 * n + 1) :=
  if h : (u : ℕ) < n then evenTypeALeftIdx n ⟨u, h⟩
  else (evenTypeALeftIdx n ⟨(u : ℕ) - n, by have := u.isLt; omega⟩).rev

private lemma evenTypeASignedIdx_ne_mid (n : ℕ) (u : Fin (2 * n)) :
    evenTypeASignedIdx n u ≠ evenTypeAMidIdx n := by
  have := u.isLt
  simp only [evenTypeASignedIdx, ne_eq, Fin.ext_iff, val_evenTypeAMidIdx]
  split_ifs with h
  · rw [val_evenTypeALeftIdx]; omega
  · rw [val_rev_evenTypeALeftIdx]; dsimp; omega

private lemma rev_evenTypeASignedIdx (n : ℕ) (u : Fin (2 * n)) :
    (evenTypeASignedIdx n u).rev = evenTypeASignedIdx n (TypeB.opp u) := by
  have := u.isLt
  ext
  simp only [evenTypeASignedIdx, TypeB.coe_opp, Fin.val_rev]
  split_ifs <;> simp only [val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx] <;> omega

private lemma evenTypeASignedIdx_injective (n : ℕ) : Injective (evenTypeASignedIdx n) := by
  intro u v huv
  have hu := u.isLt
  have hv := v.isLt
  have hval := congrArg Fin.val huv
  simp only [evenTypeASignedIdx] at hval
  split_ifs at hval with h1 h2 h2 <;>
    simp only [val_evenTypeALeftIdx, val_rev_evenTypeALeftIdx] at hval
  · exact Fin.ext hval
  · omega
  · omega
  · exact Fin.ext (by omega)

private lemma exists_evenTypeASignedIdx {n : ℕ} {a : Fin (2 * n + 1)}
    (ha : a ≠ evenTypeAMidIdx n) : ∃ u : Fin (2 * n), evenTypeASignedIdx n u = a := by
  have halt := a.isLt
  have hane : (a : ℕ) ≠ n := fun hc ↦ ha (Fin.ext hc)
  by_cases hlt : (a : ℕ) < n
  · refine ⟨⟨a, by omega⟩, ?_⟩
    rw [evenTypeASignedIdx, dite_eq_left hlt]
    rfl
  · refine ⟨⟨n + (2 * n - a), by omega⟩, ?_⟩
    have hnlt : ¬ (n + (2 * n - (a : ℕ)) < n) := by omega
    rw [evenTypeASignedIdx, dite_eq_right hnlt]
    ext
    rw [val_rev_evenTypeALeftIdx]
    dsimp
    omega

private lemma evenTypeAFoldAtom_mem_fixedSubmodule (n : ℕ) (a : Fin (2 * n + 1)) :
    evenTypeAFoldAtom K n a ∈
      LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
    evenTypeAFoldAtom, typeAZeroSumRevEquiv_vec, Fin.rev_rev]

private lemma evenTypeAFixedCoordEquiv_signedIdx (n : ℕ) (u : Fin (2 * n)) :
    evenTypeAFixedCoordEquiv K n
        ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
          evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ =
      Pi.algebraMap (Fin n) ℤ K (TypeB.signedWeight u) := by
  have hu := u.isLt
  by_cases hlt : (u : ℕ) < n
  · have hs : TypeB.signedWeight u = TypeB.weight n u := by
      rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_left hlt, ite_eq_left hlt,
        one_smul]
    simp only [evenTypeASignedIdx, dite_eq_left hlt, evenTypeAFoldAtom_left, hs]
    exact evenTypeAFixedCoordEquiv_basisVec K n ⟨u, hlt⟩
  · have hs : TypeB.signedWeight u = -TypeB.weight n ((u : ℕ) - n) := by
      rw [TypeB.signedWeight_def, TypeB.sgn_def, TypeB.axis_def, ite_eq_right hlt,
        ite_eq_right hlt, neg_one_smul]
    have hatom : (⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
        evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ :
        LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
      -⟨evenTypeABasisVec K n ⟨(u : ℕ) - n, by omega⟩,
        evenTypeABasisVec_mem_fixedSubmodule K n _⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_neg]
      dsimp only
      rw [evenTypeASignedIdx, dite_eq_right hlt, evenTypeAFoldAtom_rev, evenTypeAFoldAtom_left]
    rw [hatom, evenTypeAFixedCoordEquiv_neg, hs, map_neg]
    exact congrArg Neg.neg (evenTypeAFixedCoordEquiv_basisVec K n ⟨(u : ℕ) - n, by omega⟩)

private lemma mem_foldedIndices_of_mem_range_typeB {n : ℕ}
    {x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap}
    (hx : evenTypeAFixedCoordEquiv K n x ∈ Set.range (typeBBaseChangeRootSystem K n).root) :
    (x : singleParityCheckCode K (Fin (2 * n + 1))) ∈
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  rw [RootPairing.mem_foldedIndices]
  obtain ⟨u, v, huv, hroot⟩ : ∃ u v : Fin (2 * n),
      TypeB.IsPair u v ∧
        evenTypeAFixedCoordEquiv K n x = Pi.algebraMap (Fin n) ℤ K (TypeB.rootOfPair u v) := by
    obtain ⟨idx, hidx⟩ := hx
    rw [typeBBaseChangeRootSystem, root_rootPairingBaseChange] at hidx
    obtain ⟨u, v, huv, hr⟩ := mem_range_root_typeBSimplyConnectedRootDatum_iff.mp ⟨idx, rfl⟩
    exact ⟨u, v, huv, hidx.symm.trans (congrArg _ hr)⟩
  rcases eq_or_ne u v with rfl | hne
  · have hne_rev : evenTypeASignedIdx n u ≠ (evenTypeASignedIdx n u).rev :=
      fun hc ↦ evenTypeASignedIdx_ne_mid n u (rev_eq_self_iff_eq_evenTypeAMidIdx.mp hc.symm)
    refine ⟨⟨(evenTypeASignedIdx n u, (evenTypeASignedIdx n u).rev), hne_rev⟩, ?_⟩
    have hx' : x = ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
        evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
      apply (evenTypeAFixedCoordEquiv K n).injective
      rw [hroot, TypeB.rootOfPair_self, evenTypeAFixedCoordEquiv_signedIdx]
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_left rfl]
  · let a := evenTypeASignedIdx n u
    let b := (evenTypeASignedIdx n v).rev
    have hab : a ≠ b := by
      dsimp only [a, b]
      rw [rev_evenTypeASignedIdx]
      exact fun hc ↦ huv.ne_opp (evenTypeASignedIdx_injective n hc)
    have hnotfix : b ≠ a.rev :=
      fun hc ↦ hne (evenTypeASignedIdx_injective n (Fin.rev_inj.mp hc).symm)
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    have hx' : x = ⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
        sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
          (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ := by
      apply (evenTypeAFixedCoordEquiv K n).injective
      rw [hroot, TypeB.rootOfPair_of_ne hne, map_add]
      have hsub : (⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
          sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
            (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ :
          LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
        ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
          evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ +
        ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n v),
          evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
        apply Subtype.ext
        simp only [Submodule.coe_add, a, b, evenTypeAFoldAtom_rev, sub_neg_eq_add]
      rw [hsub, map_add, evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx]
    rw [hx', orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hnotfix]

private lemma evenTypeAFoldAtom_mem_range_typeB (n : ℕ) {a : Fin (2 * n + 1)}
    (ha : a ≠ evenTypeAMidIdx n) :
    evenTypeAFixedCoordEquiv K n ⟨evenTypeAFoldAtom K n a,
      evenTypeAFoldAtom_mem_fixedSubmodule K n a⟩ ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  obtain ⟨u, rfl⟩ := exists_evenTypeASignedIdx ha
  rw [evenTypeAFixedCoordEquiv_signedIdx, ← TypeB.rootOfPair_self, typeBBaseChangeRootSystem,
    piAlgebraMap_mem_range_root_rootPairingBaseChange_iff,
    mem_range_root_typeBSimplyConnectedRootDatum_iff]
  exact ⟨u, u, (TypeB.isPair_iff u u).mpr (Or.inl rfl), rfl⟩

private lemma evenTypeAFoldAtom_sub_mem_range_typeB (n : ℕ) {a b : Fin (2 * n + 1)}
    (hab : a ≠ b) (hnotfix : b ≠ a.rev) :
    evenTypeAFixedCoordEquiv K n
        ⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
          sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
            (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ ∈
      Set.range (typeBBaseChangeRootSystem K n).root := by
  by_cases ha : a = evenTypeAMidIdx n
  · have hb_rev : b.rev ≠ evenTypeAMidIdx n := fun hc ↦
      hab (ha.trans (by simpa [rev_evenTypeAMidIdx] using (congrArg Fin.rev hc).symm))
    have hval : (⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
        sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
          (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ :
        LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
      ⟨evenTypeAFoldAtom K n b.rev, evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
      apply Subtype.ext; dsimp only
      rw [ha, evenTypeAFoldAtom_mid, zero_sub, ← evenTypeAFoldAtom_rev]
    rw [hval]
    exact evenTypeAFoldAtom_mem_range_typeB K n hb_rev
  · by_cases hb : b = evenTypeAMidIdx n
    · have hval : (⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
          sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
            (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ :
          LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
        ⟨evenTypeAFoldAtom K n a, evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
        apply Subtype.ext; dsimp only; rw [hb, evenTypeAFoldAtom_mid, sub_zero]
      rw [hval]
      exact evenTypeAFoldAtom_mem_range_typeB K n ha
    · obtain ⟨u, hu⟩ := exists_evenTypeASignedIdx ha
      obtain ⟨v, hv⟩ := exists_evenTypeASignedIdx (a := b.rev)
        (fun hc ↦ hb (by simpa [rev_evenTypeAMidIdx] using congrArg Fin.rev hc))
      have huv_ne : u ≠ v := fun hc ↦ hnotfix (by
        have := hc ▸ hv; simpa [hu] using (congrArg Fin.rev this).symm)
      have huv_opp : u ≠ TypeB.opp v := fun hc ↦ hab (by
        rw [← hu, hc, ← rev_evenTypeASignedIdx, hv, Fin.rev_rev])
      have hp_pair : TypeB.IsPair u v :=
        (TypeB.isPair_iff u v).mpr (Or.inr fun hax ↦
          (TypeB.eq_or_eq_opp_of_axis_eq hax).elim huv_ne huv_opp)
      have hval : (⟨evenTypeAFoldAtom K n a - evenTypeAFoldAtom K n b,
          sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n a)
            (evenTypeAFoldAtom_mem_fixedSubmodule K n b)⟩ :
          LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
        ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
          evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ +
        ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n v),
          evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
        apply Subtype.ext; rw [Submodule.coe_add]; dsimp only
        rw [hu, hv, evenTypeAFoldAtom_rev, sub_eq_add_neg]
      rw [hval, map_add, evenTypeAFixedCoordEquiv_signedIdx, evenTypeAFixedCoordEquiv_signedIdx,
        ← map_add, ← TypeB.rootOfPair_of_ne huv_ne, typeBBaseChangeRootSystem,
        piAlgebraMap_mem_range_root_rootPairingBaseChange_iff,
        mem_range_root_typeBSimplyConnectedRootDatum_iff]
      exact ⟨u, v, hp_pair, rfl⟩

/-- `evenTypeAFixedCoordEquiv K n` maps the folded roots of `typeAZeroSumRootPairing K (2 * n)`
bijectively onto the roots of `typeBBaseChangeRootSystem K n`. -/
theorem mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices (n : ℕ)
    (x : LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) :
    evenTypeAFixedCoordEquiv K n x ∈ Set.range (typeBBaseChangeRootSystem K n).root ↔
      (x : singleParityCheckCode K (Fin (2 * n + 1))) ∈
        (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
  refine ⟨mem_foldedIndices_of_mem_range_typeB K, fun hx ↦ ?_⟩
  rw [RootPairing.mem_foldedIndices] at hx
  obtain ⟨p, hp⟩ := hx
  by_cases hfix : p.val.2 = p.val.1.rev
  · have ha : p.val.1 ≠ evenTypeAMidIdx n :=
      fun hc ↦ p.2 (by rw [hfix, hc, rev_evenTypeAMidIdx])
    obtain ⟨u, hu⟩ := exists_evenTypeASignedIdx ha
    have hx_eq : x = ⟨evenTypeAFoldAtom K n (evenTypeASignedIdx n u),
        evenTypeAFoldAtom_mem_fixedSubmodule K n _⟩ := by
      apply Subtype.ext
      rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_left hfix, hu]
    rw [hx_eq, evenTypeAFixedCoordEquiv_signedIdx, ← TypeB.rootOfPair_self,
      typeBBaseChangeRootSystem, piAlgebraMap_mem_range_root_rootPairingBaseChange_iff,
      mem_range_root_typeBSimplyConnectedRootDatum_iff]
    exact ⟨u, u, (TypeB.isPair_iff u u).mpr (Or.inl rfl), rfl⟩
  · have hx_eq : x = ⟨evenTypeAFoldAtom K n p.val.1 - evenTypeAFoldAtom K n p.val.2,
        sub_mem (evenTypeAFoldAtom_mem_fixedSubmodule K n p.val.1)
          (evenTypeAFoldAtom_mem_fixedSubmodule K n p.val.2)⟩ := by
      apply Subtype.ext
      rw [← hp, orbitSum_typeAZeroSumRevAut_eq, ite_eq_right hfix]
    rw [hx_eq]
    exact evenTypeAFoldAtom_sub_mem_range_typeB K n p.2 hfix

/-- `evenTypeAFixedCoordEquiv K n` sends the orbit sum of the `k`-th simple root (`k < n`) of
`A₂ₙ` to the `k`-th Bourbaki simple root of `typeBBaseChangeRootSystem K n`. -/
theorem evenTypeAFixedCoordEquiv_simpleOrbitSum (n : ℕ) (k : Fin n) :
    evenTypeAFixedCoordEquiv K n
        ⟨(typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
          (typeAZeroSumSimplePair (2 * n) ⟨k, by have := k.isLt; omega⟩),
          RootPairing.orbitSum_mem_fixedSubmodule _ _ _⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
  have hk := k.isLt
  have hrhs : (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) =
      Pi.algebraMap (Fin n) ℤ K (TypeB.weight n k - TypeB.weight n ((k : ℕ) + 1)) := by
    ext j
    have hj := j.isLt
    rw [typeBBaseChangeRootSystem, root_rootPairingBaseChange, piAlgebraMap_apply,
      piAlgebraMap_apply, root_typeBSimpleIndex]
    congr 1
    simp only [CartanMatrix.B, Matrix.of_apply, Pi.sub_apply, TypeB.weight_apply, Fin.ext_iff]
    split_ifs <;> omega
  rw [hrhs]
  by_cases hlt : (k : ℕ) + 1 < n
  · have hsub : (⟨(typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩),
        RootPairing.orbitSum_mem_fixedSubmodule _ _ _⟩ :
        LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
      ⟨evenTypeABasisVec K n k, evenTypeABasisVec_mem_fixedSubmodule K n k⟩ -
      ⟨evenTypeABasisVec K n ⟨(k : ℕ) + 1, hlt⟩,
        evenTypeABasisVec_mem_fixedSubmodule K n ⟨(k : ℕ) + 1, hlt⟩⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sub]
      dsimp only
      rw [orbitSum_typeAZeroSumRevAut_simplePair, dite_eq_left hlt]
    rw [hsub, evenTypeAFixedCoordEquiv_sub, evenTypeAFixedCoordEquiv_basisVec,
      evenTypeAFixedCoordEquiv_basisVec, ← map_sub]
  · have hlast : (k : ℕ) + 1 = n := by omega
    have hsub : (⟨(typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n))
        (typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩),
        RootPairing.orbitSum_mem_fixedSubmodule _ _ _⟩ :
        LinearMap.fixedSubmodule (typeAZeroSumRevAut K (2 * n)).weightMap) =
      ⟨evenTypeABasisVec K n k, evenTypeABasisVec_mem_fixedSubmodule K n k⟩ := by
      apply Subtype.ext
      dsimp only
      rw [orbitSum_typeAZeroSumRevAut_simplePair, dite_eq_right hlt]
    rw [hsub, evenTypeAFixedCoordEquiv_basisVec, TypeB.weight_eq_zero_of_le (le_of_eq hlast.symm),
      sub_zero]

end Field

end TauCeti.DynkinType
