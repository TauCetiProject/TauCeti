/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Folding.EvenTypeA.Model
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Folding even type-`A` root systems under diagram reversal

Let `P` be a finite reduced crystallographic root system of Cartan type `A (2 * n)` over a
characteristic-zero field `K`, equipped with a base `b`, a Bourbaki diagram labelling
`e : b.support ≃ Fin (2 * n)`, and an automorphism `σ : P.Aut` reversing `b` along `e`. Although
the two middle simple roots at `n - 1` and `n` are adjacent (pairing to `-1` rather than `0`),
transporting the coordinate model of
`TauCeti.LinearAlgebra.RootSystem.Folding.EvenTypeA.Model` along `b.equivOfCartanMatrixEq` shows
that the distinct root-orbit sums `P.foldedIndices σ` form a reduced crystallographic root system
of Cartan type `B n` on `LinearMap.fixedSubmodule σ.weightMap` paired with its dual module:

* `RootPairing.evenTypeAFoldedPairing` has roots indexed by `P.foldedIndices σ` coercing to
  `(v : M)`, dual-evaluation pairing, `2 * n ^ 2` roots, and no doubled roots `2 • (v : M)` (ruling
  out `BCₙ`). By `RootPairing.evenTypeAFoldedPairing_congr`, the folded pairing depends only on
  `(P, σ)`.
* `RootPairing.Base.evenTypeAFoldedBase` has simple roots equal to the orbit sums of `b.support`,
  positive roots equal to the orbit sums of the positive roots of `b`, and Cartan type `B n` (hence
  also `A 1` when `n = 1`).
* Evaluated on `x : LinearMap.fixedSubmodule σ.weightMap`, the `k`-th Bourbaki-numbered folded
  simple coroot multiplies `P.coroot' (e.symm ⟨k, _⟩) (x : M)` by `1` off the middle (`k + 1 < n`)
  and by `2` at the middle (`k + 1 = n`). Consequently, closed and open dominant chambers agree
  before and after folding on fixed weights, and integer simple-coroot pairings before folding
  imply integer simple-coroot pairings after folding.
* At the short simple node (`k + 1 = n`), the folded simple root lifts both to a `σ`-fixed positive
  root of `b` (orbit size `1`) and to a positive root of `b` with `σ`-orbit of size `2`.
* `RootPairing.evenTypeAFoldedEquiv` and `RootPairing.Base.map_evenTypeAFoldedBase` record
  functoriality under root-system equivalences intertwining the reversal automorphisms.

## Main definitions

* `RootPairing.evenTypeAFoldedPairing`: the folded root system of type `B n` on
  `LinearMap.fixedSubmodule σ.weightMap` and its dual.
* `RootPairing.Base.evenTypeAFoldedBase` and `RootPairing.Base.evenTypeAFoldedSimpleIndex`: the
  folded base and its Bourbaki-numbered simple roots.
* `RootPairing.foldedIndicesCongr` and `RootPairing.evenTypeAFoldedEquiv`: functoriality of the
  folded root set and folded root system under intertwining equivalences.

## Main results

* `RootPairing.coe_root_evenTypeAFoldedPairing`, `RootPairing.toLinearMap_evenTypeAFoldedPairing`,
  and `RootPairing.evenTypeAFoldedPairing_congr`: root coercion, dual-evaluation pairing, and
  independence of `(b, e)`.
* `RootPairing.natCard_foldedIndices_evenTypeA` and
  `RootPairing.two_smul_notMem_foldedIndices_evenTypeA`: `#(foldedIndices) = 2 * n ^ 2` and absence
  of doubled folded roots.
* `RootPairing.Base.mem_support_evenTypeAFoldedBase_iff`,
  `RootPairing.Base.isPos_evenTypeAFoldedBase_iff`, and
  `RootPairing.Base.hasCartanType_evenTypeAFoldedBase`: simple roots, positive roots, and Cartan
  type `B n` (plus `A 1` when `n = 1`).
* `RootPairing.Base.coroot'_evenTypeAFoldedPairing_simpleIndex`,
  `RootPairing.Base.mem_dominantChamber_evenTypeAFoldedPairing_iff`,
  `RootPairing.Base.mem_openDominantChamber_evenTypeAFoldedPairing_iff`, and
  `RootPairing.Base.exists_int_coroot'_evenTypeAFoldedPairing`: simple-coroot scaling (`1` off
  middle, `2` at middle), chamber transport, and forward integrality on fixed weights.
* `RootPairing.Base.exists_fixed_pos_lift_shortSimple` and
  `RootPairing.Base.exists_paired_pos_lift_shortSimple`: lifts of the short simple folded root of
  orbit sizes `1` and `2`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--II.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace RootPairing

open Finset Function TauCeti TauCeti.DynkinType

section ConeHelper

private lemma isPos_of_two_smul_root_mem_posRootCone {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) (b : P.Base) {v : ι} (hv0 : P.root v ≠ 0)
    (htwo : (2 : K) • P.root v ∈ posRootCone P b) :
    b.IsPos v := by
  rcases mem_posRoots_or_mem_negRoots P b v with hpos | hneg
  · exact (mem_posRoots P b v).mp hpos
  · exfalso
    have hpos' := (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b v).mpr hneg
    have hneg_root : -P.root v ∈ posRootCone P b := by
      have hr := root_mem_posRootCone_of_mem_posRoots P b hpos'
      rwa [root_reflectionPerm, reflection_apply_self] at hr
    have hneg2 : -((2 : K) • P.root v) ∈ posRootCone P b := by
      simpa [two_smul] using (posRootCone P b).nsmul_mem hneg_root 2
    have hz := (isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem htwo hneg2
    exact hv0 ((smul_eq_zero.mp hz).resolve_left two_ne_zero)

end ConeHelper

section SimpleIndex

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] {n : ℕ}

/-- The `k`-th Bourbaki-numbered folded simple root, given by the orbit sum of `e.symm ⟨k, _⟩`. -/
noncomputable def Base.evenTypeAFoldedSimpleIndex
    (b : P.Base) (σ : P.Aut) (e : b.support ≃ Fin (2 * n)) (k : Fin n) : P.foldedIndices σ :=
  ⟨P.orbitSum σ (e.symm ⟨k, by have := k.isLt; omega⟩), P.orbitSum_mem_foldedIndices σ _⟩

/-- Coercing `evenTypeAFoldedSimpleIndex` to `M` gives `P.orbitSum σ (e.symm ⟨k, _⟩)`. -/
@[simp]
theorem Base.coe_evenTypeAFoldedSimpleIndex
    (b : P.Base) (σ : P.Aut) (e : b.support ≃ Fin (2 * n)) (k : Fin n) :
    ((b.evenTypeAFoldedSimpleIndex σ e k : P.foldedIndices σ) : M) =
      P.orbitSum σ (e.symm ⟨k, by have := k.isLt; omega⟩) :=
  (rfl)

end SimpleIndex

section Folding

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  (b : P.Base) (σ : P.Aut) {n : ℕ}

omit [Finite ι] [P.IsRootSystem] [P.IsReduced] in
private lemma evenTypeAToZeroSumCartanEq
    (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (i j : b.support) :
    (typeAZeroSumBase K (2 * n)).cartanMatrix
      ((e.trans (typeAZeroSumSimpleEquiv K (2 * n))) i)
      ((e.trans (typeAZeroSumSimpleEquiv K (2 * n))) j) = b.cartanMatrix i j := by
  rw [Equiv.trans_apply, Equiv.trans_apply, cartanMatrix_typeAZeroSumBase, he,
    DynkinType.cartanMatrix_A]

/-- Transport equivalence from `(P, b)` to `typeAZeroSumRootPairing K (2 * n)`. -/
private noncomputable def evenTypeAToZeroSumEquiv
    (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.Equiv (typeAZeroSumRootPairing K (2 * n)) :=
  b.equivOfCartanMatrixEq (typeAZeroSumBase K (2 * n))
    (e.trans (typeAZeroSumSimpleEquiv K (2 * n)))
    (evenTypeAToZeroSumCartanEq P b e he)

private lemma indexEquiv_evenTypeAToZeroSumEquiv_support
    (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (j : b.support) :
    (evenTypeAToZeroSumEquiv P b e he).indexEquiv j =
      typeAZeroSumSimplePair (2 * n) (e j) := by
  simp [evenTypeAToZeroSumEquiv]

variable (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)

include hσ he hrev

private lemma autCongr_evenTypeAToZeroSumEquiv :
    (evenTypeAToZeroSumEquiv P b e he).autCongr σ = typeAZeroSumRevAut K (2 * n) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  set b₀ := typeAZeroSumBase K (2 * n)
  set θ := typeAZeroSumRevAut K (2 * n)
  have hsupp : ∀ j : b₀.support, (Φ.autCongr σ).indexEquiv j = θ.indexEquiv j := by
    intro j
    let e₀ := e.trans (typeAZeroSumSimpleEquiv K (2 * n))
    let i : b.support := e₀.symm j
    let i' : b.support := ⟨σ.indexEquiv i, hσ i.1 i.2⟩
    have hj_eq : (j : TypeAIndex (2 * n)) = typeAZeroSumSimplePair (2 * n) (e i) := by
      have hei : e i = (typeAZeroSumSimpleEquiv K (2 * n)).symm j := e.apply_symm_apply _
      rw [hei, ← coe_typeAZeroSumSimpleEquiv K, Equiv.apply_symm_apply]
    have hi : Φ.indexEquiv i = j :=
      (indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i).trans hj_eq.symm
    have hi_symm : Φ.indexEquiv.symm j = i := Φ.indexEquiv.symm_apply_eq.mpr hi.symm
    have hi' : Φ.indexEquiv i' = typeAZeroSumSimplePair (2 * n) (e i') :=
      indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i'
    have hrev_i : e i' = (e i).rev := hrev i i' rfl
    rw [Equiv.indexEquiv_autCongr_apply, hi_symm, hi', hrev_i,
      ← indexEquiv_typeAZeroSumRevAut_simplePair K (2 * n) (e i), ← hj_eq]
  apply Equiv.weightHom_injective
  apply LinearEquiv.toLinearMap_injective
  refine b₀.toWeightBasis.ext fun j ↦ ?_
  simp only [Equiv.weightHom_apply, LinearEquiv.coe_coe, Equiv.weightEquiv_apply,
    b₀.toWeightBasis_apply, Hom.root_weightMap_apply, hsupp j]

private lemma indexEquiv_evenTypeAToZeroSumEquiv_comm (j : ι) :
    (evenTypeAToZeroSumEquiv P b e he).indexEquiv (σ.indexEquiv j) =
      (typeAZeroSumRevAut K (2 * n)).indexEquiv
        ((evenTypeAToZeroSumEquiv P b e he).indexEquiv j) := by
  rw [← autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev,
    Equiv.indexEquiv_autCongr_apply, Equiv.symm_apply_apply]

private lemma weightEquiv_evenTypeAToZeroSumEquiv_intertwine :
    (evenTypeAToZeroSumEquiv P b e he).weightEquiv.toLinearMap ∘ₗ σ.weightMap =
      (typeAZeroSumRevAut K (2 * n)).weightMap ∘ₗ
        (evenTypeAToZeroSumEquiv P b e he).weightEquiv.toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  have h := Equiv.autCongr_smul (evenTypeAToZeroSumEquiv P b e he) σ x
  rw [autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev] at h
  exact h.symm

/-- Linear equivalence from `LinearMap.fixedSubmodule σ.weightMap` to `Fin n → K`. -/
private noncomputable def evenTypeAWeightEquiv :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[K] (Fin n → K) :=
  ((evenTypeAToZeroSumEquiv P b e he).weightEquiv.fixedSubmoduleCongr
    (weightEquiv_evenTypeAToZeroSumEquiv_intertwine P b σ hσ e he hrev)).trans
    (evenTypeAFixedCoordEquiv K n)

private lemma mem_foldedIndices_of_root_typeB (k : Fin (2 * n ^ 2)) :
    (((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
      ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap) : M) ∈
      P.foldedIndices σ := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  set y := ((evenTypeAFixedCoordEquiv K n).symm ((typeBBaseChangeRootSystem K n).root k))
  have hy : (y : singleParityCheckCode K (Fin (2 * n + 1))) ∈
      (typeAZeroSumRootPairing K (2 * n)).foldedIndices (typeAZeroSumRevAut K (2 * n)) := by
    refine (mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices K n y).mp ?_
    rw [LinearEquiv.apply_symm_apply]
    exact Set.mem_range_self k
  rw [mem_foldedIndices] at hy ⊢
  obtain ⟨p, hp⟩ := hy
  refine ⟨Φ.indexEquiv.symm p, ?_⟩
  apply Φ.weightEquiv.injective
  have h1 : Φ.weightEquiv (P.orbitSum σ (Φ.indexEquiv.symm p)) =
      (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p := by
    rw [Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      Equiv.apply_symm_apply]
  have h2 : Φ.weightEquiv ((((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
      ((typeBBaseChangeRootSystem K n).root k) :
      LinearMap.fixedSubmodule σ.weightMap) : M)) = (y : _) := by
    rw [evenTypeAWeightEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.fixedSubmoduleCongr_symm_apply]
    exact Φ.weightEquiv.apply_symm_apply (y : _)
  rw [h1, h2, hp]

/-- Bijection between `Fin (2 * n ^ 2)` and `P.foldedIndices σ`. -/
private noncomputable def evenTypeAIndexEquiv :
    Fin (2 * n ^ 2) ≃ P.foldedIndices σ :=
  Equiv.ofBijective
    (fun k ↦ ⟨(((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
      ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap) : M),
      mem_foldedIndices_of_root_typeB P b σ hσ e he hrev k⟩)
    ⟨fun k₁ k₂ hk ↦ by
      dsimp only at hk
      have hval := congrArg Subtype.val hk
      exact (typeBBaseChangeRootSystem K n).root.injective
        ((evenTypeAWeightEquiv P b σ hσ e he hrev).symm.injective (Subtype.ext hval)),
      fun ⟨v, hv⟩ ↦ by
        obtain ⟨j, hj⟩ := mem_foldedIndices.mp hv
        set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
        set Φ := evenTypeAToZeroSumEquiv P b e he
        have hv_fix : v ∈ LinearMap.fixedSubmodule σ.weightMap :=
          hj ▸ P.orbitSum_mem_fixedSubmodule σ j
        have himg : Ψ ⟨v, hv_fix⟩ ∈ Set.range (typeBBaseChangeRootSystem K n).root := by
          dsimp [Ψ, evenTypeAWeightEquiv]
          rw [mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices, mem_foldedIndices]
          refine ⟨Φ.indexEquiv j, ?_⟩
          rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk,
            Equiv.weightEquiv_apply, ← hj]
          exact (weightMap_orbitSum Φ
            (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev) j).symm
        obtain ⟨k, hk⟩ := himg
        refine ⟨k, Subtype.ext ?_⟩
        dsimp only
        rw [hk]
        exact congrArg Subtype.val (Ψ.symm_apply_apply ⟨v, hv_fix⟩)⟩

private lemma coe_evenTypeAIndexEquiv_apply (k : Fin (2 * n ^ 2)) :
    ((evenTypeAIndexEquiv P b σ hσ e he hrev k : P.foldedIndices σ) : M) =
      (((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
        ((typeBBaseChangeRootSystem K n).root k) :
        LinearMap.fixedSubmodule σ.weightMap) : M) :=
  rfl

/-- **The folded root system of `(P, b, σ)` of type `A (2 * n)` under diagram reversal.** Its
weight space is `LinearMap.fixedSubmodule σ.weightMap`, its coweight space is the dual module, its
roots are indexed by `P.foldedIndices σ` and coerce to `(v : M)`, and it has Cartan type `B n`. -/
noncomputable def evenTypeAFoldedPairing :
    RootPairing (P.foldedIndices σ) K
      (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  (typeBBaseChangeRootSystem K n).map
    (evenTypeAIndexEquiv P b σ hσ e he hrev)
    (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
    ((_root_.dotProductEquiv K (Fin n)).trans
      (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

/-- `evenTypeAFoldedPairing` is a root system. -/
instance instIsRootSystemEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsRootSystem := by
  delta evenTypeAFoldedPairing
  infer_instance

/-- `evenTypeAFoldedPairing` is reduced. -/
instance instIsReducedEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsReduced := by
  delta evenTypeAFoldedPairing
  infer_instance

/-- `evenTypeAFoldedPairing` is crystallographic. -/
instance instIsCrystallographicEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsCrystallographic := by
  delta evenTypeAFoldedPairing
  infer_instance

/-- The bilinear pairing of `evenTypeAFoldedPairing` is dual evaluation `x ↦ φ ↦ φ x`. -/
@[simp]
theorem toLinearMap_evenTypeAFoldedPairing
    (x : LinearMap.fixedSubmodule σ.weightMap)
    (φ : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).toLinearMap x φ = φ x := by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set g := (_root_.dotProductEquiv K (Fin n)).trans Ψ.dualMap
  delta evenTypeAFoldedPairing
  rw [toLinearMap_map, LinearEquiv.symm_symm,
    toLinearMap_typeBBaseChangeRootSystem, dotProduct_comm]
  have hg : ∀ y : Fin n → K, g y x = y ⬝ᵥ Ψ x := fun y ↦ by simp [g]
  rw [← hg, LinearEquiv.apply_symm_apply]

/-- Each root of `evenTypeAFoldedPairing` coerces in `M` to its index `(v : M)`. -/
@[simp]
theorem coe_root_evenTypeAFoldedPairing (v : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).root v :
      LinearMap.fixedSubmodule σ.weightMap) : M) = (v : M) := by
  delta evenTypeAFoldedPairing
  rw [root_map]
  exact congrArg Subtype.val ((evenTypeAIndexEquiv P b σ hσ e he hrev).apply_symm_apply v)

/-- The folded root set `P.foldedIndices σ` of even `A (2 * n)` under reversal has cardinality
`2 * n ^ 2`. -/
theorem natCard_foldedIndices_evenTypeA :
    Nat.card (P.foldedIndices σ) = 2 * n ^ 2 := by
  rw [Nat.card_congr (evenTypeAIndexEquiv P b σ hσ e he hrev).symm, Nat.card_fin]

/-- No double `2 • (v : M)` of a folded root is an orbit sum, ruling out `BCₙ`. -/
theorem two_smul_notMem_foldedIndices_evenTypeA (v : P.foldedIndices σ) :
    (2 : K) • (v : M) ∉ P.foldedIndices σ := by
  intro hmem
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let w : P.foldedIndices σ := ⟨(2 : K) • (v : M), hmem⟩
  have hrw : P'.root w = (2 : K) • P'.root v := by
    apply Subtype.ext
    rw [coe_root_evenTypeAFoldedPairing, SetLike.val_smul, coe_root_evenTypeAFoldedPairing]
  have hdep : ¬ LinearIndependent K ![P'.root v, P'.root w] := by
    intro hli
    have hrel : (2 : K) • P'.root v + (-1 : K) • P'.root w = 0 := by
      rw [hrw, neg_one_smul, add_neg_cancel]
    have h := (Fintype.linearIndependent_iff.mp hli) ![2, -1]
      (by simpa [Fin.sum_univ_two] using hrel) 0
    norm_num at h
  have hv_ne : P'.root v ≠ 0 := by
    intro hz
    have h0 : (v : M) = 0 := by
      rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev v, hz, ZeroMemClass.coe_zero]
    exact zero_notMem_foldedIndices hσ (h0 ▸ v.2)
  rcases IsReduced.eq_or_eq_neg (P := P') v w hdep with heq | hneg
  · apply hv_ne
    have h1 : (1 : K) • P'.root v = 0 := by
      calc (1 : K) • P'.root v = (2 : K) • P'.root v - P'.root v := by module
        _ = P'.root w - P'.root v := by rw [hrw]
        _ = 0 := sub_eq_zero.mpr heq.symm
    simpa using h1
  · have h3 : (3 : K) • P'.root v = 0 := by
      calc (3 : K) • P'.root v = (2 : K) • P'.root v + P'.root v := by module
        _ = P'.root w + P'.root v := by rw [hrw]
        _ = 0 := by rw [hneg, add_neg_cancel]
    exact hv_ne ((smul_eq_zero.mp h3).resolve_left (by norm_num))

/-- The folded pairing depends only on `(P, σ)`, not on the choice of base or diagram labelling. -/
theorem evenTypeAFoldedPairing_congr
    (b₂ : P.Base) {n₂ : ℕ} (hσ₂ : ∀ i ∈ b₂.support, σ.indexEquiv i ∈ b₂.support)
    (e₂ : b₂.support ≃ Fin (2 * n₂))
    (he₂ : ∀ i j, b₂.cartanMatrix i j = (DynkinType.A (2 * n₂)).cartanMatrix (e₂ i) (e₂ j))
    (hrev₂ : ∀ i j : b₂.support, σ.indexEquiv i = j → e₂ j = (e₂ i).rev) :
    P.evenTypeAFoldedPairing b σ hσ e he hrev =
      P.evenTypeAFoldedPairing b₂ σ hσ₂ e₂ he₂ hrev₂ := by
  apply IsRootSystem.ext
  · ext x φ
    simp
  · ext v : 1
    apply Subtype.ext
    simp

private noncomputable def evenTypeAFoldedEquivTypeB :
    (typeBBaseChangeRootSystem K n).Equiv (P.evenTypeAFoldedPairing b σ hσ e he hrev) := by
  delta evenTypeAFoldedPairing
  exact (typeBBaseChangeRootSystem K n).equivMap
    (evenTypeAIndexEquiv P b σ hσ e he hrev)
    (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
    ((_root_.dotProductEquiv K (Fin n)).trans
      (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

private lemma indexEquiv_evenTypeAFoldedEquivTypeB :
    (evenTypeAFoldedEquivTypeB P b σ hσ e he hrev).indexEquiv =
      evenTypeAIndexEquiv P b σ hσ e he hrev := by
  delta evenTypeAFoldedEquivTypeB evenTypeAFoldedPairing
  exact indexEquiv_equivMap ..

private lemma coroot'_evenTypeAFoldedPairing_eq (v : P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x =
      (typeBBaseChangeRootSystem K n).coroot'
        ((evenTypeAIndexEquiv P b σ hσ e he hrev).symm v)
        (evenTypeAWeightEquiv P b σ hσ e he hrev x) := by
  delta evenTypeAFoldedPairing
  rw [coroot'_map, LinearEquiv.symm_symm]

private lemma evenTypeAIndexEquiv_typeBSimpleIndex (k : Fin n) :
    evenTypeAIndexEquiv P b σ hσ e he hrev (typeBSimpleIndex n k) =
      b.evenTypeAFoldedSimpleIndex σ e k := by
  have hk := k.isLt
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set Φ := evenTypeAToZeroSumEquiv P b e he
  let jk : b.support := e.symm ⟨k, by omega⟩
  have hΦ : Φ.indexEquiv jk = typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ := by
    rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply]
  have hΨ : Ψ ⟨P.orbitSum σ jk, P.orbitSum_mem_fixedSubmodule σ jk⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
    dsimp [Ψ, evenTypeAWeightEquiv]
    rw [← evenTypeAFixedCoordEquiv_simpleOrbitSum K n k]
    congr 1
    apply Subtype.ext
    rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev), hΦ]
  apply Subtype.ext
  rw [coe_evenTypeAIndexEquiv_apply, Base.coe_evenTypeAFoldedSimpleIndex, ← hΨ]
  exact congrArg Subtype.val (Ψ.symm_apply_apply _)

variable {P}

/-- **The folded base of `(P, b, σ)`.** Its simple roots are the orbit sums of the simple roots of
`b`, and its Cartan type is `B n`. -/
noncomputable def Base.evenTypeAFoldedBase :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Base :=
  (typeBBaseChangeBase K n).map (evenTypeAFoldedEquivTypeB P b σ hσ e he hrev)

/-- `b.evenTypeAFoldedSimpleIndex σ e k` belongs to the support of `evenTypeAFoldedBase`. -/
theorem Base.evenTypeAFoldedSimpleIndex_mem_support (k : Fin n) :
    b.evenTypeAFoldedSimpleIndex σ e k ∈
      (b.evenTypeAFoldedBase σ hσ e he hrev).support := by
  classical
  rw [evenTypeAFoldedBase, Base.support_map_eq, mem_image]
  refine ⟨typeBSimpleIndex n k, ?_, ?_⟩
  · rw [mem_support_typeBBaseChangeBase_iff, typeBSimpleIndex_val]
    exact k.isLt
  · rw [indexEquiv_evenTypeAFoldedEquivTypeB]
    exact evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev k

/-- A folded root `v` lies in the support of `evenTypeAFoldedBase` if and only if it is one of the
Bourbaki-numbered folded simple roots `evenTypeAFoldedSimpleIndex`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff_exists_fin (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ k : Fin n, v = b.evenTypeAFoldedSimpleIndex σ e k := by
  classical
  rw [evenTypeAFoldedBase, Base.support_map_eq, mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [mem_support_typeBBaseChangeBase_iff] at hm
    refine ⟨⟨m, hm⟩, ?_⟩
    have hm' : m = typeBSimpleIndex n ⟨m, hm⟩ := Fin.ext (by simp)
    rw [indexEquiv_evenTypeAFoldedEquivTypeB]
    conv_lhs => rw [hm']
    exact evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev ⟨m, hm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨typeBSimpleIndex n k, ?_, ?_⟩
    · rw [mem_support_typeBBaseChangeBase_iff, typeBSimpleIndex_val]
      exact k.isLt
    · rw [indexEquiv_evenTypeAFoldedEquivTypeB]
      exact evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev k

/-- **Simple roots of the folded base.** A folded root lies in `(evenTypeAFoldedBase).support` if
and only if it is the orbit sum of a simple root of `b`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ j ∈ b.support, P.orbitSum σ j = (v : M) := by
  rw [b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev]
  constructor
  · rintro ⟨k, rfl⟩
    let jk : b.support := e.symm ⟨k, by have := k.isLt; omega⟩
    exact ⟨jk, jk.2, rfl⟩
  · rintro ⟨j, hj, hv⟩
    let m : Fin (2 * n) := e ⟨j, hj⟩
    by_cases hlt : (m : ℕ) < n
    · refine ⟨⟨m, hlt⟩, Subtype.ext ?_⟩
      rw [← hv, coe_evenTypeAFoldedSimpleIndex]
      have hjm : e.symm ⟨m, by omega⟩ = ⟨j, hj⟩ := e.symm_apply_apply ⟨j, hj⟩
      rw [hjm]
    · have hrev_lt : (m.rev : ℕ) < n := by
        have := m.isLt; rw [Fin.val_rev]; omega
      let j' : b.support := ⟨σ.indexEquiv j, hσ j hj⟩
      have hej' : e j' = m.rev := hrev ⟨j, hj⟩ j' rfl
      refine ⟨⟨m.rev, hrev_lt⟩, Subtype.ext ?_⟩
      rw [← hv, coe_evenTypeAFoldedSimpleIndex]
      have hj'm : e.symm ⟨m.rev, by omega⟩ = j' := by
        apply e.injective
        rw [e.apply_symm_apply, hej']
      rw [hj'm]
      exact (P.orbitSum_indexEquiv σ j).symm

/-- `evenTypeAFoldedBase` has Cartan type `B n`. -/
theorem Base.hasCartanType_evenTypeAFoldedBase :
    HasCartanType (P.evenTypeAFoldedPairing b σ hσ e he hrev)
      (b.evenTypeAFoldedBase σ hσ e he hrev) (.B n) :=
  (hasCartanType_typeBBaseChangeBase K n).map _

/-- In rank `n = 1` (`A₂` under reversal), the folded base has Cartan type `A 1` (`= B 1`). -/
theorem Base.hasCartanType_evenTypeAFoldedBase_of_eq_one (hn : n = 1) :
    HasCartanType (P.evenTypeAFoldedPairing b σ hσ e he hrev)
      (b.evenTypeAFoldedBase σ hσ e he hrev) (.A 1) := by
  subst hn
  obtain ⟨f, hf⟩ := (hasCartanType_iff _ _).mp
    (b.hasCartanType_evenTypeAFoldedBase σ hσ e he hrev)
  refine (hasCartanType_iff _ _).mpr ⟨f, fun i j ↦ ?_⟩
  rw [hf]
  by_cases hij : i = j
  · subst hij
    simp [DynkinType.cartanMatrix_B, DynkinType.cartanMatrix_A, CartanMatrix.B, CartanMatrix.A]
  · exfalso
    have hrank : (DynkinType.B 1).rank = 1 := rfl
    exact hij (f.injective (Fin.ext (by have := (f i).isLt; have := (f j).isLt; omega)))

/-- **Simple-coroot evaluation on fixed weights.** Evaluating the `k`-th Bourbaki-numbered folded
simple coroot on `x : LinearMap.fixedSubmodule σ.weightMap` multiplies
`P.coroot' (e.symm ⟨k, _⟩) (x : M)` by `1` off the middle (`k + 1 < n`) and by `2` at the middle
(`k + 1 = n`). -/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex (k : Fin n)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x =
      (if (k : ℕ) + 1 = n then 2 else 1) *
        P.coroot' (e.symm ⟨k, by have := k.isLt; omega⟩) (x : M) := by
  have hk := k.isLt
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set Φ := evenTypeAToZeroSumEquiv P b e he
  let jk : b.support := e.symm ⟨k, by omega⟩
  have hidx : (evenTypeAIndexEquiv P b σ hσ e he hrev).symm
      (b.evenTypeAFoldedSimpleIndex σ e k) = typeBSimpleIndex n k :=
    (evenTypeAIndexEquiv P b σ hσ e he hrev).symm_apply_eq.mpr
      (evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev k).symm
  have hΦ : Φ.indexEquiv jk = typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ := by
    rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply]
  rw [coroot'_evenTypeAFoldedPairing_eq, hidx, coroot'_typeBBaseChangeRootSystem_simpleIndex]
  dsimp only [Ψ, evenTypeAWeightEquiv, LinearEquiv.trans_apply]
  rw [evenTypeAFixedCoordEquiv_apply, LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk,
    Equiv.weightEquiv_apply, ← hΦ, Hom.coroot'_indexEquiv_weightMap]

/-- Off the middle orbit (`k + 1 < n`), the `k`-th folded simple coroot restricts the original
simple coroot without scaling. -/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex_of_lt {k : Fin n}
    (hk : (k : ℕ) + 1 < n) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x =
      P.coroot' (e.symm ⟨k, by omega⟩) (x : M) := by
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev,
    ite_eq_right (by omega), one_mul]

/-- At the middle orbit (`k + 1 = n`), the `k`-th folded simple coroot restricts twice the original
middle simple coroot. -/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex_of_eq {k : Fin n}
    (hk : (k : ℕ) + 1 = n) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x =
      2 * P.coroot' (e.symm ⟨k, by omega⟩) (x : M) := by
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, ite_eq_left hk]

omit [CharZero K] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] he in
private lemma root_add_root_indexEquiv_eq_orbitSum {i : ι} (hi : i ∈ b.support) :
    P.root i + P.root (σ.indexEquiv i) = P.orbitSum σ i := by
  classical
  let i' : b.support := ⟨σ.indexEquiv i, hσ i hi⟩
  let i'' : b.support := ⟨σ.indexEquiv i', hσ i'.1 i'.2⟩
  have h1 : e i' = (e ⟨i, hi⟩).rev := hrev ⟨i, hi⟩ i' rfl
  have h2 : e i'' = (e ⟨i, hi⟩).rev.rev := (hrev i' i'' rfl).trans (congrArg Fin.rev h1)
  rw [Fin.rev_rev] at h2
  have hinv : σ.indexEquiv (σ.indexEquiv i) = i := congrArg Subtype.val (e.injective h2)
  have hne : σ.indexEquiv i ≠ i := fun hc ↦ by
    have hc' : e i' = e ⟨i, hi⟩ := congrArg e (Subtype.ext hc)
    rw [h1] at hc'
    have := (e ⟨i, hi⟩).isLt
    have hval := congrArg Fin.val hc'
    rw [Fin.val_rev] at hval
    omega
  have horb : P.orbitIndices σ i = {i, σ.indexEquiv i} := by
    ext q
    rw [mem_orbitIndices_iff_exists_pow, mem_insert, mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro ⟨m, rfl⟩
      induction m with
      | zero => exact Or.inl rfl
      | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · rw [h]
          exact Or.inr rfl
        · rw [h, hinv]
          exact Or.inl rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, by simp⟩
  rw [orbitSum_def, horb, sum_pair hne.symm]

private lemma isPos_evenTypeAFoldedBase_of_isPos {j : ι} {w : P.foldedIndices σ}
    (hj : b.IsPos j) (hw : P.orbitSum σ j = (w : M)) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos w := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let b' := b.evenTypeAFoldedBase σ hσ e he hrev
  have hcone := P.orbitSum_mem_posRootCone hσ hj
  rw [hw, mem_posRootCone P b] at hcone
  obtain ⟨c, hc⟩ := hcone
  have hw_fix : σ.weightMap (w : M) = (w : M) :=
    LinearMap.mem_fixedSubmodule_iff.mp (hw ▸ P.orbitSum_mem_fixedSubmodule σ j)
  have hvec : (2 : K) • (w : M) = ∑ i ∈ b.support.attach, c i.1 • P.orbitSum σ i.1 := by
    calc (2 : K) • (w : M) = (w : M) + σ.weightMap (w : M) := by rw [hw_fix, two_smul]
      _ = (∑ i ∈ b.support, c i • P.root i) +
            σ.weightMap (∑ i ∈ b.support, c i • P.root i) := by rw [hc]
      _ = ∑ i ∈ b.support, c i • (P.root i + P.root (σ.indexEquiv i)) := by
            rw [map_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ ↦ ?_
            rw [map_nsmul, Hom.root_weightMap_apply, ← nsmul_add]
      _ = ∑ i ∈ b.support.attach, c i.1 • P.orbitSum σ i.1 := by
            rw [← sum_attach]
            exact sum_congr rfl fun i _ ↦ by
              rw [root_add_root_indexEquiv_eq_orbitSum b σ hσ e hrev i.2]
  have htwo : (2 : K) • P'.root w ∈ posRootCone P' b' := by
    have hroot_sum : (2 : K) • P'.root w =
        ∑ i ∈ b.support.attach, c i.1 •
          P'.root ⟨P.orbitSum σ i.1, P.orbitSum_mem_foldedIndices σ i.1⟩ := by
      apply Subtype.ext
      rw [SetLike.val_smul, coe_root_evenTypeAFoldedPairing, hvec, Submodule.coe_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [Submodule.coe_smul_of_tower, coe_root_evenTypeAFoldedPairing]
    rw [hroot_sum]
    refine (posRootCone P' b').sum_mem fun i _ ↦ (posRootCone P' b').nsmul_mem ?_ _
    refine root_mem_posRootCone_of_mem_posRoots P' b' (support_subset_posRoots P' b' ?_)
    exact (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr ⟨i.1, i.2, rfl⟩
  have hw0 : P'.root w ≠ 0 := by
    intro h0
    have hcoe0 : (w : M) = 0 := by
      rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev w, h0, ZeroMemClass.coe_zero]
    exact zero_notMem_foldedIndices hσ (hcoe0 ▸ w.2)
  exact isPos_of_two_smul_root_mem_posRootCone P' b' hw0 htwo

/-- **Positive roots of the folded base.** A folded root is positive for `evenTypeAFoldedBase` if
and only if it is the orbit sum of a positive root of `b`. -/
theorem Base.isPos_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v ↔
      ∃ j, b.IsPos j ∧ P.orbitSum σ j = (v : M) := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let b' := b.evenTypeAFoldedBase σ hσ e he hrev
  refine ⟨fun hv ↦ ?_, fun ⟨j, hj, hw⟩ ↦
    isPos_evenTypeAFoldedBase_of_isPos b σ hσ e he hrev hj hw⟩
  obtain ⟨j, hj⟩ := mem_foldedIndices.mp v.2
  by_cases hpos : b.IsPos j
  · exact ⟨j, hpos, hj⟩
  · exfalso
    have hj' : b.IsPos (P.reflectionPerm j j) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr ((mem_negRoots P b j).mpr hpos)
    have hneg_orb : P.orbitSum σ (P.reflectionPerm j j) =
        ((P'.reflectionPerm v v : P.foldedIndices σ) : M) := by
      rw [orbitSum_reflectionPerm_self, hj,
        ← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev v,
        ← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v v),
        root_reflectionPerm, reflection_apply_self, Submodule.coe_neg]
    have hv' : b'.IsPos (P'.reflectionPerm v v) :=
      isPos_evenTypeAFoldedBase_of_isPos b σ hσ e he hrev hj' hneg_orb
    exact reflectionPerm_self_notMem_posRoots P' b' ((mem_posRoots P' b' v).mpr hv)
      ((mem_posRoots P' b' _).mpr hv')

/-- **Forward simple-coroot integrality on fixed weights.** If all simple coroots of `b` take
integer values on `(x : M)`, then all simple coroots of `evenTypeAFoldedBase` take integer values
on `x`. -/
theorem Base.exists_int_coroot'_evenTypeAFoldedPairing
    (x : LinearMap.fixedSubmodule σ.weightMap)
    (hint : ∀ j ∈ b.support, ∃ z : ℤ, P.coroot' j (x : M) = z) :
    ∀ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support,
      ∃ z : ℤ, (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x = z := by
  intro v hv
  obtain ⟨k, rfl⟩ :=
    (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
  obtain ⟨z, hz⟩ := hint _ (e.symm ⟨k, by have := k.isLt; omega⟩).2
  refine ⟨(if (k : ℕ) + 1 = n then 2 else 1) * z, ?_⟩
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, hz, Int.cast_mul]
  congr 1
  split_ifs <;> norm_num

/-- The short simple folded root (at `k + 1 = n`) lifts to a `σ`-fixed positive root of `b`
(orbit of size `1`). -/
theorem Base.exists_fixed_pos_lift_shortSimple {k : Fin n} (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 1 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  let p := evenTypeAFixedShortLift n k
  obtain ⟨hp_pos, hp_card, hp_sum⟩ := evenTypeAFixedShortLift_spec K n k
  let j := Φ.indexEquiv.symm p
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) :=
    TauCeti.map_equivOfCartanMatrixEq b (typeAZeroSumBase K (2 * n)) _ _
  refine ⟨j, ?_, ?_, ?_⟩
  · have hpos : (b.map Φ).IsPos (Φ.indexEquiv j) := by
      simpa [hb_map, j] using hp_pos
    exact (b.isPos_map_iff Φ j).mp hpos
  · have hmap := map_orbitIndices Φ
      (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev) j
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map, Equiv.apply_symm_apply] at hcard
    exact hcard.trans hp_card
  · apply Φ.weightEquiv.injective
    rw [Equiv.weightEquiv_apply, Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      coe_evenTypeAFoldedSimpleIndex,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev)]
    have hjk : Φ.indexEquiv (e.symm ⟨k, by omega⟩) =
        typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ := by
      rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he (e.symm ⟨k, by omega⟩),
        Equiv.apply_symm_apply]
    rw [Equiv.apply_symm_apply, hp_sum, hjk, orbitSum_typeAZeroSumRevAut_simplePair,
      dite_eq_right (by omega)]

/-- The short simple folded root (at `k + 1 = n`) also lifts to a positive root of `b` whose
`σ`-orbit has size `2`. -/
theorem Base.exists_paired_pos_lift_shortSimple {k : Fin n} (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 2 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  let p := evenTypeAPairedShortLift n k
  obtain ⟨hp_pos, hp_card, hp_sum⟩ := evenTypeAPairedShortLift_spec K n k
  let j := Φ.indexEquiv.symm p
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) :=
    TauCeti.map_equivOfCartanMatrixEq b (typeAZeroSumBase K (2 * n)) _ _
  refine ⟨j, ?_, ?_, ?_⟩
  · have hpos : (b.map Φ).IsPos (Φ.indexEquiv j) := by
      simpa [hb_map, j] using hp_pos
    exact (b.isPos_map_iff Φ j).mp hpos
  · have hmap := map_orbitIndices Φ
      (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev) j
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map, Equiv.apply_symm_apply] at hcard
    exact hcard.trans hp_card
  · apply Φ.weightEquiv.injective
    rw [Equiv.weightEquiv_apply, Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      coe_evenTypeAFoldedSimpleIndex,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev)]
    have hjk : Φ.indexEquiv (e.symm ⟨k, by omega⟩) =
        typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ := by
      rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he (e.symm ⟨k, by omega⟩),
        Equiv.apply_symm_apply]
    rw [Equiv.apply_symm_apply, hp_sum, hjk, orbitSum_typeAZeroSumRevAut_simplePair,
      dite_eq_right (by omega)]

end Folding

section OrderedField

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  (b : P.Base) (σ : P.Aut) {n : ℕ}
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)

/-- **Closed dominant chamber transport on fixed weights.** Over a linearly ordered field, a
`σ`-fixed weight lies in `P.dominantChamber b` if and only if it lies in the folded closed dominant
chamber. -/
theorem Base.mem_dominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (x : M) ∈ P.dominantChamber b ↔
      x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).dominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) := by
  simp only [mem_dominantChamber]
  constructor
  · intro hx v hv
    obtain ⟨k, rfl⟩ :=
      (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    have hc : (0 : K) ≤ if (k : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
    exact mul_nonneg hc (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).2)
  · intro hx j hj
    let m : Fin (2 * n) := e ⟨j, hj⟩
    by_cases hlt : (m : ℕ) < n
    · have hv := hx (b.evenTypeAFoldedSimpleIndex σ e ⟨m, hlt⟩)
        (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev ⟨m, hlt⟩)
      rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev] at hv
      have hc : (0 : K) < if (m : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
      have hjm : (e.symm ⟨m, by omega⟩ : b.support) = ⟨j, hj⟩ := e.symm_apply_apply ⟨j, hj⟩
      rw [hjm] at hv
      exact (mul_nonneg_iff_of_pos_left hc).mp hv
    · have hrev_lt : (m.rev : ℕ) < n := by have := m.isLt; rw [Fin.val_rev]; omega
      let j' : b.support := ⟨σ.indexEquiv j, hσ j hj⟩
      have hej' : e j' = m.rev := hrev ⟨j, hj⟩ j' rfl
      have hj'm : (e.symm ⟨m.rev, by omega⟩ : b.support) = j' :=
        e.injective (by rw [e.apply_symm_apply, hej'])
      have hv := hx (b.evenTypeAFoldedSimpleIndex σ e ⟨m.rev, hrev_lt⟩)
        (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev ⟨m.rev, hrev_lt⟩)
      rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, hj'm] at hv
      have hc : (0 : K) < if (m.rev : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
      have hnonneg : 0 ≤ P.coroot' (σ.indexEquiv j) (x : M) :=
        (mul_nonneg_iff_of_pos_left hc).mp hv
      have hfix : σ.weightMap (x : M) = (x : M) := LinearMap.mem_fixedSubmodule_iff.mp x.2
      rwa [← hfix, Hom.coroot'_indexEquiv_weightMap] at hnonneg

/-- **Open dominant chamber transport on fixed weights.** Over a linearly ordered field, a
`σ`-fixed weight lies in `P.openDominantChamber b` if and only if it lies in the folded open
dominant chamber. -/
theorem Base.mem_openDominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (x : M) ∈ P.openDominantChamber b ↔
      x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).openDominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) := by
  simp only [mem_openDominantChamber]
  constructor
  · intro hx v hv
    obtain ⟨k, rfl⟩ :=
      (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    have hc : (0 : K) < if (k : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
    exact mul_pos hc (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).2)
  · intro hx j hj
    let m : Fin (2 * n) := e ⟨j, hj⟩
    by_cases hlt : (m : ℕ) < n
    · have hv := hx (b.evenTypeAFoldedSimpleIndex σ e ⟨m, hlt⟩)
        (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev ⟨m, hlt⟩)
      rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev] at hv
      have hc : (0 : K) < if (m : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
      have hjm : (e.symm ⟨m, by omega⟩ : b.support) = ⟨j, hj⟩ := e.symm_apply_apply ⟨j, hj⟩
      rw [hjm] at hv
      exact (mul_pos_iff_of_pos_left hc).mp hv
    · have hrev_lt : (m.rev : ℕ) < n := by have := m.isLt; rw [Fin.val_rev]; omega
      let j' : b.support := ⟨σ.indexEquiv j, hσ j hj⟩
      have hej' : e j' = m.rev := hrev ⟨j, hj⟩ j' rfl
      have hj'm : (e.symm ⟨m.rev, by omega⟩ : b.support) = j' :=
        e.injective (by rw [e.apply_symm_apply, hej'])
      have hv := hx (b.evenTypeAFoldedSimpleIndex σ e ⟨m.rev, hrev_lt⟩)
        (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev ⟨m.rev, hrev_lt⟩)
      rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, hj'm] at hv
      have hc : (0 : K) < if (m.rev : ℕ) + 1 = n then 2 else 1 := by split_ifs <;> norm_num
      have hpos : 0 < P.coroot' (σ.indexEquiv j) (x : M) :=
        (mul_pos_iff_of_pos_left hc).mp hv
      have hfix : σ.weightMap (x : M) = (x : M) := LinearMap.mem_fixedSubmodule_iff.mp x.2
      rwa [← hfix, Hom.coroot'_indexEquiv_weightMap] at hpos

end OrderedField

/-! ### Functoriality under intertwining root-system equivalences -/

section FoldedIndicesCongr

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} [Finite ι] {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι₂]

/-- An equivalence `φ : P.Equiv P₂` intertwining `σ` and `σ₂` carries `P.foldedIndices σ`
bijectively onto `P₂.foldedIndices σ₂`. -/
noncomputable def foldedIndicesCongr {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    P.foldedIndices σ ≃ P₂.foldedIndices σ₂ where
  toFun v := ⟨φ.weightMap (v : M), by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp v.2
    rw [mem_foldedIndices]
    refine ⟨φ.indexEquiv i, ?_⟩
    rw [← hi]
    exact (weightMap_orbitSum φ
      (fun j ↦ by rw [← hφ, Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply])
      i).symm⟩
  invFun w := ⟨(Equiv.symm P P₂ φ).weightMap (w : M₂), by
    obtain ⟨i₂, hi₂⟩ := mem_foldedIndices.mp w.2
    rw [mem_foldedIndices]
    refine ⟨(Equiv.symm P P₂ φ).indexEquiv i₂, ?_⟩
    rw [← hi₂]
    exact (weightMap_orbitSum (Equiv.symm P P₂ φ)
      (fun j ↦ by
        have hsymm : (Equiv.symm P P₂ φ).autCongr σ₂ = σ := by
          rw [← hφ]
          ext x <;> simp [Equiv.autCongr_apply]
        rw [← hsymm, Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply])
      i₂).symm⟩
  left_inv v := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- Coercing `foldedIndicesCongr φ hφ v` applies `φ.weightMap` to `(v : M)`. -/
@[simp]
theorem coe_foldedIndicesCongr_apply {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) (v : P.foldedIndices σ) :
    ((foldedIndicesCongr φ hφ v : P₂.foldedIndices σ₂) : M₂) = φ.weightMap (v : M) :=
  (rfl)

end FoldedIndicesCongr

section Functoriality

variable {ι ι₂ K M N M₂ N₂ : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  {P₂ : RootPairing ι₂ K M₂ N₂} [Finite ι₂]
  [P₂.IsRootSystem] [P₂.IsReduced] [P₂.IsCrystallographic]
  (b : P.Base) (σ : P.Aut) {n : ℕ}
  (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)
  (b₂ : P₂.Base) (σ₂ : P₂.Aut) {n₂ : ℕ}
  (hσ₂ : ∀ i ∈ b₂.support, σ₂.indexEquiv i ∈ b₂.support)
  (e₂ : b₂.support ≃ Fin (2 * n₂))
  (he₂ : ∀ i j, b₂.cartanMatrix i j = (DynkinType.A (2 * n₂)).cartanMatrix (e₂ i) (e₂ j))
  (hrev₂ : ∀ i j : b₂.support, σ₂.indexEquiv i = j → e₂ j = (e₂ i).rev)

/-- **Functoriality of the folded root system.** Any equivalence `φ : P.Equiv P₂` intertwining `σ`
and `σ₂` (`φ.autCongr σ = σ₂`) induces an equivalence between the two folded root pairings,
restricting `φ.weightMap` on fixed subspaces and acting by `foldedIndicesCongr` on folded roots. -/
noncomputable def evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Equiv
      (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂) :=
  Equiv.mk'
    (P.evenTypeAFoldedPairing b σ hσ e he hrev)
    (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂)
    (φ.weightEquiv.fixedSubmoduleCongr <| by
      refine LinearMap.ext fun x ↦ ?_
      have h := Equiv.autCongr_smul φ σ x
      rw [hφ] at h
      exact h.symm)
    (foldedIndicesCongr φ hφ)
    fun v ↦ by
      apply Subtype.ext
      rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
        coe_root_evenTypeAFoldedPairing, coe_root_evenTypeAFoldedPairing,
        coe_foldedIndicesCongr_apply]

/-- The weight map of `evenTypeAFoldedEquiv` restricts `φ.weightMap` to fixed submodules. -/
@[simp]
theorem coe_weightMap_evenTypeAFoldedEquiv_apply (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).weightMap x :
      LinearMap.fixedSubmodule σ₂.weightMap) : M₂) = φ.weightMap (x : M) := by
  dsimp only [evenTypeAFoldedEquiv, Equiv.mk']
  rw [LinearEquiv.coe_coe, LinearEquiv.fixedSubmoduleCongr_apply, Equiv.weightEquiv_apply]

/-- The index equivalence of `evenTypeAFoldedEquiv` is `foldedIndicesCongr φ hφ`. -/
@[simp]
theorem indexEquiv_evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).indexEquiv =
      foldedIndicesCongr φ hφ :=
  (rfl)

/-- When `φ` also maps `b` to `b₂`, `evenTypeAFoldedEquiv` maps the folded base of `b` to the
folded base of `b₂`. -/
theorem Base.map_evenTypeAFoldedBase (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂)
    (hb : b.map φ = b₂) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).map
      (evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ) =
      b₂.evenTypeAFoldedBase σ₂ hσ₂ e₂ he₂ hrev₂ := by
  classical
  ext w
  rw [Base.support_map_eq, mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨j, hj, hvj⟩ :=
      (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev v).mp hv
    refine (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ _).mpr
      ⟨φ.indexEquiv j, ?_, ?_⟩
    · rw [← hb, Base.support_map_eq]
      exact mem_image_of_mem _ hj
    · rw [indexEquiv_evenTypeAFoldedEquiv, coe_foldedIndicesCongr_apply, ← hvj]
      exact (weightMap_orbitSum φ
        (fun z ↦ by rw [← hφ, Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply])
        j).symm
  · intro hw
    obtain ⟨j₂, hj₂, hwj⟩ :=
      (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ w).mp hw
    rw [← hb, Base.support_map_eq, mem_image] at hj₂
    obtain ⟨j, hj, rfl⟩ := hj₂
    let v : P.foldedIndices σ := ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
    refine ⟨v, (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev v).mpr ⟨j, hj, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [indexEquiv_evenTypeAFoldedEquiv, coe_foldedIndicesCongr_apply, ← hwj]
    exact weightMap_orbitSum φ
      (fun z ↦ by rw [← hφ, Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply]) j

end Functoriality

end RootPairing
