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

For any finite reduced crystallographic root system `P` of Cartan type `A (2 * n)` over a
characteristic-zero field `K` with base `b`, Bourbaki labelling `e : b.support ≃ Fin (2 * n)`, and
diagram-reversing automorphism `σ : P.Aut`, transporting the coordinate model shows that
`P.foldedIndices σ` forms a reduced crystallographic root system `evenTypeAFoldedPairing` and base
`Base.evenTypeAFoldedBase` of Cartan type `B n`, with explicit simple-coroot scaling, chamber
transport, short-root lifts of sizes `1` and `2`, and functoriality `evenTypeAFoldedEquiv`.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--II.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace RootPairing

open Finset Function TauCeti TauCeti.DynkinType

private lemma isPos_of_two_smul_root_mem_posRootCone {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) (b : P.Base) {v : ι} (hv0 : P.root v ≠ 0)
    (htwo : (2 : K) • P.root v ∈ posRootCone P b) : b.IsPos v := by
  rcases mem_posRoots_or_mem_negRoots P b v with hpos | hneg
  · exact (mem_posRoots P b v).mp hpos
  · exfalso
    have hr := root_mem_posRootCone_of_mem_posRoots P b
      ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b v).mpr hneg)
    rw [root_reflectionPerm, reflection_apply_self] at hr
    have hneg2 : -((2 : K) • P.root v) ∈ posRootCone P b := by
      simpa [two_smul] using (posRootCone P b).nsmul_mem hr 2
    exact hv0 ((smul_eq_zero.mp
      ((isPointed_posRootCone P b).eq_zero_of_mem_of_neg_mem htwo hneg2)).resolve_left two_ne_zero)

section SimpleIndex

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {n : ℕ}

/-- The `k`-th Bourbaki-numbered folded simple root, given by the orbit sum of `e.symm ⟨k, _⟩`. -/
noncomputable def Base.evenTypeAFoldedSimpleIndex
    (b : P.Base) (σ : P.Aut) (e : b.support ≃ Fin (2 * n)) (k : Fin n) : P.foldedIndices σ :=
  ⟨P.orbitSum σ (e.symm ⟨k, by have := k.isLt; omega⟩), P.orbitSum_mem_foldedIndices σ _⟩

/-- Coercing `evenTypeAFoldedSimpleIndex` to `M` gives `P.orbitSum σ (e.symm ⟨k, _⟩)`. -/
@[simp] theorem Base.coe_evenTypeAFoldedSimpleIndex
    (b : P.Base) (σ : P.Aut) (e : b.support ≃ Fin (2 * n)) (k : Fin n) :
    ((b.evenTypeAFoldedSimpleIndex σ e k : P.foldedIndices σ) : M) =
      P.orbitSum σ (e.symm ⟨k, by have := k.isLt; omega⟩) := (rfl)

omit [Finite ι] in
private lemma exists_fin_of_mem_support
    (b : P.Base) (σ : P.Aut) (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (e : b.support ≃ Fin (2 * n)) (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)
    {j : ι} (hj : j ∈ b.support) :
    ∃ k : Fin n, (e.symm ⟨k, by have := k.isLt; omega⟩ : ι) = j ∨
      (e.symm ⟨k, by have := k.isLt; omega⟩ : ι) = σ.indexEquiv j := by
  let m := e ⟨j, hj⟩
  by_cases hlt : (m : ℕ) < n
  · exact ⟨⟨m, hlt⟩, Or.inl (congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩))⟩
  · refine ⟨⟨m.rev, by have := m.isLt; rw [Fin.val_rev]; omega⟩, Or.inr ?_⟩
    exact congrArg Subtype.val (e.injective
      (show e (e.symm _) = e ⟨σ.indexEquiv j, hσ j hj⟩ by
        rw [e.apply_symm_apply, hrev ⟨j, hj⟩ ⟨σ.indexEquiv j, hσ j hj⟩ rfl]))

end SimpleIndex

section Folding

variable {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
  [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) (σ : P.Aut) {n : ℕ}

omit [Finite ι] [P.IsRootSystem] [P.IsReduced] in
private lemma evenTypeAToZeroSumCartanEq (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (i j : b.support) :
    (typeAZeroSumBase K (2 * n)).cartanMatrix ((e.trans (typeAZeroSumSimpleEquiv K (2 * n))) i)
      ((e.trans (typeAZeroSumSimpleEquiv K (2 * n))) j) = b.cartanMatrix i j := by
  rw [Equiv.trans_apply, Equiv.trans_apply, cartanMatrix_typeAZeroSumBase, he,
    DynkinType.cartanMatrix_A]

private noncomputable def evenTypeAToZeroSumEquiv (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.Equiv (typeAZeroSumRootPairing K (2 * n)) :=
  b.equivOfCartanMatrixEq (typeAZeroSumBase K (2 * n))
    (e.trans (typeAZeroSumSimpleEquiv K (2 * n))) (evenTypeAToZeroSumCartanEq P b e he)

private lemma indexEquiv_evenTypeAToZeroSumEquiv_support (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
    (j : b.support) :
    (evenTypeAToZeroSumEquiv P b e he).indexEquiv j = typeAZeroSumSimplePair (2 * n) (e j) := by
  simp [evenTypeAToZeroSumEquiv]

variable (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)

include hσ he hrev

private lemma autCongr_evenTypeAToZeroSumEquiv :
    (evenTypeAToZeroSumEquiv P b e he).autCongr σ = typeAZeroSumRevAut K (2 * n) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he; set b₀ := typeAZeroSumBase K (2 * n)
  have hsupp (j : b₀.support) :
      (Φ.autCongr σ).indexEquiv j = (typeAZeroSumRevAut K (2 * n)).indexEquiv j := by
    let i : b.support := (e.trans (typeAZeroSumSimpleEquiv K (2 * n))).symm j
    let i' : b.support := ⟨σ.indexEquiv i, hσ i.1 i.2⟩
    have hj_eq : (j : TypeAIndex (2 * n)) = typeAZeroSumSimplePair (2 * n) (e i) := by
      rw [show e i = (typeAZeroSumSimpleEquiv K (2 * n)).symm j from e.apply_symm_apply _,
        ← coe_typeAZeroSumSimpleEquiv K, Equiv.apply_symm_apply]
    have hi : Φ.indexEquiv.symm j = i := Φ.indexEquiv.symm_apply_eq.mpr
      ((indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i).trans hj_eq.symm).symm
    rw [Equiv.indexEquiv_autCongr_apply, hi, indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i',
      hrev i i' rfl, ← indexEquiv_typeAZeroSumRevAut_simplePair K (2 * n) (e i), ← hj_eq]
  apply Equiv.weightHom_injective; apply LinearEquiv.toLinearMap_injective
  exact b₀.toWeightBasis.ext fun j ↦ by
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
        (evenTypeAToZeroSumEquiv P b e he).weightEquiv.toLinearMap :=
  LinearMap.ext fun x ↦ by
    have h := Equiv.autCongr_smul (evenTypeAToZeroSumEquiv P b e he) σ x
    rw [autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev] at h; exact h.symm

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
  set y := (evenTypeAFixedCoordEquiv K n).symm ((typeBBaseChangeRootSystem K n).root k)
  obtain ⟨p, hp⟩ := mem_foldedIndices.mp <|
    (mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices K n y).mp
      (by rw [LinearEquiv.apply_symm_apply]; exact Set.mem_range_self k)
  refine mem_foldedIndices.mpr ⟨Φ.indexEquiv.symm p, Φ.weightEquiv.injective ?_⟩
  rw [Equiv.weightEquiv_apply,
    weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
    Equiv.apply_symm_apply, hp, evenTypeAWeightEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.fixedSubmoduleCongr_symm_apply,
    Φ.weightEquiv.apply_symm_apply]

private noncomputable def evenTypeAIndexEquiv : Fin (2 * n ^ 2) ≃ P.foldedIndices σ :=
  Equiv.ofBijective
    (fun k ↦ ⟨(((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
      ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap) : M),
      mem_foldedIndices_of_root_typeB P b σ hσ e he hrev k⟩)
    ⟨fun k₁ k₂ hk ↦ by
      dsimp only at hk; have hval := congrArg Subtype.val hk
      exact (typeBBaseChangeRootSystem K n).root.injective
        ((evenTypeAWeightEquiv P b σ hσ e he hrev).symm.injective (Subtype.ext hval)),
      fun ⟨v, hv⟩ ↦ by
        obtain ⟨j, hj⟩ := mem_foldedIndices.mp hv
        set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
        set Φ := evenTypeAToZeroSumEquiv P b e he
        have hv_fix : v ∈ LinearMap.fixedSubmodule σ.weightMap :=
          hj ▸ P.orbitSum_mem_fixedSubmodule σ j
        obtain ⟨k, hk⟩ : Ψ ⟨v, hv_fix⟩ ∈ Set.range (typeBBaseChangeRootSystem K n).root := by
          dsimp [Ψ, evenTypeAWeightEquiv]
          rw [mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices, mem_foldedIndices]
          exact ⟨Φ.indexEquiv j, by
            rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
              ← hj]
            exact (weightMap_orbitSum Φ
              (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev) j).symm⟩
        exact ⟨k, Subtype.ext <| by
          dsimp only; rw [hk]; exact congrArg Subtype.val (Ψ.symm_apply_apply ⟨v, hv_fix⟩)⟩⟩

private lemma coe_evenTypeAIndexEquiv_apply (k : Fin (2 * n ^ 2)) :
    ((evenTypeAIndexEquiv P b σ hσ e he hrev k : P.foldedIndices σ) : M) =
      (((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
        ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap) : M) := rfl

/-- **The folded root system of `(P, b, σ)` of type `A (2 * n)` under diagram reversal.** -/
noncomputable def evenTypeAFoldedPairing :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  (typeBBaseChangeRootSystem K n).map (evenTypeAIndexEquiv P b σ hσ e he hrev)
    (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
    ((_root_.dotProductEquiv K (Fin n)).trans (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

/-- `evenTypeAFoldedPairing` is a root system. -/
instance instIsRootSystemEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsRootSystem := by
  delta evenTypeAFoldedPairing; infer_instance

/-- `evenTypeAFoldedPairing` is reduced. -/
instance instIsReducedEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsReduced := by
  delta evenTypeAFoldedPairing; infer_instance

/-- `evenTypeAFoldedPairing` is crystallographic. -/
instance instIsCrystallographicEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsCrystallographic := by
  delta evenTypeAFoldedPairing; infer_instance

/-- The bilinear pairing of `evenTypeAFoldedPairing` is dual evaluation `x ↦ φ ↦ φ x`. -/
@[simp] theorem toLinearMap_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (φ : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).toLinearMap x φ = φ x := by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set g := (_root_.dotProductEquiv K (Fin n)).trans Ψ.dualMap
  have hg : ∀ y : Fin n → K, g y x = y ⬝ᵥ Ψ x := fun y ↦ by simp [g]
  delta evenTypeAFoldedPairing
  rw [toLinearMap_map, LinearEquiv.symm_symm, toLinearMap_typeBBaseChangeRootSystem,
    dotProduct_comm, ← hg, LinearEquiv.apply_symm_apply]

/-- Each root of `evenTypeAFoldedPairing` coerces in `M` to its index `(v : M)`. -/
@[simp] theorem coe_root_evenTypeAFoldedPairing (v : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).root v :
      LinearMap.fixedSubmodule σ.weightMap) : M) = (v : M) := by
  delta evenTypeAFoldedPairing; rw [root_map]
  exact congrArg Subtype.val ((evenTypeAIndexEquiv P b σ hσ e he hrev).apply_symm_apply v)

/-- `P.foldedIndices σ` of even `A (2 * n)` under reversal has cardinality `2 * n ^ 2`. -/
theorem natCard_foldedIndices_evenTypeA : Nat.card (P.foldedIndices σ) = 2 * n ^ 2 := by
  rw [Nat.card_congr (evenTypeAIndexEquiv P b σ hσ e he hrev).symm, Nat.card_fin]

/-- No double `2 • (v : M)` of a folded root is an orbit sum, ruling out `BCₙ`. -/
theorem two_smul_notMem_foldedIndices_evenTypeA (v : P.foldedIndices σ) :
    (2 : K) • (v : M) ∉ P.foldedIndices σ := fun hmem ↦ by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let w : P.foldedIndices σ := ⟨(2 : K) • (v : M), hmem⟩
  have hrw : P'.root w = (2 : K) • P'.root v := Subtype.ext <| by
    rw [coe_root_evenTypeAFoldedPairing, SetLike.val_smul, coe_root_evenTypeAFoldedPairing]
  have hdep : ¬ LinearIndependent K ![P'.root v, P'.root w] := fun hli ↦ by
    have h := (Fintype.linearIndependent_iff.mp hli) ![2, -1]
      (by simp [Fin.sum_univ_two, hrw, add_neg_cancel]) 0
    norm_num at h
  have hv_ne : P'.root v ≠ 0 := fun hz ↦ zero_notMem_foldedIndices hσ <| by
    have h0 : (v : M) = 0 := by
      rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev v, hz, ZeroMemClass.coe_zero]
    exact h0 ▸ v.2
  rcases IsReduced.eq_or_eq_neg (P := P') v w hdep with heq | hneg
  · have h1 : (1 : K) • P'.root v = 0 := by
      rw [show (1 : K) = 2 - 1 by norm_num, sub_smul, one_smul, ← hrw, heq, sub_self]
    exact hv_ne (by simpa using h1)
  · have h3 : (3 : K) • P'.root v = 0 := by
      rw [show (3 : K) = 2 + 1 by norm_num, add_smul, one_smul, ← hrw, hneg, add_neg_cancel]
    exact hv_ne ((smul_eq_zero.mp h3).resolve_left (by norm_num))

/-- The folded pairing depends only on `(P, σ)`, not on the choice of base or diagram labelling. -/
theorem evenTypeAFoldedPairing_congr
    (b₂ : P.Base) {n₂ : ℕ} (hσ₂ : ∀ i ∈ b₂.support, σ.indexEquiv i ∈ b₂.support)
    (e₂ : b₂.support ≃ Fin (2 * n₂))
    (he₂ : ∀ i j, b₂.cartanMatrix i j = (DynkinType.A (2 * n₂)).cartanMatrix (e₂ i) (e₂ j))
    (hrev₂ : ∀ i j : b₂.support, σ.indexEquiv i = j → e₂ j = (e₂ i).rev) :
    P.evenTypeAFoldedPairing b σ hσ e he hrev =
      P.evenTypeAFoldedPairing b₂ σ hσ₂ e₂ he₂ hrev₂ :=
  IsRootSystem.ext (by ext; simp) (by ext : 1; exact Subtype.ext (by simp))

private noncomputable def evenTypeAFoldedEquivTypeB :
    (typeBBaseChangeRootSystem K n).Equiv (P.evenTypeAFoldedPairing b σ hσ e he hrev) := by
  delta evenTypeAFoldedPairing
  exact (typeBBaseChangeRootSystem K n).equivMap (evenTypeAIndexEquiv P b σ hσ e he hrev)
    (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
    ((_root_.dotProductEquiv K (Fin n)).trans (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

private lemma indexEquiv_evenTypeAFoldedEquivTypeB :
    (evenTypeAFoldedEquivTypeB P b σ hσ e he hrev).indexEquiv =
      evenTypeAIndexEquiv P b σ hσ e he hrev := by
  delta evenTypeAFoldedEquivTypeB evenTypeAFoldedPairing; exact indexEquiv_equivMap ..

private lemma coroot'_evenTypeAFoldedPairing_eq (v : P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x =
      (typeBBaseChangeRootSystem K n).coroot' ((evenTypeAIndexEquiv P b σ hσ e he hrev).symm v)
        (evenTypeAWeightEquiv P b σ hσ e he hrev x) := by
  delta evenTypeAFoldedPairing; rw [coroot'_map, LinearEquiv.symm_symm]

private lemma evenTypeAIndexEquiv_typeBSimpleIndex (k : Fin n) :
    evenTypeAIndexEquiv P b σ hσ e he hrev (typeBSimpleIndex n k) =
      b.evenTypeAFoldedSimpleIndex σ e k := by
  have hk := k.isLt
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set Φ := evenTypeAToZeroSumEquiv P b e he
  let jk : b.support := e.symm ⟨k, by omega⟩
  have hΨ : Ψ ⟨P.orbitSum σ jk, P.orbitSum_mem_fixedSubmodule σ jk⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
    dsimp [Ψ, evenTypeAWeightEquiv]; rw [← evenTypeAFixedCoordEquiv_simpleOrbitSum K n k]
    congr 1; apply Subtype.ext
    rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_evenTypeAIndexEquiv_apply, Base.coe_evenTypeAFoldedSimpleIndex, ← hΨ]
  exact congrArg Subtype.val (Ψ.symm_apply_apply _)

variable {P}

/-- **The folded base of `(P, b, σ)`,** of Cartan type `B n`. -/
noncomputable def Base.evenTypeAFoldedBase :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Base :=
  (typeBBaseChangeBase K n).map (evenTypeAFoldedEquivTypeB P b σ hσ e he hrev)

/-- `v ∈ (evenTypeAFoldedBase).support` iff `v` is one of `evenTypeAFoldedSimpleIndex`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff_exists_fin (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ k : Fin n, v = b.evenTypeAFoldedSimpleIndex σ e k := by
  classical
  rw [evenTypeAFoldedBase, Base.support_map_eq, mem_image]
  refine ⟨?_, fun ⟨k, hk⟩ ↦ ⟨typeBSimpleIndex n k,
    (mem_support_typeBBaseChangeBase_iff K n _).mpr ((typeBSimpleIndex_val k).symm ▸ k.isLt),
    by rw [hk, indexEquiv_evenTypeAFoldedEquivTypeB, evenTypeAIndexEquiv_typeBSimpleIndex]⟩⟩
  rintro ⟨m, hm, rfl⟩; rw [mem_support_typeBBaseChangeBase_iff] at hm
  refine ⟨⟨m, hm⟩, ?_⟩; rw [indexEquiv_evenTypeAFoldedEquivTypeB]
  conv_lhs => rw [show m = typeBSimpleIndex n ⟨m, hm⟩ from Fin.ext (by simp)]
  exact evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev ⟨m, hm⟩

/-- `b.evenTypeAFoldedSimpleIndex σ e k` belongs to the support of `evenTypeAFoldedBase`. -/
theorem Base.evenTypeAFoldedSimpleIndex_mem_support (k : Fin n) :
    b.evenTypeAFoldedSimpleIndex σ e k ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support :=
  (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev _).mpr ⟨k, rfl⟩

/-- **Simple roots of the folded base:** orbit sums of simple roots of `b`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ j ∈ b.support, P.orbitSum σ j = (v : M) := by
  rw [b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev]
  refine ⟨by rintro ⟨k, rfl⟩; exact ⟨_, (e.symm ⟨k, by have := k.isLt; omega⟩).2, rfl⟩, ?_⟩
  rintro ⟨j, hj, hv⟩
  rcases exists_fin_of_mem_support b σ hσ e hrev hj with ⟨k, hkj | hkj⟩
  · exact ⟨k, Subtype.ext (by rw [coe_evenTypeAFoldedSimpleIndex, hkj, hv])⟩
  · exact ⟨k, Subtype.ext <| by
      rw [coe_evenTypeAFoldedSimpleIndex, hkj, P.orbitSum_indexEquiv, hv]⟩

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
  have hij : i = j := f.injective (Fin.ext (by
    have := (f i).isLt; have := (f j).isLt; change _ < 1 at *; omega))
  subst hij; rw [hf]
  simp [DynkinType.cartanMatrix_B, DynkinType.cartanMatrix_A, CartanMatrix.B, CartanMatrix.A]

/-- **Simple-coroot evaluation on fixed weights:** scales by `1` for `k + 1 < n` and `2` for
`k + 1 = n`. -/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex (k : Fin n)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x =
      (if (k : ℕ) + 1 = n then 2 else 1) *
        P.coroot' (e.symm ⟨k, by have := k.isLt; omega⟩) (x : M) := by
  have hk := k.isLt
  set Φ := evenTypeAToZeroSumEquiv P b e he; let jk : b.support := e.symm ⟨k, by omega⟩
  have hidx : (evenTypeAIndexEquiv P b σ hσ e he hrev).symm
      (b.evenTypeAFoldedSimpleIndex σ e k) = typeBSimpleIndex n k :=
    (evenTypeAIndexEquiv P b σ hσ e he hrev).symm_apply_eq.mpr
      (evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev k).symm
  rw [coroot'_evenTypeAFoldedPairing_eq, hidx, coroot'_typeBBaseChangeRootSystem_simpleIndex]
  dsimp only [evenTypeAWeightEquiv, LinearEquiv.trans_apply]
  rw [evenTypeAFixedCoordEquiv_apply, LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk,
    Equiv.weightEquiv_apply,
    show typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ = Φ.indexEquiv jk by
      rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply],
    Hom.coroot'_indexEquiv_weightMap]

/-- Off the middle orbit (`k + 1 < n`), the `k`-th folded simple coroot restricts without scaling.
-/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex_of_lt {k : Fin n}
    (hk : (k : ℕ) + 1 < n) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x = P.coroot' (e.symm ⟨k, by omega⟩) (x : M) := by
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, ite_eq_right (by omega), one_mul]

/-- At the middle orbit (`k + 1 = n`), the folded simple coroot restricts twice the middle coroot.
-/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex_of_eq {k : Fin n}
    (hk : (k : ℕ) + 1 = n) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x = 2 * P.coroot' (e.symm ⟨k, by omega⟩) (x : M) := by
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, ite_eq_left hk]

omit [CharZero K] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] he in
private lemma root_add_root_indexEquiv_eq_orbitSum {i : ι} (hi : i ∈ b.support) :
    P.root i + P.root (σ.indexEquiv i) = P.orbitSum σ i := by
  classical
  let i' : b.support := ⟨σ.indexEquiv i, hσ i hi⟩
  let i'' : b.support := ⟨σ.indexEquiv i', hσ i'.1 i'.2⟩
  have h1 : e i' = (e ⟨i, hi⟩).rev := hrev ⟨i, hi⟩ i' rfl
  have hinv : σ.indexEquiv (σ.indexEquiv i) = i := congrArg Subtype.val
    (e.injective (show e i'' = e ⟨i, hi⟩ by rw [hrev i' i'' rfl, h1, Fin.rev_rev]))
  have hne : σ.indexEquiv i ≠ i := fun hc ↦ by
    have hval := congrArg (Fin.val ∘ e) (Subtype.ext hc : i' = ⟨i, hi⟩)
    dsimp at hval; rw [h1, Fin.val_rev] at hval; have := (e ⟨i, hi⟩).isLt; omega
  have horb : P.orbitIndices σ i = {i, σ.indexEquiv i} := by
    ext q; rw [mem_orbitIndices_iff_exists_pow, mem_insert, mem_singleton]
    refine ⟨?_, by rintro (rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, by simp⟩]⟩
    rintro ⟨m, rfl⟩; induction m with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.elim (fun h ↦ Or.inr (by rw [h])) (fun h ↦ Or.inl (by rw [h, hinv]))
  rw [orbitSum_def, horb, sum_pair hne.symm]

private lemma isPos_evenTypeAFoldedBase_of_isPos {j : ι} {w : P.foldedIndices σ}
    (hj : b.IsPos j) (hw : P.orbitSum σ j = (w : M)) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos w := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let b' := b.evenTypeAFoldedBase σ hσ e he hrev
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (hw ▸ P.orbitSum_mem_posRootCone hσ hj)
  have hw_fix : σ.weightMap (w : M) = (w : M) :=
    LinearMap.mem_fixedSubmodule_iff.mp (hw ▸ P.orbitSum_mem_fixedSubmodule σ j)
  have hvec : (2 : K) • (w : M) = ∑ i ∈ b.support.attach, c i.1 • P.orbitSum σ i.1 := by
    calc (2 : K) • (w : M) = (w : M) + σ.weightMap (w : M) := by rw [hw_fix, two_smul]
      _ = ∑ i ∈ b.support, c i • (P.root i + P.root (σ.indexEquiv i)) := by
            rw [hc, map_sum, ← sum_add_distrib]
            exact sum_congr rfl fun i _ ↦ by rw [map_nsmul, Hom.root_weightMap_apply, ← nsmul_add]
      _ = ∑ i ∈ b.support.attach, c i.1 • P.orbitSum σ i.1 := by
            rw [← sum_attach]; exact sum_congr rfl fun i _ ↦ by
              rw [root_add_root_indexEquiv_eq_orbitSum b σ hσ e hrev i.2]
  have htwo : (2 : K) • P'.root w ∈ posRootCone P' b' := by
    rw [show (2 : K) • P'.root w = ∑ i ∈ b.support.attach, c i.1 •
        P'.root ⟨P.orbitSum σ i.1, P.orbitSum_mem_foldedIndices σ i.1⟩ from Subtype.ext <| by
      rw [SetLike.val_smul, coe_root_evenTypeAFoldedPairing, hvec, Submodule.coe_sum]
      exact sum_congr rfl fun i _ ↦ by
        rw [Submodule.coe_smul_of_tower, coe_root_evenTypeAFoldedPairing]]
    refine (posRootCone P' b').sum_mem fun i _ ↦ (posRootCone P' b').nsmul_mem ?_ _
    exact root_mem_posRootCone_of_mem_posRoots P' b' (support_subset_posRoots P' b' <|
      (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr ⟨i.1, i.2, rfl⟩)
  have hw0 : P'.root w ≠ 0 := fun h0 ↦ zero_notMem_foldedIndices hσ <| by
    have hcoe0 : (w : M) = 0 := by
      rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev w, h0, ZeroMemClass.coe_zero]
    exact hcoe0 ▸ w.2
  exact isPos_of_two_smul_root_mem_posRootCone P' b' hw0 htwo

/-- **Positive roots of the folded base:** orbit sums of positive roots of `b`. -/
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
    exact reflectionPerm_self_notMem_posRoots P' b' ((mem_posRoots P' b' v).mpr hv)
      ((mem_posRoots P' b' _).mpr
        (isPos_evenTypeAFoldedBase_of_isPos b σ hσ e he hrev hj' hneg_orb))

/-- **Forward simple-coroot integrality on fixed weights.** -/
theorem Base.exists_int_coroot'_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (hint : ∀ j ∈ b.support, ∃ z : ℤ, P.coroot' j (x : M) = z) :
    ∀ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support,
      ∃ z : ℤ, (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x = z := fun v hv ↦ by
  obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
  obtain ⟨z, hz⟩ := hint _ (e.symm ⟨k, by have := k.isLt; omega⟩).2
  refine ⟨(if (k : ℕ) + 1 = n then 2 else 1) * z, ?_⟩
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, hz, Int.cast_mul]
  congr 1; split_ifs <;> norm_num

private lemma exists_pos_lift_shortSimple_of_spec {k : Fin n} (hk : (k : ℕ) + 1 = n)
    (p : TypeAIndex (2 * n)) (m : ℕ)
    (hp : (typeAZeroSumBase K (2 * n)).IsPos p ∧
      #((typeAZeroSumRootPairing K (2 * n)).orbitIndices (typeAZeroSumRevAut K (2 * n)) p) = m ∧
      (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p =
        evenTypeABasisVec K n k) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = m ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) := by
  obtain ⟨hp_pos, hp_card, hp_sum⟩ := hp
  set Φ := evenTypeAToZeroSumEquiv P b e he; let j := Φ.indexEquiv.symm p
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) :=
    TauCeti.map_equivOfCartanMatrixEq b (typeAZeroSumBase K (2 * n)) _ _
  refine ⟨j, (b.isPos_map_iff Φ j).mp (by simpa [hb_map, j] using hp_pos), ?_, ?_⟩
  · have hcard := congrArg Finset.card
      (map_orbitIndices Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev) j)
    rw [Finset.card_map, Equiv.apply_symm_apply] at hcard; exact hcard.trans hp_card
  · apply Φ.weightEquiv.injective
    rw [Equiv.weightEquiv_apply, Equiv.weightEquiv_apply,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      Base.coe_evenTypeAFoldedSimpleIndex,
      weightMap_orbitSum Φ (indexEquiv_evenTypeAToZeroSumEquiv_comm P b σ hσ e he hrev),
      Equiv.apply_symm_apply, hp_sum,
      indexEquiv_evenTypeAToZeroSumEquiv_support P b e he (e.symm ⟨k, by omega⟩),
      Equiv.apply_symm_apply, orbitSum_typeAZeroSumRevAut_simplePair, dite_eq_right (by omega)]

/-- The short simple folded root (`k + 1 = n`) lifts to a `σ`-fixed positive root of `b`. -/
theorem Base.exists_fixed_pos_lift_shortSimple {k : Fin n} (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 1 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) :=
  exists_pos_lift_shortSimple_of_spec b σ hσ e he hrev hk _ 1 (evenTypeAFixedShortLift_spec K n k)

/-- The short simple folded root (`k + 1 = n`) lifts to a positive root of `b` of orbit size `2`. -/
theorem Base.exists_paired_pos_lift_shortSimple {k : Fin n} (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 2 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) :=
  exists_pos_lift_shortSimple_of_spec b σ hσ e he hrev hk _ 2 (evenTypeAPairedShortLift_spec K n k)

end Folding

section OrderedField

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  (b : P.Base) (σ : P.Aut) {n : ℕ} (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)

include hσ he hrev in
private lemma exists_folded_coroot'_eq_pos_mul (x : LinearMap.fixedSubmodule σ.weightMap)
    {j : ι} (hj : j ∈ b.support) :
    ∃ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support, ∃ c : K, 0 < c ∧
      (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x = c * P.coroot' j (x : M) := by
  obtain ⟨k, hkj⟩ := exists_fin_of_mem_support b σ hσ e hrev hj
  refine ⟨b.evenTypeAFoldedSimpleIndex σ e k,
    b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev k,
    if (k : ℕ) + 1 = n then 2 else 1, by split_ifs <;> norm_num, ?_⟩
  rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
  rcases hkj with hkj | hkj
  · rw [hkj]
  · conv_lhs =>
      rw [hkj, ← LinearMap.mem_fixedSubmodule_iff.mp x.2, Hom.coroot'_indexEquiv_weightMap]

/-- **Closed dominant chamber transport on fixed weights.** -/
theorem Base.mem_dominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (x : M) ∈ P.dominantChamber b ↔
      x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).dominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) := by
  simp only [mem_dominantChamber]
  refine ⟨fun hx v hv ↦ ?_, fun hx j hj ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    exact mul_nonneg (by split_ifs <;> norm_num) (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).2)
  · obtain ⟨v, hv, c, hc, hcv⟩ := exists_folded_coroot'_eq_pos_mul b σ hσ e he hrev x hj
    exact (mul_nonneg_iff_of_pos_left hc).mp (hcv ▸ hx v hv)

/-- **Open dominant chamber transport on fixed weights.** -/
theorem Base.mem_openDominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (x : M) ∈ P.openDominantChamber b ↔
      x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).openDominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) := by
  simp only [mem_openDominantChamber]
  refine ⟨fun hx v hv ↦ ?_, fun hx j hj ↦ ?_⟩
  · obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    exact mul_pos (by split_ifs <;> norm_num) (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).2)
  · obtain ⟨v, hv, c, hc, hcv⟩ := exists_folded_coroot'_eq_pos_mul b σ hσ e he hrev x hj
    exact (mul_pos_iff_of_pos_left hc).mp (hcv ▸ hx v hv)

end OrderedField

section FoldedIndicesCongr

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} [Finite ι] {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι₂]

private lemma weightMap_orbitSum_of_autCongr {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) (i : ι) :
    φ.weightMap (P.orbitSum σ i) = P₂.orbitSum σ₂ (φ.indexEquiv i) :=
  weightMap_orbitSum φ
    (fun j ↦ by rw [← hφ, Equiv.indexEquiv_autCongr_apply, _root_.Equiv.symm_apply_apply]) i

private lemma mem_foldedIndices_weightMap {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) (v : P.foldedIndices σ) :
    φ.weightMap (v : M) ∈ P₂.foldedIndices σ₂ := by
  obtain ⟨i, hi⟩ := mem_foldedIndices.mp v.2
  exact mem_foldedIndices.mpr ⟨φ.indexEquiv i, hi ▸ (weightMap_orbitSum_of_autCongr φ hφ i).symm⟩

/-- An intertwining equivalence `φ : P.Equiv P₂` carries `P.foldedIndices σ` onto
`P₂.foldedIndices σ₂`. -/
noncomputable def foldedIndicesCongr {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) : P.foldedIndices σ ≃ P₂.foldedIndices σ₂ where
  toFun v := ⟨φ.weightMap (v : M), mem_foldedIndices_weightMap φ hφ v⟩
  invFun w := ⟨(Equiv.symm P P₂ φ).weightMap (w : M₂), mem_foldedIndices_weightMap
    (Equiv.symm P P₂ φ) (by rw [← hφ]; ext x <;> simp [Equiv.autCongr_apply]) w⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

/-- Coercing `foldedIndicesCongr φ hφ v` applies `φ.weightMap` to `(v : M)`. -/
@[simp] theorem coe_foldedIndicesCongr_apply {σ : P.Aut} {σ₂ : P₂.Aut}
    (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) (v : P.foldedIndices σ) :
    ((foldedIndicesCongr φ hφ v : P₂.foldedIndices σ₂) : M₂) = φ.weightMap (v : M) := (rfl)

end FoldedIndicesCongr

section Functoriality

variable {ι ι₂ K M N M₂ N₂ : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
  {P₂ : RootPairing ι₂ K M₂ N₂} [Finite ι₂] [P₂.IsRootSystem] [P₂.IsReduced] [P₂.IsCrystallographic]
  (b : P.Base) (σ : P.Aut) {n : ℕ} (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (e : b.support ≃ Fin (2 * n))
  (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j))
  (hrev : ∀ i j : b.support, σ.indexEquiv i = j → e j = (e i).rev)
  (b₂ : P₂.Base) (σ₂ : P₂.Aut) {n₂ : ℕ} (hσ₂ : ∀ i ∈ b₂.support, σ₂.indexEquiv i ∈ b₂.support)
  (e₂ : b₂.support ≃ Fin (2 * n₂))
  (he₂ : ∀ i j, b₂.cartanMatrix i j = (DynkinType.A (2 * n₂)).cartanMatrix (e₂ i) (e₂ j))
  (hrev₂ : ∀ i j : b₂.support, σ₂.indexEquiv i = j → e₂ j = (e₂ i).rev)

/-- **Functoriality of the folded root system** under intertwining equivalences `φ : P.Equiv P₂`. -/
noncomputable def evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Equiv
      (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂) :=
  Equiv.mk' (P.evenTypeAFoldedPairing b σ hσ e he hrev)
    (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂)
    (φ.weightEquiv.fixedSubmoduleCongr <| LinearMap.ext fun x ↦ by
      have h := Equiv.autCongr_smul φ σ x; rw [hφ] at h; exact h.symm)
    (foldedIndicesCongr φ hφ)
    fun v ↦ Subtype.ext <| by
      rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
        coe_root_evenTypeAFoldedPairing, coe_root_evenTypeAFoldedPairing,
        coe_foldedIndicesCongr_apply]

/-- The weight map of `evenTypeAFoldedEquiv` restricts `φ.weightMap` to fixed submodules. -/
@[simp] theorem coe_weightMap_evenTypeAFoldedEquiv_apply (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).weightMap x :
      LinearMap.fixedSubmodule σ₂.weightMap) : M₂) = φ.weightMap (x : M) := by
  dsimp only [evenTypeAFoldedEquiv, Equiv.mk']
  rw [LinearEquiv.coe_coe, LinearEquiv.fixedSubmoduleCongr_apply, Equiv.weightEquiv_apply]

/-- The index equivalence of `evenTypeAFoldedEquiv` is `foldedIndicesCongr φ hφ`. -/
@[simp] theorem indexEquiv_evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).indexEquiv =
      foldedIndicesCongr φ hφ := (rfl)

/-- When `φ` maps `b` to `b₂`, `evenTypeAFoldedEquiv` maps the folded base of `b` to that of `b₂`.
-/
theorem Base.map_evenTypeAFoldedBase (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂)
    (hb : b.map φ = b₂) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).map
      (evenTypeAFoldedEquiv b σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ) =
      b₂.evenTypeAFoldedBase σ₂ hσ₂ e₂ he₂ hrev₂ := by
  classical
  ext w; rw [Base.support_map_eq, mem_image]
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨j, hj, hvj⟩ := (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev v).mp hv
    refine (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ _).mpr
      ⟨φ.indexEquiv j, by rw [← hb, Base.support_map_eq]; exact mem_image_of_mem _ hj, ?_⟩
    rw [indexEquiv_evenTypeAFoldedEquiv, coe_foldedIndicesCongr_apply, ← hvj]
    exact (weightMap_orbitSum_of_autCongr φ hφ j).symm
  · obtain ⟨j₂, hj₂, hwj⟩ := (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ w).mp hw
    rw [← hb, Base.support_map_eq, mem_image] at hj₂; obtain ⟨j, hj, rfl⟩ := hj₂
    let v : P.foldedIndices σ := ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩
    refine ⟨v, (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev v).mpr ⟨j, hj, rfl⟩,
      Subtype.ext ?_⟩
    rw [indexEquiv_evenTypeAFoldedEquiv, coe_foldedIndicesCongr_apply, ← hwj]
    exact weightMap_orbitSum_of_autCongr φ hφ j

end Functoriality

end RootPairing
