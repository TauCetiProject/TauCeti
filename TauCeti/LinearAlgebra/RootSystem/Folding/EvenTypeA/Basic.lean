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
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Folding even type-`A` root systems under diagram reversal

For any finite reduced crystallographic root system `P` of Cartan type `A (2 * n)` over a
characteristic-zero field `K` with base `b`, Bourbaki labelling `e : b.support ≃ Fin (2 * n)`, and
diagram-reversing automorphism `σ : P.Aut`, transporting the coordinate model shows that
`P.foldedIndices σ` forms a reduced crystallographic root system `evenTypeAFoldedPairing` and base
`Base.evenTypeAFoldedBase` of Cartan type `B n`. It also gives general-index formulas for the
folded coroots (`coroot_evenTypeAFoldedPairing`, `coroot'_evenTypeAFoldedPairing`), root-coroot
pairings (`pairing_evenTypeAFoldedPairing`, `pairingIn_evenTypeAFoldedPairing`), and reflections
(`coe_reflection_evenTypeAFoldedPairing`, `coe_reflectionPerm_evenTypeAFoldedPairing`, plus the
explicit Weyl-element formulas for fixed, orthogonal, and adjacent `σ`-orbits), as well as
simple-coroot scaling, chamber transport, short-root lifts of sizes `1` and `2`, and functoriality
`Base.evenTypeAFoldedEquiv`.

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--II.
* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, page 1.
-/

public section

namespace RootPairing

open Finset Function TauCeti TauCeti.DynkinType

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
    exact congrArg Subtype.val (e.symm_apply_eq.mpr
      (hrev ⟨j, hj⟩ ⟨σ.indexEquiv j, hσ j hj⟩ rfl).symm)

end SimpleIndex

section Folding

variable {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
  [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) (σ : P.Aut) {n : ℕ}

private noncomputable def evenTypeAToZeroSumEquiv (e : b.support ≃ Fin (2 * n))
    (he : ∀ i j, b.cartanMatrix i j = (DynkinType.A (2 * n)).cartanMatrix (e i) (e j)) :
    P.Equiv (typeAZeroSumRootPairing K (2 * n)) :=
  b.equivOfCartanMatrixEq (typeAZeroSumBase K (2 * n))
    (e.trans (typeAZeroSumSimpleEquiv K (2 * n))) fun i j ↦ by
      rw [Equiv.trans_apply, Equiv.trans_apply, cartanMatrix_typeAZeroSumBase, he,
        DynkinType.cartanMatrix_A]

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
    let i' : b.support := ⟨σ.indexEquiv i, hσ i.val i.property⟩
    have hj_eq : (j : TypeAIndex (2 * n)) = typeAZeroSumSimplePair (2 * n) (e i) := by
      dsimp only [i]; rw [Equiv.symm_trans_apply, e.apply_symm_apply,
        ← coe_typeAZeroSumSimpleEquiv K, Equiv.apply_symm_apply]
    have hi : Φ.indexEquiv.symm j = i := Φ.indexEquiv.symm_apply_eq.mpr
      ((indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i).trans hj_eq.symm).symm
    rw [Equiv.indexEquiv_autCongr_apply, hi, indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i',
      hrev i i' rfl, ← indexEquiv_typeAZeroSumRevAut_simplePair K (2 * n) (e i), ← hj_eq]
  exact Equiv.weightHom_injective _ <| LinearEquiv.toLinearMap_injective <| b₀.toWeightBasis.ext
    fun j ↦ by simp only [Equiv.weightHom_apply, LinearEquiv.coe_coe, Equiv.weightEquiv_apply,
      b₀.toWeightBasis_apply, Hom.root_weightMap_apply, hsupp j]

private noncomputable def evenTypeAWeightEquiv :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[K] (Fin n → K) :=
  ((evenTypeAToZeroSumEquiv P b e he).weightEquiv.fixedSubmoduleCongr <| LinearMap.ext fun x ↦ by
    have h := Equiv.autCongr_smul (evenTypeAToZeroSumEquiv P b e he) σ x
    rw [autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev] at h; exact h.symm).trans
    (evenTypeAFixedCoordEquiv K n)

private lemma mem_range_root_typeB_iff_mem_foldedIndices
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    evenTypeAWeightEquiv P b σ hσ e he hrev x ∈ Set.range (typeBBaseChangeRootSystem K n).root ↔
      (x : M) ∈ P.foldedIndices σ := by
  dsimp only [evenTypeAWeightEquiv, LinearEquiv.trans_apply]
  rw [mem_range_root_typeBBaseChangeRootSystem_iff_mem_foldedIndices,
    LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
    Equiv.mem_foldedIndices_weightMap_iff _ (autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev)]

private noncomputable def evenTypeAIndexEquiv : Fin (2 * n ^ 2) ≃ P.foldedIndices σ :=
  Equiv.ofBijective
    (fun k ↦ ⟨(((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
        ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap) : M),
      (mem_range_root_typeB_iff_mem_foldedIndices P b σ hσ e he hrev _).mp
        (by rw [LinearEquiv.apply_symm_apply]; exact Set.mem_range_self k)⟩)
    ⟨fun _ _ hk ↦ (typeBBaseChangeRootSystem K n).root.injective
      ((evenTypeAWeightEquiv P b σ hσ e he hrev).symm.injective
        (Subtype.ext (Subtype.mk.inj hk))),
      fun ⟨v, hv⟩ ↦ by
        obtain ⟨j, hj⟩ := mem_foldedIndices.mp hv
        set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
        let x : LinearMap.fixedSubmodule σ.weightMap :=
          ⟨v, hj ▸ P.orbitSum_mem_fixedSubmodule σ j⟩
        obtain ⟨k, hk⟩ := (mem_range_root_typeB_iff_mem_foldedIndices P b σ hσ e he hrev x).mpr hv
        exact ⟨k, Subtype.ext <| by
          dsimp only; rw [hk]; exact congrArg Subtype.val (Ψ.symm_apply_apply x)⟩⟩

/-- **The folded root system of `(P, b, σ)` of type `A (2 * n)` under diagram reversal.** -/
noncomputable def evenTypeAFoldedPairing :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  (typeBBaseChangeRootSystem K n).map (evenTypeAIndexEquiv P b σ hσ e he hrev)
    (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
    ((_root_.dotProductEquiv K (Fin n)).trans (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

private lemma evenTypeAFoldedPairing_eq_map :
    P.evenTypeAFoldedPairing b σ hσ e he hrev =
      (typeBBaseChangeRootSystem K n).map (evenTypeAIndexEquiv P b σ hσ e he hrev)
        (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
        ((_root_.dotProductEquiv K (Fin n)).trans
          (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap) := rfl

/-- `evenTypeAFoldedPairing` is a root system. -/
instance instIsRootSystemEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsRootSystem := by
  rw [evenTypeAFoldedPairing_eq_map]; infer_instance

/-- `evenTypeAFoldedPairing` is reduced. -/
instance instIsReducedEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsReduced := by
  rw [evenTypeAFoldedPairing_eq_map]; infer_instance

/-- `evenTypeAFoldedPairing` is crystallographic. -/
instance instIsCrystallographicEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsCrystallographic := by
  rw [evenTypeAFoldedPairing_eq_map]; infer_instance

/-- The bilinear pairing of `evenTypeAFoldedPairing` is dual evaluation `x ↦ φ ↦ φ x`. -/
@[simp] theorem toLinearMap_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (φ : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).toLinearMap x φ = φ x := by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  set g := (_root_.dotProductEquiv K (Fin n)).trans Ψ.dualMap
  have hg : ∀ y : Fin n → K, g y x = y ⬝ᵥ Ψ x := fun y ↦ by simp [g]
  rw [evenTypeAFoldedPairing_eq_map, toLinearMap_map, LinearEquiv.symm_symm,
    toLinearMap_typeBBaseChangeRootSystem, dotProduct_comm, ← hg, LinearEquiv.apply_symm_apply]

/-- Each root of `evenTypeAFoldedPairing` coerces in `M` to its index `(v : M)`. -/
@[simp] theorem coe_root_evenTypeAFoldedPairing (v : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).root v :
      LinearMap.fixedSubmodule σ.weightMap) : M) = (v : M) := by
  rw [evenTypeAFoldedPairing_eq_map, root_map]
  exact congrArg Subtype.val ((evenTypeAIndexEquiv P b σ hσ e he hrev).apply_symm_apply v)

/-- `P.foldedIndices σ` of even `A (2 * n)` under reversal has cardinality `2 * n ^ 2`. -/
theorem natCard_foldedIndices_evenTypeA : Nat.card (P.foldedIndices σ) = 2 * n ^ 2 := by
  rw [Nat.card_congr (evenTypeAIndexEquiv P b σ hσ e he hrev).symm, Nat.card_fin]

/-- No double `2 • (v : M)` of a folded root is an orbit sum, ruling out `BCₙ`. -/
theorem two_smul_notMem_foldedIndices_evenTypeA (v : P.foldedIndices σ) :
    (2 : K) • (v : M) ∉ P.foldedIndices σ := fun hmem ↦ by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  have : HasUniqueDiv (LinearMap.fixedSubmodule σ.weightMap) := .of_isTorsionFree K _
  refine P'.nsmul_notMem_range_root (n := 2) (i := v) ⟨⟨(2 : K) • (v : M), hmem⟩, Subtype.ext ?_⟩
  rw [coe_root_evenTypeAFoldedPairing, Submodule.coe_smul_of_tower,
    coe_root_evenTypeAFoldedPairing, ← Nat.cast_smul_eq_nsmul K, Nat.cast_ofNat]

/-- The folded pairing depends only on `(P, σ)`, not on the choice of base or diagram labelling. -/
theorem evenTypeAFoldedPairing_congr
    (b₂ : P.Base) {n₂ : ℕ} (hσ₂ : ∀ i ∈ b₂.support, σ.indexEquiv i ∈ b₂.support)
    (e₂ : b₂.support ≃ Fin (2 * n₂))
    (he₂ : ∀ i j, b₂.cartanMatrix i j = (DynkinType.A (2 * n₂)).cartanMatrix (e₂ i) (e₂ j))
    (hrev₂ : ∀ i j : b₂.support, σ.indexEquiv i = j → e₂ j = (e₂ i).rev) :
    P.evenTypeAFoldedPairing b σ hσ e he hrev =
      P.evenTypeAFoldedPairing b₂ σ hσ₂ e₂ he₂ hrev₂ :=
  IsRootSystem.ext (by ext; simp) (by ext : 1; exact Subtype.ext (by simp))

private lemma indexEquiv_evenTypeAToZeroSumEquiv_comp_aut (r : ι) :
    (evenTypeAToZeroSumEquiv P b e he).indexEquiv (σ.indexEquiv r) =
      finDistinctPairsRevSwap (2 * n + 1) ((evenTypeAToZeroSumEquiv P b e he).indexEquiv r) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  have h := Equiv.indexEquiv_autCongr_apply Φ σ (Φ.indexEquiv r)
  rw [autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev, indexEquiv_typeAZeroSumRevAut,
    Equiv.symm_apply_apply] at h
  exact h.symm

private lemma indexEquiv_indexEquiv (j : ι) : σ.indexEquiv (σ.indexEquiv j) = j := by
  apply (evenTypeAToZeroSumEquiv P b e he).indexEquiv.injective
  rw [indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev,
    indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev,
    finDistinctPairsRevSwap_finDistinctPairsRevSwap]

/-- Every root `j` of even type `A (2 * n)` under diagram reversal is either fixed by `σ`,
orthogonal to `σ.indexEquiv j`, or adjacent to `σ.indexEquiv j` with
`P.pairingIn ℤ (σ.indexEquiv j) j = -1`. -/
theorem indexEquiv_eq_self_or_pairingIn_eq_zero_or_neg_one_evenTypeA (j : ι) :
    σ.indexEquiv j = j ∨ P.pairingIn ℤ (σ.indexEquiv j) j = 0 ∨
      P.pairingIn ℤ (σ.indexEquiv j) j = -1 := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  set p := Φ.indexEquiv j
  have hq : Φ.indexEquiv (σ.indexEquiv j) = finDistinctPairsRevSwap (2 * n + 1) p :=
    indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev j
  have hpair : P.pairing (σ.indexEquiv j) j =
      (if p.val.2.rev = p.val.1 then (1 : K) else 0) -
        (if p.val.2.rev = p.val.2 then 1 else 0) -
        (if p.val.1.rev = p.val.1 then 1 else 0) +
        (if p.val.1.rev = p.val.2 then 1 else 0) := by
    rw [← Φ.toHom.pairing (i := σ.indexEquiv j) (j := j), hq, ← root_coroot_eq_pairing,
      toLinearMap_typeAZeroSumRootPairing, root_typeAZeroSumRootPairing,
      coroot_typeAZeroSumRootPairing, typeAZeroSumVec_dotProduct,
      finDistinctPairsRevSwap_apply_val]
    dsimp only [p]
    ring
  by_cases hfix : p.val.2.rev = p.val.1
  · left
    apply Φ.indexEquiv.injective
    rw [hq]
    exact (finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev p).mpr (by rw [← hfix, Fin.rev_rev])
  · right
    have hfix' : p.val.1.rev ≠ p.val.2 := fun h ↦ hfix (by rw [← h, Fin.rev_rev])
    rw [ite_eq_right hfix, ite_eq_right hfix'] at hpair
    by_cases h2 : p.val.2.rev = p.val.2 <;> by_cases h1 : p.val.1.rev = p.val.1
    · exfalso
      exact p.property ((rev_eq_self_iff_eq_evenTypeAMidIdx.mp h1).trans
        (rev_eq_self_iff_eq_evenTypeAMidIdx.mp h2).symm)
    · right
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [algebraMap_pairingIn, hpair, map_neg, map_one]; simp [h2, h1]
    · right
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [algebraMap_pairingIn, hpair, map_neg, map_one]; simp [h2, h1]
    · left
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [algebraMap_pairingIn, hpair, map_zero]; simp [h2, h1]

private lemma pairing_symm_indexEquiv (j : ι) :
    P.pairing j (σ.indexEquiv j) = P.pairing (σ.indexEquiv j) j := by
  have h := σ.toHom.pairing (i := j) (j := σ.indexEquiv j)
  rw [indexEquiv_indexEquiv P b σ hσ e he hrev j] at h
  exact h.symm

private lemma orbitSum_eq_add_of_indexEquiv_ne {j : ι} (hne : σ.indexEquiv j ≠ j) :
    P.orbitSum σ j = P.root j + P.root (σ.indexEquiv j) := by
  classical
  rw [orbitSum_def,
    orbitIndices_eq_pair_of_apply_apply (indexEquiv_indexEquiv P b σ hσ e he hrev j),
    sum_pair hne.symm]

private lemma reflection_reflection_comm_of_pairing_eq_zero {j : ι}
    (h0 : P.pairing (σ.indexEquiv j) j = 0) (y : M) :
    P.reflection j (P.reflection (σ.indexEquiv j) y) =
      P.reflection (σ.indexEquiv j) (P.reflection j y) := by
  have h0' : P.pairing j (σ.indexEquiv j) = 0 :=
    (pairing_symm_indexEquiv P b σ hσ e he hrev j).trans h0
  rw [RootPairing.reflection_reflection_of_pairing_eq_zero P h0 y,
    RootPairing.reflection_reflection_of_pairing_eq_zero P h0' y, sub_right_comm]

private lemma reflectionPerm_reflectionPerm_comm_of_pairing_eq_zero {j : ι}
    (h0 : P.pairing (σ.indexEquiv j) j = 0) (r : ι) :
    P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j) r) =
      P.reflectionPerm (σ.indexEquiv j) (P.reflectionPerm j r) := by
  apply P.root.injective
  simp only [root_reflectionPerm]
  exact reflection_reflection_comm_of_pairing_eq_zero P b σ hσ e he hrev h0 (P.root r)

private lemma reflection_braid_of_pairing_eq_neg_one {j : ι}
    (hneg : P.pairing (σ.indexEquiv j) j = -1) (y : M) :
    P.reflection j (P.reflection (σ.indexEquiv j) (P.reflection j y)) =
      y - (P.coroot' j y + P.coroot' (σ.indexEquiv j) y) •
        (P.root j + P.root (σ.indexEquiv j)) := by
  have hneg' : P.pairing j (σ.indexEquiv j) = -1 :=
    (pairing_symm_indexEquiv P b σ hσ e he hrev j).trans hneg
  have hx1 : P.coroot' (σ.indexEquiv j) (P.reflection j y) =
      P.coroot' (σ.indexEquiv j) y + P.coroot' j y := by
    rw [reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, hneg',
      smul_eq_mul, mul_neg_one, sub_neg_eq_add]
  have hx2 : P.coroot' j (P.reflection (σ.indexEquiv j) (P.reflection j y)) =
      P.coroot' (σ.indexEquiv j) y := by
    rw [reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, hneg, hx1,
      reflection_apply, map_sub, map_smul, root_coroot'_eq_pairing, pairing_same,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [reflection_apply, hx2, reflection_apply, hx1, reflection_apply,
    smul_add, add_smul, add_smul, add_smul]
  abel

private lemma reflection_braid_comm_of_pairing_eq_neg_one {j : ι}
    (hneg : P.pairing (σ.indexEquiv j) j = -1) (y : M) :
    P.reflection j (P.reflection (σ.indexEquiv j) (P.reflection j y)) =
      P.reflection (σ.indexEquiv j) (P.reflection j (P.reflection (σ.indexEquiv j) y)) := by
  have hneg' : P.pairing (σ.indexEquiv (σ.indexEquiv j)) (σ.indexEquiv j) = -1 := by
    rw [indexEquiv_indexEquiv P b σ hσ e he hrev j]
    exact (pairing_symm_indexEquiv P b σ hσ e he hrev j).trans hneg
  have h1 := reflection_braid_of_pairing_eq_neg_one P b σ hσ e he hrev hneg y
  have h2 := reflection_braid_of_pairing_eq_neg_one P b σ hσ e he hrev hneg' y
  rw [indexEquiv_indexEquiv P b σ hσ e he hrev j] at h2
  rw [h1, h2, add_comm (P.coroot' j y), add_comm (P.root j)]

private lemma reflectionPerm_braid_comm_of_pairing_eq_neg_one {j : ι}
    (hneg : P.pairing (σ.indexEquiv j) j = -1) (r : ι) :
    P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j) (P.reflectionPerm j r)) =
      P.reflectionPerm (σ.indexEquiv j)
        (P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j) r)) := by
  apply P.root.injective
  simp only [root_reflectionPerm]
  exact reflection_braid_comm_of_pairing_eq_neg_one P b σ hσ e he hrev hneg (P.root r)

private lemma indexEquiv_reflection_mul_comm_of_pairing_eq_zero {j : ι}
    (h0K : P.pairing (σ.indexEquiv j) j = 0) (r : ι) :
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j)).indexEquiv (σ.indexEquiv r) =
      σ.indexEquiv ((Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j)).indexEquiv r) := by
  rw [Equiv.indexEquiv_mul_apply, Equiv.indexEquiv_mul_apply, Equiv.reflection_indexEquiv,
    Equiv.reflection_indexEquiv, σ.toHom.indexEquiv_reflectionPerm,
    σ.toHom.indexEquiv_reflectionPerm, indexEquiv_indexEquiv P b σ hσ e he hrev j,
    reflectionPerm_reflectionPerm_comm_of_pairing_eq_zero P b σ hσ e he hrev h0K]

private lemma indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one {j : ι}
    (hnegK : P.pairing (σ.indexEquiv j) j = -1) (r : ι) :
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) * Equiv.reflection P j).indexEquiv
        (σ.indexEquiv r) =
      σ.indexEquiv ((Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) *
        Equiv.reflection P j).indexEquiv r) := by
  rw [Equiv.indexEquiv_mul_apply, Equiv.indexEquiv_mul_apply, Equiv.indexEquiv_mul_apply,
    Equiv.indexEquiv_mul_apply, Equiv.reflection_indexEquiv, Equiv.reflection_indexEquiv,
    σ.toHom.indexEquiv_reflectionPerm, σ.toHom.indexEquiv_reflectionPerm,
    σ.toHom.indexEquiv_reflectionPerm, indexEquiv_indexEquiv P b σ hσ e he hrev j,
    reflectionPerm_braid_comm_of_pairing_eq_neg_one P b σ hσ e he hrev hnegK]

omit [P.IsRootSystem] [P.IsReduced] b hσ e he hrev in
private lemma reflection_fixed_eq_preReflection_of_indexEquiv_eq {j : ι}
    (hfix : σ.indexEquiv j = j) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (x : M) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  have hne : P.pairingIn ℤ (σ.indexEquiv j) j ≠ -1 := by rw [hfix, P.pairingIn_same]; decide
  rw [ite_eq_right hne, one_mul, orbitSum_eq_root_of_indexEquiv_eq hfix, reflection_apply]

private lemma reflection_fixed_eq_preReflection_of_pairingIn_eq_zero {j : ι}
    (h0 : P.pairingIn ℤ (σ.indexEquiv j) j = 0) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (P.reflection (σ.indexEquiv j) (x : M)) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  have hne_neg : P.pairingIn ℤ (σ.indexEquiv j) j ≠ -1 := by rw [h0]; decide
  have hne : σ.indexEquiv j ≠ j := P.ne_of_pairingIn_ne_two (by rw [h0]; decide)
  have h0K : P.pairing (σ.indexEquiv j) j = 0 := by
    rw [← P.algebraMap_pairingIn ℤ, h0, map_zero]
  rw [ite_eq_right hne_neg, one_mul, orbitSum_eq_add_of_indexEquiv_ne P b σ hσ e he hrev hne,
    RootPairing.reflection_reflection_of_pairing_eq_zero P h0K,
    P.coroot'_indexEquiv_of_mem_fixedSubmodule σ j x.property, smul_add, sub_sub,
    add_comm (P.coroot' j (x : M) • P.root (σ.indexEquiv j))]

private lemma reflection_fixed_eq_preReflection_of_pairingIn_eq_neg_one {j : ι}
    (hneg : P.pairingIn ℤ (σ.indexEquiv j) j = -1) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (P.reflection (σ.indexEquiv j) (P.reflection j (x : M))) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  have hne : σ.indexEquiv j ≠ j := P.ne_of_pairingIn_ne_two (by rw [hneg]; decide)
  have hnegK : P.pairing (σ.indexEquiv j) j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ, hneg, map_neg, map_one]
  rw [ite_eq_left hneg, orbitSum_eq_add_of_indexEquiv_ne P b σ hσ e he hrev hne,
    reflection_braid_of_pairing_eq_neg_one P b σ hσ e he hrev hnegK,
    P.coroot'_indexEquiv_of_mem_fixedSubmodule σ j x.property, ← two_mul]

private lemma exists_aut_comm_eq_preReflection (j : ι) :
    (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (P.orbitSum σ j) = 2 ∧
      ∃ w : P.Aut,
        (∀ r, w.indexEquiv (σ.indexEquiv r) = σ.indexEquiv (w.indexEquiv r)) ∧
        ∀ x : LinearMap.fixedSubmodule σ.weightMap,
          w.weightMap (x : M) =
            (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
              P.coroot' j (x : M)) • P.orbitSum σ j := by
  rcases P.indexEquiv_eq_self_or_pairingIn_eq_zero_or_neg_one_evenTypeA b σ hσ e he hrev j with
    hfix | h0 | hneg
  · have hne : P.pairingIn ℤ (σ.indexEquiv j) j ≠ -1 := by rw [hfix, P.pairingIn_same]; decide
    refine ⟨by rw [ite_eq_right hne, one_mul, orbitSum_eq_root_of_indexEquiv_eq hfix,
      root_coroot'_eq_pairing, pairing_same], Equiv.reflection P j,
      σ.indexEquiv_reflection_comm_of_indexEquiv_eq hfix, fun x ↦ by
        rw [P.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_indexEquiv_eq P σ hfix x]⟩
  · have hne_neg : P.pairingIn ℤ (σ.indexEquiv j) j ≠ -1 := by rw [h0]; decide
    have hne : σ.indexEquiv j ≠ j := P.ne_of_pairingIn_ne_two (by rw [h0]; decide)
    have h0K : P.pairing (σ.indexEquiv j) j = 0 := by
      rw [← P.algebraMap_pairingIn ℤ, h0, map_zero]
    refine ⟨?_, Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j),
      indexEquiv_reflection_mul_comm_of_pairing_eq_zero P b σ hσ e he hrev h0K, fun x ↦ by
        rw [Equiv.weightMap_mul_apply, P.reflection_weightMap_apply, P.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_pairingIn_eq_zero P b σ hσ e he hrev h0 x]⟩
    rw [ite_eq_right hne_neg, one_mul,
      orbitSum_eq_add_of_indexEquiv_ne P b σ hσ e he hrev hne, map_add,
      root_coroot'_eq_pairing, root_coroot'_eq_pairing, pairing_same, h0K, add_zero]
  · have hne : σ.indexEquiv j ≠ j := P.ne_of_pairingIn_ne_two (by rw [hneg]; decide)
    have hnegK : P.pairing (σ.indexEquiv j) j = -1 := by
      rw [← P.algebraMap_pairingIn ℤ, hneg, map_neg, map_one]
    refine ⟨?_, Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) * Equiv.reflection P j,
      indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one P b σ hσ e he hrev hnegK, fun x ↦ by
        rw [Equiv.weightMap_mul_apply, Equiv.weightMap_mul_apply, P.reflection_weightMap_apply,
          P.reflection_weightMap_apply, P.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_pairingIn_eq_neg_one P b σ hσ e he hrev hneg x]⟩
    rw [ite_eq_left hneg, orbitSum_eq_add_of_indexEquiv_ne P b σ hσ e he hrev hne, map_add,
      root_coroot'_eq_pairing, root_coroot'_eq_pairing, pairing_same, hnegK]; norm_num

/-- The coroot functional `coroot'` of `evenTypeAFoldedPairing` coincides with its `coroot`
because the bilinear pairing is dual evaluation. -/
@[simp] theorem coroot'_evenTypeAFoldedPairing_eq_coroot (v : P.foldedIndices σ) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v =
      (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot v :=
  LinearMap.ext fun x ↦ toLinearMap_evenTypeAFoldedPairing P b σ hσ e he hrev x _

/-- Evaluating the folded coroot functional at any folded index `v = P.orbitSum σ j` on a fixed
weight `x` scales `P.coroot' j x` by `2` when `P.pairingIn ℤ (σ.indexEquiv j) j = -1` and by `1`
otherwise. -/
theorem coroot'_evenTypeAFoldedPairing {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (x : M) := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let c : K := if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1
  let f : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
    c • (P.coroot' j).comp (LinearMap.fixedSubmodule σ.weightMap).subtype
  obtain ⟨hc2, w, hw_comm, hw_eq⟩ := exists_aut_comm_eq_preReflection P b σ hσ e he hrev j
  have hf_root : f (P'.root v) = 2 := by
    dsimp only [f]
    rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      coe_root_evenTypeAFoldedPairing, smul_eq_mul, ← hv]
    exact hc2
  have hf_mapsTo : Set.MapsTo (Module.preReflection (P'.root v) f)
      (Set.range P'.root) (Set.range P'.root) := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.property
    refine ⟨⟨P.orbitSum σ (w.indexEquiv i), P.orbitSum_mem_foldedIndices σ _⟩, Subtype.ext ?_⟩
    rw [coe_root_evenTypeAFoldedPairing, Subtype.coe_mk, Module.preReflection_apply,
      Submodule.coe_sub, Submodule.coe_smul_of_tower, coe_root_evenTypeAFoldedPairing,
      coe_root_evenTypeAFoldedPairing]
    dsimp only [f]
    rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      coe_root_evenTypeAFoldedPairing, smul_eq_mul, ← hv]
    have hu := hw_eq (P'.root u)
    rw [coe_root_evenTypeAFoldedPairing] at hu
    rw [← hu, ← hi, weightMap_orbitSum w hw_comm i]
  have heq : P'.coroot' v = f :=
    Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range P'.root)
      IsRootSystem.span_root_eq_top (P'.coroot_root_two v) (P'.mapsTo_reflection_root v)
      hf_root hf_mapsTo
  exact (LinearMap.congr_fun heq x).trans (by
    dsimp only [f, c]
    rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype, smul_eq_mul])

/-- Evaluating the folded coroot at any folded index `v = P.orbitSum σ j` on a fixed weight `x`
scales `P.coroot' j x` by `2` when `P.pairingIn ℤ (σ.indexEquiv j) j = -1` and by `1` otherwise. -/
theorem coroot_evenTypeAFoldedPairing {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot v x =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (x : M) := by
  rw [← coroot'_evenTypeAFoldedPairing_eq_coroot]
  exact coroot'_evenTypeAFoldedPairing P b σ hσ e he hrev hv x

/-- Simp normal form for the folded coroot at `⟨P.orbitSum σ j, h⟩` evaluated on a fixed weight. -/
@[simp] theorem coroot_evenTypeAFoldedPairing_mk (j : ι) (h : P.orbitSum σ j ∈ P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot ⟨P.orbitSum σ j, h⟩ x =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (x : M) :=
  coroot_evenTypeAFoldedPairing P b σ hσ e he hrev rfl x

/-- Pairing of folded roots `u` and `v = P.orbitSum σ j` in terms of `P.coroot' j (u : M)`. -/
theorem pairing_evenTypeAFoldedPairing {u v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairing u v =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (u : M) := by
  rw [← root_coroot'_eq_pairing, coroot'_evenTypeAFoldedPairing P b σ hσ e he hrev hv,
    coe_root_evenTypeAFoldedPairing]

/-- Simp normal form for the pairing of `u` with `⟨P.orbitSum σ j, hj⟩`. -/
@[simp] theorem pairing_evenTypeAFoldedPairing_mk (u : P.foldedIndices σ) (j : ι)
    (hj : P.orbitSum σ j ∈ P.foldedIndices σ) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairing u ⟨P.orbitSum σ j, hj⟩ =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (u : M) :=
  pairing_evenTypeAFoldedPairing P b σ hσ e he hrev rfl

/-- Pairing of folded roots `u = P.orbitSum σ i` and `v = P.orbitSum σ j` as a scaled sum of
ambient pairings over the `σ`-orbit of `i`. -/
theorem pairing_evenTypeAFoldedPairing_eq_sum {u v : P.foldedIndices σ} {i j : ι}
    (hu : P.orbitSum σ i = (u : M)) (hv : P.orbitSum σ j = (v : M)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairing u v =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        ∑ r ∈ P.orbitIndices σ i, P.pairing r j := by
  rw [pairing_evenTypeAFoldedPairing P b σ hσ e he hrev hv, ← hu, coroot'_orbitSum]

/-- Integer-valued pairing of folded roots `u = P.orbitSum σ i` and `v = P.orbitSum σ j`. -/
theorem pairingIn_evenTypeAFoldedPairing {u v : P.foldedIndices σ} {i j : ι}
    (hu : P.orbitSum σ i = (u : M)) (hv : P.orbitSum σ j = (v : M)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ u v =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        ∑ r ∈ P.orbitIndices σ i, P.pairingIn ℤ r j := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [algebraMap_pairingIn, pairing_evenTypeAFoldedPairing_eq_sum P b σ hσ e he hrev hu hv,
    map_mul, map_sum, apply_ite (algebraMap ℤ K), map_ofNat, map_one]
  congr 1
  exact sum_congr rfl fun r _ ↦ (P.algebraMap_pairingIn ℤ r j).symm

/-- Simp normal form for the integer-valued pairing of folded orbit sums. -/
@[simp] theorem pairingIn_evenTypeAFoldedPairing_mk (i j : ι)
    (hi : P.orbitSum σ i ∈ P.foldedIndices σ) (hj : P.orbitSum σ j ∈ P.foldedIndices σ) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ
        ⟨P.orbitSum σ i, hi⟩ ⟨P.orbitSum σ j, hj⟩ =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        ∑ r ∈ P.orbitIndices σ i, P.pairingIn ℤ r j :=
  pairingIn_evenTypeAFoldedPairing P b σ hσ e he hrev rfl rfl

/-- Action of the folded reflection at `v = P.orbitSum σ j` on a fixed weight `x`, coerced to `M`.
-/
theorem coe_reflection_evenTypeAFoldedPairing {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection v x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        P.coroot' j (x : M)) • (v : M) := by
  rw [reflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower,
    coe_root_evenTypeAFoldedPairing, coroot'_evenTypeAFoldedPairing P b σ hσ e he hrev hv]

/-- Simp normal form for the coercion of `reflection ⟨P.orbitSum σ j, hj⟩ x` to `M`. -/
@[simp] theorem coe_reflection_evenTypeAFoldedPairing_mk (j : ι)
    (hj : P.orbitSum σ j ∈ P.foldedIndices σ) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection ⟨P.orbitSum σ j, hj⟩ x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j :=
  coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev rfl x

/-- At a `σ`-fixed root `j`, the folded reflection restricts `P.reflection j`. -/
theorem coe_reflection_evenTypeAFoldedPairing_of_indexEquiv_eq {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (hfix : σ.indexEquiv j = j)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection v x :
      LinearMap.fixedSubmodule σ.weightMap) : M) = P.reflection j (x : M) := by
  rw [coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev hv, ← hv,
    reflection_fixed_eq_preReflection_of_indexEquiv_eq P σ hfix x]

/-- At an orthogonal pair (`P.pairingIn ℤ (σ.indexEquiv j) j = 0`), the folded reflection restricts
the commuting product `P.reflection j ∘ P.reflection (σ.indexEquiv j)`. -/
theorem coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_zero {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (h0 : P.pairingIn ℤ (σ.indexEquiv j) j = 0)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection v x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.reflection j (P.reflection (σ.indexEquiv j) (x : M)) := by
  rw [coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev hv, ← hv,
    reflection_fixed_eq_preReflection_of_pairingIn_eq_zero P b σ hσ e he hrev h0 x]

/-- At an adjacent pair (`P.pairingIn ℤ (σ.indexEquiv j) j = -1`), the folded reflection restricts
the braid product `P.reflection j ∘ P.reflection (σ.indexEquiv j) ∘ P.reflection j`. -/
theorem coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_neg_one {v : P.foldedIndices σ}
    {j : ι} (hv : P.orbitSum σ j = (v : M)) (hneg : P.pairingIn ℤ (σ.indexEquiv j) j = -1)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection v x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.reflection j (P.reflection (σ.indexEquiv j) (P.reflection j (x : M))) := by
  rw [coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev hv, ← hv,
    reflection_fixed_eq_preReflection_of_pairingIn_eq_neg_one P b σ hσ e he hrev hneg x]

/-- Coercion to `M` of the folded reflection permutation `reflectionPerm v w` for
`v = P.orbitSum σ j`. -/
theorem coe_reflectionPerm_evenTypeAFoldedPairing {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (w : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w : P.foldedIndices σ) : M) =
      (w : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        P.coroot' j (w : M)) • (v : M) := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v w),
    root_reflectionPerm, coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev hv,
    coe_root_evenTypeAFoldedPairing]

/-- Simp normal form for the coercion of `reflectionPerm ⟨P.orbitSum σ j, hj⟩ w` to `M`. -/
@[simp] theorem coe_reflectionPerm_evenTypeAFoldedPairing_mk (j : ι)
    (hj : P.orbitSum σ j ∈ P.foldedIndices σ) (w : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm
        ⟨P.orbitSum σ j, hj⟩ w : P.foldedIndices σ) : M) =
      (w : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) *
        P.coroot' j (w : M)) • P.orbitSum σ j :=
  coe_reflectionPerm_evenTypeAFoldedPairing P b σ hσ e he hrev rfl w

/-- Self-reflection of a folded index negates its coercion in `M`. -/
@[simp] theorem coe_reflectionPerm_evenTypeAFoldedPairing_self (v : P.foldedIndices σ) :
    (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v v : P.foldedIndices σ) : M) =
      -(v : M) := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v v),
    root_reflectionPerm, reflection_apply_self, Submodule.coe_neg,
    coe_root_evenTypeAFoldedPairing]

/-- At a `σ`-fixed root `j`, the folded reflection permutation sends the orbit of `i` to the orbit
of `P.reflectionPerm j i`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_indexEquiv_eq {v w : P.foldedIndices σ} {i j : ι}
    (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M)) (hfix : σ.indexEquiv j = j) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j i), P.orbitSum_mem_foldedIndices σ _⟩ := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  apply Subtype.ext
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v w),
    root_reflectionPerm,
    coe_reflection_evenTypeAFoldedPairing_of_indexEquiv_eq P b σ hσ e he hrev hv hfix,
    coe_root_evenTypeAFoldedPairing, ← hw, ← P.reflection_weightMap_apply]
  have h := weightMap_orbitSum (σ := σ) (τ := σ) (Equiv.reflection P j)
    (σ.indexEquiv_reflection_comm_of_indexEquiv_eq hfix) i
  rwa [Equiv.reflection_indexEquiv] at h

/-- At an orthogonal pair (`P.pairingIn ℤ (σ.indexEquiv j) j = 0`), the folded reflection
permutation acts on orbit representatives by
`P.reflectionPerm j ∘ P.reflectionPerm (σ.indexEquiv j)`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_pairingIn_eq_zero {v w : P.foldedIndices σ}
    {i j : ι} (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M))
    (h0 : P.pairingIn ℤ (σ.indexEquiv j) j = 0) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j) i)),
        P.orbitSum_mem_foldedIndices σ _⟩ := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  have h0K : P.pairing (σ.indexEquiv j) j = 0 := by
    rw [← P.algebraMap_pairingIn ℤ, h0, map_zero]
  apply Subtype.ext
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v w),
    root_reflectionPerm,
    coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_zero P b σ hσ e he hrev hv h0,
    coe_root_evenTypeAFoldedPairing, ← hw]
  have h := weightMap_orbitSum (σ := σ) (τ := σ)
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j))
    (indexEquiv_reflection_mul_comm_of_pairing_eq_zero P b σ hσ e he hrev h0K) i
  rwa [Equiv.weightMap_mul_apply, P.reflection_weightMap_apply, P.reflection_weightMap_apply,
    Equiv.indexEquiv_mul_apply, Equiv.reflection_indexEquiv, Equiv.reflection_indexEquiv] at h

/-- At an adjacent pair (`P.pairingIn ℤ (σ.indexEquiv j) j = -1`), the folded reflection
permutation acts on orbit representatives by
`P.reflectionPerm j ∘ P.reflectionPerm (σ.indexEquiv j) ∘ P.reflectionPerm j`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_pairingIn_eq_neg_one {v w : P.foldedIndices σ}
    {i j : ι} (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M))
    (hneg : P.pairingIn ℤ (σ.indexEquiv j) j = -1) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j)
          (P.reflectionPerm j i))), P.orbitSum_mem_foldedIndices σ _⟩ := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  have hnegK : P.pairing (σ.indexEquiv j) j = -1 := by
    rw [← P.algebraMap_pairingIn ℤ, hneg, map_neg, map_one]
  apply Subtype.ext
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev (P'.reflectionPerm v w),
    root_reflectionPerm,
    coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_neg_one P b σ hσ e he hrev hv hneg,
    coe_root_evenTypeAFoldedPairing, ← hw]
  have h := weightMap_orbitSum (σ := σ) (τ := σ)
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) * Equiv.reflection P j)
    (indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one P b σ hσ e he hrev hnegK) i
  rwa [Equiv.weightMap_mul_apply, Equiv.weightMap_mul_apply, P.reflection_weightMap_apply,
    P.reflection_weightMap_apply, P.reflection_weightMap_apply, Equiv.indexEquiv_mul_apply,
    Equiv.indexEquiv_mul_apply, Equiv.reflection_indexEquiv, Equiv.reflection_indexEquiv] at h

private lemma evenTypeAIndexEquiv_typeBSimpleIndex (k : Fin n) :
    evenTypeAIndexEquiv P b σ hσ e he hrev (typeBSimpleIndex n k) =
      b.evenTypeAFoldedSimpleIndex σ e k := by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev; set Φ := evenTypeAToZeroSumEquiv P b e he
  let jk : b.support := e.symm ⟨k, by have := k.isLt; omega⟩
  have hΨ : Ψ ⟨P.orbitSum σ jk, P.orbitSum_mem_fixedSubmodule σ jk⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
    dsimp [Ψ, evenTypeAWeightEquiv]; rw [← evenTypeAFixedCoordEquiv_simpleOrbitSum K n k]
    congr 1; apply Subtype.ext
    rw [LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk, Equiv.weightEquiv_apply,
      Φ.weightMap_orbitSum_of_autCongr (autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev),
      indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply]
  exact Subtype.ext (by
    have hcoe : ((evenTypeAIndexEquiv P b σ hσ e he hrev (typeBSimpleIndex n k) : _) : M) =
        ((Ψ.symm ((typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k)) : _) : M) := rfl
    rw [hcoe, Base.coe_evenTypeAFoldedSimpleIndex, ← hΨ, Ψ.symm_apply_apply])

variable {P}

/-- **The folded base of `(P, b, σ)`,** of Cartan type `B n`. -/
noncomputable def Base.evenTypeAFoldedBase :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Base :=
  (typeBBaseChangeBase K n).map <|
    (typeBBaseChangeRootSystem K n).equivMap (evenTypeAIndexEquiv P b σ hσ e he hrev)
      (evenTypeAWeightEquiv P b σ hσ e he hrev).symm
      ((_root_.dotProductEquiv K (Fin n)).trans (evenTypeAWeightEquiv P b σ hσ e he hrev).dualMap)

-- `Base.evenTypeAFoldedBase` has dependent type `(P.evenTypeAFoldedPairing ...).Base`, so
-- `rw [evenTypeAFoldedPairing_eq_map]` cannot rewrite inside `Base.support` directly; unfold both
-- definitions here once so downstream proofs rewrite with `support_evenTypeAFoldedBase_eq`.
private lemma support_evenTypeAFoldedBase_eq [DecidableEq (P.foldedIndices σ)] :
    (b.evenTypeAFoldedBase σ hσ e he hrev).support =
      (typeBBaseChangeBase K n).support.image (evenTypeAIndexEquiv P b σ hσ e he hrev) := by
  delta Base.evenTypeAFoldedBase evenTypeAFoldedPairing
  rw [Base.support_map_eq, indexEquiv_equivMap]

/-- `v ∈ (evenTypeAFoldedBase).support` iff `v` is one of `evenTypeAFoldedSimpleIndex`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff_exists_fin (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ k : Fin n, v = b.evenTypeAFoldedSimpleIndex σ e k := by
  classical
  rw [support_evenTypeAFoldedBase_eq, mem_image]
  refine ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, (mem_support_typeBBaseChangeBase_iff K n m).mp hm⟩, ?_⟩,
    fun ⟨k, hk⟩ ↦ ⟨typeBSimpleIndex n k,
      (mem_support_typeBBaseChangeBase_iff K n _).mpr ((typeBSimpleIndex_val k).symm ▸ k.isLt),
      by rw [hk, evenTypeAIndexEquiv_typeBSimpleIndex]⟩⟩
  rw [← h, ← evenTypeAIndexEquiv_typeBSimpleIndex]
  exact congrArg _ (Fin.ext (by simp))

/-- `b.evenTypeAFoldedSimpleIndex σ e k` belongs to the support of `evenTypeAFoldedBase`. -/
theorem Base.evenTypeAFoldedSimpleIndex_mem_support (k : Fin n) :
    b.evenTypeAFoldedSimpleIndex σ e k ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support :=
  (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev _).mpr ⟨k, rfl⟩

/-- **Simple roots of the folded base:** orbit sums of simple roots of `b`. -/
theorem Base.mem_support_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support ↔
      ∃ j ∈ b.support, P.orbitSum σ j = (v : M) := by
  rw [b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev]
  refine ⟨by rintro ⟨k, rfl⟩; exact ⟨_, (e.symm ⟨k, by have := k.isLt; omega⟩).property, rfl⟩,
    fun ⟨j, hj, hv⟩ ↦ let ⟨k, hk⟩ := exists_fin_of_mem_support b σ hσ e hrev hj
      ⟨k, Subtype.ext <| hk.elim (fun h ↦ by rw [coe_evenTypeAFoldedSimpleIndex, h, hv])
        (fun h ↦ by rw [coe_evenTypeAFoldedSimpleIndex, h, P.orbitSum_indexEquiv, hv])⟩⟩

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
  obtain ⟨f, hf⟩ := (hasCartanType_iff _ _).mp (b.hasCartanType_evenTypeAFoldedBase σ hσ e he hrev)
  refine (hasCartanType_iff _ _).mpr ⟨f, fun i j ↦ ?_⟩
  have : (B 1).rank = 1 := rfl
  obtain rfl : i = j := f.injective (Fin.ext (by have := (f i).isLt; have := (f j).isLt; omega))
  rw [hf]
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
  have hpair : typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ = Φ.indexEquiv jk := by
    rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk, Equiv.apply_symm_apply]
  rw [evenTypeAFoldedPairing_eq_map, coroot'_map, LinearEquiv.symm_symm, hidx,
    coroot'_typeBBaseChangeRootSystem_simpleIndex]
  dsimp only [evenTypeAWeightEquiv, LinearEquiv.trans_apply]
  rw [evenTypeAFixedCoordEquiv_apply, LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk,
    Equiv.weightEquiv_apply, hpair, Hom.coroot'_weightMap]

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
  have h1 : e i' = (e ⟨i, hi⟩).rev := hrev ⟨i, hi⟩ i' rfl
  have hinv : σ.indexEquiv (σ.indexEquiv i) = i :=
    congrArg Subtype.val <| e.injective (by rw [hrev i' _ rfl, h1, Fin.rev_rev] :
      e ⟨σ.indexEquiv i', hσ i'.val i'.property⟩ = e ⟨i, hi⟩)
  have hne : σ.indexEquiv i ≠ i := fun hc ↦ by
    have hval := congrArg (Fin.val ∘ e) (Subtype.ext hc : i' = ⟨i, hi⟩)
    dsimp at hval; rw [h1, Fin.val_rev] at hval; have := (e ⟨i, hi⟩).isLt; omega
  rw [orbitSum_def, orbitIndices_eq_pair_of_apply_apply hinv, sum_pair hne.symm]

private lemma isPos_evenTypeAFoldedBase_of_isPos {j : ι} {w : P.foldedIndices σ}
    (hj : b.IsPos j) (hw : P.orbitSum σ j = (w : M)) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos w := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let b' := b.evenTypeAFoldedBase σ hσ e he hrev
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (hw ▸ P.orbitSum_mem_posRootCone hσ hj)
  have hw_fix : σ.weightMap (w : M) = (w : M) :=
    LinearMap.mem_fixedSubmodule_iff.mp (hw ▸ P.orbitSum_mem_fixedSubmodule σ j)
  have h2 : 2 • (w : M) = (w : M) + σ.weightMap (w : M) := by rw [hw_fix, two_nsmul]
  have hvec : 2 • (w : M) = ∑ i ∈ b.support.attach, c i.val • P.orbitSum σ i.val := by
    rw [h2, hc, map_sum, ← sum_add_distrib, ← sum_attach]
    exact sum_congr rfl fun i _ ↦ by
      rw [map_nsmul, Hom.root_weightMap_apply, ← nsmul_add,
        root_add_root_indexEquiv_eq_orbitSum b σ hσ e hrev i.property]
  refine (mem_posRoots P' b' w).mp ((P'.nsmul_root_mem_posRootCone_iff b' two_ne_zero).mp ?_)
  rw [(Subtype.ext (by simp [P', hvec]) : 2 • P'.root w = ∑ i ∈ b.support.attach, c i.val •
      P'.root ⟨P.orbitSum σ i.val, P.orbitSum_mem_foldedIndices σ i.val⟩)]
  exact (posRootCone P' b').sum_mem fun i _ ↦ (posRootCone P' b').nsmul_mem
    (root_mem_posRootCone_of_mem_posRoots P' b' (support_subset_posRoots P' b' <|
      (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr ⟨i.val, i.property, rfl⟩)) _

/-- **Positive roots of the folded base:** orbit sums of positive roots of `b`. -/
theorem Base.isPos_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v ↔
      ∃ j, b.IsPos j ∧ P.orbitSum σ j = (v : M) := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev
  let b' := b.evenTypeAFoldedBase σ hσ e he hrev
  refine ⟨fun hv ↦ ?_, fun ⟨j, hj, hw⟩ ↦ isPos_evenTypeAFoldedBase_of_isPos b σ hσ e he hrev hj hw⟩
  obtain ⟨j, hj⟩ := mem_foldedIndices.mp v.property
  by_cases hpos : b.IsPos j
  · exact ⟨j, hpos, hj⟩
  · exfalso
    have hj' : b.IsPos (P.reflectionPerm j j) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr ((mem_negRoots P b j).mpr hpos)
    refine reflectionPerm_self_notMem_posRoots P' b' ((mem_posRoots P' b' v).mpr hv)
      ((mem_posRoots P' b' _).mpr (isPos_evenTypeAFoldedBase_of_isPos b σ hσ e he hrev hj' ?_))
    rw [orbitSum_reflectionPerm_self, hj,
      coe_reflectionPerm_evenTypeAFoldedPairing_self P b σ hσ e he hrev v]

/-- **Forward simple-coroot integrality on fixed weights.** -/
theorem Base.exists_int_coroot'_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (hint : ∀ j ∈ b.support, ∃ z : ℤ, P.coroot' j (x : M) = z) :
    ∀ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support,
      ∃ z : ℤ, (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x = z := fun v hv ↦ by
  obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
  obtain ⟨z, hz⟩ := hint _ (e.symm ⟨k, by have := k.isLt; omega⟩).property
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
  have hφ := autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) :=
    TauCeti.map_equivOfCartanMatrixEq b (typeAZeroSumBase K (2 * n)) _ _
  refine ⟨j, (b.isPos_map_iff Φ j).mp (by simpa [hb_map, j] using hp_pos), ?_, ?_⟩
  · have hcard := congrArg Finset.card <|
      map_orbitIndices (σ := σ) (τ := typeAZeroSumRevAut K (2 * n)) Φ
        (fun q ↦ by rw [← hφ, Equiv.indexEquiv_autCongr_apply, Equiv.symm_apply_apply]) j
    rw [Finset.card_map, Equiv.apply_symm_apply] at hcard; exact hcard.trans hp_card
  · apply Φ.weightEquiv.injective
    rw [Equiv.weightEquiv_apply, Equiv.weightEquiv_apply, Φ.weightMap_orbitSum_of_autCongr hφ,
      Base.coe_evenTypeAFoldedSimpleIndex, Φ.weightMap_orbitSum_of_autCongr hφ,
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
  · conv_lhs => rw [hkj, ← LinearMap.mem_fixedSubmodule_iff.mp x.property, Hom.coroot'_weightMap]

/-- **Closed dominant chamber transport on fixed weights:** a fixed weight lies in the closed
dominant chamber of `evenTypeAFoldedPairing` with respect to `evenTypeAFoldedBase` if and only if
its coercion lies in `P.dominantChamber b`. -/
theorem Base.mem_dominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).dominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) ↔
      (x : M) ∈ P.dominantChamber b := by
  simp only [mem_dominantChamber]
  refine ⟨fun hx j hj ↦ ?_, fun hx v hv ↦ ?_⟩
  · obtain ⟨v, hv, c, hc, hcv⟩ := exists_folded_coroot'_eq_pos_mul b σ hσ e he hrev x hj
    exact (mul_nonneg_iff_of_pos_left hc).mp (hcv ▸ hx v hv)
  · obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    exact mul_nonneg (by split_ifs <;> norm_num)
      (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).property)

/-- **Open dominant chamber transport on fixed weights:** a fixed weight lies in the open
dominant chamber of `evenTypeAFoldedPairing` with respect to `evenTypeAFoldedBase` if and only if
its coercion lies in `P.openDominantChamber b`. -/
theorem Base.mem_openDominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).openDominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) ↔
      (x : M) ∈ P.openDominantChamber b := by
  simp only [mem_openDominantChamber]
  refine ⟨fun hx j hj ↦ ?_, fun hx v hv ↦ ?_⟩
  · obtain ⟨v, hv, c, hc, hcv⟩ := exists_folded_coroot'_eq_pos_mul b σ hσ e he hrev x hj
    exact (mul_pos_iff_of_pos_left hc).mp (hcv ▸ hx v hv)
  · obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev]
    exact mul_pos (by split_ifs <;> norm_num)
      (hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).property)

end OrderedField

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
noncomputable def Base.evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).Equiv
      (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂) :=
  Equiv.mk' (P.evenTypeAFoldedPairing b σ hσ e he hrev)
    (P₂.evenTypeAFoldedPairing b₂ σ₂ hσ₂ e₂ he₂ hrev₂)
    (φ.weightEquiv.fixedSubmoduleCongr <| LinearMap.ext fun x ↦ by
      have h := Equiv.autCongr_smul φ σ x; rw [hφ] at h; exact h.symm)
    (φ.foldedIndicesCongr hφ)
    fun v ↦ Subtype.ext (by simp)

/-- The weight map of `Base.evenTypeAFoldedEquiv` restricts `φ.weightMap` to fixed submodules. -/
@[simp] theorem Base.coe_weightMap_evenTypeAFoldedEquiv_apply (φ : P.Equiv P₂)
    (hφ : φ.autCongr σ = σ₂) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((b.evenTypeAFoldedEquiv σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).weightMap x :
      LinearMap.fixedSubmodule σ₂.weightMap) : M₂) = φ.weightMap (x : M) := by
  simp [Base.evenTypeAFoldedEquiv, Equiv.mk']

/-- The index equivalence of `Base.evenTypeAFoldedEquiv` is `φ.foldedIndicesCongr hφ`. -/
@[simp] theorem Base.indexEquiv_evenTypeAFoldedEquiv (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂) :
    (b.evenTypeAFoldedEquiv σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ).indexEquiv =
      φ.foldedIndicesCongr hφ := (rfl)

/-- When `φ` maps `b` to `b₂`, `Base.evenTypeAFoldedEquiv` maps the folded base of `b` to that
of `b₂`. -/
theorem Base.map_evenTypeAFoldedBase (φ : P.Equiv P₂) (hφ : φ.autCongr σ = σ₂)
    (hb : b.map φ = b₂) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).map
      (b.evenTypeAFoldedEquiv σ hσ e he hrev b₂ σ₂ hσ₂ e₂ he₂ hrev₂ φ hφ) =
      b₂.evenTypeAFoldedBase σ₂ hσ₂ e₂ he₂ hrev₂ := by
  classical
  ext w; rw [Base.support_map_eq, mem_image]
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨j, hj, hvj⟩ := (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev v).mp hv
    refine (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ _).mpr
      ⟨φ.indexEquiv j, by rw [← hb, Base.support_map_eq]; exact mem_image_of_mem _ hj,
        by rw [Base.indexEquiv_evenTypeAFoldedEquiv, Equiv.coe_foldedIndicesCongr_apply, ← hvj,
          φ.weightMap_orbitSum_of_autCongr hφ j]⟩
  · obtain ⟨j₂, hj₂, hwj⟩ := (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ w).mp hw
    rw [← hb, Base.support_map_eq, mem_image] at hj₂; obtain ⟨j, hj, rfl⟩ := hj₂
    refine ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
      (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr ⟨j, hj, rfl⟩,
      Subtype.ext (by rw [Base.indexEquiv_evenTypeAFoldedEquiv, Equiv.coe_foldedIndicesCongr_apply,
        ← hwj, φ.weightMap_orbitSum_of_autCongr hφ j])⟩

end Functoriality

end RootPairing
