/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Folding.EvenTypeA.Model
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Realization
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.LinearAlgebra.FixedSubmodule
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Folding even type-`A` root systems under diagram reversal

For any finite reduced crystallographic root system `P` of Cartan type `A (2 * n)` over a
characteristic-zero field `K` with base `b`, Bourbaki labelling `e : b.support ≃ Fin (2 * n)`, and
diagram-reversing automorphism `σ : P.Aut`, `P.foldedIndices σ` forms a reduced crystallographic
root system `evenTypeAFoldedPairing` with base `Base.evenTypeAFoldedBase` and realization
`Base.evenTypeAOrbitSumRealization` of Cartan type `B n`. This file provides formulas for folded
coroots (`coroot_evenTypeAFoldedPairing`, `coroot'_evenTypeAFoldedPairing`), pairings
(`pairing_evenTypeAFoldedPairing`, `pairingIn_evenTypeAFoldedPairing`), reflections
(`coe_reflection_evenTypeAFoldedPairing`, `coe_reflectionPerm_evenTypeAFoldedPairing`, and Weyl
formulas for fixed/orthogonal/adjacent orbits), simple-coroot scaling, chamber transport, lifts
(`Base.exists_fixed_pos_lift_evenTypeAFoldedBase`,
`Base.exists_paired_pos_lift_evenTypeAFoldedBase`), and functoriality `Base.evenTypeAFoldedEquiv`.

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
  exact if hlt : (m : ℕ) < n then
    ⟨⟨m, hlt⟩, Or.inl (congrArg Subtype.val (e.symm_apply_apply _))⟩
  else ⟨⟨m.rev, by have := m.isLt; rw [Fin.val_rev]; omega⟩, Or.inr <|
    congrArg Subtype.val <| e.symm_apply_eq.mpr
      (hrev ⟨j, hj⟩ ⟨σ.indexEquiv j, hσ j hj⟩ rfl).symm⟩

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
    have hj_eq : (j : TypeAIndex (2 * n)) = typeAZeroSumSimplePair (2 * n) (e i) := by
      simp [i, ← coe_typeAZeroSumSimpleEquiv K]
    have hi : Φ.indexEquiv.symm j = i := Φ.indexEquiv.symm_apply_eq.mpr
      ((indexEquiv_evenTypeAToZeroSumEquiv_support P b e he i).trans hj_eq.symm).symm
    rw [Equiv.indexEquiv_autCongr_apply, hi, indexEquiv_evenTypeAToZeroSumEquiv_support P b e he
      ⟨σ.indexEquiv i, hσ i.val i.property⟩, hrev i ⟨_, hσ i.val i.property⟩ rfl,
      ← indexEquiv_typeAZeroSumRevAut_typeAZeroSumSimplePair K (2 * n) (e i), ← hj_eq]
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
    (fun k ↦ ⟨((evenTypeAWeightEquiv P b σ hσ e he hrev).symm
        ((typeBBaseChangeRootSystem K n).root k) : LinearMap.fixedSubmodule σ.weightMap),
      (mem_range_root_typeB_iff_mem_foldedIndices P b σ hσ e he hrev _).mp
        (by rw [LinearEquiv.apply_symm_apply]; exact Set.mem_range_self k)⟩)
    ⟨fun _ _ hk ↦ (typeBBaseChangeRootSystem K n).root.injective
      ((evenTypeAWeightEquiv P b σ hσ e he hrev).symm.injective
        (Subtype.ext (Subtype.mk.inj hk))),
      fun ⟨_, hv⟩ ↦ by
        set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
        obtain ⟨k, hk⟩ := (mem_range_root_typeB_iff_mem_foldedIndices P b σ hσ e he hrev
          ⟨_, P.orbitSum_mem_fixedSubmodule σ (mem_foldedIndices.mp hv).choose⟩).mpr
            (P.orbitSum_mem_foldedIndices σ _)
        exact ⟨k, Subtype.ext <| by
          dsimp only; rw [hk]; exact (congrArg Subtype.val
            (Ψ.symm_apply_apply ⟨_, _⟩)).trans (mem_foldedIndices.mp hv).choose_spec⟩⟩

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
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsRootSystem :=
  inferInstanceAs ((typeBBaseChangeRootSystem K n).map _ _ _).IsRootSystem

/-- `evenTypeAFoldedPairing` is reduced. -/
instance instIsReducedEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsReduced :=
  inferInstanceAs ((typeBBaseChangeRootSystem K n).map _ _ _).IsReduced

/-- `evenTypeAFoldedPairing` is crystallographic. -/
instance instIsCrystallographicEvenTypeAFoldedPairing :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).IsCrystallographic :=
  inferInstanceAs ((typeBBaseChangeRootSystem K n).map _ _ _).IsCrystallographic

/-- The bilinear pairing of `evenTypeAFoldedPairing` is dual evaluation `x ↦ φ ↦ φ x`. -/
@[simp] theorem toLinearMap_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (φ : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).toLinearMap x φ = φ x := by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev
  have hg : ∀ y : Fin n → K, ((_root_.dotProductEquiv K (Fin n)).trans Ψ.dualMap) y x =
      y ⬝ᵥ Ψ x := fun y ↦ by simp
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
      finDistinctPairsRevSwap (2 * n + 1) ((evenTypeAToZeroSumEquiv P b e he).indexEquiv r) :=
  ((evenTypeAToZeroSumEquiv P b e he).indexEquiv_apply_of_autCongr_eq
    (autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev) r).trans
    (by rw [indexEquiv_typeAZeroSumRevAut])

/-- Diagram reversal `σ` of even type `A (2 * n)` acts as an involution on root indices. -/
theorem indexEquiv_indexEquiv_evenTypeA (j : ι) : σ.indexEquiv (σ.indexEquiv j) = j := by
  apply (evenTypeAToZeroSumEquiv P b e he).indexEquiv.injective
  rw [indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev,
    indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev,
    finDistinctPairsRevSwap_finDistinctPairsRevSwap]

private lemma orbitSum_eq_add_evenTypeA {j : ι} (h : σ.indexEquiv j ≠ j) :
    P.orbitSum σ j = P.root j + P.root (σ.indexEquiv j) :=
  P.orbitSum_eq_add_of_apply_apply (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j) h

private lemma orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA {j : ι}
    (h : P.pairingIn ℤ (σ.indexEquiv j) j ≠ 2) :
    P.orbitSum σ j = P.root j + P.root (σ.indexEquiv j) :=
  orbitSum_eq_add_evenTypeA P b σ hσ e he hrev (P.ne_of_pairingIn_ne_two h)

private lemma pairing_indexEquiv_eq_neg_one_symm_evenTypeA {j : ι}
    (h : P.pairingIn ℤ (σ.indexEquiv j) j = -1) :
    P.pairing j (σ.indexEquiv j) = -1 :=
  (σ.pairing_indexEquiv_comm_of_apply_apply
    (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j)).trans
    (P.pairing_eq_neg_one_of_pairingIn_eq_neg_one h)

/-- Every root `j` of even type `A (2 * n)` under diagram reversal is either fixed by `σ`,
orthogonal to `σ.indexEquiv j`, or adjacent to `σ.indexEquiv j` with
`P.pairingIn ℤ (σ.indexEquiv j) j = -1`. -/
theorem indexEquiv_eq_self_or_pairingIn_eq_zero_or_neg_one_evenTypeA (j : ι) :
    σ.indexEquiv j = j ∨ P.pairingIn ℤ (σ.indexEquiv j) j = 0 ∨
      P.pairingIn ℤ (σ.indexEquiv j) j = -1 := by
  set Φ := evenTypeAToZeroSumEquiv P b e he; set p := Φ.indexEquiv j
  have hq : Φ.indexEquiv (σ.indexEquiv j) = finDistinctPairsRevSwap (2 * n + 1) p :=
    indexEquiv_evenTypeAToZeroSumEquiv_comp_aut P b σ hσ e he hrev j
  have hpair : P.pairing (σ.indexEquiv j) j = (if p.val.2.rev = p.val.1 then (1 : K) else 0) -
      (if p.val.2.rev = p.val.2 then 1 else 0) - (if p.val.1.rev = p.val.1 then 1 else 0) +
      (if p.val.1.rev = p.val.2 then 1 else 0) := by
    rw [← Φ.toHom.pairing, hq, ← root_coroot_eq_pairing, toLinearMap_typeAZeroSumRootPairing,
      root_typeAZeroSumRootPairing, coroot_typeAZeroSumRootPairing,
      typeAZeroSumVec_dotProduct_typeAZeroSumVec, finDistinctPairsRevSwap_apply_val]; ring
  by_cases hfix : p.val.2.rev = p.val.1
  · exact Or.inl <| Φ.indexEquiv.injective <| hq.trans
      ((finDistinctPairsRevSwap_eq_self_iff_snd_eq_rev p).mpr (by rw [← hfix, Fin.rev_rev]))
  · right; have hfix' : p.val.1.rev ≠ p.val.2 := fun h ↦ hfix (by rw [← h, Fin.rev_rev])
    rw [ite_eq_right hfix, ite_eq_right hfix'] at hpair
    by_cases h2 : p.val.2.rev = p.val.2 <;> by_cases h1 : p.val.1.rev = p.val.1
    · exact absurd ((rev_eq_self_iff_eq_evenTypeAMidIdx.mp h1).trans
        (rev_eq_self_iff_eq_evenTypeAMidIdx.mp h2).symm) p.property
    · exact Or.inr <| P.pairingIn_eq_of_pairing_eq_intCast (by simp [hpair, h2, h1])
    · exact Or.inr <| P.pairingIn_eq_of_pairing_eq_intCast (by simp [hpair, h2, h1])
    · exact Or.inl <| P.pairingIn_eq_of_pairing_eq_intCast (by simp [hpair, h2, h1])

omit [P.IsRootSystem] [P.IsReduced] b hσ e he hrev in
private lemma reflection_fixed_eq_preReflection_of_indexEquiv_eq {j : ι}
    (hfix : σ.indexEquiv j = j) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (x : M) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  rw [ite_eq_right (by rw [hfix, P.pairingIn_same]; decide), one_mul,
    orbitSum_eq_root_of_indexEquiv_eq hfix, reflection_apply]

private lemma reflection_fixed_eq_preReflection_of_pairingIn_eq_zero {j : ι}
    (h0 : P.pairingIn ℤ (σ.indexEquiv j) j = 0) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (P.reflection (σ.indexEquiv j) (x : M)) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  rw [ite_eq_right (by rw [h0]; decide), one_mul,
    orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA P b σ hσ e he hrev (by rw [h0]; decide),
    P.reflection_reflection_of_pairing_eq_zero (P.pairing_eq_zero_of_pairingIn_eq_zero h0),
    P.coroot'_indexEquiv_of_mem_fixedSubmodule σ j x.property, smul_add, sub_sub,
    add_comm (P.coroot' j (x : M) • P.root (σ.indexEquiv j))]

private lemma reflection_fixed_eq_preReflection_of_pairingIn_eq_neg_one {j : ι}
    (hneg : P.pairingIn ℤ (σ.indexEquiv j) j = -1) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.reflection j (P.reflection (σ.indexEquiv j) (P.reflection j (x : M))) =
      (x : M) - ((if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then (2 : K) else 1) *
        P.coroot' j (x : M)) • P.orbitSum σ j := by
  rw [ite_eq_left hneg,
    orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA P b σ hσ e he hrev (by rw [hneg]; decide),
    P.reflection_reflection_reflection_of_pairing_eq_neg_one
      (P.pairing_eq_neg_one_of_pairingIn_eq_neg_one hneg)
      (pairing_indexEquiv_eq_neg_one_symm_evenTypeA P b σ hσ e he hrev hneg),
    P.coroot'_indexEquiv_of_mem_fixedSubmodule σ j x.property,
    add_comm (P.coroot' j (x : M)), add_comm (P.root (σ.indexEquiv j)), ← two_mul]

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
  · exact ⟨by rw [ite_eq_right (by rw [hfix, P.pairingIn_same]; decide), one_mul,
      orbitSum_eq_root_of_indexEquiv_eq hfix, root_coroot'_eq_pairing, pairing_same],
      Equiv.reflection P j, σ.indexEquiv_reflection_comm_of_indexEquiv_eq hfix, fun x ↦ by
        rw [Equiv.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_indexEquiv_eq P σ hfix x]⟩
  · have h0K := P.pairing_eq_zero_of_pairingIn_eq_zero h0
    refine ⟨?_, Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j),
      σ.indexEquiv_reflection_mul_comm_of_pairing_eq_zero
        (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j) h0K, fun x ↦ by
        simp only [Equiv.weightMap_mul_apply, Equiv.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_pairingIn_eq_zero P b σ hσ e he hrev h0 x]⟩
    rw [ite_eq_right (by rw [h0]; decide), one_mul,
      orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA P b σ hσ e he hrev (by rw [h0]; decide),
      map_add, root_coroot'_eq_pairing, root_coroot'_eq_pairing, pairing_same, h0K, add_zero]
  · have hnegK := P.pairing_eq_neg_one_of_pairingIn_eq_neg_one hneg
    refine ⟨?_, Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) * Equiv.reflection P j,
      σ.indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one
        (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j) hnegK, fun x ↦ by
        simp only [Equiv.weightMap_mul_apply, Equiv.reflection_weightMap_apply,
          reflection_fixed_eq_preReflection_of_pairingIn_eq_neg_one P b σ hσ e he hrev hneg x]⟩
    rw [ite_eq_left hneg,
      orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA P b σ hσ e he hrev (by rw [hneg]; decide),
      map_add, root_coroot'_eq_pairing, root_coroot'_eq_pairing, pairing_same, hnegK]; norm_num

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
  have heq : P'.coroot' v = f := Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range P'.root)
    IsRootSystem.span_root_eq_top (P'.coroot_root_two v) (P'.mapsTo_reflection_root v)
    (by dsimp only [f]; rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      coe_root_evenTypeAFoldedPairing, smul_eq_mul, ← hv]; exact hc2)
    (by
      rintro _ ⟨u, rfl⟩
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.property
      refine ⟨⟨P.orbitSum σ (w.indexEquiv i), P.orbitSum_mem_foldedIndices σ _⟩, Subtype.ext ?_⟩
      have hu := hw_eq (P'.root u); rw [coe_root_evenTypeAFoldedPairing] at hu
      dsimp only [f]; rw [coe_root_evenTypeAFoldedPairing, Subtype.coe_mk,
        Module.preReflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower,
        coe_root_evenTypeAFoldedPairing, coe_root_evenTypeAFoldedPairing, LinearMap.smul_apply,
        LinearMap.comp_apply, Submodule.coe_subtype, coe_root_evenTypeAFoldedPairing, smul_eq_mul,
        ← hv, ← hu, ← hi, weightMap_orbitSum w hw_comm i])
  exact LinearMap.congr_fun heq x

/-- Evaluating the folded coroot at any folded index `v = P.orbitSum σ j` on a fixed weight `x`
scales `P.coroot' j x` by `2` when `P.pairingIn ℤ (σ.indexEquiv j) j = -1` and by `1` otherwise. -/
theorem coroot_evenTypeAFoldedPairing {v : P.foldedIndices σ} {j : ι}
    (hv : P.orbitSum σ j = (v : M)) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot v x =
      (if P.pairingIn ℤ (σ.indexEquiv j) j = -1 then 2 else 1) * P.coroot' j (x : M) :=
  coroot'_evenTypeAFoldedPairing_eq_coroot P b σ hσ e he hrev v ▸
    coroot'_evenTypeAFoldedPairing P b σ hσ e he hrev hv x

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
theorem pairing_evenTypeAFoldedPairing_eq_mul_sum {u v : P.foldedIndices σ} {i j : ι}
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
  refine FaithfulSMul.algebraMap_injective ℤ K ?_
  rw [algebraMap_pairingIn, pairing_evenTypeAFoldedPairing_eq_mul_sum P b σ hσ e he hrev hu hv,
    map_mul, map_sum, apply_ite (algebraMap ℤ K)]
  simp only [map_ofNat, map_one, algebraMap_pairingIn]

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
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev _, root_reflectionPerm,
    coe_reflection_evenTypeAFoldedPairing P b σ hσ e he hrev hv, coe_root_evenTypeAFoldedPairing]

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
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev _, root_reflectionPerm,
    reflection_apply_self, Submodule.coe_neg, coe_root_evenTypeAFoldedPairing]

private lemma reflectionPerm_evenTypeAFoldedPairing_of_aut {v w : P.foldedIndices σ} {i : ι}
    (u : P.Aut) (hu_comm : ∀ r, u.indexEquiv (σ.indexEquiv r) = σ.indexEquiv (u.indexEquiv r))
    (hact : ∀ x : LinearMap.fixedSubmodule σ.weightMap,
      (((P.evenTypeAFoldedPairing b σ hσ e he hrev).reflection v x :
        LinearMap.fixedSubmodule σ.weightMap) : M) = u.weightMap (x : M))
    (hw : P.orbitSum σ i = (w : M)) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (u.indexEquiv i), P.orbitSum_mem_foldedIndices σ _⟩ := Subtype.ext <| by
  rw [← coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev _, root_reflectionPerm, hact,
    coe_root_evenTypeAFoldedPairing, ← hw, weightMap_orbitSum u hu_comm i]

/-- At a `σ`-fixed root `j`, the folded reflection permutation sends the orbit of `i` to the orbit
of `P.reflectionPerm j i`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_indexEquiv_eq {v w : P.foldedIndices σ} {i j : ι}
    (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M)) (hfix : σ.indexEquiv j = j) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j i), P.orbitSum_mem_foldedIndices σ _⟩ :=
  reflectionPerm_evenTypeAFoldedPairing_of_aut P b σ hσ e he hrev (Equiv.reflection P j)
    (σ.indexEquiv_reflection_comm_of_indexEquiv_eq hfix)
    (fun x ↦ (coe_reflection_evenTypeAFoldedPairing_of_indexEquiv_eq P b σ hσ e he hrev
      hv hfix x).trans (Equiv.reflection_weightMap_apply _ _ _).symm) hw

/-- At an orthogonal pair (`P.pairingIn ℤ (σ.indexEquiv j) j = 0`), the folded reflection
permutation acts on orbit representatives by
`P.reflectionPerm j ∘ P.reflectionPerm (σ.indexEquiv j)`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_pairingIn_eq_zero {v w : P.foldedIndices σ}
    {i j : ι} (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M))
    (h0 : P.pairingIn ℤ (σ.indexEquiv j) j = 0) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j) i)),
        P.orbitSum_mem_foldedIndices σ _⟩ :=
  reflectionPerm_evenTypeAFoldedPairing_of_aut P b σ hσ e he hrev
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j))
    (σ.indexEquiv_reflection_mul_comm_of_pairing_eq_zero
      (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j)
      (P.pairing_eq_zero_of_pairingIn_eq_zero h0))
    (fun x ↦ (coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_zero P b σ hσ e he hrev
      hv h0 x).trans (by
        simp only [Equiv.weightMap_mul_apply, Equiv.reflection_weightMap_apply])) hw

/-- At an adjacent pair (`P.pairingIn ℤ (σ.indexEquiv j) j = -1`), the folded reflection
permutation acts on orbit representatives by
`P.reflectionPerm j ∘ P.reflectionPerm (σ.indexEquiv j) ∘ P.reflectionPerm j`. -/
theorem reflectionPerm_evenTypeAFoldedPairing_of_pairingIn_eq_neg_one {v w : P.foldedIndices σ}
    {i j : ι} (hv : P.orbitSum σ j = (v : M)) (hw : P.orbitSum σ i = (w : M))
    (hneg : P.pairingIn ℤ (σ.indexEquiv j) j = -1) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).reflectionPerm v w =
      ⟨P.orbitSum σ (P.reflectionPerm j (P.reflectionPerm (σ.indexEquiv j)
          (P.reflectionPerm j i))), P.orbitSum_mem_foldedIndices σ _⟩ :=
  reflectionPerm_evenTypeAFoldedPairing_of_aut P b σ hσ e he hrev
    (Equiv.reflection P j * Equiv.reflection P (σ.indexEquiv j) * Equiv.reflection P j)
    (σ.indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one
      (indexEquiv_indexEquiv_evenTypeA P b σ hσ e he hrev j)
      (P.pairing_eq_neg_one_of_pairingIn_eq_neg_one hneg))
    (fun x ↦ (coe_reflection_evenTypeAFoldedPairing_of_pairingIn_eq_neg_one P b σ hσ e he hrev
      hv hneg x).trans (by
        simp only [Equiv.weightMap_mul_apply, Equiv.reflection_weightMap_apply])) hw

private lemma evenTypeAIndexEquiv_typeBSimpleIndex (k : Fin n) :
    evenTypeAIndexEquiv P b σ hσ e he hrev (typeBSimpleIndex n k) =
      b.evenTypeAFoldedSimpleIndex σ e k := Subtype.ext <| by
  set Ψ := evenTypeAWeightEquiv P b σ hσ e he hrev; set Φ := evenTypeAToZeroSumEquiv P b e he
  let jk : b.support := e.symm ⟨k, by have := k.isLt; omega⟩
  have hΨ : Ψ ⟨P.orbitSum σ jk, P.orbitSum_mem_fixedSubmodule σ jk⟩ =
      (typeBBaseChangeRootSystem K n).root (typeBSimpleIndex n k) := by
    dsimp [Ψ, evenTypeAWeightEquiv]
    rw [← evenTypeAFixedCoordEquiv_orbitSum_typeAZeroSumSimplePair K n k]
    refine congrArg _ <| Subtype.ext ?_
    simp only [LinearEquiv.fixedSubmoduleCongr_apply, Equiv.weightEquiv_apply]
    rw [Φ.weightMap_orbitSum_of_autCongr (autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev),
      indexEquiv_evenTypeAToZeroSumEquiv_support P b e he jk]; simp [jk]
  change ((Ψ.symm _ : LinearMap.fixedSubmodule σ.weightMap) : M) = _
  rw [Base.coe_evenTypeAFoldedSimpleIndex, ← hΨ, Ψ.symm_apply_apply]

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
  refine ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, (mem_support_typeBBaseChangeBase_iff K n m).mp hm⟩,
      by rw [← h, ← evenTypeAIndexEquiv_typeBSimpleIndex]; exact congrArg _ (Fin.ext (by simp))⟩,
    fun ⟨k, hk⟩ ↦ ⟨typeBSimpleIndex n k, (mem_support_typeBBaseChangeBase_iff K n _).mpr
      ((typeBSimpleIndex_val k).symm ▸ k.isLt), by rw [hk, evenTypeAIndexEquiv_typeBSimpleIndex]⟩⟩

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

/-- **Bundled orbit-sum realization** of `(P, b, σ)` from `evenTypeAFoldedPairing` and
`evenTypeAFoldedBase`. -/
noncomputable def Base.evenTypeAOrbitSumRealization : P.OrbitSumRealization b σ where
  pairing := P.evenTypeAFoldedPairing b σ hσ e he hrev
  base := b.evenTypeAFoldedBase σ hσ e he hrev
  rootSystem := inferInstance
  reduced := inferInstance
  crystallographic := inferInstance
  evaluation := toLinearMap_evenTypeAFoldedPairing P b σ hσ e he hrev
  root_eq := coe_root_evenTypeAFoldedPairing P b σ hσ e he hrev
  base_eq := b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev

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
  obtain ⟨f, _⟩ := (hasCartanType_iff _ _).mp (b.hasCartanType_evenTypeAFoldedBase σ hσ e he hrev)
  refine (hasCartanType_iff _ _).mpr ⟨f, fun i j ↦ ?_⟩
  obtain rfl : i = j := f.injective (Fin.ext (by
    have hi : (f i : ℕ) < 1 := (f i).isLt; have hj : (f j : ℕ) < 1 := (f j).isLt; omega))
  simp [DynkinType.cartanMatrix_A, CartanMatrix.A]

/-- **Simple-coroot evaluation on fixed weights:** scales by `1` for `k + 1 < n` and `2` for
`k + 1 = n`. -/
theorem Base.coroot'_evenTypeAFoldedPairing_simpleIndex (k : Fin n)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot'
        (b.evenTypeAFoldedSimpleIndex σ e k) x =
      (if (k : ℕ) + 1 = n then 2 else 1) *
        P.coroot' (e.symm ⟨k, by have := k.isLt; omega⟩) (x : M) := by
  have hk := k.isLt; set Φ := evenTypeAToZeroSumEquiv P b e he
  rw [evenTypeAFoldedPairing_eq_map, coroot'_map, LinearEquiv.symm_symm,
    (evenTypeAIndexEquiv P b σ hσ e he hrev).symm_apply_eq.mpr
      (evenTypeAIndexEquiv_typeBSimpleIndex P b σ hσ e he hrev k).symm,
    coroot'_typeBBaseChangeRootSystem_simpleIndex]
  dsimp only [evenTypeAWeightEquiv, LinearEquiv.trans_apply]
  rw [evenTypeAFixedCoordEquiv_apply, LinearEquiv.fixedSubmoduleCongr_apply, Subtype.coe_mk,
    Equiv.weightEquiv_apply, show typeAZeroSumSimplePair (2 * n) ⟨k, by omega⟩ =
      Φ.indexEquiv (e.symm ⟨k, by omega⟩) by
        rw [indexEquiv_evenTypeAToZeroSumEquiv_support P b e he, Equiv.apply_symm_apply],
    Hom.coroot'_weightMap]

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

/-- **Positive roots of the folded base:** orbit sums of positive roots of `b`. -/
theorem Base.isPos_evenTypeAFoldedBase_iff (v : P.foldedIndices σ) :
    (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v ↔
      ∃ j, b.IsPos j ∧ P.orbitSum σ j = (v : M) :=
  (b.evenTypeAOrbitSumRealization σ hσ e he hrev).isPos_iff_exists_isPos hσ v

/-- **Forward simple-coroot integrality on fixed weights.** -/
theorem Base.exists_int_coroot'_evenTypeAFoldedPairing (x : LinearMap.fixedSubmodule σ.weightMap)
    (hint : ∀ j ∈ b.support, ∃ z : ℤ, P.coroot' j (x : M) = z) :
    ∀ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support,
      ∃ z : ℤ, (P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x = z := fun v hv ↦ by
  obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
  obtain ⟨z, hz⟩ := hint _ (e.symm ⟨k, by have := k.isLt; omega⟩).property
  exact ⟨(if (k : ℕ) + 1 = n then 2 else 1) * z, by
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev, hz]; split_ifs <;> simp⟩

private lemma not_eq_neg_evenTypeABasisVec_of_isPos {v : P.foldedIndices σ}
    (hv_pos : (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v) (i : Fin n) :
    (evenTypeAToZeroSumEquiv P b e he).weightMap (v : M) ≠ -evenTypeABasisVec K n i := fun hneg ↦ by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev; set Φ := evenTypeAToZeroSumEquiv P b e he
  have hφ := autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) := TauCeti.map_equivOfCartanMatrixEq ..
  obtain ⟨hp_pos, _, hp_sum⟩ := evenTypeAFixedShortLift_spec K n i
  let r := Φ.indexEquiv.symm (evenTypeAFixedShortLift n i)
  refine reflectionPerm_self_notMem_posRoots P' _ ((mem_posRoots P' _ v).mpr hv_pos)
    ((mem_posRoots P' _ _).mpr <| (b.isPos_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr
      ⟨r, (b.isPos_map_iff Φ r).mp (by simpa [hb_map, r] using hp_pos),
        (Φ.weightEquiv.injective <| by
          simp [Φ.weightMap_orbitSum_of_autCongr hφ, r, hp_sum, hneg]).trans
          (coe_reflectionPerm_evenTypeAFoldedPairing_self P b σ hσ e he hrev v).symm⟩)

private lemma indexEquiv_ne_and_pairingIn_ne_neg_one_of_dotProduct_eq_four {r : ι}
    (hdot : (((evenTypeAToZeroSumEquiv P b e he).weightMap (P.orbitSum σ r) :
      singleParityCheckCode K (Fin (2 * n + 1))) : Fin (2 * n + 1) → K) ⬝ᵥ
      ((evenTypeAToZeroSumEquiv P b e he).weightMap (P.orbitSum σ r) :
        Fin (2 * n + 1) → K) = 4) :
    σ.indexEquiv r ≠ r ∧ P.pairingIn ℤ (σ.indexEquiv r) r ≠ -1 := by
  set Φ := evenTypeAToZeroSumEquiv P b e he; set q := Φ.indexEquiv r
  have hφ := autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev
  refine ⟨fun hfix ↦ ?_, fun hneg ↦ ?_⟩
  · rw [show Φ.weightMap (P.orbitSum σ r) = (typeAZeroSumRootPairing K (2 * n)).root q from by
        rw [Φ.weightMap_orbitSum_of_autCongr hφ r, orbitSum_eq_root_of_indexEquiv_eq
          (by rw [← Φ.indexEquiv_apply_of_autCongr_eq hφ, hfix])],
      root_typeAZeroSumRootPairing, typeAZeroSumVec_dotProduct_self K q.property] at hdot
    norm_num at hdot
  · have hadd : Φ.weightMap (P.orbitSum σ r) = (typeAZeroSumRootPairing K (2 * n)).root q +
        (typeAZeroSumRootPairing K (2 * n)).root (Φ.indexEquiv (σ.indexEquiv r)) := by
      rw [orbitSum_eq_add_of_pairingIn_ne_two_evenTypeA P b σ hσ e he hrev (by rw [hneg]; decide),
        map_add, Hom.root_weightMap_apply, Hom.root_weightMap_apply]
    simp only [q, hadd, Submodule.coe_add, add_dotProduct, dotProduct_add,
      root_dotProduct_root_typeAZeroSumRootPairing, pairing_same,
      Φ.toHom.pairing.trans (P.pairing_eq_neg_one_of_pairingIn_eq_neg_one hneg),
      Φ.toHom.pairing.trans
        (pairing_indexEquiv_eq_neg_one_symm_evenTypeA P b σ hσ e he hrev hneg)] at hdot
    norm_num at hdot

private lemma not_short_of_mem_long_orbit {v : P.foldedIndices σ}
    (hv_short : ∀ w : P.foldedIndices σ,
      2 ∣ (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ w v)
    {i j : Fin n} (hij : i ≠ j)
    (hsum : (evenTypeAToZeroSumEquiv P b e he).weightMap (v : M) =
        evenTypeABasisVec K n i + evenTypeABasisVec K n j ∨
      (evenTypeAToZeroSumEquiv P b e he).weightMap (v : M) =
        evenTypeABasisVec K n i - evenTypeABasisVec K n j ∨
      (evenTypeAToZeroSumEquiv P b e he).weightMap (v : M) =
        -evenTypeABasisVec K n i + evenTypeABasisVec K n j ∨
      (evenTypeAToZeroSumEquiv P b e he).weightMap (v : M) =
        -evenTypeABasisVec K n i - evenTypeABasisVec K n j) : False := by
  let P' := P.evenTypeAFoldedPairing b σ hσ e he hrev; set Φ := evenTypeAToZeroSumEquiv P b e he
  have hφ := autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp v.property; let q := Φ.indexEquiv r
  obtain ⟨hne, hc_ne⟩ := indexEquiv_ne_and_pairingIn_ne_neg_one_of_dotProduct_eq_four
    b σ hσ e he hrev (hr.symm ▸ evenTypeABasisVec_signed_add_dotProduct_self K hij hsum)
  have hx_add : Φ.weightMap (v : M) = (typeAZeroSumRootPairing K (2 * n)).root q +
      (typeAZeroSumRootPairing K (2 * n)).root ((typeAZeroSumRevAut K (2 * n)).indexEquiv q) := by
    have h := congrArg Φ.weightMap
      (hr.symm.trans (orbitSum_eq_add_evenTypeA P b σ hσ e he hrev hne))
    rwa [map_add, Hom.root_weightMap_apply, Hom.root_weightMap_apply,
      Φ.indexEquiv_apply_of_autCongr_eq hφ] at h
  let w : P.foldedIndices σ := (Φ.foldedIndicesCongr hφ).symm
    ⟨evenTypeABasisVec K n i, (evenTypeAFixedShortLift_spec K n i).2.2 ▸
      orbitSum_mem_foldedIndices _ _ _⟩
  obtain ⟨z, hz⟩ := hv_short w
  have hpair_val : P'.pairing w v = (evenTypeABasisVec K n i : Fin (2 * n + 1) → K) ⬝ᵥ
      ((typeAZeroSumRootPairing K (2 * n)).root q : Fin (2 * n + 1) → K) := by
    dsimp only [w]
    rw [pairing_evenTypeAFoldedPairing P b σ hσ e he hrev hr, ite_eq_right hc_ne, one_mul,
      ← Φ.toHom.coroot'_weightMap r, ← Equiv.weightEquiv_apply,
      Equiv.coe_foldedIndicesCongr_symm_apply, LinearEquiv.apply_symm_apply,
      coroot'_typeAZeroSumRootPairing, root_typeAZeroSumRootPairing, coe_typeAZeroSumVec]
    simp [dotProduct_sub, dotProduct_single, q]
  have hsym := (typeAZeroSumRootPairing K (2 * n)).coroot'_indexEquiv_of_mem_fixedSubmodule
    (typeAZeroSumRevAut K (2 * n)) q (evenTypeABasisVec_mem_fixedSubmodule K n i)
  simp only [RootPairing.coroot', LinearMap.flip_apply, toLinearMap_typeAZeroSumRootPairing,
    coroot_typeAZeroSumRootPairing, ← root_typeAZeroSumRootPairing] at hsym
  have h4 := evenTypeABasisVec_dotProduct_signed_add K hij hsum
  rw [hx_add, Submodule.coe_add, dotProduct_add, hsym, ← two_mul, ← hpair_val,
    ← P'.algebraMap_pairingIn ℤ, hz] at h4
  simp only [eq_intCast] at h4
  rcases h4 with h4 | h4 <;> norm_cast at h4 <;> omega

private lemma exists_pos_lift_of_short {v : P.foldedIndices σ}
    (hv_pos : (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v)
    (hv_short : ∀ w : P.foldedIndices σ,
      2 ∣ (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ w v) (m : ℕ)
    (hm : ∀ i : Fin n, ∃ p : TypeAIndex (2 * n), (typeAZeroSumBase K (2 * n)).IsPos p ∧
        #((typeAZeroSumRootPairing K (2 * n)).orbitIndices (typeAZeroSumRevAut K (2 * n)) p) = m ∧
        (typeAZeroSumRootPairing K (2 * n)).orbitSum (typeAZeroSumRevAut K (2 * n)) p =
          evenTypeABasisVec K n i) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = m ∧ P.orbitSum σ j = (v : M) := by
  set Φ := evenTypeAToZeroSumEquiv P b e he
  have hφ := autCongr_evenTypeAToZeroSumEquiv P b σ hσ e he hrev
  have hb_map : b.map Φ = typeAZeroSumBase K (2 * n) := TauCeti.map_equivOfCartanMatrixEq ..
  have h_exists_i : ∃ i : Fin n, Φ.weightMap (v : M) = evenTypeABasisVec K n i := by
    rcases (mem_foldedIndices_typeAZeroSumRevAut_iff K n (Φ.weightMap (v : M))).mp
        (Φ.mem_foldedIndices_weightMap hφ v) with ⟨i, hi | hneg⟩ | ⟨i, j, hij, hsum⟩
    · exact ⟨i, hi⟩
    · exact absurd hneg (not_eq_neg_evenTypeABasisVec_of_isPos b σ hσ e he hrev hv_pos i)
    · exact absurd hsum (not_short_of_mem_long_orbit b σ hσ e he hrev hv_short hij)
  obtain ⟨i, hi⟩ := h_exists_i; obtain ⟨p, hp_pos, hp_card, hp_sum⟩ := hm i
  let j := Φ.indexEquiv.symm p
  refine ⟨j, (b.isPos_map_iff Φ j).mp (by simpa [hb_map, j] using hp_pos),
    ?_, Φ.weightEquiv.injective <| by simp [Φ.weightMap_orbitSum_of_autCongr hφ, j, hp_sum, hi]⟩
  have hcard := congrArg Finset.card <| map_orbitIndices (σ := σ)
    (τ := typeAZeroSumRevAut K (2 * n)) Φ (Φ.indexEquiv_apply_of_autCongr_eq hφ) j
  rw [Finset.card_map, Equiv.apply_symm_apply] at hcard; exact hcard.trans hp_card

/-- Every positive short folded root (`2 ∣ P'.pairingIn ℤ w v` for all `w`) lifts to a `σ`-fixed
positive root of `b`. -/
theorem Base.exists_fixed_pos_lift_evenTypeAFoldedBase {v : P.foldedIndices σ}
    (hv_pos : (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v)
    (hv_short : ∀ w : P.foldedIndices σ,
      2 ∣ (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ w v) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 1 ∧ P.orbitSum σ j = (v : M) :=
  exists_pos_lift_of_short b σ hσ e he hrev hv_pos hv_short 1
    fun i ↦ ⟨evenTypeAFixedShortLift n i, evenTypeAFixedShortLift_spec K n i⟩

/-- Every positive short folded root (`2 ∣ P'.pairingIn ℤ w v` for all `w`) lifts to a positive
root of `b` of orbit size `2`. -/
theorem Base.exists_paired_pos_lift_evenTypeAFoldedBase {v : P.foldedIndices σ}
    (hv_pos : (b.evenTypeAFoldedBase σ hσ e he hrev).IsPos v)
    (hv_short : ∀ w : P.foldedIndices σ,
      2 ∣ (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ w v) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 2 ∧ P.orbitSum σ j = (v : M) :=
  exists_pos_lift_of_short b σ hσ e he hrev hv_pos hv_short 2
    fun i ↦ ⟨evenTypeAPairedShortLift n i, evenTypeAPairedShortLift_spec K n i⟩

private lemma even_dvd_pairingIn_simpleIndex {k : Fin n} (hk : (k : ℕ) + 1 = n)
    (w : P.foldedIndices σ) :
    2 ∣ (P.evenTypeAFoldedPairing b σ hσ e he hrev).pairingIn ℤ w
      (b.evenTypeAFoldedSimpleIndex σ e k) := by
  obtain ⟨i, hi⟩ := mem_foldedIndices.mp w.property
  let jk : b.support := e.symm ⟨k, by have := k.isLt; omega⟩
  have hjk : (e jk : ℕ) = n - 1 := by simp [jk]; omega
  have hrev_jk : (e ⟨σ.indexEquiv jk, hσ jk jk.property⟩ : ℕ) = n := by
    rw [hrev jk _ rfl, Fin.val_rev, hjk]; have := k.isLt; omega
  have hneg : P.pairingIn ℤ (σ.indexEquiv jk) jk = -1 := by
    rw [← Base.cartanMatrixIn_def (b := b) (S := ℤ) ⟨σ.indexEquiv jk, hσ jk jk.property⟩ jk,
      ← Base.cartanMatrix, he, DynkinType.cartanMatrix_A]
    simp [CartanMatrix.A, Fin.ext_iff, hrev_jk, hjk]; omega
  rw [pairingIn_evenTypeAFoldedPairing P b σ hσ e he hrev hi
    (Base.coe_evenTypeAFoldedSimpleIndex b σ e k).symm, ite_eq_left hneg]
  exact dvd_mul_right 2 _

/-- The short simple folded root (`k + 1 = n`) lifts to a `σ`-fixed positive root of `b`. -/
theorem Base.exists_fixed_pos_lift_shortSimple_evenTypeAFoldedBase {k : Fin n}
    (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 1 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) :=
  b.exists_fixed_pos_lift_evenTypeAFoldedBase σ hσ e he hrev
    ((b.evenTypeAFoldedBase σ hσ e he hrev).isPos_of_mem_support
      (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev k))
    (even_dvd_pairingIn_simpleIndex b σ hσ e he hrev hk)

/-- The short simple folded root (`k + 1 = n`) lifts to a positive root of `b` of orbit size `2`. -/
theorem Base.exists_paired_pos_lift_shortSimple_evenTypeAFoldedBase {k : Fin n}
    (hk : (k : ℕ) + 1 = n) :
    ∃ j, b.IsPos j ∧ #(P.orbitIndices σ j) = 2 ∧
      P.orbitSum σ j = (b.evenTypeAFoldedSimpleIndex σ e k : M) :=
  b.exists_paired_pos_lift_evenTypeAFoldedBase σ hσ e he hrev
    ((b.evenTypeAFoldedBase σ hσ e he hrev).isPos_of_mem_support
      (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev k))
    (even_dvd_pairingIn_simpleIndex b σ hσ e he hrev hk)

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
private lemma mem_chamber_evenTypeAFoldedPairing_iff {R : K → Prop}
    (hR : ∀ {a c : K}, 0 < a → (R (a * c) ↔ R c)) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (∀ v ∈ (b.evenTypeAFoldedBase σ hσ e he hrev).support,
        R ((P.evenTypeAFoldedPairing b σ hσ e he hrev).coroot' v x)) ↔
      ∀ j ∈ b.support, R (P.coroot' j (x : M)) := by
  refine ⟨fun hx j hj ↦ ?_, fun hx v hv ↦ ?_⟩
  · obtain ⟨k, hkj⟩ := exists_fin_of_mem_support b σ hσ e hrev hj
    have hv := hx _ (b.evenTypeAFoldedSimpleIndex_mem_support σ hσ e he hrev k)
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev] at hv
    rw [hR (by split_ifs <;> norm_num)] at hv
    rcases hkj with hkj | hkj
    · rwa [← hkj]
    · rwa [hkj, ← LinearMap.mem_fixedSubmodule_iff.mp x.property, Hom.coroot'_weightMap] at hv
  · obtain ⟨k, rfl⟩ := (b.mem_support_evenTypeAFoldedBase_iff_exists_fin σ hσ e he hrev v).mp hv
    rw [b.coroot'_evenTypeAFoldedPairing_simpleIndex σ hσ e he hrev,
      hR (by split_ifs <;> norm_num)]
    exact hx _ (e.symm ⟨k, by have := k.isLt; omega⟩).property

/-- **Closed dominant chamber transport on fixed weights:** a fixed weight lies in the closed
dominant chamber of `evenTypeAFoldedPairing` with respect to `evenTypeAFoldedBase` if and only if
its coercion lies in `P.dominantChamber b`. -/
theorem Base.mem_dominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).dominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) ↔ (x : M) ∈ P.dominantChamber b := by
  simpa only [mem_dominantChamber] using mem_chamber_evenTypeAFoldedPairing_iff b σ hσ e he hrev
    (fun hc ↦ mul_nonneg_iff_of_pos_left hc) x

/-- **Open dominant chamber transport on fixed weights:** a fixed weight lies in the open
dominant chamber of `evenTypeAFoldedPairing` with respect to `evenTypeAFoldedBase` if and only if
its coercion lies in `P.openDominantChamber b`. -/
theorem Base.mem_openDominantChamber_evenTypeAFoldedPairing_iff
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    x ∈ (P.evenTypeAFoldedPairing b σ hσ e he hrev).openDominantChamber
        (b.evenTypeAFoldedBase σ hσ e he hrev) ↔ (x : M) ∈ P.openDominantChamber b := by
  simpa only [mem_openDominantChamber] using mem_chamber_evenTypeAFoldedPairing_iff b σ hσ e he hrev
    (fun hc ↦ mul_pos_iff_of_pos_left hc) x

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
    (φ.foldedIndicesCongr hφ) fun v ↦ Subtype.ext (by simp)

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
    exact (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ _).mpr
      ⟨φ.indexEquiv j, by rw [← hb, Base.support_map_eq]; exact mem_image_of_mem _ hj,
        by simp [← hvj, φ.weightMap_orbitSum_of_autCongr hφ j]⟩
  · obtain ⟨j₂, hj₂, hwj⟩ := (b₂.mem_support_evenTypeAFoldedBase_iff σ₂ hσ₂ e₂ he₂ hrev₂ w).mp hw
    rw [← hb, Base.support_map_eq, mem_image] at hj₂; obtain ⟨j, hj, rfl⟩ := hj₂
    exact ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
      (b.mem_support_evenTypeAFoldedBase_iff σ hσ e he hrev _).mpr ⟨j, hj, rfl⟩,
      Subtype.ext (by simp [← hwj, φ.weightMap_orbitSum_of_autCongr hφ j])⟩

end Functoriality

end RootPairing
