/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Transport
public import TauCeti.Algebra.Lie.Weights.PairingInvariance
public import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Vector

import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Realizing Chevalley structure constants from a Killing Chevalley system

Given a finite-dimensional characteristic-zero Killing Lie algebra `L` with splitting Cartan
subalgebra `H` and `hx : TauCeti.IsChevalleySystem ω x`, this file extracts
`IsChevalleySystem.chevalleyConstants` on `P : RootPairing ι ℤ X Y` along `e : ι ≃ H.root`,
compares `ChevalleyLieAlgebra` with `hx.chevalleyLieLattice` (`toChevalleyLieLattice`,
`toChevalleyLieLatticeEquiv`), and specializes to `TauCeti.DynkinType`
(`simplyConnectedChevalleyConstants`, `simplyConnectedChevalleyLieEquiv`, `chevalleyConstants`).

## References

* C. Chevalley, *Sur certains groupes simples*, Tohoku Math. J. (2) **7** (1955), 14--66.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.2.
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule Module Set
open RootPairing (ChevalleyLieAlgebra)

namespace TauCeti

namespace IsChevalleySystem

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : IsChevalleySystem ω x)
  {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing ι ℤ X Y) (e : ι ≃ H.root)
  (he : ∀ i j, (rootSystem H).pairingIn ℤ (e i) (e j) = P.pairing i j)

private noncomputable def rawStructConst (i j : ι) : ℤ :=
  P.rootSumElim i j fun k hk ↦ hx.intStructureConstant (e i) (e j) (e k)
    (H.isNonZero_coe_root _) (coe_weight_eq_add_of_root_eq_add e he hk)

private theorem rawStructConst_of_root_eq_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    hx.rawStructConst P e he i j = hx.intStructureConstant (e i) (e j) (e k)
      (H.isNonZero_coe_root _) (coe_weight_eq_add_of_root_eq_add e he hk) :=
  P.rootSumElim_of_root_eq_add hk _

private theorem rawStructConst_of_notMem {i j : ι} (hnot : P.root i + P.root j ∉ range P.root) :
    hx.rawStructConst P e he i j = 0 := P.rootSumElim_of_notMem_range hnot _

private theorem lie_eq_rawStructConst_zsmul {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    ⁅x (e i), x (e j)⁆ = hx.rawStructConst P e he i j • x (e k) := by
  rw [hx.rawStructConst_of_root_eq_add P e he hk]
  exact hx.lie_eq_intStructureConstant_zsmul (e i) (e j) (e k) (H.isNonZero_coe_root _)
    (coe_weight_eq_add_of_root_eq_add e he hk)

private theorem lie_lie_eq_tripleRootCoeff_zsmul {a b c l : ι}
    (hl : P.root l = P.root a + P.root b + P.root c) :
    ⁅x (e a), ⁅x (e b), x (e c)⁆⁆ =
      P.tripleRootCoeff (hx.rawStructConst P e he) a b c l • x (e l) := by
  by_cases hbc0 : P.root b + P.root c = 0
  · obtain rfl : l = a := P.root.injective (by rw [hl, add_assoc, hbc0, add_zero])
    rw [P.tripleRootCoeff_of_add_eq_zero _ hbc0, ite_eq_left rfl,
      weight_eq_neg_of_root_add_eq_zero e he hbc0,
      hx.toIsSl2System.lie_neg (e b) (H.isNonZero_coe_root _),
      ← lie_skew (x (e l)) (coroot (e b : Weight K H L) : L),
      hx.toIsSl2System.lie_coroot (e l) (e b), coe_root_coroot_eq_pairing e he, ← neg_smul,
      ← Int.cast_neg, Int.cast_smul_eq_zsmul]
  · by_cases hmem : P.root b + P.root c ∈ range P.root
    · obtain ⟨m, hm⟩ := hmem
      have hlm : P.root l = P.root a + P.root m := by rw [hl, hm, add_assoc]
      rw [P.tripleRootCoeff_of_root_eq_add _ hm, ite_eq_left hlm,
        hx.lie_eq_rawStructConst_zsmul P e he hm, lie_zsmul,
        hx.lie_eq_rawStructConst_zsmul P e he hlm, mul_comm, mul_smul]
    · rw [P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hmem hbc0, zero_smul,
        hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot (e b) (e c)
          (rootSpace_add_eq_bot_of_notMem e he hmem hbc0), lie_zero]

include hx

private theorem rawStructConst_swap (i j : ι) :
    hx.rawStructConst P e he j i = -hx.rawStructConst P e he i j := by
  by_cases hmem : P.root i + P.root j ∈ range P.root
  · obtain ⟨k, hk⟩ := hmem
    rw [hx.rawStructConst_of_root_eq_add P e he (hk.trans (add_comm _ _)), eq_comm,
      hx.eq_intStructureConstant_iff, ← lie_skew (x (e j)),
      hx.lie_eq_rawStructConst_zsmul P e he hk, neg_smul]
  · rw [hx.rawStructConst_of_notMem P e he (add_comm (P.root i) _ ▸ hmem),
      hx.rawStructConst_of_notMem P e he hmem, neg_zero]

private theorem rawStructConst_reflectionPerm (i j : ι) :
    hx.rawStructConst P e he (P.reflectionPerm i i) (P.reflectionPerm j j) =
      -hx.rawStructConst P e he i j := by
  by_cases hmem : P.root i + P.root j ∈ range P.root
  · obtain ⟨k, hk⟩ := hmem
    have hneg (a : ι) : (e (P.reflectionPerm a a) : Weight K H L) = -(e a : Weight K H L) := by
      rw [map_reflectionPerm_self_eq_neg e he, val_neg_root]
    rw [hx.rawStructConst_of_root_eq_add P e he
        (P.root_reflectionPerm_self_eq_add_of_root_eq_add hk), eq_comm,
      hx.eq_intStructureConstant_iff, hneg i, hneg j, hneg k]
    simpa [LieEquiv.map_lie, hx.map_root, smul_neg, neg_smul] using
      congrArg ω (hx.lie_eq_rawStructConst_zsmul P e he hk)
  · rw [hx.rawStructConst_of_notMem P e he
        (mt (P.root_reflectionPerm_add_mem_range_iff i j).mp hmem),
      hx.rawStructConst_of_notMem P e he hmem, neg_zero]

private theorem lie_lie_eq_rawStructConst_zsmul_coroot {a b c : ι}
    (habc : P.root a + P.root b + P.root c = 0) : ⁅x (e a), ⁅x (e b), x (e c)⁆⁆ =
      hx.rawStructConst P e he b c • (coroot (e a : Weight K H L) : L) := by
  rw [hx.lie_eq_rawStructConst_zsmul P e he
      (RootPairing.root_reflectionPerm_self_eq_add_of_add_add_eq_zero habc), lie_zsmul,
    show (e (P.reflectionPerm a a) : Weight K H L) = -(e a : Weight K H L) by
      rw [map_reflectionPerm_self_eq_neg e he, val_neg_root],
    hx.toIsSl2System.lie_neg (e a) (H.isNonZero_coe_root _)]

private theorem rawStructConst_root_jacobi (i j k l : ι) :
    P.tripleRootCoeff (hx.rawStructConst P e he) i j k l +
      P.tripleRootCoeff (hx.rawStructConst P e he) j k i l +
      P.tripleRootCoeff (hx.rawStructConst P e he) k i j l = 0 := by
  by_cases hl : P.root l = P.root i + P.root j + P.root k
  · have hjac := lie_jacobi (x (e i)) (x (e j)) (x (e k))
    rw [hx.lie_lie_eq_tripleRootCoeff_zsmul P e he hl,
      hx.lie_lie_eq_tripleRootCoeff_zsmul P e he (by rw [hl]; abel),
      hx.lie_lie_eq_tripleRootCoeff_zsmul P e he (by rw [hl]; abel),
      ← add_smul, ← add_smul, ← Int.cast_smul_eq_zsmul K] at hjac
    exact Int.cast_eq_zero.mp ((smul_eq_zero.mp hjac).resolve_right
      (hx.toIsSl2System.ne_zero (e l) (H.isNonZero_coe_root _)))
  · rw [P.tripleRootCoeff_eq_zero_of_ne_sum _ hl,
      P.tripleRootCoeff_eq_zero_of_ne_sum _ (fun h ↦ hl (by rw [h]; abel)),
      P.tripleRootCoeff_eq_zero_of_ne_sum _ (fun h ↦ hl (by rw [h]; abel)), add_zero, add_zero]

variable [Finite ι]

private theorem natAbs_rawStructConst {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    (hx.rawStructConst P e he i j).natAbs = P.chainBotCoeff i j + 1 := by
  let heIn := RootPairing.pairingIn_eq_of_pairingIn_eq_pairing he
  have hli := (rootSystem H).linearIndependent_of_add_mem_range_root'
    ⟨e k, (RootPairing.root_eq_add_iff_of_pairingIn e heIn k i j).mpr hk⟩
  rw [hx.rawStructConst_of_root_eq_add P e he hk, ← ((rootSystem_chainCoeffs_eq hli).2.symm.trans
    (RootPairing.chainBotCoeff_eq_of_pairingIn e heIn i j))]
  rcases hx.intStructureConstant_eq_natCast_or_eq_neg_natCast (e i) (e j) (e k)
      (H.isNonZero_coe_root _) (H.isNonZero_coe_root _) (H.isNonZero_coe_root _)
      (coe_weight_eq_add_of_root_eq_add e he hk) with hN | hN <;>
    simp only [hN, Int.natAbs_neg, Int.natAbs_natCast]

private theorem rawStructConst_coroot_jacobi {i j k : ι} (h : P.root i + P.root j + P.root k = 0) :
    hx.rawStructConst P e he j k • P.coroot i + hx.rawStructConst P e he k i • P.coroot j +
      hx.rawStructConst P e he i j • P.coroot k = 0 := by
  have hjac := lie_jacobi (x (e i)) (x (e j)) (x (e k))
  rw [hx.lie_lie_eq_rawStructConst_zsmul_coroot P e he h,
    hx.lie_lie_eq_rawStructConst_zsmul_coroot P e he (by rw [← h]; abel),
    hx.lie_lie_eq_rawStructConst_zsmul_coroot P e he (by rw [← h]; abel)] at hjac
  have hH : hx.rawStructConst P e he j k • (rootSystem H).coroot (e i) +
      hx.rawStructConst P e he k i • (rootSystem H).coroot (e j) +
      hx.rawStructConst P e he i j • (rootSystem H).coroot (e k) = 0 :=
    Subtype.ext (by simpa [rootSystem_coroot_apply, add_assoc] using hjac)
  refine (P.zsmul_add_zsmul_add_zsmul_coroot_eq_zero_iff _ _ _ _ _ _).mpr fun s ↦ ?_
  have hs := congrArg ((e s : Weight K H L).toLinear) hH
  simp only [map_add, LinearMap.map_smul_of_tower, map_zero, Weight.toLinear_apply,
    rootSystem_coroot_apply, coe_root_coroot_eq_pairing e he, zsmul_eq_mul, ← Int.cast_mul,
    ← Int.cast_add] at hs
  simp only [P.pairingIn_eq_pairing]; exact Int.cast_eq_zero.mp hs

/-- **Chevalley structure constants from a Killing Chevalley system `hx` along `e`.** -/
noncomputable def chevalleyConstants : P.ChevalleyConstants where
  structConst := hx.rawStructConst P e he
  structConst_eq_zero_of_notMem_range _ _ := hx.rawStructConst_of_notMem P e he
  structConst_swap := hx.rawStructConst_swap P e he
  natAbs_structConst := hx.natAbs_rawStructConst P e he
  structConst_reflectionPerm := hx.rawStructConst_reflectionPerm P e he
  coroot_jacobi := hx.rawStructConst_coroot_jacobi P e he
  root_jacobi := hx.rawStructConst_root_jacobi P e he

/-- On root sums, `(hx.chevalleyConstants P e he).structConst` equals `hx.intStructureConstant`. -/
theorem chevalleyConstants_structConst_of_root_eq_add {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    (hx.chevalleyConstants P e he).structConst i j = hx.intStructureConstant (e i) (e j) (e k)
      (H.isNonZero_coe_root _) (coe_weight_eq_add_of_root_eq_add e he hk) :=
  hx.rawStructConst_of_root_eq_add P e he hk

/-- On `P.root k = P.root i + P.root j`, `⁅x (e i), x (e j)⁆ = Nᵢⱼ • x (e k)`. -/
theorem lie_eq_chevalleyConstants_structConst_zsmul {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    ⁅x (e i), x (e j)⁆ = (hx.chevalleyConstants P e he).structConst i j • x (e k) :=
  hx.lie_eq_rawStructConst_zsmul P e he hk

/-! ### Comparison with the Chevalley Lie lattice -/

/-- **The `ℤ`-Lie homomorphism from `ChevalleyLieAlgebra` into `hx.chevalleyLieLattice`** induced by
a compatible cocharacter map `γ : Y →ₗ[ℤ] H`. -/
noncomputable def toChevalleyLieLattice (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) :
    ChevalleyLieAlgebra (hx.chevalleyConstants P e he) →ₗ⁅ℤ⁆ hx.chevalleyLieLattice :=
  let γL : Y →ₗ[ℤ] hx.chevalleyLieLattice :=
    { toFun y := ⟨(γ y : L), hγ_mem y⟩, map_add' _ _ := Subtype.ext (by simp)
      map_smul' _ _ := Subtype.ext (by simp) }
  ChevalleyLieAlgebra.liftLieHom (hx.chevalleyConstants P e he) γL
    (fun i ↦ ⟨x (e i), hx.rootVector_mem_chevalleyLieLattice (e i)⟩)
    (fun y z ↦ Subtype.ext <| LieSubalgebra.lie_eq_zero_of_mem (γ y).2 (γ z).2)
    (fun y i ↦ Subtype.ext <| by
      simp only [LieSubalgebra.coe_bracket, SetLike.val_smul, γL, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace
        (hx.toIsSl2System.mem_rootSpace (e i)) (γ y), hγ_pair, Int.cast_smul_eq_zsmul])
    (fun {i j} h0 ↦ Subtype.ext <| by
      simp only [LieSubalgebra.coe_bracket, γL, LinearMap.coe_mk, AddHom.coe_mk]
      rw [weight_eq_neg_of_root_add_eq_zero e he h0, hx.toIsSl2System.lie_neg (e i)
        (H.isNonZero_coe_root _), map_coroot_eq_rootSystem_coroot e he γ hγ_pair i,
        rootSystem_coroot_apply])
    (fun {_ _ _} hk ↦ Subtype.ext <| hx.lie_eq_chevalleyConstants_structConst_zsmul P e he hk)
    (fun {i j} hnot h0 ↦ Subtype.ext <| hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot
      (e i) (e j) (rootSpace_add_eq_bot_of_notMem e he hnot h0))

@[simp] theorem coe_toChevalleyLieLattice_cartan (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (y : Y) :
    (hx.toChevalleyLieLattice P e he γ hγ_mem hγ_pair (ChevalleyLieAlgebra.cartan _ y) : L) =
      (γ y : L) := by simp [toChevalleyLieLattice]

@[simp] theorem coe_toChevalleyLieLattice_root (γ : Y →ₗ[ℤ] H)
    (hγ_mem : ∀ y, (γ y : L) ∈ hx.chevalleyLieLattice)
    (hγ_pair : ∀ y i, (e i : Weight K H L) (γ y) = (P.toLinearMap (P.root i) y : K)) (i : ι) :
    (hx.toChevalleyLieLattice P e he γ hγ_mem hγ_pair (ChevalleyLieAlgebra.root _ i) : L) =
      x (e i) := by simp [toChevalleyLieLattice]

variable (b : (rootSystem H).Base) {J : Type*} (bY : Basis J ℤ Y) (s : J ≃ b.support)

omit hx [Finite ι] in
private noncomputable def simpleCorootCoweightMap : Y →ₗ[ℤ] H :=
  bY.constr ℤ fun j : J ↦ (rootSystem H).coroot (s j : H.root)

omit [Finite ι] in
private theorem simpleCorootCoweightMap_mem (y : Y) :
    (simpleCorootCoweightMap b bY s y : L) ∈ hx.chevalleyLieLattice := by
  have hy : y ∈ Submodule.span ℤ (range bY) := by simp [bY.span_eq]
  induction hy using Submodule.span_induction with
  | mem _ hv =>
    obtain ⟨j, rfl⟩ := hv; rw [simpleCorootCoweightMap, Basis.constr_basis, rootSystem_coroot_apply]
    exact hx.coroot_mem_chevalleyLieLattice ((s j : H.root) : Weight K H L)
  | zero => rw [map_zero, ZeroMemClass.coe_zero]; exact zero_mem _
  | add _ _ _ _ hu hv => rw [map_add, AddMemClass.coe_add]; exact add_mem hu hv
  | smul z _ _ hu => rw [map_smul, SetLike.val_smul_of_tower]; exact Submodule.smul_mem _ z hu

variable (hbY : ∀ j : J, bY j = P.coroot (e.symm (s j)))

include he hbY

omit hx [Finite ι] in
private theorem simpleCorootCoweightMap_pair (y : Y) (i : ι) :
    (e i : Weight K H L) (simpleCorootCoweightMap b bY s y) = (P.toLinearMap (P.root i) y : K) := by
  let lhs : Y →ₗ[ℤ] K := ((e i : Weight K H L).toLinear.restrictScalars ℤ).comp
    (simpleCorootCoweightMap b bY s)
  let rhs : Y →ₗ[ℤ] K := (Int.castAddHom K).toIntLinearMap.comp (P.toLinearMap (P.root i))
  have h : lhs = rhs := bY.ext fun j ↦ by
    simp only [lhs, rhs, LinearMap.comp_apply, LinearMap.coe_restrictScalars, Weight.toLinear_apply,
      AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom]
    rw [simpleCorootCoweightMap, Basis.constr_basis, rootSystem_coroot_apply, hbY,
      P.root_coroot_eq_pairing, ← coe_root_coroot_eq_pairing e he, e.apply_symm_apply]
  simpa [lhs, rhs] using DFunLike.congr_fun h y

/-- **Simply connected identification with `hx.chevalleyLieLattice`** when `Y` has a `ℤ`-basis `bY`
of simple coroots indexed by `J ≃ b.support`. -/
noncomputable def toChevalleyLieLatticeEquiv :
    ChevalleyLieAlgebra (hx.chevalleyConstants P e he) ≃ₗ⁅ℤ⁆ hx.chevalleyLieLattice :=
  let f := hx.toChevalleyLieLattice P e he (simpleCorootCoweightMap b bY s)
    (hx.simpleCorootCoweightMap_mem b bY s) (simpleCorootCoweightMap_pair P e he b bY s hbY)
  LieEquiv.ofBijective f <| by
    let σ : J ⊕ ι ≃ H.root ⊕ b.support := (Equiv.sumCongr s e).trans (Equiv.sumComm _ _)
    let b0 := ChevalleyLieAlgebra.basis (hx.chevalleyConstants P e he) bY
    let b1 := (hx.rootSimpleCorootBasis b).reindex σ.symm
    have hf_eq : f.toLinearMap = (b0.equiv b1 (.refl _)).toLinearMap := b0.ext fun idx ↦ by
      rw [LinearEquiv.coe_toLinearMap, Basis.equiv_apply, Equiv.refl_apply]
      rcases idx with j | i <;> apply Subtype.ext <;> simp [f, b0, b1, σ, simpleCorootCoweightMap]
    rw [← LieHom.coe_toLinearMap, hf_eq]; exact (b0.equiv b1 (.refl _)).bijective

@[simp] theorem coe_toChevalleyLieLatticeEquiv_cartan_coroot (i : ι) :
    (hx.toChevalleyLieLatticeEquiv P e he b bY s hbY
      (ChevalleyLieAlgebra.cartan _ (P.coroot i)) : L) = (coroot (e i : Weight K H L) : L) := by
  simp [toChevalleyLieLatticeEquiv, map_coroot_eq_rootSystem_coroot e he _
    (simpleCorootCoweightMap_pair P e he b bY s hbY), rootSystem_coroot_apply]

/-- Not `@[simp]` because `hbY` is an explicit hypothesis rewriting `bY j` under `simpNF`; see
`coe_toChevalleyLieLatticeEquiv_cartan_coroot`. -/
theorem coe_toChevalleyLieLatticeEquiv_cartan_basis (j : J) :
    (hx.toChevalleyLieLatticeEquiv P e he b bY s hbY (ChevalleyLieAlgebra.cartan _ (bY j)) : L) =
      (coroot ((s j : H.root) : Weight K H L) : L) := by simp [hbY]

@[simp] theorem coe_toChevalleyLieLatticeEquiv_root (i : ι) :
    (hx.toChevalleyLieLatticeEquiv P e he b bY s hbY (ChevalleyLieAlgebra.root _ i) : L) =
      x (e i) := by simp [toChevalleyLieLatticeEquiv]

end IsChevalleySystem

/-! ## Pinned Dynkin types and general integral root data -/

namespace DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- **The canonical Chevalley structure-constant table on the pinned simply connected root datum**
of type `t`, extracted from `TauCeti.DynkinType.isChevalleySystem_chevalleySystem`. -/
noncomputable def simplyConnectedChevalleyConstants :
    (t.simplyConnectedRootDatum ht).ChevalleyConstants :=
  (t.isChevalleySystem_chevalleySystem ht).chevalleyConstants
    (t.simplyConnectedRootDatum ht) (t.rootEquiv ht) (t.pairingIn_rootEquiv ht)

/-- On root sums, `t.simplyConnectedChevalleyConstants ht` equals `intStructureConstant`. -/
theorem simplyConnectedChevalleyConstants_structConst_of_root_eq_add {i j k : Fin t.numRoots}
    (hk : (t.simplyConnectedRootDatum ht).root k =
      (t.simplyConnectedRootDatum ht).root i + (t.simplyConnectedRootDatum ht).root j) :
    (t.simplyConnectedChevalleyConstants ht).structConst i j =
      (t.isChevalleySystem_chevalleySystem ht).intStructureConstant
        (t.rootEquiv ht i) (t.rootEquiv ht j) (t.rootEquiv ht k)
        ((t.cartanSubalgebra ht).isNonZero_coe_root _) (t.coe_rootEquiv_eq_add_iff.mpr hk) :=
  (t.isChevalleySystem_chevalleySystem ht).chevalleyConstants_structConst_of_root_eq_add _ _ _ hk

open Classical in
private noncomputable def killingSimpleSupportEquiv :
    Fin t.rank ≃ ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht)).support :=
  (t.simpleSupportEquiv ht).trans
    ((t.rationalBase ht).supportMapEquiv (t.rationalRootSystemEquiv ht))

open Classical in
private theorem coe_killingSimpleSupportEquiv (j : Fin t.rank) :
    ((t.killingSimpleSupportEquiv ht j :
      ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht)).support) :
      (t.cartanSubalgebra ht).root) = t.rootEquiv ht (t.simpleIndex ht j) :=
  (RootPairing.Base.supportMapEquiv_apply_coe (t.rationalBase ht)
    (t.rationalRootSystemEquiv ht) (t.simpleSupportEquiv ht j)).trans <|
    (congrArg (t.rationalRootSystemEquiv ht).indexEquiv (t.coe_simpleSupportEquiv ht j)).trans
      (DFunLike.congr_fun (t.rootEquiv_eq_indexEquiv ht).symm _)

open Classical in
private theorem killingSimpleCoroot_eq (j : Fin t.rank) :
    Pi.basisFun ℤ (Fin t.rank) j = (t.simplyConnectedRootDatum ht).coroot
      ((t.rootEquiv ht).symm (t.killingSimpleSupportEquiv ht j)) := by
  rw [t.coe_killingSimpleSupportEquiv ht j, (t.rootEquiv ht).symm_apply_apply,
    t.coroot_simpleIndex ht, Pi.basisFun_apply]

/-- **The abstract simply connected `ChevalleyLieAlgebra` of type `t` is canonically isomorphic over
`ℤ` to the Chevalley lattice of the pinned rational Lie algebra.** -/
noncomputable def simplyConnectedChevalleyLieEquiv :
    ChevalleyLieAlgebra (t.simplyConnectedChevalleyConstants ht) ≃ₗ⁅ℤ⁆
      (t.isChevalleySystem_chevalleySystem ht).chevalleyLieLattice :=
  (t.isChevalleySystem_chevalleySystem ht).toChevalleyLieLatticeEquiv _ _ _
    ((t.rationalBase ht).map (t.rationalRootSystemEquiv ht))
    (Pi.basisFun ℤ (Fin t.rank)) (t.killingSimpleSupportEquiv ht) (t.killingSimpleCoroot_eq ht)

/-- `simplyConnectedChevalleyLieEquiv` maps `cartan _ (Pi.basisFun _ _ j)` to `h j`. -/
theorem coe_simplyConnectedChevalleyLieEquiv_cartan_basisFun (j : Fin t.rank) :
    (t.simplyConnectedChevalleyLieEquiv ht
      (ChevalleyLieAlgebra.cartan _ (Pi.basisFun ℤ (Fin t.rank) j)) : t.lieAlgebra ht) =
      (t.lieBasis ht).h j := by
  refine ((t.isChevalleySystem_chevalleySystem ht).coe_toChevalleyLieLatticeEquiv_cartan_basis
    _ _ _ _ _ _ _ j).trans ?_
  rw [t.coe_killingSimpleSupportEquiv ht j, t.rootEquiv_simpleIndex ht j]
  -- `coroot_eq_h'` uses `(t.lieBasis ht).isCartanSubalgebra`, and `(h' j : L)` is `h j` by defeq.
  exact congrArg Subtype.val (by convert (t.lieBasis ht).coroot_eq_h' j using 1)

@[simp] theorem coe_simplyConnectedChevalleyLieEquiv_cartan_single (j : Fin t.rank) :
    (t.simplyConnectedChevalleyLieEquiv ht (ChevalleyLieAlgebra.cartan _ (Pi.single j 1)) :
      t.lieAlgebra ht) = (t.lieBasis ht).h j := by
  simpa using t.coe_simplyConnectedChevalleyLieEquiv_cartan_basisFun ht j

@[simp] theorem coe_simplyConnectedChevalleyLieEquiv_root (i : Fin t.numRoots) :
    (t.simplyConnectedChevalleyLieEquiv ht (ChevalleyLieAlgebra.root _ i) : t.lieAlgebra ht) =
      t.chevalleySystem ht i :=
  ((t.isChevalleySystem_chevalleySystem ht).coe_toChevalleyLieLatticeEquiv_root _ _ _ _ _ _ _
    i).trans (extendRootFamily_rootEquiv _ i)

/-- **Chevalley structure constants on an integral root datum of Dynkin type `t`**, transported from
`simplyConnectedChevalleyConstants` along `e`. -/
noncomputable def chevalleyConstants {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : ι ≃ Fin t.numRoots)
    (he : ∀ i j, P.pairing i j = (t.simplyConnectedRootDatum ht).pairing (e i) (e j)) :
    letI : Finite ι := Finite.of_equiv _ e.symm; P.ChevalleyConstants :=
  letI : Finite ι := Finite.of_equiv _ e.symm
  (t.simplyConnectedChevalleyConstants ht).reindex e.symm fun i j ↦ by
    rw [he (e.symm i) (e.symm j), e.apply_symm_apply, e.apply_symm_apply]

@[simp] theorem chevalleyConstants_structConst {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : ι ≃ Fin t.numRoots)
    (he : ∀ i j, P.pairing i j = (t.simplyConnectedRootDatum ht).pairing (e i) (e j)) (i j : ι) :
    letI : Finite ι := Finite.of_equiv _ e.symm
    (t.chevalleyConstants ht P e he).structConst i j =
      (t.simplyConnectedChevalleyConstants ht).structConst (e i) (e j) := by
  have : Finite ι := Finite.of_equiv _ e.symm; simp [chevalleyConstants]

end DynkinType

end TauCeti
