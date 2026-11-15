/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.DistinctPairs
public import TauCeti.InformationTheory.Coding.Elementary.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.Map
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.A
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The classical sum-zero root system of type `Aₘ`

This file constructs Bourbaki's classical realization `typeAZeroSumRootPairing K m` of type `Aₘ` on
`singleParityCheckCode K (Fin (m + 1))` paired by the ambient dot product, its Bourbaki base
`typeAZeroSumBase K m` and simple-root basis `typeAZeroSumBasis`, the canonical equivalence
`typeABaseChangeEquivZeroSum K m` from `typeABaseChangeRootSystem K m`, and the diagram-reversal
automorphism `typeAZeroSumRevAut K m` (`(θ x) a = -x (rev a)`).

## References
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public section

namespace TauCeti.DynkinType

open Finset Function Submodule

section CommRing

variable (R : Type*) [CommRing R] {m : ℕ}

/-- The classical difference vector `eₐ - e_b` in `singleParityCheckCode R (Fin (m + 1))`. -/
def typeAZeroSumVec (a b : Fin (m + 1)) : singleParityCheckCode R (Fin (m + 1)) :=
  ⟨Pi.single a 1 - Pi.single b 1, by simp⟩

/-- Coercing `typeAZeroSumVec R a b` to the ambient tuple gives `Pi.single a 1 - Pi.single b 1`. -/
@[simp] theorem coe_typeAZeroSumVec (a b : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) = Pi.single a 1 - Pi.single b 1 := (rfl)

/-- Coordinate evaluation of `typeAZeroSumVec R a b`. -/
@[simp] theorem typeAZeroSumVec_apply (a b k : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) k =
      (if k = a then 1 else 0) - (if k = b then 1 else 0) := by simp [Pi.single_apply, eq_comm]

/-- A difference vector with equal indices vanishes. -/
@[simp] theorem typeAZeroSumVec_self (a : Fin (m + 1)) : typeAZeroSumVec R a a = 0 :=
  Subtype.ext (by simp)

/-- Negating `typeAZeroSumVec R a b` swaps its two indices. -/
@[simp] theorem neg_typeAZeroSumVec (a b : Fin (m + 1)) :
    -typeAZeroSumVec R a b = typeAZeroSumVec R b a := Subtype.ext (by simp)

/-- Ambient dot product of two difference vectors `eₐ - e_b` and `e_c - e_d`. -/
theorem typeAZeroSumVec_dotProduct (a b c d : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R c d : Fin (m + 1) → R) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
        ((if b = c then 1 else 0) - (if b = d then 1 else 0)) := by
  simp only [coe_typeAZeroSumVec, sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
    Pi.single_apply]; ring

/-- Every classical root `eₐ - e_b` (`a ≠ b`) has squared length `2` for the ambient dot product. -/
theorem typeAZeroSumVec_dotProduct_self {a b : Fin (m + 1)} (h : a ≠ b) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R a b : Fin (m + 1) → R) = 2 := by
  rw [typeAZeroSumVec_dotProduct]; simp only [ite_true, h, h.symm, ite_false]; norm_num

/-- The `i`-th Bourbaki simple root `αᵢ = eᵢ - eᵢ₊₁` in `singleParityCheckCode R (Fin (m + 1))`. -/
def typeAZeroSumSimpleRoot (m : ℕ) (i : Fin m) : singleParityCheckCode R (Fin (m + 1)) :=
  typeAZeroSumVec R i.castSucc i.succ

/-- Unfolding equation for `typeAZeroSumSimpleRoot`. -/
theorem typeAZeroSumSimpleRoot_def (m : ℕ) (i : Fin m) :
    typeAZeroSumSimpleRoot R m i = typeAZeroSumVec R i.castSucc i.succ := (rfl)

private lemma sum_Iic_typeAZeroSumSimpleRoot (i k : Fin m) :
    ∑ j ∈ Iic k.castSucc, (typeAZeroSumSimpleRoot R m i : Fin (m + 1) → R) j =
      if i = k then 1 else 0 := by
  rw [typeAZeroSumSimpleRoot_def, coe_typeAZeroSumVec]
  simp only [Pi.sub_apply, sum_sub_distrib, Pi.single_apply, Finset.sum_ite_eq', mem_Iic]
  simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

private lemma coe_sum_singleParityCheckCode {ι : Type*} (s : Finset ι)
    (f : ι → singleParityCheckCode R (Fin (m + 1))) (a : Fin (m + 1)) :
    ((∑ i ∈ s, f i : singleParityCheckCode R (Fin (m + 1))) : Fin (m + 1) → R) a =
      ∑ i ∈ s, (f i : Fin (m + 1) → R) a := by simp

private lemma sum_Iic_sum_smul_simpleRoot (c : Fin m → R) (k : Fin m) :
    ∑ j ∈ Iic k.castSucc, ((∑ i : Fin m, c i • typeAZeroSumSimpleRoot R m i :
      singleParityCheckCode R (Fin (m + 1))) : Fin (m + 1) → R) j = c k := by
  simp_rw [coe_sum_singleParityCheckCode]; rw [sum_comm]
  simp_rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum,
    sum_Iic_typeAZeroSumSimpleRoot R]; simp

private def typeAZeroSumCoordEquiv (m : ℕ) :
    singleParityCheckCode R (Fin (m + 1)) ≃ₗ[R] (Fin m → R) where
  toFun x i := ∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j
  map_add' _ _ := by ext; simp [sum_add_distrib]
  map_smul' _ _ := by ext; simp [mul_sum]
  invFun y := ∑ i : Fin m, y i • typeAZeroSumSimpleRoot R m i
  right_inv y := funext (sum_Iic_sum_smul_simpleRoot R y)
  left_inv x := by
    set z : singleParityCheckCode R (Fin (m + 1)) :=
      (∑ i : Fin m, (∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j) •
        typeAZeroSumSimpleRoot R m i) - x
    refine sub_eq_zero.mp (Subtype.ext (eq_zero_of_forall_sum_Iic_eq_zero <| Fin.lastCases ?_ ?_))
    · rw [show Iic (Fin.last m) = univ from eq_univ_of_forall fun j ↦ mem_Iic.mpr (Fin.le_last j)]
      exact (mem_singleParityCheckCode R (Fin (m + 1))).mp z.2
    · intro k; simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, sum_sub_distrib, sub_eq_zero]
      exact sum_Iic_sum_smul_simpleRoot R _ k

/-- The Bourbaki simple roots `αᵢ = eᵢ - eᵢ₊₁` form an `R`-basis of `singleParityCheckCode`. -/
noncomputable def typeAZeroSumBasis (m : ℕ) :
    Module.Basis (Fin m) R (singleParityCheckCode R (Fin (m + 1))) :=
  Module.Basis.ofRepr
    ((typeAZeroSumCoordEquiv R m).trans (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm)

/-- The `i`-th vector of `typeAZeroSumBasis` is `typeAZeroSumSimpleRoot R m i`. -/
@[simp] theorem typeAZeroSumBasis_apply (m : ℕ) (i : Fin m) :
    typeAZeroSumBasis R m i = typeAZeroSumSimpleRoot R m i := by
  rw [typeAZeroSumBasis, Module.Basis.coe_ofRepr]
  change ∑ j : Fin m, (Finsupp.single i (1 : R) : Fin m → R) j • typeAZeroSumSimpleRoot R m j = _
  simp [Finsupp.single_apply]

/-- The `i`-th coordinate of `x` in `typeAZeroSumBasis` is the partial sum `∑_{j ≤ i} xⱼ`. -/
@[simp] theorem typeAZeroSumBasis_repr_apply (m : ℕ)
    (x : singleParityCheckCode R (Fin (m + 1))) (i : Fin m) :
    (typeAZeroSumBasis R m).repr x i = ∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j := (rfl)

/-- Expansion of `eₐ - e_b` in `typeAZeroSumBasis`: coordinate `i` is `[a ≤ i] - [b ≤ i]`. -/
theorem typeAZeroSumBasis_repr_vec (a b : Fin (m + 1)) (i : Fin m) :
    (typeAZeroSumBasis R m).repr (typeAZeroSumVec R a b) i =
      (if a ≤ i.castSucc then 1 else 0) - (if b ≤ i.castSucc then 1 else 0) := by
  rw [typeAZeroSumBasis_repr_apply, coe_typeAZeroSumVec]; simp [Pi.single_apply]

/-- The reversal linear involution `(θ x) a = -x (rev a)` on the sum-zero hyperplane. -/
def typeAZeroSumRevEquiv (m : ℕ) :
    singleParityCheckCode R (Fin (m + 1)) ≃ₗ[R] singleParityCheckCode R (Fin (m + 1)) :=
  LinearEquiv.ofInvolutive
    { toFun x := ⟨fun a ↦ -(x : Fin (m + 1) → R) a.rev, by
        rw [mem_singleParityCheckCode, sum_neg_distrib, neg_eq_zero]
        exact (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1))) _).trans
          ((mem_singleParityCheckCode R (Fin (m + 1))).mp x.2)⟩
      map_add' _ _ := Subtype.ext (funext fun _ ↦ by simp; ring)
      map_smul' _ _ := Subtype.ext (funext fun _ ↦ by simp) }
    fun _ ↦ Subtype.ext (funext fun _ ↦ by simp)

/-- Coordinate evaluation of `typeAZeroSumRevEquiv`. -/
@[simp] theorem coe_typeAZeroSumRevEquiv_apply (x : singleParityCheckCode R (Fin (m + 1)))
    (a : Fin (m + 1)) :
    (typeAZeroSumRevEquiv R m x : Fin (m + 1) → R) a = -(x : Fin (m + 1) → R) a.rev := (rfl)

/-- `typeAZeroSumRevEquiv` is an involution. -/
@[simp] theorem typeAZeroSumRevEquiv_apply_self (x : singleParityCheckCode R (Fin (m + 1))) :
    typeAZeroSumRevEquiv R m (typeAZeroSumRevEquiv R m x) = x := by ext; simp

/-- `typeAZeroSumRevEquiv` is its own inverse. -/
@[simp] theorem typeAZeroSumRevEquiv_symm (m : ℕ) :
    (typeAZeroSumRevEquiv R m).symm = typeAZeroSumRevEquiv R m :=
  LinearEquiv.ext fun x ↦
    (typeAZeroSumRevEquiv R m).symm_apply_eq.mpr (typeAZeroSumRevEquiv_apply_self R x).symm

/-- Reversal sends `eₐ - e_b` to `e_{rev b} - e_{rev a}`. -/
@[simp] theorem typeAZeroSumRevEquiv_vec (a b : Fin (m + 1)) :
    typeAZeroSumRevEquiv R m (typeAZeroSumVec R a b) = typeAZeroSumVec R b.rev a.rev := by
  ext k; simp only [coe_typeAZeroSumRevEquiv_apply, typeAZeroSumVec_apply, Fin.rev_eq_iff]; ring

/-- Reversal sends the `i`-th Bourbaki simple root to the `(rev i)`-th Bourbaki simple root. -/
@[simp] theorem typeAZeroSumRevEquiv_simpleRoot (i : Fin m) :
    typeAZeroSumRevEquiv R m (typeAZeroSumSimpleRoot R m i) =
      typeAZeroSumSimpleRoot R m i.rev := by
  rw [typeAZeroSumSimpleRoot_def, typeAZeroSumRevEquiv_vec, typeAZeroSumSimpleRoot_def,
    Fin.rev_succ, Fin.rev_castSucc]

end CommRing

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- Entrywise base-changed root system of type `Aₘ` on `Fin m → K`. -/
def typeABaseChangeRootSystem (m : ℕ) :
    RootPairing (Fin (m * (m + 1))) K (Fin m → K) (Fin m → K) :=
  rootPairingBaseChange K (typeASimplyConnectedRootDatum m)
    (fun x y ↦ toLinearMap_typeASimplyConnectedRootDatum x y)

/-- The Bourbaki-numbered base of `typeABaseChangeRootSystem K m`. -/
def typeABaseChangeBase (m : ℕ) : (typeABaseChangeRootSystem K m).Base :=
  rootPairingBaseChangeBase K (typeASimplyConnectedRootDatum m)
    (fun x y ↦ toLinearMap_typeASimplyConnectedRootDatum x y) (typeASimplyConnectedBase m)

/-- Base change preserves crystallographicity for `typeABaseChangeRootSystem K m`. -/
instance instIsCrystallographicTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsCrystallographic :=
  isCrystallographic_rootPairingBaseChange ..

/-- Base change preserves reducedness for `typeABaseChangeRootSystem K m`. -/
instance instIsReducedTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsReduced :=
  let _ : (typeASimplyConnectedRootDatum m).IsReduced :=
    RootPairing.isReduced_of_pairing_comm _ pairing_typeASimplyConnectedRootDatum_comm
  isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeABaseChangeRootSystem K m`
span `Fin m → K`. -/
instance instIsRootSystemTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsRootSystem where
  span_root_eq_top := top_le_iff.mp <| by
    have hcard : Fintype.card (typeABaseChangeBase K m).support =
        Module.finrank K (Fin m → K) := by
      rw [Fintype.card_coe, Module.finrank_fin_fun, typeABaseChangeBase,
        support_rootPairingBaseChangeBase,
        (hasCartanType_typeASimplyConnectedRootDatum m).card_support, DynkinType.rank_A]
    rw [← (typeABaseChangeBase K m).linearIndepOn_root.span_eq_top_of_card_eq_finrank' hcard]
    exact Submodule.span_mono <| by
      rintro - ⟨i, rfl⟩; exact Set.mem_range_self (i : Fin (m * (m + 1)))
  span_coroot_eq_top := span_range_coroot_rootPairingBaseChange_eq_top K _ _
    (corootSpan_typeASimplyConnectedRootDatum_eq_top m)

/-- `typeABaseChangeBase K m` has Cartan type `A m`. -/
theorem hasCartanType_typeABaseChangeBase (m : ℕ) :
    HasCartanType (typeABaseChangeRootSystem K m) (typeABaseChangeBase K m) (.A m) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).mp (hasCartanType_typeASimplyConnectedRootDatum m)
  exact (hasCartanType_iff _ _).mpr ⟨(supportEquivRootPairingBaseChangeBase K _ _ _).trans e,
    fun i j ↦ (cartanMatrix_rootPairingBaseChangeBase K _ _ _ i j).trans (he _ _)⟩

/-- The graph automorphism of `typeABaseChangeRootSystem K m`, reversing `Fin m → K`. -/
noncomputable def typeABaseChangeGraphAut (m : ℕ) :
    RootPairing.Aut (typeABaseChangeRootSystem K m) :=
  RootPairing.Equiv.mk' (typeABaseChangeRootSystem K m) (typeABaseChangeRootSystem K m)
    (LinearEquiv.funCongrLeft K K (Fin.revPerm : Equiv.Perm (Fin m)))
    (typeAGraphAut m).indexEquiv fun i ↦ funext fun k ↦ by
      have h := congrFun (RootPairing.Hom.root_weightMap_apply
        (typeASimplyConnectedRootDatum m) (typeASimplyConnectedRootDatum m) i
        (typeAGraphAut m).toHom) k
      rw [weightMap_typeAGraphAut_apply] at h
      simpa [typeABaseChangeRootSystem, piAlgebraMap_apply] using congrArg (algebraMap ℤ K) h

/-- The index permutation of `typeABaseChangeGraphAut K m` agrees with `typeAGraphAut m`. -/
@[simp] theorem indexEquiv_typeABaseChangeGraphAut (m : ℕ) :
    (typeABaseChangeGraphAut K m).indexEquiv = (typeAGraphAut m).indexEquiv := (rfl)

/-- `typeABaseChangeGraphAut K m` reverses weight coordinates. -/
@[simp] theorem weightMap_typeABaseChangeGraphAut_apply (m : ℕ) (x : Fin m → K) (k : Fin m) :
    (typeABaseChangeGraphAut K m).weightMap x k = x k.rev := (rfl)

private def zeroSumDiffMap (m : ℕ) : singleParityCheckCode K (Fin (m + 1)) →ₗ[K] (Fin m → K) where
  toFun u k := (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ
  map_add' _ _ := funext fun _ ↦ by simp; ring
  map_smul' _ _ := funext fun _ ↦ by simp [mul_sub]

private lemma zeroSumDiffMap_injective (m : ℕ) : Injective (zeroSumDiffMap K m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]; intro u hu
  have hc (a : Fin (m + 1)) : (u : Fin (m + 1) → K) a = (u : Fin (m + 1) → K) 0 :=
    Fin.induction rfl (fun k ih ↦ (sub_eq_zero.mp (congrFun hu k)).symm.trans ih) a
  have hsum := (mem_singleParityCheckCode K (Fin (m + 1))).mp u.2
  simp_rw [hc, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hu0 := (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
  exact Subtype.ext (funext fun a ↦ (hc a).trans hu0)

private noncomputable def zeroSumWeightEquiv (m : ℕ) :
    singleParityCheckCode K (Fin (m + 1)) ≃ₗ[K] (Fin m → K) :=
  haveI := Module.Finite.of_basis (typeAZeroSumBasis K m)
  (zeroSumDiffMap K m).linearEquivOfInjective (zeroSumDiffMap_injective K m) <| by
    rw [Module.finrank_eq_card_basis (typeAZeroSumBasis K m), Module.finrank_fin_fun,
      Fintype.card_fin]

omit [CharZero K] in
private noncomputable def zeroSumCoweightEquiv (m : ℕ) :
    (Fin m → K) ≃ₗ[K] singleParityCheckCode K (Fin (m + 1)) :=
  (Finsupp.linearEquivFunOnFinite K K (Fin m)).symm.trans (typeAZeroSumBasis K m).repr.symm

private lemma zeroSumWeightEquiv_dotProduct (m : ℕ)
    (u v : singleParityCheckCode K (Fin (m + 1))) :
    zeroSumWeightEquiv K m u ⬝ᵥ (zeroSumCoweightEquiv K m).symm v =
      (u : Fin (m + 1) → K) ⬝ᵥ (v : Fin (m + 1) → K) := by
  have hv : (v : Fin (m + 1) → K) = ∑ k : Fin m,
      ((zeroSumCoweightEquiv K m).symm v k) • (typeAZeroSumSimpleRoot K m k : Fin (m + 1) → K) :=
    funext fun a ↦ by
      rw [congrArg (fun w : singleParityCheckCode K (Fin (m + 1)) ↦ (w : Fin (m + 1) → K) a)
        ((typeAZeroSumBasis K m).sum_repr v).symm, coe_sum_singleParityCheckCode, Finset.sum_apply]
      exact sum_congr rfl fun k _ ↦ by rw [typeAZeroSumBasis_apply]; rfl
  rw [hv, dotProduct_sum, dotProduct]
  exact sum_congr rfl fun k _ ↦ by
    rw [dotProduct_smul, smul_eq_mul, typeAZeroSumSimpleRoot_def, coe_typeAZeroSumVec,
      dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one, mul_comm]; rfl

private lemma zeroSumWeightEquiv_vec (m : ℕ) (p : TypeAIndex m) :
    zeroSumWeightEquiv K m (typeAZeroSumVec K p.val.1 p.val.2) =
      (typeABaseChangeRootSystem K m).root (typeAIndexEquiv m p) := funext fun k ↦ by
  change (typeAZeroSumVec K p.val.1 p.val.2 : Fin (m + 1) → K) k.castSucc -
      (typeAZeroSumVec K p.val.1 p.val.2 : Fin (m + 1) → K) k.succ = _
  rw [typeABaseChangeRootSystem, root_rootPairingBaseChange, piAlgebraMap_apply,
    root_typeAIndexEquiv]
  simp only [typeAZeroSumVec_apply, eq_comm, algebraMap_int_eq, eq_intCast, Int.cast_sub,
    apply_ite Int.cast, Int.cast_one, Int.cast_zero]; ring

private lemma zeroSumCoweightEquiv_coroot (m : ℕ) (p : TypeAIndex m) :
    zeroSumCoweightEquiv K m ((typeABaseChangeRootSystem K m).coroot (typeAIndexEquiv m p)) =
      typeAZeroSumVec K p.val.1 p.val.2 := by
  apply (zeroSumCoweightEquiv K m).symm.injective; rw [LinearEquiv.symm_apply_apply]; ext k
  change _ = (typeAZeroSumBasis K m).repr (typeAZeroSumVec K p.val.1 p.val.2) k
  rw [typeAZeroSumBasis_repr_vec, typeABaseChangeRootSystem, coroot_rootPairingBaseChange,
    piAlgebraMap_apply, coroot_typeAIndexEquiv]
  simp [algebraMap_int_eq, apply_ite Int.cast]

/-- **The classical sum-zero root system of type `Aₘ` over `K`.** -/
noncomputable def typeAZeroSumRootPairing (m : ℕ) :
    RootPairing (TypeAIndex m) K
      (singleParityCheckCode K (Fin (m + 1))) (singleParityCheckCode K (Fin (m + 1))) :=
  (typeABaseChangeRootSystem K m).map (typeAIndexEquiv m).symm
    (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m)

/-- `typeAZeroSumRootPairing K m` is a root system. -/
instance instIsRootSystemTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsRootSystem := by delta typeAZeroSumRootPairing; infer_instance

/-- `typeAZeroSumRootPairing K m` is crystallographic. -/
instance instIsCrystallographicTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsCrystallographic := by
  delta typeAZeroSumRootPairing; infer_instance

/-- `typeAZeroSumRootPairing K m` is reduced. -/
instance instIsReducedTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsReduced := by delta typeAZeroSumRootPairing; infer_instance

/-- Canonical equivalence from `typeABaseChangeRootSystem K m` to `typeAZeroSumRootPairing K m`. -/
noncomputable def typeABaseChangeEquivZeroSum (m : ℕ) :
    (typeABaseChangeRootSystem K m).Equiv (typeAZeroSumRootPairing K m) :=
  (typeABaseChangeRootSystem K m).equivMap (typeAIndexEquiv m).symm
    (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m)

/-- The Bourbaki-numbered base of `typeAZeroSumRootPairing K m`. -/
noncomputable def typeAZeroSumBase (m : ℕ) : (typeAZeroSumRootPairing K m).Base :=
  (typeABaseChangeBase K m).map (typeABaseChangeEquivZeroSum K m)

/-- The bilinear pairing of `typeAZeroSumRootPairing K m` is the ambient dot product. -/
@[simp] theorem toLinearMap_typeAZeroSumRootPairing (m : ℕ)
    (u v : singleParityCheckCode K (Fin (m + 1))) :
    (typeAZeroSumRootPairing K m).toLinearMap u v =
      (u : Fin (m + 1) → K) ⬝ᵥ (v : Fin (m + 1) → K) := by
  rw [typeAZeroSumRootPairing, RootPairing.toLinearMap_map, LinearEquiv.symm_symm,
    typeABaseChangeRootSystem, toLinearMap_rootPairingBaseChange, zeroSumWeightEquiv_dotProduct]

/-- The root of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp] theorem root_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).root p = typeAZeroSumVec K p.val.1 p.val.2 := by
  rw [typeAZeroSumRootPairing, RootPairing.root_map, Equiv.symm_symm, ← zeroSumWeightEquiv_vec,
    LinearEquiv.symm_apply_apply]

/-- The coroot of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp] theorem coroot_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).coroot p = typeAZeroSumVec K p.val.1 p.val.2 := by
  rw [typeAZeroSumRootPairing, RootPairing.coroot_map, Equiv.symm_symm, zeroSumCoweightEquiv_coroot]

/-- Evaluating the coroot functional at `p = (a, b)` on `u` computes `uₐ - u_b`. -/
theorem coroot'_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m)
    (u : singleParityCheckCode K (Fin (m + 1))) :
    (typeAZeroSumRootPairing K m).coroot' p u =
      (u : Fin (m + 1) → K) p.val.1 - (u : Fin (m + 1) → K) p.val.2 := by
  rw [RootPairing.coroot', LinearMap.flip_apply, toLinearMap_typeAZeroSumRootPairing,
    coroot_typeAZeroSumRootPairing, coe_typeAZeroSumVec, dotProduct_sub, dotProduct_single,
    dotProduct_single, mul_one, mul_one]

/-- Reflection in `p` swaps the entries `p.1` and `p.2` inside any root pair `q`. -/
theorem reflectionPerm_typeAZeroSumRootPairing_val (m : ℕ) (p q : TypeAIndex m) :
    ((typeAZeroSumRootPairing K m).reflectionPerm p q).val =
      (Equiv.swap p.val.1 p.val.2 q.val.1, Equiv.swap p.val.1 p.val.2 q.val.2) := by
  rw [typeAZeroSumRootPairing, RootPairing.reflectionPerm_map, Equiv.symm_symm,
    typeABaseChangeRootSystem, reflectionPerm_rootPairingBaseChange,
    typeAIndexEquiv_symm_reflectionPerm]

/-- Self-reflection in `p = (a, b)` reverses the pair to `(b, a)`. -/
@[simp] theorem reflectionPerm_self_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).reflectionPerm p p = ⟨(p.val.2, p.val.1), p.2.symm⟩ :=
  Subtype.ext (by rw [reflectionPerm_typeAZeroSumRootPairing_val, Equiv.swap_apply_left,
    Equiv.swap_apply_right])

/-- The index equivalence of `typeABaseChangeEquivZeroSum K m` is `(typeAIndexEquiv m).symm`. -/
@[simp] theorem indexEquiv_typeABaseChangeEquivZeroSum (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).indexEquiv = (typeAIndexEquiv m).symm :=
  RootPairing.indexEquiv_equivMap ..

/-- The `i`-th consecutive pair `(i, i + 1)` indexing the `i`-th Bourbaki simple root. -/
def typeAZeroSumSimplePair (m : ℕ) (i : Fin m) : TypeAIndex m :=
  ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ.ne⟩

/-- Unfolding equation for the underlying pair of `typeAZeroSumSimplePair`. -/
@[simp] theorem typeAZeroSumSimplePair_val (m : ℕ) (i : Fin m) :
    (typeAZeroSumSimplePair m i).val = (i.castSucc, i.succ) := (rfl)

/-- `typeAZeroSumSimplePair m` is injective. -/
theorem typeAZeroSumSimplePair_injective (m : ℕ) : Injective (typeAZeroSumSimplePair m) :=
  fun _ _ h ↦ Fin.castSucc_injective m (congrArg (fun p : TypeAIndex m ↦ p.val.1) h)

/-- `(typeAIndexEquiv m).symm` maps `typeASimpleIndex m i` to `typeAZeroSumSimplePair m i`. -/
theorem typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair (m : ℕ) (i : Fin m) :
    (typeAIndexEquiv m).symm (typeASimpleIndex m i) = typeAZeroSumSimplePair m i := by
  rw [typeAIndexEquiv_symm_typeASimpleIndex]; rfl

/-- The support of `typeAZeroSumBase K m` consists of the consecutive pairs `(i, i + 1)`. -/
theorem mem_support_typeAZeroSumBase_iff {m : ℕ} {p : TypeAIndex m} :
    p ∈ (typeAZeroSumBase K m).support ↔ ∃ i : Fin m, p = typeAZeroSumSimplePair m i := by
  classical
  rw [typeAZeroSumBase, RootPairing.Base.support_map_eq, mem_image, typeABaseChangeBase,
    support_rootPairingBaseChangeBase]
  refine ⟨?_, fun ⟨i, hi⟩ ↦ ⟨typeASimpleIndex m i,
    mem_typeASimplyConnectedBase_support.mpr ((typeASimpleIndex_val i).symm ▸ i.isLt),
    by rw [hi, indexEquiv_typeABaseChangeEquivZeroSum,
      typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair]⟩⟩
  rintro ⟨k, hk, rfl⟩; rw [mem_typeASimplyConnectedBase_support] at hk
  refine ⟨⟨k, hk⟩, ?_⟩; rw [indexEquiv_typeABaseChangeEquivZeroSum]
  conv_lhs => rw [show k = typeASimpleIndex m ⟨k, hk⟩ from Fin.ext (by simp)]
  exact typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair m ⟨k, hk⟩

/-- `typeAZeroSumBase K m` has Cartan type `A m`. -/
theorem hasCartanType_typeAZeroSumBase (m : ℕ) :
    HasCartanType (typeAZeroSumRootPairing K m) (typeAZeroSumBase K m) (.A m) :=
  (hasCartanType_typeABaseChangeBase K m).map (typeABaseChangeEquivZeroSum K m)

/-- Bourbaki node equivalence `Fin m ≃ (typeAZeroSumBase K m).support`. -/
noncomputable def typeAZeroSumSimpleEquiv (m : ℕ) : Fin m ≃ (typeAZeroSumBase K m).support :=
  Equiv.ofBijective
    (fun i ↦ ⟨typeAZeroSumSimplePair m i, (mem_support_typeAZeroSumBase_iff K).mpr ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ typeAZeroSumSimplePair_injective m (congrArg Subtype.val h), fun ⟨_, hp⟩ ↦
      let ⟨i, hi⟩ := (mem_support_typeAZeroSumBase_iff K).mp hp; ⟨i, Subtype.ext hi.symm⟩⟩

/-- Coercing `typeAZeroSumSimpleEquiv K m i` gives `typeAZeroSumSimplePair m i`. -/
@[simp] theorem coe_typeAZeroSumSimpleEquiv (m : ℕ) (i : Fin m) :
    (typeAZeroSumSimpleEquiv K m i : TypeAIndex m) = typeAZeroSumSimplePair m i := (rfl)

/-- The Cartan matrix of `typeAZeroSumBase K m` along `typeAZeroSumSimpleEquiv` is `A m`. -/
@[simp] theorem cartanMatrix_typeAZeroSumBase (m : ℕ) (i j : Fin m) :
    (typeAZeroSumBase K m).cartanMatrix (typeAZeroSumSimpleEquiv K m i)
      (typeAZeroSumSimpleEquiv K m j) = CartanMatrix.A m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    RootPairing.algebraMap_pairingIn, ← RootPairing.root_coroot'_eq_pairing,
    coe_typeAZeroSumSimpleEquiv, coe_typeAZeroSumSimpleEquiv, coroot'_typeAZeroSumRootPairing,
    root_typeAZeroSumRootPairing]
  have hcast (a b c d : Fin (m + 1)) :
      (typeAZeroSumVec K a b : Fin (m + 1) → K) c - (typeAZeroSumVec K a b : Fin (m + 1) → K) d =
        algebraMap ℤ K ((typeAZeroSumVec ℤ a b : Fin (m + 1) → ℤ) c -
          (typeAZeroSumVec ℤ a b : Fin (m + 1) → ℤ) d) := by
    simp [typeAZeroSumVec_apply, algebraMap_int_eq, apply_ite Int.cast]
  rw [hcast]; congr 1
  simp only [typeAZeroSumSimplePair_val, typeAZeroSumVec_apply, CartanMatrix.A, Matrix.of_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; split_ifs <;> omega

/-- A root pair `p = (a, b)` is positive for `typeAZeroSumBase K m` if and only if `a < b`. -/
theorem isPos_typeAZeroSumBase_iff {m : ℕ} {p : TypeAIndex m} :
    (typeAZeroSumBase K m).IsPos p ↔ p.val.1 < p.val.2 := by
  have hbij : Set.BijOn (typeAZeroSumSimplePair m) Set.univ
      ((typeAZeroSumBase K m).support : Set (TypeAIndex m)) :=
    ⟨fun i _ ↦ (mem_support_typeAZeroSumBase_iff K).mpr ⟨i, rfl⟩,
      fun _ _ _ _ h ↦ typeAZeroSumSimplePair_injective m h,
      fun _ hr ↦ let ⟨i, hi⟩ := (mem_support_typeAZeroSumBase_iff K).mp hr; ⟨i, trivial, hi.symm⟩⟩
  have hfwd (q : TypeAIndex m) (hlt : q.val.1 < q.val.2) : (typeAZeroSumBase K m).IsPos q := by
    rw [← mem_posRoots, mem_posRoots_iff_root_mem_posRootCone,
      mem_posRootCone_iff_exists_nat_of_bijOn _ _ hbij]
    refine ⟨fun i ↦ if q.val.1 ≤ i.castSucc ∧ i.castSucc < q.val.2 then 1 else 0,
      (typeAZeroSumBasis K m).repr.injective (Finsupp.ext fun k ↦ ?_)⟩
    rw [root_typeAZeroSumRootPairing, typeAZeroSumBasis_repr_vec, map_sum,
      ← Finsupp.lapply_apply (R := K), map_sum]
    simp_rw [Finsupp.lapply_apply, map_nsmul, Finsupp.coe_smul, Pi.smul_apply,
      root_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val, ← typeAZeroSumSimpleRoot_def,
      ← typeAZeroSumBasis_apply, Module.Basis.repr_self_apply]
    rw [sum_eq_single k (fun i _ hik ↦ by rw [ite_eq_right hik, nsmul_zero]) (by simp),
      ite_eq_left rfl]
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc]
    have : (q.val.1 : ℕ) < (q.val.2 : ℕ) := hlt; split_ifs <;> first | omega | norm_num
  refine ⟨fun hpos ↦ (lt_or_gt_of_ne p.2).resolve_right fun hgt ↦ ?_, hfwd p⟩
  have hq : _ ∈ posRoots _ _ := (mem_posRoots _ _ _).mpr (hfwd ⟨(p.val.2, p.val.1), p.2.symm⟩ hgt)
  rw [← reflectionPerm_self_typeAZeroSumRootPairing K m p] at hq
  exact reflectionPerm_self_notMem_posRoots _ _ ((mem_posRoots _ _ _).mpr hpos) hq

/-- **The diagram-reversal automorphism of `typeAZeroSumRootPairing K m`.** -/
noncomputable def typeAZeroSumRevAut (m : ℕ) : RootPairing.Aut (typeAZeroSumRootPairing K m) :=
  RootPairing.Equiv.mk' (typeAZeroSumRootPairing K m) (typeAZeroSumRootPairing K m)
    (typeAZeroSumRevEquiv K m) (finDistinctPairsRevSwap (m + 1)) fun _ ↦ by simp

/-- The weight map of `typeAZeroSumRevAut K m` is `typeAZeroSumRevEquiv K m`. -/
@[simp] theorem weightMap_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).weightMap = (typeAZeroSumRevEquiv K m).toLinearMap := (rfl)

/-- The index permutation of `typeAZeroSumRevAut K m` is `finDistinctPairsRevSwap (m + 1)`. -/
@[simp] theorem indexEquiv_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).indexEquiv = finDistinctPairsRevSwap (m + 1) := (rfl)

/-- `typeAZeroSumRevAut K m` reverses the Bourbaki-numbered simple pairs. -/
theorem indexEquiv_typeAZeroSumRevAut_simplePair (m : ℕ) (i : Fin m) :
    (typeAZeroSumRevAut K m).indexEquiv (typeAZeroSumSimplePair m i) =
      typeAZeroSumSimplePair m i.rev := Subtype.ext <| by
  rw [indexEquiv_typeAZeroSumRevAut, finDistinctPairsRevSwap_apply_val,
    typeAZeroSumSimplePair_val, typeAZeroSumSimplePair_val, Fin.rev_succ, Fin.rev_castSucc]

/-- `typeAZeroSumRevAut K m` preserves the support of `typeAZeroSumBase K m`. -/
theorem indexEquiv_typeAZeroSumRevAut_mem_support {m : ℕ} {p : TypeAIndex m}
    (hp : p ∈ (typeAZeroSumBase K m).support) :
    (typeAZeroSumRevAut K m).indexEquiv p ∈ (typeAZeroSumBase K m).support := by
  obtain ⟨i, rfl⟩ := (mem_support_typeAZeroSumBase_iff K).mp hp
  exact indexEquiv_typeAZeroSumRevAut_simplePair K m i ▸
    (mem_support_typeAZeroSumBase_iff K).mpr ⟨i.rev, rfl⟩

/-- Conjugating `typeABaseChangeGraphAut` to zero-sum coordinates gives `typeAZeroSumRevAut`. -/
theorem autCongr_typeABaseChangeEquivZeroSum_graphAut (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).autCongr (typeABaseChangeGraphAut K m) =
      typeAZeroSumRevAut K m := by
  apply RootPairing.Equiv.weightHom_injective
  refine LinearEquiv.ext fun u ↦ (zeroSumWeightEquiv K m).injective (funext fun k ↦ ?_)
  rw [RootPairing.Equiv.weightHom_apply, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.weightEquiv_autCongr_apply,
    RootPairing.Equiv.weightEquiv_apply (typeAZeroSumRevAut K m), weightMap_typeAZeroSumRevAut,
    LinearEquiv.coe_coe, show (typeABaseChangeEquivZeroSum K m).weightEquiv =
      (zeroSumWeightEquiv K m).symm from RootPairing.weightEquiv_equivMap ..,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, RootPairing.Equiv.weightEquiv_apply,
    weightMap_typeABaseChangeGraphAut_apply]
  change (u : Fin (m + 1) → K) k.rev.castSucc - (u : Fin (m + 1) → K) k.rev.succ =
    (typeAZeroSumRevEquiv K m u : Fin (m + 1) → K) k.castSucc -
      (typeAZeroSumRevEquiv K m u : Fin (m + 1) → K) k.succ
  simp only [coe_typeAZeroSumRevEquiv_apply, Fin.rev_castSucc, Fin.rev_succ]; ring

end Field

end TauCeti.DynkinType
