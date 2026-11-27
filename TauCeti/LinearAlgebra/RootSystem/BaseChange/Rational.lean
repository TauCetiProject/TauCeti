/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Basis
import TauCeti.Algebra.Algebra.Pi
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# The rational coordinate model of a crystallographic root system

For a crystallographic root system `P` over a characteristic-zero ring `R` with base `b`,
expanding roots in the simple-root basis `b` gives `b.rationalModel` on `b.support → ℚ` paired
by the dot product, with canonical base `b.rationalModelBase`. When `P` is finite, reduced, and
irreducible over a characteristic-zero domain `R`, irreducibility transfers to `b.rationalModel`
and to its base change to any characteristic-zero field `S` (alongside the general root-system and
reducedness instances in `TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi`). Over any
characteristic-zero `ℚ`-algebra `K`, `b.equivBaseChangeRationalModel` identifies `P` with the
base change of `b.rationalModel` to `K`.
-/

public section

open Function Matrix Set TauCeti

namespace RootPairing.Base

section Ring

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

variable [P.IsCrystallographic]

omit [CharZero R] in
private lemma injective_pairingIn_support [P.IsRootSystem] :
    Injective (fun j (k : b.support) ↦ P.pairingIn ℤ k j) := fun i j hij ↦ by
  apply P.coroot.injective
  apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
  refine b.toWeightBasis.ext fun k ↦ ?_
  simp only [LinearMap.flip_apply, toWeightBasis_apply, root_coroot_eq_pairing,
    ← P.algebraMap_pairingIn ℤ]
  exact congrArg (algebraMap ℤ R) (congrFun hij k)

private lemma pairingIn_reflectionPerm_support (i j : ι) (k : b.support) :
    P.pairingIn ℤ k (P.reflectionPerm i j) =
      P.pairingIn ℤ k j - P.pairingIn ℤ i j * P.pairingIn ℤ k i := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [map_sub, map_mul, P.algebraMap_pairingIn ℤ, P.algebraMap_pairingIn ℤ,
    P.algebraMap_pairingIn ℤ, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing,
    P.coroot_reflectionPerm, coreflection_apply, map_sub, map_smul, root_coroot_eq_pairing,
    root_coroot_eq_pairing, root'_coroot_eq_pairing, smul_eq_mul]

variable [P.IsRootSystem]

@[simps]
private noncomputable def rationalModelRoot : ι ↪ (b.support → ℚ) :=
  ⟨fun i k ↦ (b.rootCoefficients i k : ℚ), fun _ _ h ↦
    b.rootCoefficients_injective (funext fun k ↦ Int.cast_injective (congrFun h k))⟩

@[simps]
private noncomputable def rationalModelCoroot : ι ↪ (b.support → ℚ) :=
  ⟨fun j k ↦ (P.pairingIn ℤ k j : ℚ), fun _ _ h ↦
    b.injective_pairingIn_support (funext fun k ↦ Int.cast_injective (congrFun h k))⟩

/-- **The rational coordinate model of a crystallographic root system.** Its weight and coweight
spaces are `b.support → ℚ` paired by the dot product. -/
noncomputable def rationalModel : RootPairing ι ℚ (b.support → ℚ) (b.support → ℚ) where
  toLinearMap := dotProductBilin ℚ ℚ
  root := b.rationalModelRoot
  coroot := b.rationalModelCoroot
  root_coroot_two i := by
    rw [dotProductBilin_apply_apply]
    simpa [rationalModelRoot_apply, rationalModelCoroot_apply, dotProduct,
      P.pairingIn_same ℤ i] using
      congrArg (Int.cast (R := ℚ)) (b.rootCoefficients_dotProduct_pairingIn i i)
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext k
    simp only [dotProductBilin_apply_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      rationalModelRoot_apply, rationalModelCoroot_apply, dotProduct]
    have hdot := congrArg (Int.cast (R := ℚ)) (b.rootCoefficients_dotProduct_pairingIn j i)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul] at hdot
    rw [hdot, b.rootCoefficients_reflectionPerm i j]
    simp [zsmul_eq_mul]
  reflectionPerm_coroot i j := by
    ext k
    simp only [dotProductBilin_apply_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      rationalModelRoot_apply, rationalModelCoroot_apply, dotProduct]
    have hdot := congrArg (Int.cast (R := ℚ)) (b.rootCoefficients_dotProduct_pairingIn i j)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul] at hdot
    rw [hdot, b.pairingIn_reflectionPerm_support i j k]
    simp

/-- The bilinear pairing of `b.rationalModel` is the standard dot product. -/
@[simp]
theorem rationalModel_toLinearMap (x y : b.support → ℚ) :
    b.rationalModel.toLinearMap x y = x ⬝ᵥ y := (rfl)

@[simp]
theorem rationalModel_reflectionPerm : b.rationalModel.reflectionPerm = P.reflectionPerm := (rfl)

@[simp]
theorem rationalModel_root_apply (i : ι) (k : b.support) :
    b.rationalModel.root i k = (b.rootCoefficients i k : ℚ) := (rfl)

@[simp]
theorem rationalModel_coroot_apply (j : ι) (k : b.support) :
    b.rationalModel.coroot j k = (P.pairingIn ℤ k j : ℚ) := (rfl)

@[simp]
theorem rationalModel_root_support [DecidableEq ι] (i : b.support) :
    b.rationalModel.root i = Pi.single i (1 : ℚ) := by
  ext k
  simp [rationalModel_root_apply, b.rootCoefficients_coe, Pi.single_apply, apply_ite]

private lemma rationalModel_root_eq_pi_basisFun :
    (fun i : (b.support : Set ι) ↦ b.rationalModel.root i) =
      Pi.basisFun ℚ (b.support : Set ι) := by
  classical
  exact funext fun i ↦ by rw [rationalModel_root_support, Pi.basisFun_apply]

@[simp]
theorem rationalModel_pairing (i j : ι) :
    b.rationalModel.pairing i j = (P.pairingIn ℤ i j : ℚ) := by
  rw [← root_coroot_eq_pairing, rationalModel_toLinearMap]
  simpa [dotProduct, rationalModel_root_apply, rationalModel_coroot_apply] using
    congrArg (Int.cast (R := ℚ)) (b.rootCoefficients_dotProduct_pairingIn i j)

instance isCrystallographic_rationalModel : b.rationalModel.IsCrystallographic where
  exists_value i j := ⟨P.pairingIn ℤ i j, by simp⟩

@[simp]
theorem rationalModel_pairingIn (i j : ι) :
    b.rationalModel.pairingIn ℤ i j = P.pairingIn ℤ i j := by
  apply Int.cast_injective (α := ℚ)
  rw [← eq_intCast (algebraMap ℤ ℚ), b.rationalModel.algebraMap_pairingIn ℤ,
    rationalModel_pairing]

private lemma linearIndependent_rationalModel_coroot :
    LinearIndependent ℚ (fun j : b.support ↦ b.rationalModel.coroot j) := by
  let A : Matrix b.support b.support ℤ := Matrix.of fun j k ↦ P.pairingIn ℤ k j
  have hrow : (fun j : b.support ↦ b.rationalModel.coroot j) = (A.map ((↑) : ℤ → ℚ)).row :=
    funext fun j ↦ funext fun k ↦ (b.rationalModel_coroot_apply j k).symm
  rw [hrow, Matrix.linearIndependent_rat_row_iff, Fintype.linearIndependent_iff]
  intro a ha
  have hN : ∑ j : b.support, a j • P.coroot j = 0 := by
    apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
    refine b.toWeightBasis.ext fun k ↦ ?_
    have hk : ∑ j : b.support, a j * P.pairingIn ℤ k j = 0 := by
      simpa [Matrix.row_apply, A] using congrFun ha k
    simp only [toWeightBasis_apply, map_zero, LinearMap.zero_apply, map_sum, map_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.flip_apply, root_coroot_eq_pairing]
    rw [show ∑ j : b.support, a j • P.pairing k j =
        algebraMap ℤ R (∑ j : b.support, a j * P.pairingIn ℤ k j) by
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_mul, P.algebraMap_pairingIn ℤ, zsmul_eq_mul, eq_intCast], hk, map_zero]
  exact Fintype.linearIndependent_iff.1 (b.linearIndepOn_coroot.restrict_scalars' ℤ) a hN

private lemma rationalModel_root_eq_sum_nat (f : ι → ℕ) {i' : ι}
    (hi' : P.root i' = ∑ j ∈ b.support, f j • P.root j) :
    b.rationalModel.root i' = ∑ j : b.support, f j • b.rationalModel.root j := by
  classical
  have hc : b.rootCoefficients i' = fun j : b.support ↦ (f j : ℤ) :=
    b.rootCoefficients_eq_iff.2 (by
      rw [hi', ← Finset.sum_coe_sort b.support]; simp [natCast_zsmul])
  ext k
  simp [rationalModel_root_apply, rationalModel_root_support, Pi.single_apply, hc]

private lemma zsmul_rationalModel_coroot_eq_sum_nat (f : ι → ℕ) {y : N}
    (hy : y = ∑ j ∈ b.flip.support, f j • P.flip.root j) (s : ℤ)
    (hs : ∀ k : b.support, algebraMap ℤ R (s * P.pairingIn ℤ k i) = P.toLinearMap (P.root k) y) :
    s • b.rationalModel.coroot i = ∑ j : b.support, f j • b.rationalModel.coroot j := by
  ext k
  have hk : s * P.pairingIn ℤ k i = ∑ j : b.support, (f j : ℤ) * P.pairingIn ℤ k j := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    rw [hs, hy, ← Finset.sum_coe_sort b.flip.support]
    simp only [map_sum, map_nsmul, map_mul, P.algebraMap_pairingIn ℤ, flip_root,
      root_coroot_eq_pairing, eq_intCast, nsmul_eq_mul, Int.cast_natCast]; rfl
  simpa [rationalModel_coroot_apply, nsmul_eq_mul] using congrArg (Int.cast (R := ℚ)) hk

/-- The canonical base of `b.rationalModel`, supported on `b.support`. -/
noncomputable def rationalModelBase : b.rationalModel.Base where
  support := b.support
  linearIndepOn_root := by
    rw [LinearIndepOn, b.rationalModel_root_eq_pi_basisFun]
    exact (Pi.basisFun ℚ (b.support : Set ι)).linearIndependent
  linearIndepOn_coroot := b.linearIndependent_rationalModel_coroot
  root_mem_or_neg_mem i := by
    classical
    have hsum_mem (f : ι → ℕ) :
        ∑ j : b.support, f j • b.rationalModel.root j ∈
          AddSubmonoid.closure (b.rationalModel.root '' b.support) :=
      sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.property)) _
    obtain ⟨f, -, hroot | hroot⟩ := b.exists_root_eq_sum_nat_or_neg i
    · exact Or.inl (b.rationalModel_root_eq_sum_nat f hroot ▸ hsum_mem f)
    · refine Or.inr ?_
      have hneg := congrArg Neg.neg hroot
      rw [neg_neg, ← reflection_apply_self P i, ← P.root_reflectionPerm] at hneg
      have hneg_eq : -b.rationalModel.root i = b.rationalModel.root (P.reflectionPerm i i) := by
        ext k; simp [rationalModel_root_apply]
      rw [hneg_eq, b.rationalModel_root_eq_sum_nat f hneg]
      exact hsum_mem f
  coroot_mem_or_neg_mem i := by
    have hsum_mem (f : ι → ℕ) :
        ∑ j : b.support, f j • b.rationalModel.coroot j ∈
          AddSubmonoid.closure (b.rationalModel.coroot '' b.support) :=
      sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.property)) _
    obtain ⟨f, -, hcoroot | hcoroot⟩ := b.flip.exists_root_eq_sum_nat_or_neg i
    · refine Or.inl ?_
      rw [← one_smul ℤ (b.rationalModel.coroot i), b.zsmul_rationalModel_coroot_eq_sum_nat f hcoroot
        1 fun k ↦ by rw [one_mul, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, flip_root]]
      exact hsum_mem f
    · refine Or.inr ?_
      have hneg : -P.flip.root i = ∑ j ∈ b.flip.support, f j • P.flip.root j := by
        rw [hcoroot, neg_neg]
      have h' := b.zsmul_rationalModel_coroot_eq_sum_nat f hneg (-1) fun k ↦ by
        rw [neg_one_mul, map_neg, P.algebraMap_pairingIn ℤ, flip_root, map_neg,
          root_coroot_eq_pairing]
      rw [neg_one_zsmul] at h'
      rw [h']
      exact hsum_mem f

@[simp]
theorem support_rationalModelBase : b.rationalModelBase.support = b.support := (rfl)

/-- The supports of `b.rationalModelBase` and `b` name the same indices. -/
noncomputable def supportEquivRationalModelBase : b.rationalModelBase.support ≃ b.support :=
  _root_.Equiv.subtypeEquivRight fun _ ↦ by rw [support_rationalModelBase]

@[simp]
theorem coe_supportEquivRationalModelBase (i : b.rationalModelBase.support) :
    (b.supportEquivRationalModelBase i : ι) = i := (rfl)

@[simp]
theorem cartanMatrix_rationalModelBase (i j : b.rationalModelBase.support) :
    b.rationalModelBase.cartanMatrix i j =
      b.cartanMatrix (b.supportEquivRationalModelBase i) (b.supportEquivRationalModelBase j) :=
  b.rationalModel_pairingIn i j

instance isRootSystem_rationalModel : b.rationalModel.IsRootSystem where
  span_root_eq_top := by
    have hspan : Submodule.span ℚ (range ⇑(Pi.basisFun ℚ (b.support : Set ι))) = ⊤ :=
      (Pi.basisFun ℚ (b.support : Set ι)).span_eq
    rw [eq_top_iff, ← hspan, ← b.rationalModel_root_eq_pi_basisFun]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩
  span_coroot_eq_top := by
    rw [eq_top_iff, ← Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card b.linearIndependent_rationalModel_coroot).trans
        (Module.finrank_pi ℚ).symm)]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩

instance isReduced_rationalModel [P.IsReduced] : b.rationalModel.IsReduced where
  eq_or_eq_neg i j hdep := by
    let A : Matrix (Fin 2) b.support ℤ := Matrix.of ![b.rootCoefficients i, b.rootCoefficients j]
    have hrow : ![b.rationalModel.root i, b.rationalModel.root j] = (A.map ((↑) : ℤ → ℚ)).row := by
      ext m k
      fin_cases m <;> rfl
    have hZ : ¬ LinearIndependent ℤ A.row := by
      rw [← Matrix.linearIndependent_rat_row_iff, ← hrow]
      exact hdep
    have hR : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦ hZ (by
      rw [Fintype.linearIndependent_iff]; intro a ha
      have hsum_coord (k : b.support) :
          a 0 * b.rootCoefficients i k + a 1 * b.rootCoefficients j k = 0 := by
        simpa [Matrix.row_apply, A, Fin.sum_univ_two] using congrFun ha k
      have hsumR : ∑ m : Fin 2, (a m : R) • ![P.root i, P.root j] m = 0 := by
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_smul_eq_zsmul,
          ← b.sum_rootCoefficients_smul_root i, ← b.sum_rootCoefficients_smul_root j,
          Finset.smul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun k _ ↦ by
          rw [smul_smul, smul_smul, ← add_smul, hsum_coord k, zero_smul]
      have ha0 := Fintype.linearIndependent_iff.1 hli (fun m ↦ (a m : R)) hsumR
      intro m
      exact Int.cast_injective (α := R) (by simpa using ha0 m))
    rcases IsReduced.eq_or_eq_neg i j hR with h | h
    · exact Or.inl (by rw [P.root.injective h])
    · refine Or.inr ?_
      have hneg : b.rootCoefficients i = -b.rootCoefficients j := by
        rw [b.rootCoefficients_eq_iff]
        simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
          b.sum_rootCoefficients_smul_root, h]
      ext k; simp [rationalModel_root_apply, hneg]

instance isIrreducible_rationalModel [IsDomain R] [Finite ι] [P.IsReduced] [P.IsIrreducible] :
    b.rationalModel.IsIrreducible :=
  b.isIrreducible_of_cartanMatrix_equiv b.rationalModelBase b.supportEquivRationalModelBase
    b.cartanMatrix_rationalModelBase

end Ring

section BaseChange

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
  (S : Type*) [CommRing S] [IsDomain S] [Algebra ℚ S]

/-- The supports of the base-changed rational model base over `S` and of `b` name the same root
indices. -/
noncomputable def supportEquivRootPairingBaseChangeRationalModel :
    (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).support ≃ b.support :=
  (supportEquivRootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase).trans b.supportEquivRationalModelBase

@[simp]
theorem coe_supportEquivRootPairingBaseChangeRationalModel
    (i : (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).support) :
    (b.supportEquivRootPairingBaseChangeRationalModel S i : ι) = i := by
  simp [supportEquivRootPairingBaseChangeRationalModel]

/-- Base change of `b.rationalModel` to a `ℚ`-algebra domain of characteristic zero preserves the
Cartan matrix of `b`. -/
theorem cartanMatrix_rootPairingBaseChangeRationalModel [CharZero S]
    (i j : (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).support) :
    (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).cartanMatrix i j =
      b.cartanMatrix (b.supportEquivRootPairingBaseChangeRationalModel S i)
        (b.supportEquivRootPairingBaseChangeRationalModel S j) := by
  simp [supportEquivRootPairingBaseChangeRationalModel]

/-- For a finite reduced irreducible crystallographic root system `P` over a characteristic-zero
domain `R`, irreducibility transfers to the base change of `b.rationalModel` to any
characteristic-zero field `S`. -/
instance isIrreducible_rootPairingBaseChange_rationalModel {S : Type*} [Field S] [CharZero S]
    [IsDomain R] [Finite ι] [P.IsReduced] [P.IsIrreducible] :
    (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap).IsIrreducible :=
  b.isIrreducible_of_cartanMatrix_equiv
    (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap b.rationalModelBase)
    (b.supportEquivRootPairingBaseChangeRationalModel S)
    (b.cartanMatrix_rootPairingBaseChangeRationalModel S)

end BaseChange

section EquivOverRing

variable {ι K M N : Type*} [CommRing K] [CharZero K] [Algebra ℚ K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)

/-- **Comparison with the base-changed rational model.** Over a characteristic-zero `ℚ`-algebra
`K`, expanding weights in `b.toWeightBasis` identifies `P` with the base change of
`b.rationalModel` to `K`, with trivial permutation of root indices. -/
noncomputable def equivBaseChangeRationalModel :
    P.Equiv (rootPairingBaseChange K b.rationalModel b.rationalModel_toLinearMap) where
  weightMap := b.toWeightBasis.equivFun.toLinearMap
  coweightMap := b.fundamentalCoweightBasis.equivFun.symm.toLinearMap
  indexEquiv := _root_.Equiv.refl ι
  weight_coweight_transpose := by
    ext y x
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      flip_toLinearMap, LinearMap.toPerfPair_apply, LinearMap.flip_apply,
      toLinearMap_rootPairingBaseChange, dotProduct, Module.Basis.equivFun_apply]
    conv_rhs => rw [← b.toWeightBasis.sum_repr x]
    simp only [toWeightBasis_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    have hk : P.root' k (b.fundamentalCoweightBasis.equivFun.symm y) = y k := by
      rw [← b.fundamentalCoweightBasis_repr, ← Module.Basis.equivFun_apply,
        LinearEquiv.apply_symm_apply]
    exact hk.symm
  root_weightMap := by
    classical
    ext i k
    simpa [root_rootPairingBaseChange, piAlgebraMap_apply, rationalModel_root_apply, map_sum,
      map_zsmul, b.toWeightBasis_repr_root, Finsupp.single_apply] using
      congrArg (fun x ↦ b.toWeightBasis.repr x k) (b.sum_rootCoefficients_smul_root i).symm
  coroot_coweightMap := by
    ext j
    dsimp only [Function.comp_apply, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]; ext k
    simp [Module.Basis.equivFun_apply, b.fundamentalCoweightBasis_repr, ← P.algebraMap_pairingIn ℤ,
      coroot_rootPairingBaseChange, piAlgebraMap_apply]
  bijective_weightMap := b.toWeightBasis.equivFun.bijective
  bijective_coweightMap := b.fundamentalCoweightBasis.equivFun.symm.bijective

@[simp]
theorem equivBaseChangeRationalModel_indexEquiv :
    b.equivBaseChangeRationalModel.indexEquiv = _root_.Equiv.refl ι := (rfl)

@[simp]
theorem equivBaseChangeRationalModel_weightEquiv :
    b.equivBaseChangeRationalModel.weightEquiv = b.toWeightBasis.equivFun :=
  LinearEquiv.ext fun _ ↦ rfl

@[simp]
theorem equivBaseChangeRationalModel_coweightEquiv :
    b.equivBaseChangeRationalModel.coweightEquiv = b.fundamentalCoweightBasis.equivFun.symm :=
  LinearEquiv.ext fun _ ↦ rfl

end EquivOverRing

end RootPairing.Base
