/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import Mathlib.LinearAlgebra.Dual.Basis
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

/-!
# The rational coordinate model of a crystallographic root system

For a crystallographic root system `P` over a characteristic-zero ring `R` with base `b`,
expanding roots in the simple-root basis `b` gives `b.rationalModel` on `b.support → ℚ` paired
by the dot product, with canonical base `b.rationalModelBase`. Base-changing `b.rationalModel` to
any characteristic-zero field `S` preserves the root-system, reducedness, and irreducibility
properties, and over a characteristic-zero field `K` itself, `b.equivBaseChangeRationalModel`
identifies `P` with the base change of `b.rationalModel` to `K`.
-/

public section

open Function Matrix Set TauCeti

namespace RootPairing.Base

section Ring

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

private noncomputable def rootCoordInt (i : ι) : b.support → ℤ :=
  fun k ↦ b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k

private lemma sum_rootCoordInt_smul (i : ι) :
    ∑ k : b.support, b.rootCoordInt i k • P.root k = P.root i := by
  simpa [rootCoordInt] using
    congrArg Subtype.val (b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ i))

private lemma rootCoordInt_injective : Injective b.rootCoordInt := fun i j hij ↦
  P.root.injective (by rw [← b.sum_rootCoordInt_smul i, ← b.sum_rootCoordInt_smul j, hij])

variable [P.IsCrystallographic]

omit [CharZero R] in
private lemma corootCoordInt_injective [P.IsRootSystem] :
    Injective (fun j (k : b.support) ↦ P.pairingIn ℤ k j) := fun i j hij ↦ by
  apply P.coroot.injective
  apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
  refine b.toWeightBasis.ext fun k ↦ ?_
  simp only [LinearMap.flip_apply, toWeightBasis_apply, root_coroot_eq_pairing,
    ← P.algebraMap_pairingIn ℤ]
  exact congrArg (algebraMap ℤ R) (congrFun hij k)

private lemma rootCoordInt_dot_corootCoordInt (i j : ι) :
    b.rootCoordInt i ⬝ᵥ (fun k : b.support ↦ P.pairingIn ℤ k j) = P.pairingIn ℤ i j := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [P.algebraMap_pairingIn ℤ i j, dotProduct, map_sum]
  conv_rhs => rw [← root_coroot_eq_pairing, ← b.sum_rootCoordInt_smul i, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, map_zsmul,
    LinearMap.smul_apply, zsmul_eq_mul, eq_intCast]

private lemma rootCoordInt_reflectionPerm (i j : ι) :
    b.rootCoordInt (P.reflectionPerm i j) =
      b.rootCoordInt j - P.pairingIn ℤ j i • b.rootCoordInt i := by
  ext k
  have hmem : P.rootSpanMem ℤ (P.reflectionPerm i j) =
      P.rootSpanMem ℤ j - P.pairingIn ℤ j i • P.rootSpanMem ℤ i := by
    apply Subtype.ext
    simpa [Int.cast_smul_eq_zsmul, ← P.algebraMap_pairingIn ℤ, eq_intCast] using
      (P.reflectionPerm_root i j).symm
  rw [rootCoordInt, hmem, map_sub, map_zsmul]
  simp [rootCoordInt]

private lemma corootCoordInt_reflectionPerm (i j : ι) (k : b.support) :
    P.pairingIn ℤ k (P.reflectionPerm i j) =
      P.pairingIn ℤ k j - P.pairingIn ℤ i j * P.pairingIn ℤ k i := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [map_sub, map_mul, P.algebraMap_pairingIn ℤ, P.algebraMap_pairingIn ℤ,
    P.algebraMap_pairingIn ℤ, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing,
    P.coroot_reflectionPerm, coreflection_apply, map_sub, map_smul, root_coroot_eq_pairing,
    root_coroot_eq_pairing, root'_coroot_eq_pairing, smul_eq_mul]

variable [P.IsRootSystem]

/-- **The rational coordinate model of a crystallographic root system.** Its weight and coweight
spaces are `b.support → ℚ` paired by the dot product. -/
noncomputable def rationalModel : RootPairing ι ℚ (b.support → ℚ) (b.support → ℚ) where
  toLinearMap := dotProductBilin ℚ ℚ
  root := ⟨fun i k ↦ (b.rootCoordInt i k : ℚ), fun _ _ h ↦
    b.rootCoordInt_injective (funext fun k ↦ Int.cast_injective (congrFun h k))⟩
  coroot := ⟨fun j k ↦ (P.pairingIn ℤ k j : ℚ), fun _ _ h ↦
    b.corootCoordInt_injective (funext fun k ↦ Int.cast_injective (congrFun h k))⟩
  root_coroot_two i := by
    change (fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k i : ℚ)) = 2
    have h := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i i)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul, P.pairingIn_same ℤ i, Int.cast_ofNat] at h
    exact h
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext k
    have hdot := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt j i)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul] at hdot
    change (b.rootCoordInt j k : ℚ) -
      ((fun k ↦ (b.rootCoordInt j k : ℚ)) ⬝ᵥ fun k ↦ (P.pairingIn ℤ k i : ℚ)) *
        (b.rootCoordInt i k : ℚ) = (b.rootCoordInt (P.reflectionPerm i j) k : ℚ)
    rw [show (fun k ↦ (b.rootCoordInt j k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k i : ℚ)) =
        (P.pairingIn ℤ j i : ℚ) from hdot, b.rootCoordInt_reflectionPerm i j]
    simp [zsmul_eq_mul]
  reflectionPerm_coroot i j := by
    ext k
    have hdot := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i j)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul] at hdot
    change (P.pairingIn ℤ k j : ℚ) -
      ((fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ fun k ↦ (P.pairingIn ℤ k j : ℚ)) *
        (P.pairingIn ℤ k i : ℚ) = (P.pairingIn ℤ k (P.reflectionPerm i j) : ℚ)
    rw [show (fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k j : ℚ)) =
        (P.pairingIn ℤ i j : ℚ) from hdot, b.corootCoordInt_reflectionPerm i j k]
    simp

/-- The bilinear pairing of `b.rationalModel` is the standard dot product. -/
theorem rationalModel_toLinearMap (x y : b.support → ℚ) :
    b.rationalModel.toLinearMap x y = x ⬝ᵥ y := (rfl)

@[simp]
theorem rationalModel_reflectionPerm : b.rationalModel.reflectionPerm = P.reflectionPerm := (rfl)

@[simp]
theorem rationalModel_root_apply (i : ι) (k : b.support) :
    b.rationalModel.root i k = (b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k : ℚ) := (rfl)

@[simp]
theorem rationalModel_coroot_apply (j : ι) (k : b.support) :
    b.rationalModel.coroot j k = (P.pairingIn ℤ k j : ℚ) := (rfl)

@[simp]
theorem rationalModel_root_support [DecidableEq ι] (i : b.support) :
    b.rationalModel.root i = Pi.single i (1 : ℚ) := by
  ext k
  have h : b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) = Finsupp.single i (1 : ℤ) := by
    rw [show P.rootSpanMem ℤ i = b.toWeightBasisInt i from
      Subtype.ext (b.coe_toWeightBasisInt_apply i).symm, b.toWeightBasisInt.repr_self]
  rw [rationalModel_root_apply, h, Finsupp.single_apply, Pi.single_apply]
  by_cases hki : k = i <;> simp [hki, Ne.symm]

@[simp]
theorem rationalModel_pairing (i j : ι) :
    b.rationalModel.pairing i j = (P.pairingIn ℤ i j : ℚ) := by
  rw [← root_coroot_eq_pairing, rationalModel_toLinearMap]
  simpa [dotProduct, rationalModel_root_apply, rationalModel_coroot_apply, rootCoordInt] using
    congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i j)

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
  rw [Fintype.linearIndependent_iff]; intro c hc
  let d : ℕ := ∏ j : b.support, (c j).den
  have hd : (d : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.2 fun j _ ↦ (c j).den_pos.ne')
  have hint (j : b.support) : ∃ a : ℤ, (a : ℚ) = (d : ℚ) * c j := by
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j ↦ (c j).den) (Finset.mem_univ j)
    refine ⟨(c j).num * m, ?_⟩
    dsimp only [d]; rw [hm]; push_cast; rw [← Rat.mul_den_eq_num]; ring
  choose a ha using hint
  have hN : ∑ j : b.support, a j • P.coroot j = 0 := by
    apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
    refine b.toWeightBasis.ext fun k ↦ ?_
    simp only [toWeightBasis_apply, map_zero, LinearMap.zero_apply, map_sum, map_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.flip_apply, root_coroot_eq_pairing]
    have hk' : ∑ j : b.support, a j * P.pairingIn ℤ k j = 0 :=
      Int.cast_injective (α := ℚ) (by
        simpa [ha, mul_assoc, ← Finset.mul_sum, rationalModel_coroot_apply] using
          congrArg ((d : ℚ) * ·) (congrFun hc k))
    rw [show ∑ j : b.support, a j • P.pairing k j =
        algebraMap ℤ R (∑ j : b.support, a j * P.pairingIn ℤ k j) by
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_mul, P.algebraMap_pairingIn ℤ, zsmul_eq_mul, eq_intCast], hk', map_zero]
  have ha0 := Fintype.linearIndependent_iff.1 (b.linearIndepOn_coroot.restrict_scalars' ℤ) a hN
  exact fun j ↦ (mul_eq_zero.1 (by rw [← ha j, ha0 j, Int.cast_zero])).resolve_left hd

/-- The canonical base of `b.rationalModel`, supported on `b.support`. -/
noncomputable def rationalModelBase : b.rationalModel.Base where
  support := b.support
  linearIndepOn_root := by
    classical
    have hfun : (fun i : b.support ↦ b.rationalModel.root i) =
        fun i : b.support ↦ Pi.basisFun ℚ b.support i :=
      funext fun i ↦ by rw [rationalModel_root_support, Pi.basisFun_apply]
    change LinearIndependent ℚ (fun i : b.support ↦ b.rationalModel.root i)
    rw [hfun]; exact (Pi.basisFun ℚ b.support).linearIndependent
  linearIndepOn_coroot := b.linearIndependent_rationalModel_coroot
  root_mem_or_neg_mem i := by
    classical
    have hsum_mem (f : ι → ℕ) :
        ∑ j : b.support, f j • b.rationalModel.root j ∈
          AddSubmonoid.closure (b.rationalModel.root '' b.support) :=
      sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.property)) _
    have hrepr (f : ι → ℕ) (x : P.rootSpan ℤ)
        (hx : (x : M) = ∑ j ∈ b.support, f j • P.root j) :
        (fun k : b.support ↦ (b.toWeightBasisInt.repr x k : ℚ)) =
          ∑ j : b.support, f j • b.rationalModel.root j := by
      have hm : x = ∑ j : b.support, (f j : ℤ) • b.toWeightBasisInt j :=
        Subtype.ext (by simpa [Finset.sum_attach b.support (fun j ↦ f j • P.root j)] using hx)
      ext k; simpa [rationalModel_root_support, Pi.single_apply, Finsupp.single_apply] using
        congrArg (fun z ↦ (b.toWeightBasisInt.repr z k : ℚ)) hm
    obtain ⟨f, -, hroot | hroot⟩ := b.exists_root_eq_sum_nat_or_neg i
    · exact Or.inl (by rw [show b.rationalModel.root i = _ from hrepr f _ hroot]; exact hsum_mem f)
    · refine Or.inr (by
        have hneg' := congrArg Neg.neg hroot; rw [neg_neg] at hneg'
        have hneg_eq : -b.rationalModel.root i =
            fun k : b.support ↦ (b.toWeightBasisInt.repr (-P.rootSpanMem ℤ i) k : ℚ) := by
          ext k; simp [rationalModel_root_apply]
        rw [hneg_eq, hrepr f (-P.rootSpanMem ℤ i) hneg']; exact hsum_mem f)
  coroot_mem_or_neg_mem i := by
    have hsum_mem (f : ι → ℕ) :
        ∑ j : b.support, f j • b.rationalModel.coroot j ∈
          AddSubmonoid.closure (b.rationalModel.coroot '' b.support) :=
      sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.property)) _
    have hcor (f : ι → ℕ) (y : N) (hy : y = ∑ j ∈ b.flip.support, f j • P.flip.root j)
        (s : ℤ) (hs : ∀ k : b.support, algebraMap ℤ R (s * P.pairingIn ℤ k i) =
          P.toLinearMap (P.root k) y) :
        s • b.rationalModel.coroot i = ∑ j : b.support, f j • b.rationalModel.coroot j := by
      ext k
      have hk : s * P.pairingIn ℤ k i = ∑ j : b.support, (f j : ℤ) * P.pairingIn ℤ k j := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        rw [hs, hy, ← Finset.sum_coe_sort b.flip.support]
        simp only [map_sum, map_nsmul, map_mul, P.algebraMap_pairingIn ℤ, flip_root,
          root_coroot_eq_pairing, eq_intCast, nsmul_eq_mul, Int.cast_natCast]; rfl
      simpa [rationalModel_coroot_apply, nsmul_eq_mul] using congrArg (Int.cast (R := ℚ)) hk
    obtain ⟨f, -, hcoroot | hcoroot⟩ := b.flip.exists_root_eq_sum_nat_or_neg i
    · exact Or.inl (by
        rw [← one_smul ℤ (b.rationalModel.coroot i), hcor f _ hcoroot 1 fun k ↦ by
          rw [one_mul, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, flip_root]]
        exact hsum_mem f)
    · exact Or.inr (by
        have h' := hcor f _ (by simpa using congrArg Neg.neg hcoroot) (-1) fun k ↦ by
          rw [neg_one_mul, map_neg, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, map_neg]
        rw [neg_one_zsmul] at h'; rw [h']; exact hsum_mem f)

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
    classical
    rw [eq_top_iff, ← (Pi.basisFun ℚ b.support).span_eq,
      show ⇑(Pi.basisFun ℚ b.support) = fun i : b.support ↦ b.rationalModel.root i from
        funext fun i ↦ by rw [rationalModel_root_support, Pi.basisFun_apply]]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩
  span_coroot_eq_top := by
    rw [eq_top_iff, ← Submodule.eq_top_of_finrank_eq
      ((finrank_span_eq_card b.linearIndependent_rationalModel_coroot).trans
        (Module.finrank_pi ℚ).symm)]
    exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩

instance isReduced_rationalModel [P.IsReduced] : b.rationalModel.IsReduced where
  eq_or_eq_neg i j hdep := by
    have hR : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦ hdep (by
      rw [Fintype.linearIndependent_iff]; intro c hc
      let d : ℕ := (c 0).den * (c 1).den; have hd : (d : ℚ) ≠ 0 := by positivity
      let a : Fin 2 → ℤ := ![((c 0).num * (c 1).den : ℤ), ((c 1).num * (c 0).den : ℤ)]
      have ha (m : Fin 2) : (a m : ℚ) = (d : ℚ) * c m := by
        fin_cases m <;> simp [a, d, ← Rat.mul_den_eq_num] <;> ring
      have hsumR : ∑ m : Fin 2, (a m : R) • ![P.root i, P.root j] m = 0 := by
        have hsum_coord (k : b.support) :
            a 0 * b.rootCoordInt i k + a 1 * b.rootCoordInt j k = 0 := by
          apply Int.cast_injective (α := ℚ); have hk := congrFun hc k
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rationalModel_root_apply] at hk
          push_cast; rw [ha 0, ha 1, rootCoordInt, rootCoordInt]; linear_combination (d : ℚ) * hk
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_smul_eq_zsmul,
          ← b.sum_rootCoordInt_smul i, ← b.sum_rootCoordInt_smul j, Finset.smul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun k _ ↦ by
          rw [smul_smul, smul_smul, ← add_smul, hsum_coord k, zero_smul]
      have ha0 := Fintype.linearIndependent_iff.1 hli (fun m ↦ (a m : R)) hsumR
      intro m; have ham : a m = 0 := Int.cast_injective (α := R) (by simpa using ha0 m)
      exact (mul_eq_zero.1 (by rw [← ha m, ham, Int.cast_zero])).resolve_left hd)
    rcases IsReduced.eq_or_eq_neg i j hR with h | h
    · exact Or.inl (by rw [P.root.injective h])
    · exact Or.inr (by ext k; simp [rationalModel_root_apply,
        show P.rootSpanMem ℤ i = -P.rootSpanMem ℤ j from Subtype.ext h])

omit [CharZero R] [P.IsCrystallographic] in
private lemma nonempty_support_of_isIrreducible [P.IsIrreducible] : Nonempty b.support := by
  have := IsIrreducible.nontrivial P; by_contra h; rw [not_nonempty_iff] at h
  exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton

private lemma isIrreducible_of_cartanMatrix_equiv [IsDomain R] [Finite ι] [P.IsReduced]
    [P.IsIrreducible] {S M' N' : Type*} [Field S] [CharZero S] [AddCommGroup M'] [Module S M']
    [AddCommGroup N'] [Module S N'] {Q : RootPairing ι S M' N'} [Q.IsRootSystem]
    [Q.IsCrystallographic] (bQ : Q.Base) (e : bQ.support ≃ b.support)
    (hC : ∀ u v, bQ.cartanMatrix u v = b.cartanMatrix (e u) (e v)) : Q.IsIrreducible := by
  have hne' : Nonempty bQ.support := b.nonempty_support_of_isIrreducible.map e.symm
  let iso : diagramGraph bQ.cartanMatrix ≃g diagramGraph b.cartanMatrix :=
    { toEquiv := e, map_rel_iff' := @fun u v ↦ by simp [diagramGraph_adj, hC] }
  refine isIrreducible_of_connected_diagramGraph_cartanMatrix bQ ⟨fun u v ↦ ?_⟩
  obtain ⟨w⟩ := preconnected_diagramGraph_cartanMatrix b (iso u) (iso v)
  simpa using (w.map iso.symm.toHom).reachable

instance isIrreducible_rationalModel [IsDomain R] [Finite ι] [P.IsReduced] [P.IsIrreducible] :
    b.rationalModel.IsIrreducible :=
  b.isIrreducible_of_cartanMatrix_equiv b.rationalModelBase b.supportEquivRationalModelBase
    b.cartanMatrix_rationalModelBase

end Ring

section BaseChangeField

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
  (S : Type*) [Field S] [CharZero S]

/-- Base-changing `b.rationalModel` to any characteristic-zero field `S` gives a root system. -/
instance isRootSystem_rootPairingBaseChange_rationalModel :
    (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap).IsRootSystem where
  span_root_eq_top := span_range_root_rootPairingBaseChange_eq_top S _ _
    IsRootSystem.span_root_eq_top
  span_coroot_eq_top := span_range_coroot_rootPairingBaseChange_eq_top S _ _
    IsRootSystem.span_coroot_eq_top

/-- Base-changing `b.rationalModel` to any characteristic-zero field `S` preserves reducedness. -/
instance isReduced_rootPairingBaseChange_rationalModel [P.IsReduced] :
    (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap).IsReduced :=
  isReduced_rootPairingBaseChange S _ _

/-- Base-changing `b.rationalModel` to any characteristic-zero field `S` preserves
irreducibility. -/
instance isIrreducible_rootPairingBaseChange_rationalModel [IsDomain R] [Finite ι] [P.IsReduced]
    [P.IsIrreducible] :
    (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap).IsIrreducible := by
  let bS := rootPairingBaseChangeBase S b.rationalModel
    b.rationalModel_toLinearMap b.rationalModelBase
  let e : bS.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  exact b.isIrreducible_of_cartanMatrix_equiv bS e fun u v ↦ by simp [bS, e]

end BaseChangeField

section EquivOverField

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)

private noncomputable def coweightEquivFun : N ≃ₗ[K] (b.support → K) := by
  classical
  exact P.flip.toPerfPair.trans b.toWeightBasis.dualBasis.equivFun

omit [CharZero K] [P.IsCrystallographic] in
private lemma coweightEquivFun_apply (y : N) (k : b.support) :
    b.coweightEquivFun y k = P.toLinearMap (P.root k) y := by
  classical
  simp [coweightEquivFun, Module.Basis.dualBasis_equivFun]

/-- **Comparison with the base-changed rational model.** Over a characteristic-zero field `K`,
expanding weights in `b.toWeightBasis` identifies `P` with the base change of `b.rationalModel`
to `K`, with trivial permutation of root indices. -/
noncomputable def equivBaseChangeRationalModel :
    P.Equiv (rootPairingBaseChange K b.rationalModel b.rationalModel_toLinearMap) where
  weightMap := b.toWeightBasis.equivFun.toLinearMap
  coweightMap := b.coweightEquivFun.symm.toLinearMap
  indexEquiv := _root_.Equiv.refl ι
  weight_coweight_transpose := by
    ext y x
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      flip_toLinearMap, LinearMap.toPerfPair_apply, LinearMap.flip_apply]
    conv_rhs => rw [← b.toWeightBasis.sum_repr x]
    simp [toLinearMap_rootPairingBaseChange, dotProduct, ← b.coweightEquivFun_apply]
  root_weightMap := by
    classical
    ext i k
    simpa [root_rootPairingBaseChange, piAlgebraMap_apply, rationalModel_root_apply, map_sum,
      map_zsmul, b.toWeightBasis_repr_root, Finsupp.single_apply, rootCoordInt] using
      congrArg (fun x ↦ b.toWeightBasis.repr x k) (b.sum_rootCoordInt_smul i).symm
  coroot_coweightMap := by
    ext j; change b.coweightEquivFun.symm _ = _; rw [LinearEquiv.symm_apply_eq]; ext k
    simp [b.coweightEquivFun_apply, root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ,
      coroot_rootPairingBaseChange, piAlgebraMap_apply]
  bijective_weightMap := b.toWeightBasis.equivFun.bijective
  bijective_coweightMap := b.coweightEquivFun.symm.bijective

@[simp]
theorem equivBaseChangeRationalModel_indexEquiv :
    b.equivBaseChangeRationalModel.indexEquiv = _root_.Equiv.refl ι := (rfl)

@[simp]
theorem equivBaseChangeRationalModel_weightEquiv :
    b.equivBaseChangeRationalModel.weightEquiv = b.toWeightBasis.equivFun :=
  LinearEquiv.ext fun _ ↦ rfl

end EquivOverField

end RootPairing.Base
