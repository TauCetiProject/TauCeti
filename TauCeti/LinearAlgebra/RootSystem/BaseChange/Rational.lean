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

Let `P` be a crystallographic root system over a commutative ring `R` of characteristic zero,
equipped with a base `b`. Expanding every root in the simple-root basis `b` and evaluating every
coroot against the simple roots produces integer vectors in `b.support → ℤ` whose dot products
recover the integral pairings `P.pairingIn ℤ i j`. Viewing these coordinates over `ℚ` gives a
canonical rational root system `RootPairing.Base.rationalModel b` on `b.support → ℚ` paired by
the dot product, with the same root indices, reflection permutations, Cartan matrix, reducedness,
and irreducibility as `P`.

Because `b.rationalModel` is carried by `b.support → ℚ` with the dot-product pairing,
`TauCeti.rootPairingBaseChange` extends it to any characteristic-zero field `S` (such as `ℝ`,
`ℂ`, or the original base field `K`). Over `K` itself, the simple-root coordinate equivalence
`b.toWeightBasis.equivFun` induces a root-pairing equivalence
`RootPairing.Base.equivBaseChangeRationalModel b` with trivial index permutation. This lets
ordered-field or complex arguments (such as Weyl chambers or complex eigenvectors) be transferred
to crystallographic root systems over arbitrary characteristic-zero fields.

## Main definitions

* `RootPairing.Base.rationalModel`: the rational root system on `b.support → ℚ` obtained from
  the simple-root coordinates of `b`.
* `RootPairing.Base.rationalModelBase`: the canonical base of `b.rationalModel` supported on
  `b.support`.
* `RootPairing.Base.equivBaseChangeRationalModel`: over a characteristic-zero field `K`, the
  equivalence between `P` and the base change of `b.rationalModel` to `K`.

## Main results

* `RootPairing.Base.isCrystallographic_rationalModel`,
  `RootPairing.Base.isRootSystem_rationalModel`, `RootPairing.Base.isReduced_rationalModel`,
  `RootPairing.Base.isIrreducible_rationalModel`: `b.rationalModel` inherits the crystallographic,
  root-system, reduced, and irreducible properties of `P`.
* `RootPairing.Base.isRootSystem_rootPairingBaseChange_rationalModel` and
  `RootPairing.Base.isIrreducible_rootPairingBaseChange_rationalModel`: base-changing
  `b.rationalModel` to any characteristic-zero field `S` preserves being a root system and
  irreducibility.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1.
-/

public section

open Function Matrix Set TauCeti

namespace RootPairing.Base

section Ring

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

/-- The integer coordinate vector of a root in the simple-root basis `b`. -/
private noncomputable def rootCoordInt (i : ι) : b.support → ℤ :=
  fun k ↦ b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k

private lemma sum_rootCoordInt_smul (i : ι) :
    ∑ k : b.support, b.rootCoordInt i k • P.root k = P.root i := by
  have h := congrArg Subtype.val (b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ i))
  simpa [rootCoordInt] using h

private lemma rootCoordInt_injective : Injective b.rootCoordInt := by
  intro i j hij
  apply P.root.injective
  rw [← b.sum_rootCoordInt_smul i, ← b.sum_rootCoordInt_smul j, hij]

variable [P.IsCrystallographic]

omit [CharZero R] in
private lemma corootCoordInt_injective [P.IsRootSystem] :
    Injective (fun j (k : b.support) ↦ P.pairingIn ℤ k j) := by
  intro i j hij
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
  simp only [map_mul, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing]
  calc ∑ k : b.support,
          algebraMap ℤ R (b.rootCoordInt i k) * P.toLinearMap (P.root k) (P.coroot j)
      = ∑ k : b.support, P.toLinearMap (b.rootCoordInt i k • P.root k) (P.coroot j) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, eq_intCast]
    _ = P.toLinearMap (∑ k : b.support, b.rootCoordInt i k • P.root k) (P.coroot j) := by
          rw [map_sum, LinearMap.sum_apply]
    _ = P.pairing i j := by rw [b.sum_rootCoordInt_smul, root_coroot_eq_pairing]

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
    P.algebraMap_pairingIn ℤ, P.algebraMap_pairingIn ℤ]
  rw [← root_coroot_eq_pairing, P.coroot_reflectionPerm, coreflection_apply, map_sub, map_smul,
    root_coroot_eq_pairing, root_coroot_eq_pairing, root'_coroot_eq_pairing, smul_eq_mul]

variable [P.IsRootSystem]

/-- **The rational coordinate model of a crystallographic root system.** Its weight and coweight
spaces are `b.support → ℚ` paired by the dot product, its roots are the simple-root coordinate
vectors of `P.root`, and its coroots are the pairings against the simple roots of `b`. -/
noncomputable def rationalModel : RootPairing ι ℚ (b.support → ℚ) (b.support → ℚ) where
  toLinearMap := dotProductBilin ℚ ℚ
  root := ⟨fun i k ↦ (b.rootCoordInt i k : ℚ), fun i j h ↦
    b.rootCoordInt_injective (funext fun k ↦ Int.cast_injective (congrFun h k))⟩
  coroot := ⟨fun j k ↦ (P.pairingIn ℤ k j : ℚ), fun i j h ↦
    b.corootCoordInt_injective (funext fun k ↦ Int.cast_injective (congrFun h k))⟩
  root_coroot_two i := by
    change (fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k i : ℚ)) = 2
    have h := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i i)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul, P.pairingIn_same ℤ i, Int.cast_ofNat] at h
    exact h
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    have hdot :
        (fun k ↦ (b.rootCoordInt j k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k i : ℚ)) =
          (P.pairingIn ℤ j i : ℚ) := by
      have h := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt j i)
      simpa [dotProduct] using h
    ext k
    have h := congrArg (fun f : b.support → ℤ ↦ (f k : ℚ))
      (b.rootCoordInt_reflectionPerm i j)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProductBilin_apply_apply]
    change (b.rootCoordInt j k : ℚ) -
        ((fun k ↦ (b.rootCoordInt j k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k i : ℚ))) *
          (b.rootCoordInt i k : ℚ) =
      (b.rootCoordInt (P.reflectionPerm i j) k : ℚ)
    rw [hdot]
    simpa [Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul] using h.symm
  reflectionPerm_coroot i j := by
    have hdot :
        (fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k j : ℚ)) =
          (P.pairingIn ℤ i j : ℚ) := by
      have h := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i j)
      simpa [dotProduct] using h
    ext k
    have h := congrArg (Int.cast (R := ℚ)) (b.corootCoordInt_reflectionPerm i j k)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProductBilin_apply_apply]
    change (P.pairingIn ℤ k j : ℚ) -
        ((fun k ↦ (b.rootCoordInt i k : ℚ)) ⬝ᵥ (fun k ↦ (P.pairingIn ℤ k j : ℚ))) *
          (P.pairingIn ℤ k i : ℚ) =
      (P.pairingIn ℤ k (P.reflectionPerm i j) : ℚ)
    rw [hdot]
    simpa using h.symm

/-- The bilinear pairing of `b.rationalModel` is the standard dot product. -/
theorem rationalModel_toLinearMap (x y : b.support → ℚ) :
    b.rationalModel.toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

@[simp]
theorem rationalModel_reflectionPerm : b.rationalModel.reflectionPerm = P.reflectionPerm :=
  (rfl)

@[simp]
theorem rationalModel_root_apply (i : ι) (k : b.support) :
    b.rationalModel.root i k = (b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k : ℚ) :=
  (rfl)

@[simp]
theorem rationalModel_coroot_apply (j : ι) (k : b.support) :
    b.rationalModel.coroot j k = (P.pairingIn ℤ k j : ℚ) :=
  (rfl)

@[simp]
theorem rationalModel_root_support [DecidableEq ι] (i : b.support) :
    b.rationalModel.root i = Pi.single i (1 : ℚ) := by
  ext k
  have h : b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) = Finsupp.single i (1 : ℤ) := by
    have hi : P.rootSpanMem ℤ i = b.toWeightBasisInt i :=
      Subtype.ext (b.coe_toWeightBasisInt_apply i).symm
    rw [hi, b.toWeightBasisInt.repr_self]
  rw [rationalModel_root_apply, h, Finsupp.single_apply, Pi.single_apply]
  by_cases hki : k = i
  · subst hki; simp
  · simp [hki, Ne.symm hki]

@[simp]
theorem rationalModel_pairing (i j : ι) :
    b.rationalModel.pairing i j = (P.pairingIn ℤ i j : ℚ) := by
  rw [← root_coroot_eq_pairing, rationalModel_toLinearMap]
  have h := congrArg (Int.cast (R := ℚ)) (b.rootCoordInt_dot_corootCoordInt i j)
  simpa [dotProduct, rationalModel_root_apply, rationalModel_coroot_apply, rootCoordInt] using h

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
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Clear denominators so the relation holds over `ℤ`, then lift to `N` via `b.toWeightBasis`.
  let d : ℕ := ∏ j : b.support, (c j).den
  have hd : (d : ℚ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.2 fun j _ ↦ (c j).den_pos.ne')
  have hint (j : b.support) : ∃ a : ℤ, (a : ℚ) = (d : ℚ) * c j := by
    obtain ⟨m, hm⟩ :=
      Finset.dvd_prod_of_mem (fun j : b.support ↦ (c j).den) (Finset.mem_univ j)
    refine ⟨(c j).num * (m : ℤ), ?_⟩
    dsimp only [d]
    rw [hm]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  choose a ha using hint
  have hN : ∑ j : b.support, a j • P.coroot j = 0 := by
    apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
    refine b.toWeightBasis.ext fun k ↦ ?_
    simp only [toWeightBasis_apply, map_zero, LinearMap.zero_apply, map_sum, map_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.flip_apply, root_coroot_eq_pairing]
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      rationalModel_coroot_apply] at hk
    have hk' : ∑ j : b.support, a j * P.pairingIn ℤ k j = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      simp_rw [ha, mul_assoc, ← Finset.mul_sum, hk, mul_zero]
    calc ∑ j : b.support, a j • P.pairing k j
        = algebraMap ℤ R (∑ j : b.support, a j * P.pairingIn ℤ k j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [map_mul, P.algebraMap_pairingIn ℤ, zsmul_eq_mul, eq_intCast]
      _ = 0 := by rw [hk', map_zero]
  have ha0 := Fintype.linearIndependent_iff.1 (b.linearIndepOn_coroot.restrict_scalars' ℤ) a hN
  intro j
  have hdj : (d : ℚ) * c j = 0 := by rw [← ha j, ha0 j, Int.cast_zero]
  exact (mul_eq_zero.1 hdj).resolve_left hd

/-- The canonical base of `b.rationalModel`, supported on `b.support`. -/
noncomputable def rationalModelBase : b.rationalModel.Base where
  support := b.support
  linearIndepOn_root := by
    classical
    have hfun : (fun i : b.support ↦ b.rationalModel.root i) =
        fun i : b.support ↦ Pi.basisFun ℚ b.support i := by
      funext i
      rw [rationalModel_root_support, Pi.basisFun_apply]
    change LinearIndependent ℚ (fun i : b.support ↦ b.rationalModel.root i)
    rw [hfun]
    exact (Pi.basisFun ℚ b.support).linearIndependent
  linearIndepOn_coroot := b.linearIndependent_rationalModel_coroot
  root_mem_or_neg_mem i := by
    classical
    obtain ⟨f, _, hroot | hroot⟩ := b.exists_root_eq_sum_nat_or_neg i
    · left
      have hrepr : b.rationalModel.root i = ∑ j : b.support, f j • b.rationalModel.root j := by
        have hmem :
            P.rootSpanMem ℤ i = ∑ j : b.support, (f j : ℤ) • b.toWeightBasisInt j := by
          apply Subtype.ext
          simpa [Finset.sum_attach b.support (fun j ↦ f j • P.root j)] using hroot
        ext k
        simp [rationalModel_root_apply, hmem, Finsupp.single_apply, rationalModel_root_support,
          Pi.single_apply]
      rw [hrepr]
      exact sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.2)) _
    · right
      have hrepr : -b.rationalModel.root i = ∑ j : b.support, f j • b.rationalModel.root j := by
        have hmem :
            -P.rootSpanMem ℤ i = ∑ j : b.support, (f j : ℤ) • b.toWeightBasisInt j := by
          apply Subtype.ext
          have hneg' := congrArg Neg.neg hroot
          rw [neg_neg] at hneg'
          simpa [Finset.sum_attach b.support (fun j ↦ f j • P.root j)] using hneg'
        ext k
        have hneg : b.toWeightBasisInt.repr (P.rootSpanMem ℤ i) k =
            -(b.toWeightBasisInt.repr (-P.rootSpanMem ℤ i) k) := by simp
        simp [rationalModel_root_apply, hneg, hmem, Finsupp.single_apply,
          rationalModel_root_support, Pi.single_apply]
      rw [hrepr]
      exact sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.2)) _
  coroot_mem_or_neg_mem i := by
    obtain ⟨f, _, hcoroot | hcoroot⟩ := b.flip.exists_root_eq_sum_nat_or_neg i
    · left
      have hrepr :
          b.rationalModel.coroot i = ∑ j : b.support, f j • b.rationalModel.coroot j := by
        ext k
        have hk : P.pairingIn ℤ k i = ∑ j : b.support, (f j : ℤ) * P.pairingIn ℤ k j := by
          apply FaithfulSMul.algebraMap_injective ℤ R
          rw [P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, ← flip_root, hcoroot,
            ← Finset.sum_coe_sort b.flip.support]
          simp only [map_sum, map_nsmul, map_mul, P.algebraMap_pairingIn ℤ, flip_root,
            root_coroot_eq_pairing, eq_intCast, nsmul_eq_mul, Int.cast_natCast]
          rfl
        simpa [rationalModel_coroot_apply, nsmul_eq_mul] using congrArg (Int.cast (R := ℚ)) hk
      rw [hrepr]
      exact sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.2)) _
    · right
      have hrepr :
          -b.rationalModel.coroot i = ∑ j : b.support, f j • b.rationalModel.coroot j := by
        ext k
        have hk : -P.pairingIn ℤ k i = ∑ j : b.support, (f j : ℤ) * P.pairingIn ℤ k j := by
          apply FaithfulSMul.algebraMap_injective ℤ R
          have hneg' := congrArg Neg.neg hcoroot
          rw [neg_neg] at hneg'
          rw [map_neg, P.algebraMap_pairingIn ℤ, ← root_coroot_eq_pairing, ← map_neg,
            ← flip_root, hneg', ← Finset.sum_coe_sort b.flip.support]
          simp only [map_sum, map_nsmul, map_mul, P.algebraMap_pairingIn ℤ, flip_root,
            root_coroot_eq_pairing, eq_intCast, nsmul_eq_mul, Int.cast_natCast]
          rfl
        simpa [rationalModel_coroot_apply, nsmul_eq_mul] using congrArg (Int.cast (R := ℚ)) hk
      rw [hrepr]
      exact sum_mem fun j _ ↦ nsmul_mem (AddSubmonoid.subset_closure (mem_image_of_mem _ j.2)) _

@[simp]
theorem support_rationalModelBase : b.rationalModelBase.support = b.support :=
  (rfl)

/-- The supports of `b.rationalModelBase` and `b` name the same indices. -/
noncomputable def supportEquivRationalModelBase : b.rationalModelBase.support ≃ b.support :=
  _root_.Equiv.subtypeEquivRight fun _ ↦ by rw [support_rationalModelBase]

@[simp]
theorem coe_supportEquivRationalModelBase (i : b.rationalModelBase.support) :
    (b.supportEquivRationalModelBase i : ι) = i :=
  (rfl)

@[simp]
theorem cartanMatrix_rationalModelBase (i j : b.rationalModelBase.support) :
    b.rationalModelBase.cartanMatrix i j =
      b.cartanMatrix (b.supportEquivRationalModelBase i) (b.supportEquivRationalModelBase j) :=
  b.rationalModel_pairingIn i j

instance isRootSystem_rationalModel : b.rationalModel.IsRootSystem where
  span_root_eq_top := by
    classical
    rw [eq_top_iff]
    calc (⊤ : Submodule ℚ (b.support → ℚ))
        = Submodule.span ℚ (range fun i : b.support ↦ b.rationalModel.root i) := by
          have hfun : (fun i : b.support ↦ b.rationalModel.root i) =
              fun i : b.support ↦ Pi.basisFun ℚ b.support i := by
            funext i
            rw [rationalModel_root_support, Pi.basisFun_apply]
          rw [hfun, (Pi.basisFun ℚ b.support).span_eq]
      _ ≤ Submodule.span ℚ (range b.rationalModel.root) :=
          Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩
  span_coroot_eq_top := by
    rw [eq_top_iff]
    calc (⊤ : Submodule ℚ (b.support → ℚ))
        = Submodule.span ℚ (range fun i : b.support ↦ b.rationalModel.coroot i) := by
          symm
          exact Submodule.eq_top_of_finrank_eq
            ((finrank_span_eq_card b.linearIndependent_rationalModel_coroot).trans
              (Module.finrank_pi ℚ).symm)
      _ ≤ Submodule.span ℚ (range b.rationalModel.coroot) :=
          Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨i, hi⟩

instance isReduced_rationalModel [P.IsReduced] : b.rationalModel.IsReduced where
  eq_or_eq_neg i j hdep := by
    have hR : ¬ LinearIndependent R ![P.root i, P.root j] := by
      intro hli
      apply hdep
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let d : ℕ := (c 0).den * (c 1).den
      have hd : (d : ℚ) ≠ 0 := by positivity
      let a : Fin 2 → ℤ := ![((c 0).num * (c 1).den : ℤ), ((c 1).num * (c 0).den : ℤ)]
      have ha (m : Fin 2) : (a m : ℚ) = (d : ℚ) * c m := by
        fin_cases m
        · simp only [a, d, Fin.zero_eta, Matrix.cons_val_zero, Int.cast_mul, Int.cast_natCast,
            Nat.cast_mul]
          rw [← Rat.mul_den_eq_num]
          ring
        · simp only [a, d, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_mul,
            Int.cast_natCast, Nat.cast_mul]
          rw [← Rat.mul_den_eq_num]
          ring
      have hsumR : ∑ m : Fin 2, (a m : R) • ![P.root i, P.root j] m = 0 := by
        have hsum_coord : ∀ k : b.support,
            a 0 * b.rootCoordInt i k + a 1 * b.rootCoordInt j k = 0 := fun k ↦ by
          apply Int.cast_injective (α := ℚ)
          have hk := congrFun hc k
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
            rationalModel_root_apply] at hk
          push_cast
          rw [ha 0, ha 1, rootCoordInt, rootCoordInt]
          linear_combination (d : ℚ) * hk
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_smul_eq_zsmul]
        rw [← b.sum_rootCoordInt_smul i, ← b.sum_rootCoordInt_smul j, Finset.smul_sum,
          Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        rw [smul_smul, smul_smul, ← add_smul, hsum_coord k, zero_smul]
      have ha0 := Fintype.linearIndependent_iff.1 hli (fun m ↦ (a m : R)) hsumR
      intro m
      have ham : a m = 0 := Int.cast_injective (α := R) (by simpa using ha0 m)
      have hdm : (d : ℚ) * c m = 0 := by rw [← ha m, ham, Int.cast_zero]
      exact (mul_eq_zero.1 hdm).resolve_left hd
    rcases IsReduced.eq_or_eq_neg i j hR with h | h
    · left
      rw [P.root.injective h]
    · right
      have hneg : P.rootSpanMem ℤ i = -P.rootSpanMem ℤ j := Subtype.ext h
      ext k
      simp [rationalModel_root_apply, hneg]

omit [CharZero R] [P.IsCrystallographic] in
private lemma nonempty_support_of_isIrreducible [P.IsIrreducible] :
    Nonempty b.support := by
  have := IsIrreducible.nontrivial P
  by_contra h
  rw [not_nonempty_iff] at h
  exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton

instance isIrreducible_rationalModel [IsDomain R] [Finite ι] [P.IsReduced] [P.IsIrreducible] :
    b.rationalModel.IsIrreducible := by
  have hne : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have hne' : Nonempty b.rationalModelBase.support :=
    hne.map b.supportEquivRationalModelBase.symm
  let iso : diagramGraph b.rationalModelBase.cartanMatrix ≃g diagramGraph b.cartanMatrix :=
    { toEquiv := b.supportEquivRationalModelBase
      map_rel_iff' := by
        intro u v
        simp [diagramGraph_adj] }
  have hconn : (diagramGraph b.rationalModelBase.cartanMatrix).Connected := by
    refine ⟨fun u v ↦ ?_⟩
    obtain ⟨w⟩ := preconnected_diagramGraph_cartanMatrix b (iso u) (iso v)
    simpa using (w.map iso.symm.toHom).reachable
  exact isIrreducible_of_connected_diagramGraph_cartanMatrix b.rationalModelBase hconn

end Ring

section BaseChangeField

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsRootSystem]
  (b : P.Base)

variable (S : Type*) [Field S] [CharZero S]

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
  have hne : Nonempty bS.support := b.nonempty_support_of_isIrreducible.map e.symm
  let iso : diagramGraph bS.cartanMatrix ≃g diagramGraph b.cartanMatrix :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        simp [bS, e, diagramGraph_adj] }
  have hconn : (diagramGraph bS.cartanMatrix).Connected := by
    refine ⟨fun u v ↦ ?_⟩
    obtain ⟨w⟩ := preconnected_diagramGraph_cartanMatrix b (iso u) (iso v)
    simpa using (w.map iso.symm.toHom).reachable
  exact isIrreducible_of_connected_diagramGraph_cartanMatrix bS hconn

end BaseChangeField

section EquivOverField

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsCrystallographic] [P.IsRootSystem]
  (b : P.Base)

/-- The coweight equivalence identifying `N` with `b.support → K` by pairing against the simple
roots of `b`. -/
private noncomputable def coweightEquivFun : N ≃ₗ[K] (b.support → K) := by
  classical
  exact P.flip.toPerfPair.trans b.toWeightBasis.dualBasis.equivFun

omit [CharZero K] [P.IsCrystallographic] in
private lemma coweightEquivFun_apply (y : N) (k : b.support) :
    b.coweightEquivFun y k = P.toLinearMap (P.root k) y := by
  classical
  change (P.flip.toPerfPair.trans b.toWeightBasis.dualBasis.equivFun) y k = _
  rw [LinearEquiv.trans_apply, Module.Basis.dualBasis_equivFun]
  simp

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
    have hcoord (k : b.support) : P.toLinearMap (P.root k) (b.coweightEquivFun.symm y) = y k := by
      rw [← b.coweightEquivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe,
      flip_toLinearMap, LinearMap.toPerfPair_apply, LinearMap.flip_apply]
    conv_rhs => rw [← b.toWeightBasis.sum_repr x]
    simp only [map_sum, map_smul, toWeightBasis_apply, Module.Basis.equivFun_apply]
    simp [toLinearMap_rootPairingBaseChange, dotProduct, hcoord]
  root_weightMap := by
    ext i k
    simp only [Function.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply,
      _root_.Equiv.refl_apply, root_rootPairingBaseChange, piAlgebraMap_apply,
      rationalModel_root_apply, map_intCast]
    have h := congrArg (fun x ↦ b.toWeightBasis.repr x k) (b.sum_rootCoordInt_smul i).symm
    classical
    simpa [map_sum, map_zsmul, b.toWeightBasis_repr_root, Finsupp.single_apply, rootCoordInt]
      using h
  coroot_coweightMap := by
    ext j
    simp only [Function.comp_apply, LinearEquiv.coe_coe, _root_.Equiv.refl_symm,
      _root_.Equiv.refl_apply, coroot_rootPairingBaseChange]
    rw [LinearEquiv.symm_apply_eq]
    ext k
    rw [b.coweightEquivFun_apply, root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ,
      piAlgebraMap_apply, rationalModel_coroot_apply, map_intCast, eq_intCast]
  bijective_weightMap := b.toWeightBasis.equivFun.bijective
  bijective_coweightMap := b.coweightEquivFun.symm.bijective

@[simp]
theorem equivBaseChangeRationalModel_indexEquiv :
    b.equivBaseChangeRationalModel.indexEquiv = _root_.Equiv.refl ι :=
  (rfl)

@[simp]
theorem equivBaseChangeRationalModel_weightEquiv :
    b.equivBaseChangeRationalModel.weightEquiv = b.toWeightBasis.equivFun :=
  LinearEquiv.ext fun _ ↦ rfl

end EquivOverField

end RootPairing.Base
