/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.DistinctPairs
public import TauCeti.InformationTheory.Coding.Elementary.Basis
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.A
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.Isomorphism
public import TauCeti.LinearAlgebra.RootSystem.Map
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The classical sum-zero root system of type `Aₘ`

This file constructs Bourbaki's classical realization `typeAZeroSumRootPairing K m` of type `Aₘ` on
`singleParityCheckCode K (Fin (m + 1))` paired by the ambient dot product, its Bourbaki base
`typeAZeroSumBase K m` (using the adjacent-difference basis `singleParityCheckCodeBasis K m` from
`TauCeti.InformationTheory.Coding.Elementary.Basis`), the canonical equivalence
`typeABaseChangeEquivZeroSum K m` from `typeABaseChangeRootSystem K m`, and the diagram-reversal
automorphism `typeAZeroSumRevAut K m` (`(θ x) a = -x (rev a)`) together with its root orbits
`orbitIndices_typeAZeroSumRevAut`.

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
theorem typeAZeroSumVec_dotProduct_typeAZeroSumVec (a b c d : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R c d : Fin (m + 1) → R) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
        ((if b = c then 1 else 0) - (if b = d then 1 else 0)) := by
  simp only [coe_typeAZeroSumVec, sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
    Pi.single_apply]; ring

/-- Every classical root `eₐ - e_b` (`a ≠ b`) has squared length `2` for the ambient dot product. -/
theorem typeAZeroSumVec_dotProduct_self {a b : Fin (m + 1)} (h : a ≠ b) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R a b : Fin (m + 1) → R) = 2 := by
  rw [typeAZeroSumVec_dotProduct_typeAZeroSumVec]
  simp only [ite_true, h, h.symm, ite_false]; norm_num

/-- The `i`-th vector of `singleParityCheckCodeBasis R m` is the Bourbaki simple root
`eᵢ - eᵢ₊₁`. -/
theorem singleParityCheckCodeBasis_eq_typeAZeroSumVec (i : Fin m) :
    singleParityCheckCodeBasis R m i = typeAZeroSumVec R i.castSucc i.succ :=
  Subtype.ext (coe_singleParityCheckCodeBasis_apply R m i)

/-- Expansion of `eₐ - e_b` in `singleParityCheckCodeBasis`: coordinate `i` is
`[a ≤ i] - [b ≤ i]`. -/
theorem singleParityCheckCodeBasis_repr_typeAZeroSumVec (a b : Fin (m + 1)) (i : Fin m) :
    (singleParityCheckCodeBasis R m).repr (typeAZeroSumVec R a b) i =
      (if a ≤ i.castSucc then 1 else 0) - (if b ≤ i.castSucc then 1 else 0) := by
  rw [singleParityCheckCodeBasis_repr_apply, coe_typeAZeroSumVec]; simp [Pi.single_apply]

private lemma singleParityCheckCodeBasis_repr_typeAZeroSumVec_of_lt {a b : Fin (m + 1)}
    (hlt : a < b) (i : Fin m) :
    (singleParityCheckCodeBasis R m).repr (typeAZeroSumVec R a b) i =
      ((if a ≤ i.castSucc ∧ i.castSucc < b then 1 else 0 : ℕ) : R) := by
  rw [singleParityCheckCodeBasis_repr_typeAZeroSumVec]
  by_cases ha : a ≤ i.castSucc <;> by_cases hb : i.castSucc < b
  · simp [ha, hb, not_le.mpr hb]
  · simp [ha, hb, not_lt.mp hb]
  · simp [ha, hb]
  · exact absurd (lt_of_lt_of_le hlt (not_lt.mp hb)) (lt_asymm (not_le.mp ha))

/-- The reversal linear involution `(θ x) a = -x (rev a)` on the sum-zero hyperplane. -/
def typeAZeroSumNegRevEquiv (m : ℕ) :
    singleParityCheckCode R (Fin (m + 1)) ≃ₗ[R] singleParityCheckCode R (Fin (m + 1)) :=
  LinearEquiv.ofInvolutive
    { toFun x := ⟨fun a ↦ -(x : Fin (m + 1) → R) a.rev, by
        rw [mem_singleParityCheckCode, sum_neg_distrib, neg_eq_zero]
        exact (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1))) _).trans
          ((mem_singleParityCheckCode R (Fin (m + 1))).mp x.property)⟩
      map_add' _ _ := Subtype.ext (funext fun _ ↦ by simp; ring)
      map_smul' _ _ := Subtype.ext (funext fun _ ↦ by simp) }
    fun _ ↦ Subtype.ext (funext fun _ ↦ by simp)

/-- Coordinate evaluation of `typeAZeroSumNegRevEquiv`. -/
@[simp] theorem coe_typeAZeroSumNegRevEquiv_apply (x : singleParityCheckCode R (Fin (m + 1)))
    (a : Fin (m + 1)) :
    (typeAZeroSumNegRevEquiv R m x : Fin (m + 1) → R) a = -(x : Fin (m + 1) → R) a.rev := (rfl)

/-- `typeAZeroSumNegRevEquiv` is an involution. -/
@[simp] theorem typeAZeroSumNegRevEquiv_apply_self (x : singleParityCheckCode R (Fin (m + 1))) :
    typeAZeroSumNegRevEquiv R m (typeAZeroSumNegRevEquiv R m x) = x := by ext; simp

/-- `typeAZeroSumNegRevEquiv` is its own inverse. -/
@[simp] theorem typeAZeroSumNegRevEquiv_symm (m : ℕ) :
    (typeAZeroSumNegRevEquiv R m).symm = typeAZeroSumNegRevEquiv R m :=
  LinearEquiv.ext fun _ ↦ by simp [LinearEquiv.symm_apply_eq]

/-- Reversal sends `eₐ - e_b` to `e_{rev b} - e_{rev a}`. -/
@[simp] theorem typeAZeroSumNegRevEquiv_vec (a b : Fin (m + 1)) :
    typeAZeroSumNegRevEquiv R m (typeAZeroSumVec R a b) = typeAZeroSumVec R b.rev a.rev := by
  ext k; simp only [coe_typeAZeroSumNegRevEquiv_apply, typeAZeroSumVec_apply, Fin.rev_eq_iff]; ring

/-- Reversal sends the `i`-th vector of `singleParityCheckCodeBasis` to the `(rev i)`-th. -/
@[simp] theorem typeAZeroSumNegRevEquiv_singleParityCheckCodeBasis (i : Fin m) :
    typeAZeroSumNegRevEquiv R m (singleParityCheckCodeBasis R m i) =
      singleParityCheckCodeBasis R m i.rev := by
  rw [singleParityCheckCodeBasis_eq_typeAZeroSumVec, typeAZeroSumNegRevEquiv_vec,
    singleParityCheckCodeBasis_eq_typeAZeroSumVec, Fin.rev_succ, Fin.rev_castSucc]

end CommRing

section Field

variable (K : Type*) [Field K] [CharZero K]

private def zeroSumDiffMap (m : ℕ) : singleParityCheckCode K (Fin (m + 1)) →ₗ[K] (Fin m → K) where
  toFun u k := (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ
  map_add' _ _ := funext fun _ ↦ by simp; ring
  map_smul' _ _ := funext fun _ ↦ by simp [mul_sub]

omit [CharZero K] in
private lemma zeroSumDiffMap_apply (m : ℕ) (u : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    zeroSumDiffMap K m u k =
      (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ := rfl

private lemma zeroSumDiffMap_injective (m : ℕ) : Injective (zeroSumDiffMap K m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]; intro u hu
  have hker : zeroSumDiffMap K m u = 0 := LinearMap.mem_ker.mp hu
  have hc (a : Fin (m + 1)) : (u : Fin (m + 1) → K) a = (u : Fin (m + 1) → K) 0 :=
    Fin.induction rfl (fun k ih ↦ by
      have hk := congrFun hker k
      rw [zeroSumDiffMap_apply, Pi.zero_apply, sub_eq_zero] at hk
      exact hk.symm.trans ih) a
  have hsum := (mem_singleParityCheckCode K (Fin (m + 1))).mp u.property
  simp_rw [hc, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hu0 := (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
  exact Subtype.ext (funext fun a ↦ (hc a).trans hu0)

private noncomputable def zeroSumWeightEquiv (m : ℕ) :
    singleParityCheckCode K (Fin (m + 1)) ≃ₗ[K] (Fin m → K) :=
  haveI := Module.Finite.of_basis (singleParityCheckCodeBasis K m)
  (zeroSumDiffMap K m).linearEquivOfInjective (zeroSumDiffMap_injective K m) <| by
    rw [Module.finrank_eq_card_basis (singleParityCheckCodeBasis K m), Module.finrank_fin_fun,
      Fintype.card_fin]

private lemma zeroSumWeightEquiv_apply (m : ℕ)
    (u : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    zeroSumWeightEquiv K m u k =
      (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ :=
  zeroSumDiffMap_apply K m u k

omit [CharZero K] in
private noncomputable def zeroSumCoweightEquiv (m : ℕ) :
    (Fin m → K) ≃ₗ[K] singleParityCheckCode K (Fin (m + 1)) :=
  (Finsupp.linearEquivFunOnFinite K K (Fin m)).symm.trans (singleParityCheckCodeBasis K m).repr.symm

omit [CharZero K] in
private lemma zeroSumCoweightEquiv_symm_apply (m : ℕ)
    (v : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    (zeroSumCoweightEquiv K m).symm v k = (singleParityCheckCodeBasis K m).repr v k := rfl

private lemma zeroSumWeightEquiv_dotProduct (m : ℕ)
    (u v : singleParityCheckCode K (Fin (m + 1))) :
    zeroSumWeightEquiv K m u ⬝ᵥ (zeroSumCoweightEquiv K m).symm v =
      (u : Fin (m + 1) → K) ⬝ᵥ (v : Fin (m + 1) → K) := by
  conv_rhs => rw [← (singleParityCheckCodeBasis K m).sum_repr v]
  rw [Submodule.coe_sum, dotProduct_sum, dotProduct]
  exact sum_congr rfl fun k _ ↦ by
    rw [SetLike.val_smul, dotProduct_smul, smul_eq_mul, coe_singleParityCheckCodeBasis_apply,
      dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one, mul_comm,
      zeroSumWeightEquiv_apply, zeroSumCoweightEquiv_symm_apply]

private lemma zeroSumWeightEquiv_vec (m : ℕ) (p : TypeAIndex m) :
    zeroSumWeightEquiv K m (typeAZeroSumVec K p.val.1 p.val.2) =
      (typeABaseChangeRootSystem K m).root (typeAIndexEquiv m p) := funext fun k ↦ by
  rw [zeroSumWeightEquiv_apply, root_typeABaseChangeRootSystem, piAlgebraMap_apply,
    root_typeAIndexEquiv]
  simp only [typeAZeroSumVec_apply, eq_comm, algebraMap_int_eq, eq_intCast, Int.cast_sub,
    apply_ite Int.cast, Int.cast_one, Int.cast_zero]; ring

private lemma zeroSumCoweightEquiv_coroot (m : ℕ) (p : TypeAIndex m) :
    zeroSumCoweightEquiv K m ((typeABaseChangeRootSystem K m).coroot (typeAIndexEquiv m p)) =
      typeAZeroSumVec K p.val.1 p.val.2 := by
  apply (zeroSumCoweightEquiv K m).symm.injective; rw [LinearEquiv.symm_apply_apply]; ext k
  rw [zeroSumCoweightEquiv_symm_apply, singleParityCheckCodeBasis_repr_typeAZeroSumVec,
    coroot_typeABaseChangeRootSystem, piAlgebraMap_apply, coroot_typeAIndexEquiv]
  simp [algebraMap_int_eq, apply_ite Int.cast]

/-- **The classical sum-zero root system of type `Aₘ` over `K`.** -/
noncomputable def typeAZeroSumRootPairing (m : ℕ) :
    RootPairing (TypeAIndex m) K
      (singleParityCheckCode K (Fin (m + 1))) (singleParityCheckCode K (Fin (m + 1))) :=
  (typeABaseChangeRootSystem K m).map (typeAIndexEquiv m).symm
    (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m)

private lemma typeAZeroSumRootPairing_eq_map (m : ℕ) :
    typeAZeroSumRootPairing K m =
      (typeABaseChangeRootSystem K m).map (typeAIndexEquiv m).symm
        (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m) := rfl

/-- `typeAZeroSumRootPairing K m` is a root system. -/
instance instIsRootSystemTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsRootSystem := by
  rw [typeAZeroSumRootPairing_eq_map]; infer_instance

/-- `typeAZeroSumRootPairing K m` is crystallographic. -/
instance instIsCrystallographicTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsCrystallographic := by
  rw [typeAZeroSumRootPairing_eq_map]; infer_instance

/-- `typeAZeroSumRootPairing K m` is reduced. -/
instance instIsReducedTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsReduced := by
  rw [typeAZeroSumRootPairing_eq_map]; infer_instance

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
    toLinearMap_typeABaseChangeRootSystem, zeroSumWeightEquiv_dotProduct]

/-- The root of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp] theorem root_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).root p = typeAZeroSumVec K p.val.1 p.val.2 := by
  rw [typeAZeroSumRootPairing, RootPairing.root_map, Equiv.symm_symm, ← zeroSumWeightEquiv_vec,
    LinearEquiv.symm_apply_apply]

/-- The coroot of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp] theorem coroot_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).coroot p = typeAZeroSumVec K p.val.1 p.val.2 := by
  rw [typeAZeroSumRootPairing, RootPairing.coroot_map, Equiv.symm_symm, zeroSumCoweightEquiv_coroot]

-- Not `@[simp]`: `RootPairing.coroot'` is an `abbrev`, so `simp` already proves this via
-- `LinearMap.flip_apply`, `coroot_typeAZeroSumRootPairing`, and
-- `toLinearMap_typeAZeroSumRootPairing` (`simpNF`).
/-- Evaluating the coroot functional at `p = (a, b)` on `u` computes `uₐ - u_b`. -/
theorem coroot'_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m)
    (u : singleParityCheckCode K (Fin (m + 1))) :
    (typeAZeroSumRootPairing K m).coroot' p u =
      (u : Fin (m + 1) → K) p.val.1 - (u : Fin (m + 1) → K) p.val.2 := by
  simp [RootPairing.coroot', dotProduct_sub]

/-- Reflection in `p` swaps the entries `p.1` and `p.2` inside any root pair `q`. -/
theorem reflectionPerm_typeAZeroSumRootPairing_val (m : ℕ) (p q : TypeAIndex m) :
    ((typeAZeroSumRootPairing K m).reflectionPerm p q).val =
      (Equiv.swap p.val.1 p.val.2 q.val.1, Equiv.swap p.val.1 p.val.2 q.val.2) := by
  rw [typeAZeroSumRootPairing, RootPairing.reflectionPerm_map, Equiv.symm_symm,
    reflectionPerm_typeABaseChangeRootSystem, typeAIndexEquiv_symm_reflectionPerm]

/-- Self-reflection in `p = (a, b)` reverses the pair to `(b, a)`. -/
@[simp] theorem reflectionPerm_self_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).reflectionPerm p p = ⟨(p.val.2, p.val.1), p.property.symm⟩ :=
  Subtype.ext (by simp [reflectionPerm_typeAZeroSumRootPairing_val])

-- `typeABaseChangeEquivZeroSum` has dependent target type `typeAZeroSumRootPairing K m`, so
-- `rw [typeAZeroSumRootPairing_eq_map]` cannot rewrite its codomain directly; the `equivMap`
-- simp lemmas apply directly to the definitional `equivMap` expression.
private lemma typeABaseChangeEquivZeroSum_weightEquiv (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).weightEquiv = (zeroSumWeightEquiv K m).symm :=
  RootPairing.weightEquiv_equivMap ..

private lemma typeABaseChangeEquivZeroSum_coweightMap_apply (m : ℕ)
    (v : singleParityCheckCode K (Fin (m + 1))) :
    (typeABaseChangeEquivZeroSum K m).coweightMap v = (zeroSumCoweightEquiv K m).symm v :=
  RootPairing.coweightMap_equivMap_apply ..

/-- The index equivalence of `typeABaseChangeEquivZeroSum K m` is `(typeAIndexEquiv m).symm`. -/
@[simp] theorem indexEquiv_typeABaseChangeEquivZeroSum (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).indexEquiv = (typeAIndexEquiv m).symm :=
  RootPairing.indexEquiv_equivMap ..

/-- The inverse weight map of `typeABaseChangeEquivZeroSum K m` takes adjacent differences. -/
@[simp] theorem weightEquiv_symm_typeABaseChangeEquivZeroSum_apply (m : ℕ)
    (u : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    (typeABaseChangeEquivZeroSum K m).weightEquiv.symm u k =
      (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ := by
  rw [typeABaseChangeEquivZeroSum_weightEquiv, LinearEquiv.symm_symm, zeroSumWeightEquiv_apply]

/-- The contravariant coweight map of `typeABaseChangeEquivZeroSum K m` takes coordinates in
`singleParityCheckCodeBasis K m`. -/
@[simp] theorem coweightMap_typeABaseChangeEquivZeroSum_apply (m : ℕ)
    (v : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    (typeABaseChangeEquivZeroSum K m).coweightMap v k =
      (singleParityCheckCodeBasis K m).repr v k := by
  rw [typeABaseChangeEquivZeroSum_coweightMap_apply, zeroSumCoweightEquiv_symm_apply]

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
  refine Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
    simp [typeAIndexEquiv_symm_typeASimpleIndex]

/-- The support of `typeAZeroSumBase K m` consists of the consecutive pairs `(i, i + 1)`. -/
theorem mem_support_typeAZeroSumBase_iff {m : ℕ} {p : TypeAIndex m} :
    p ∈ (typeAZeroSumBase K m).support ↔ ∃ i : Fin m, p = typeAZeroSumSimplePair m i := by
  classical
  rw [typeAZeroSumBase, RootPairing.Base.support_map_eq, mem_image]
  refine ⟨?_, fun ⟨i, hi⟩ ↦ ⟨typeASimpleIndex m i,
    (mem_support_typeABaseChangeBase_iff K m _).mpr ((typeASimpleIndex_val i).symm ▸ i.isLt),
    by rw [hi, indexEquiv_typeABaseChangeEquivZeroSum,
      typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair]⟩⟩
  rintro ⟨k, hk, rfl⟩; rw [mem_support_typeABaseChangeBase_iff] at hk
  exact ⟨⟨k, hk⟩, by
    rw [indexEquiv_typeABaseChangeEquivZeroSum,
      ← typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair]
    exact congrArg _ (Fin.ext (by simp))⟩

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
  simp only [typeAZeroSumSimplePair_val, typeAZeroSumVec_apply, CartanMatrix.A, Matrix.of_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, apply_ite (algebraMap ℤ K), map_ofNat, map_neg,
    map_one, map_zero]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

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
    refine ⟨fun i ↦ if q.val.1 ≤ i.castSucc ∧ i.castSucc < q.val.2 then 1 else 0, ?_⟩
    rw [root_typeAZeroSumRootPairing,
      ← (singleParityCheckCodeBasis K m).sum_repr (typeAZeroSumVec K q.val.1 q.val.2)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [singleParityCheckCodeBasis_repr_typeAZeroSumVec_of_lt K hlt i, Nat.cast_smul_eq_nsmul,
      root_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val,
      singleParityCheckCodeBasis_eq_typeAZeroSumVec]
  refine ⟨fun hpos ↦ (lt_or_gt_of_ne p.property).resolve_right fun hgt ↦ ?_, hfwd p⟩
  have hq : _ ∈ posRoots _ _ :=
    (mem_posRoots _ _ _).mpr (hfwd ⟨(p.val.2, p.val.1), p.property.symm⟩ hgt)
  rw [← reflectionPerm_self_typeAZeroSumRootPairing K m p] at hq
  exact reflectionPerm_self_notMem_posRoots _ _ ((mem_posRoots _ _ _).mpr hpos) hq

/-- **The diagram-reversal automorphism of `typeAZeroSumRootPairing K m`.** -/
noncomputable def typeAZeroSumRevAut (m : ℕ) : RootPairing.Aut (typeAZeroSumRootPairing K m) :=
  RootPairing.Equiv.mk' (typeAZeroSumRootPairing K m) (typeAZeroSumRootPairing K m)
    (typeAZeroSumNegRevEquiv K m) (finDistinctPairsRevSwap (m + 1)) fun _ ↦ by simp

/-- The weight map of `typeAZeroSumRevAut K m` is `typeAZeroSumNegRevEquiv K m`. -/
@[simp] theorem weightMap_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).weightMap = (typeAZeroSumNegRevEquiv K m).toLinearMap := (rfl)

/-- The index permutation of `typeAZeroSumRevAut K m` is `finDistinctPairsRevSwap (m + 1)`. -/
@[simp] theorem indexEquiv_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).indexEquiv = finDistinctPairsRevSwap (m + 1) := (rfl)

/-- The root orbit of `p : TypeAIndex m` under `typeAZeroSumRevAut K m` is
`{p, finDistinctPairsRevSwap (m + 1) p}`. -/
theorem orbitIndices_typeAZeroSumRevAut (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).orbitIndices (typeAZeroSumRevAut K m) p =
      {p, finDistinctPairsRevSwap (m + 1) p} := by
  rw [← indexEquiv_typeAZeroSumRevAut K m]
  exact RootPairing.orbitIndices_eq_pair_of_apply_apply (by
    rw [indexEquiv_typeAZeroSumRevAut]; exact finDistinctPairsRevSwap_finDistinctPairsRevSwap p)

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
  refine LinearEquiv.ext fun u ↦
    (typeABaseChangeEquivZeroSum K m).weightEquiv.symm.injective (funext fun k ↦ ?_)
  rw [RootPairing.Equiv.weightHom_apply, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.weightEquiv_autCongr_apply, LinearEquiv.symm_apply_apply]
  simp only [RootPairing.Equiv.weightEquiv_apply, weightMap_typeABaseChangeGraphAut_apply,
    weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe,
    weightEquiv_symm_typeABaseChangeEquivZeroSum_apply, coe_typeAZeroSumNegRevEquiv_apply,
    Fin.rev_castSucc, Fin.rev_succ]
  ring

end Field

end TauCeti.DynkinType
