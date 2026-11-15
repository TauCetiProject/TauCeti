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

In Bourbaki's classical coordinates, the root system of type `Aₘ` sits inside `(m + 1)`-space on
the sum-zero hyperplane `singleParityCheckCode K (Fin (m + 1))` of tuples `x : Fin (m + 1) → K`
satisfying `∑ a, x a = 0`, paired with itself by the ambient dot product. Its `m * (m + 1)` roots
and coroots are the differences `eₐ - e_b` (`a ≠ b`), its Bourbaki-numbered simple roots are
`αᵢ = eᵢ - eᵢ₊₁`, and the diagram reversal acts by `(θ x) a = -x (rev a)`, sending `eₐ - e_b` to
`e_{rev b} - e_{rev a}`.

This file develops the sum-zero basis `α₀, …, α_{m-1}` over an arbitrary commutative ring `R`,
constructs the sum-zero root system `typeAZeroSumRootPairing K m` over any characteristic-zero
field `K` by pushing forward the base change of `typeASimplyConnectedRootDatum m` along explicit
weight and coweight coordinate equivalences, equips it with its Bourbaki base
`typeAZeroSumBase K m` (whose positive roots are the pairs `(a, b)` with `a < b`), and intertwines
its reversal automorphism `typeAZeroSumRevAut K m` with the base-changed pinned graph automorphism
`typeAGraphAut m`.

## Main definitions

* `TauCeti.DynkinType.typeAZeroSumVec` and `TauCeti.DynkinType.typeAZeroSumSimpleRoot`: the
  difference vectors `eₐ - e_b` and simple roots `eᵢ - eᵢ₊₁` in
  `singleParityCheckCode R (Fin (m + 1))`.
* `TauCeti.DynkinType.typeAZeroSumBasis`: the simple-root `R`-basis of
  `singleParityCheckCode R (Fin (m + 1))`, with partial-sum coordinates.
* `TauCeti.DynkinType.typeAZeroSumRevEquiv`: the `R`-linear involution `x ↦ (a ↦ -x (rev a))` of
  the sum-zero hyperplane.
* `TauCeti.DynkinType.typeABaseChangeRootSystem`, `TauCeti.DynkinType.typeABaseChangeBase`, and
  `TauCeti.DynkinType.typeABaseChangeGraphAut`: the `K`-base-changed root system, Bourbaki base, and
  pinned graph automorphism of `typeASimplyConnectedRootDatum m`.
* `TauCeti.DynkinType.typeAZeroSumRootPairing` and `TauCeti.DynkinType.typeAZeroSumBase`: the
  classical sum-zero root system of type `Aₘ` over a characteristic-zero field `K`, together with
  its Bourbaki base.
* `TauCeti.DynkinType.typeAZeroSumSimplePair` and `TauCeti.DynkinType.typeAZeroSumSimpleEquiv`: the
  Bourbaki simple pairs `(i, i + 1)` and their bijection with `(typeAZeroSumBase K m).support`.
* `TauCeti.DynkinType.typeABaseChangeEquivZeroSum`: the based root-system equivalence from
  `typeABaseChangeRootSystem K m` to `typeAZeroSumRootPairing K m`.
* `TauCeti.DynkinType.typeAZeroSumRevAut`: the diagram-reversal automorphism of
  `typeAZeroSumRootPairing K m`.

## Main results

* `TauCeti.DynkinType.toLinearMap_typeAZeroSumRootPairing`,
  `TauCeti.DynkinType.root_typeAZeroSumRootPairing`, and
  `TauCeti.DynkinType.coroot_typeAZeroSumRootPairing`: the pairing is the ambient dot product and
  both roots and coroots are `eₐ - e_b`.
* `TauCeti.DynkinType.hasCartanType_typeAZeroSumBase`: `typeAZeroSumBase K m` has Cartan type
  `A m`.
* `TauCeti.DynkinType.isPos_typeAZeroSumBase_iff`: a pair `(a, b)` is positive for the Bourbaki
  base if and only if `a < b`.
* `TauCeti.DynkinType.autCongr_typeABaseChangeEquivZeroSum_graphAut`: the based equivalence
  intertwines the base-changed pinned graph automorphism with `typeAZeroSumRevAut K m`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate I.
-/

public section

namespace TauCeti.DynkinType

open Finset Function Submodule

/-! ### Sum-zero difference vectors, simple-root basis, and reversal over a commutative ring -/

section CommRing

variable (R : Type*) [CommRing R] {m : ℕ}

/-- The classical difference vector `eₐ - e_b` in the sum-zero hyperplane
`singleParityCheckCode R (Fin (m + 1))`. -/
def typeAZeroSumVec (a b : Fin (m + 1)) : singleParityCheckCode R (Fin (m + 1)) :=
  ⟨Pi.single a 1 - Pi.single b 1, by simp⟩

/-- Coercing `typeAZeroSumVec R a b` to the ambient tuple gives `Pi.single a 1 - Pi.single b 1`. -/
@[simp]
theorem coe_typeAZeroSumVec (a b : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) = Pi.single a 1 - Pi.single b 1 :=
  (rfl)

/-- Coordinate evaluation of `typeAZeroSumVec R a b`. -/
@[simp]
theorem typeAZeroSumVec_apply (a b k : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) k =
      (if k = a then 1 else 0) - (if k = b then 1 else 0) := by
  simp [Pi.single_apply, eq_comm]

/-- A difference vector with equal indices vanishes. -/
@[simp]
theorem typeAZeroSumVec_self (a : Fin (m + 1)) :
    typeAZeroSumVec R a a = 0 :=
  Subtype.ext (by simp)

/-- Negating `typeAZeroSumVec R a b` swaps its two indices. -/
@[simp]
theorem neg_typeAZeroSumVec (a b : Fin (m + 1)) :
    -typeAZeroSumVec R a b = typeAZeroSumVec R b a :=
  Subtype.ext (by simp)

/-- Ambient dot product of two difference vectors `eₐ - e_b` and `e_c - e_d`. -/
theorem typeAZeroSumVec_dotProduct (a b c d : Fin (m + 1)) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R c d : Fin (m + 1) → R) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) -
        ((if b = c then 1 else 0) - (if b = d then 1 else 0)) := by
  simp only [coe_typeAZeroSumVec, sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
    Pi.single_apply]
  ring

/-- Every classical root `eₐ - e_b` (`a ≠ b`) has squared length `2` for the ambient dot product. -/
theorem typeAZeroSumVec_dotProduct_self {a b : Fin (m + 1)} (h : a ≠ b) :
    (typeAZeroSumVec R a b : Fin (m + 1) → R) ⬝ᵥ (typeAZeroSumVec R a b : Fin (m + 1) → R) = 2 := by
  rw [typeAZeroSumVec_dotProduct]
  simp only [ite_true, h, h.symm, ite_false]
  norm_num

/-- The `i`-th Bourbaki simple root `αᵢ = eᵢ - eᵢ₊₁` in `singleParityCheckCode R (Fin (m + 1))`. -/
def typeAZeroSumSimpleRoot (m : ℕ) (i : Fin m) : singleParityCheckCode R (Fin (m + 1)) :=
  typeAZeroSumVec R i.castSucc i.succ

/-- Unfolding equation for `typeAZeroSumSimpleRoot`. -/
theorem typeAZeroSumSimpleRoot_def (m : ℕ) (i : Fin m) :
    typeAZeroSumSimpleRoot R m i = typeAZeroSumVec R i.castSucc i.succ :=
  (rfl)

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
      ∑ i ∈ s, (f i : Fin (m + 1) → R) a := by
  simp

/-- Linear equivalence identifying `singleParityCheckCode R (Fin (m + 1))` with `Fin m → R` via
the lower partial sums `x ↦ (∑_{j ≤ i} xⱼ)ᵢ`. -/
private def typeAZeroSumCoordEquiv (m : ℕ) :
    singleParityCheckCode R (Fin (m + 1)) ≃ₗ[R] (Fin m → R) where
  toFun x i := ∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j
  map_add' x y := by
    ext i
    simp [sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [mul_sum]
  invFun y := ∑ i : Fin m, y i • typeAZeroSumSimpleRoot R m i
  right_inv y := by
    ext k
    simp_rw [coe_sum_singleParityCheckCode]
    rw [sum_comm]
    simp_rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum,
      sum_Iic_typeAZeroSumSimpleRoot R]
    simp
  left_inv x := by
    set z : singleParityCheckCode R (Fin (m + 1)) :=
      (∑ i : Fin m, (∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j) •
        typeAZeroSumSimpleRoot R m i) - x
    suffices hz : z = 0 from sub_eq_zero.mp hz
    apply Subtype.ext
    refine eq_zero_of_forall_sum_Iic_eq_zero fun a ↦ ?_
    refine Fin.lastCases ?_ (fun k ↦ ?_) a
    · have hl : Iic (Fin.last m) = univ := eq_univ_of_forall fun j ↦ mem_Iic.mpr (Fin.le_last j)
      rw [hl]
      exact (mem_singleParityCheckCode R (Fin (m + 1))).mp z.2
    · simp only [z, AddSubgroupClass.coe_sub, Pi.sub_apply, sum_sub_distrib, sub_eq_zero]
      simp_rw [coe_sum_singleParityCheckCode]
      rw [sum_comm]
      simp_rw [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum,
        sum_Iic_typeAZeroSumSimpleRoot R]
      simp

/-- The Bourbaki simple roots `αᵢ = eᵢ - eᵢ₊₁` form an `R`-basis of the sum-zero hyperplane
`singleParityCheckCode R (Fin (m + 1))`. -/
noncomputable def typeAZeroSumBasis (m : ℕ) :
    Module.Basis (Fin m) R (singleParityCheckCode R (Fin (m + 1))) :=
  Module.Basis.ofRepr
    ((typeAZeroSumCoordEquiv R m).trans (Finsupp.linearEquivFunOnFinite R R (Fin m)).symm)

/-- The `i`-th vector of `typeAZeroSumBasis` is `typeAZeroSumSimpleRoot R m i`. -/
@[simp]
theorem typeAZeroSumBasis_apply (m : ℕ) (i : Fin m) :
    typeAZeroSumBasis R m i = typeAZeroSumSimpleRoot R m i := by
  rw [typeAZeroSumBasis, Module.Basis.coe_ofRepr]
  dsimp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  -- Evaluate `(typeAZeroSumCoordEquiv R m).symm` on `Finsupp.single i 1` as a finite sum.
  change ∑ j : Fin m, (Finsupp.single i (1 : R) : Fin m → R) j • typeAZeroSumSimpleRoot R m j = _
  simp [Finsupp.single_apply]

/-- The `i`-th coordinate of `x` in `typeAZeroSumBasis` is the partial sum `∑_{j ≤ i} xⱼ`. -/
@[simp]
theorem typeAZeroSumBasis_repr_apply (m : ℕ)
    (x : singleParityCheckCode R (Fin (m + 1))) (i : Fin m) :
    (typeAZeroSumBasis R m).repr x i = ∑ j ∈ Iic i.castSucc, (x : Fin (m + 1) → R) j :=
  (rfl)

/-- Expansion of any difference vector `eₐ - e_b` in the simple-root basis: the `i`-th coordinate
is `[a ≤ i] - [b ≤ i]`. -/
theorem typeAZeroSumBasis_repr_vec (a b : Fin (m + 1)) (i : Fin m) :
    (typeAZeroSumBasis R m).repr (typeAZeroSumVec R a b) i =
      (if a ≤ i.castSucc then 1 else 0) - (if b ≤ i.castSucc then 1 else 0) := by
  rw [typeAZeroSumBasis_repr_apply, coe_typeAZeroSumVec]
  simp [Pi.single_apply]

/-- The reversal linear involution `(θ x) a = -x (rev a)` on the sum-zero hyperplane. -/
def typeAZeroSumRevEquiv (m : ℕ) :
    singleParityCheckCode R (Fin (m + 1)) ≃ₗ[R] singleParityCheckCode R (Fin (m + 1)) :=
  LinearEquiv.ofInvolutive
    { toFun x := ⟨fun a ↦ -(x : Fin (m + 1) → R) a.rev, by
        rw [mem_singleParityCheckCode, sum_neg_distrib, neg_eq_zero]
        exact (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1))) _).trans
          ((mem_singleParityCheckCode R (Fin (m + 1))).mp x.2)⟩
      map_add' x y := Subtype.ext (funext fun a ↦ by simp; ring)
      map_smul' c x := Subtype.ext (funext fun a ↦ by simp) }
    fun x ↦ Subtype.ext (funext fun a ↦ by simp)

/-- Coordinate evaluation of `typeAZeroSumRevEquiv`. -/
@[simp]
theorem coe_typeAZeroSumRevEquiv_apply (x : singleParityCheckCode R (Fin (m + 1)))
    (a : Fin (m + 1)) :
    (typeAZeroSumRevEquiv R m x : Fin (m + 1) → R) a = -(x : Fin (m + 1) → R) a.rev :=
  (rfl)

/-- `typeAZeroSumRevEquiv` is an involution. -/
@[simp]
theorem typeAZeroSumRevEquiv_apply_self (x : singleParityCheckCode R (Fin (m + 1))) :
    typeAZeroSumRevEquiv R m (typeAZeroSumRevEquiv R m x) = x := by
  ext a
  simp

/-- `typeAZeroSumRevEquiv` is its own inverse. -/
@[simp]
theorem typeAZeroSumRevEquiv_symm (m : ℕ) :
    (typeAZeroSumRevEquiv R m).symm = typeAZeroSumRevEquiv R m :=
  LinearEquiv.ext fun x ↦
    (typeAZeroSumRevEquiv R m).symm_apply_eq.mpr (typeAZeroSumRevEquiv_apply_self R x).symm

/-- Reversal sends `eₐ - e_b` to `e_{rev b} - e_{rev a}`. -/
@[simp]
theorem typeAZeroSumRevEquiv_vec (a b : Fin (m + 1)) :
    typeAZeroSumRevEquiv R m (typeAZeroSumVec R a b) = typeAZeroSumVec R b.rev a.rev := by
  ext k
  simp only [coe_typeAZeroSumRevEquiv_apply, typeAZeroSumVec_apply, Fin.rev_eq_iff]
  ring

/-- Reversal sends the `i`-th Bourbaki simple root to the `(rev i)`-th Bourbaki simple root. -/
@[simp]
theorem typeAZeroSumRevEquiv_simpleRoot (i : Fin m) :
    typeAZeroSumRevEquiv R m (typeAZeroSumSimpleRoot R m i) =
      typeAZeroSumSimpleRoot R m i.rev := by
  rw [typeAZeroSumSimpleRoot_def, typeAZeroSumRevEquiv_vec, typeAZeroSumSimpleRoot_def,
    Fin.rev_succ, Fin.rev_castSucc]

end CommRing

/-! ### Base-changed type-`A` system and the classical sum-zero root system over a field -/

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- The root system of type `Aₘ` on `Fin m → K` obtained by entrywise base change from
`typeASimplyConnectedRootDatum m`. -/
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
    (typeABaseChangeRootSystem K m).IsReduced := by
  let _ : (typeASimplyConnectedRootDatum m).IsReduced :=
    RootPairing.isReduced_of_pairing_comm _ pairing_typeASimplyConnectedRootDatum_comm
  exact isReduced_rootPairingBaseChange K _ _

/-- Over a characteristic-zero field, the roots and coroots of `typeABaseChangeRootSystem K m`
span `Fin m → K`. -/
instance instIsRootSystemTypeABaseChangeRootSystem (m : ℕ) :
    (typeABaseChangeRootSystem K m).IsRootSystem where
  span_root_eq_top := by
    have hli : LinearIndependent K fun i : (typeABaseChangeBase K m).support ↦
        (typeABaseChangeRootSystem K m).root i := (typeABaseChangeBase K m).linearIndepOn_root
    have hcard : Fintype.card (typeABaseChangeBase K m).support =
        Module.finrank K (Fin m → K) := by
      rw [Fintype.card_coe, Module.finrank_fin_fun, typeABaseChangeBase,
        support_rootPairingBaseChangeBase,
        (hasCartanType_typeASimplyConnectedRootDatum m).card_support, DynkinType.rank_A]
    refine top_le_iff.mp ?_
    rw [← hli.span_eq_top_of_card_eq_finrank' hcard]
    exact Submodule.span_mono
      (by rintro - ⟨i, rfl⟩; exact Set.mem_range_self (i : Fin (m * (m + 1))))
  span_coroot_eq_top :=
    span_range_coroot_rootPairingBaseChange_eq_top K _ _
      (corootSpan_typeASimplyConnectedRootDatum_eq_top m)

/-- `typeABaseChangeBase K m` has Cartan type `A m`. -/
theorem hasCartanType_typeABaseChangeBase (m : ℕ) :
    HasCartanType (typeABaseChangeRootSystem K m) (typeABaseChangeBase K m) (.A m) := by
  obtain ⟨e, he⟩ := (hasCartanType_iff _ _).mp (hasCartanType_typeASimplyConnectedRootDatum m)
  refine (hasCartanType_iff _ _).mpr
    ⟨(supportEquivRootPairingBaseChangeBase K _ _ _).trans e, fun i j ↦ ?_⟩
  exact (cartanMatrix_rootPairingBaseChangeBase K _ _ _ i j).trans (he _ _)

/-- The graph automorphism of `typeABaseChangeRootSystem K m`, reversing `Fin m → K` on both
weight and coweight spaces. -/
noncomputable def typeABaseChangeGraphAut (m : ℕ) :
    RootPairing.Aut (typeABaseChangeRootSystem K m) :=
  RootPairing.Equiv.mk' (typeABaseChangeRootSystem K m) (typeABaseChangeRootSystem K m)
    (LinearEquiv.funCongrLeft K K (Fin.revPerm : Equiv.Perm (Fin m)))
    (typeAGraphAut m).indexEquiv
    fun i ↦ by
      ext k
      have h := congrFun (RootPairing.Hom.root_weightMap_apply
        (typeASimplyConnectedRootDatum m) (typeASimplyConnectedRootDatum m) i
        (typeAGraphAut m).toHom) k
      rw [weightMap_typeAGraphAut_apply] at h
      simpa [typeABaseChangeRootSystem, piAlgebraMap_apply] using congrArg (algebraMap ℤ K) h

/-- The index permutation of `typeABaseChangeGraphAut K m` agrees with `typeAGraphAut m`. -/
@[simp]
theorem indexEquiv_typeABaseChangeGraphAut (m : ℕ) :
    (typeABaseChangeGraphAut K m).indexEquiv = (typeAGraphAut m).indexEquiv :=
  (rfl)

/-- `typeABaseChangeGraphAut K m` reverses weight coordinates. -/
@[simp]
theorem weightMap_typeABaseChangeGraphAut_apply (m : ℕ) (x : Fin m → K) (k : Fin m) :
    (typeABaseChangeGraphAut K m).weightMap x k = x k.rev :=
  (rfl)

/-- Linear map sending a sum-zero vector `u` to its successive differences `(uᵢ - uᵢ₊₁)ᵢ`, its
pairings against the simple coroots. -/
private def zeroSumDiffMap (m : ℕ) :
    singleParityCheckCode K (Fin (m + 1)) →ₗ[K] (Fin m → K) where
  toFun u k := (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ
  map_add' u v := funext fun k ↦ by simp; ring
  map_smul' c u := funext fun k ↦ by simp [mul_sub]

private lemma zeroSumDiffMap_injective (m : ℕ) : Injective (zeroSumDiffMap K m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  have hstep : ∀ k : Fin m, (u : Fin (m + 1) → K) k.castSucc = (u : Fin (m + 1) → K) k.succ :=
    fun k ↦ sub_eq_zero.mp (congrFun hu k)
  have hconst : ∀ a : Fin (m + 1), (u : Fin (m + 1) → K) a = (u : Fin (m + 1) → K) 0 := by
    intro a
    refine Fin.induction rfl (fun k ih ↦ ?_) a
    exact (hstep k).symm.trans ih
  have hsum : ∑ a : Fin (m + 1), (u : Fin (m + 1) → K) a = 0 :=
    (mem_singleParityCheckCode K (Fin (m + 1))).mp u.2
  simp_rw [hconst] at hsum
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hu0 : (u : Fin (m + 1) → K) 0 = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
  exact Subtype.ext (funext fun a ↦ (hconst a).trans hu0)

/-- The weight-coordinate equivalence `singleParityCheckCode K (Fin (m + 1)) ≃ₗ[K] (Fin m → K)`
sending `u` to `(uᵢ - uᵢ₊₁)ᵢ`. -/
private noncomputable def zeroSumWeightEquiv (m : ℕ) :
    singleParityCheckCode K (Fin (m + 1)) ≃ₗ[K] (Fin m → K) :=
  haveI : FiniteDimensional K (singleParityCheckCode K (Fin (m + 1))) :=
    Module.Finite.of_basis (typeAZeroSumBasis K m)
  (zeroSumDiffMap K m).linearEquivOfInjective (zeroSumDiffMap_injective K m) <| by
    rw [Module.finrank_eq_card_basis (typeAZeroSumBasis K m), Module.finrank_fin_fun,
      Fintype.card_fin]

private lemma zeroSumWeightEquiv_apply (m : ℕ)
    (u : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    zeroSumWeightEquiv K m u k =
      (u : Fin (m + 1) → K) k.castSucc - (u : Fin (m + 1) → K) k.succ :=
  rfl

omit [CharZero K] in
/-- The coweight-coordinate equivalence `(Fin m → K) ≃ₗ[K] singleParityCheckCode K (Fin (m + 1))`
expanding simple-coroot coordinates along `typeAZeroSumBasis K m`. -/
private noncomputable def zeroSumCoweightEquiv (m : ℕ) :
    (Fin m → K) ≃ₗ[K] singleParityCheckCode K (Fin (m + 1)) :=
  (Finsupp.linearEquivFunOnFinite K K (Fin m)).symm.trans (typeAZeroSumBasis K m).repr.symm

omit [CharZero K] in
private lemma zeroSumCoweightEquiv_symm_apply (m : ℕ)
    (v : singleParityCheckCode K (Fin (m + 1))) (k : Fin m) :
    (zeroSumCoweightEquiv K m).symm v k = ∑ j ∈ Iic k.castSucc, (v : Fin (m + 1) → K) j :=
  rfl

private lemma zeroSumWeightEquiv_dotProduct (m : ℕ)
    (u v : singleParityCheckCode K (Fin (m + 1))) :
    zeroSumWeightEquiv K m u ⬝ᵥ (zeroSumCoweightEquiv K m).symm v =
      (u : Fin (m + 1) → K) ⬝ᵥ (v : Fin (m + 1) → K) := by
  have hv : (v : Fin (m + 1) → K) =
      ∑ k : Fin m, ((zeroSumCoweightEquiv K m).symm v k) •
        (typeAZeroSumSimpleRoot K m k : Fin (m + 1) → K) := by
    have hv' := ((typeAZeroSumBasis K m).sum_repr v).symm
    ext a
    rw [congrArg (fun w : singleParityCheckCode K (Fin (m + 1)) ↦ (w : Fin (m + 1) → K) a) hv',
      coe_sum_singleParityCheckCode, Finset.sum_apply]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [typeAZeroSumBasis_apply]
    rfl
  rw [hv, dotProduct_sum]
  rw [dotProduct]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul, typeAZeroSumSimpleRoot_def, coe_typeAZeroSumVec,
    dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one,
    zeroSumWeightEquiv_apply, mul_comm]

private lemma zeroSumWeightEquiv_vec (m : ℕ) (p : TypeAIndex m) :
    zeroSumWeightEquiv K m (typeAZeroSumVec K p.val.1 p.val.2) =
      (typeABaseChangeRootSystem K m).root (typeAIndexEquiv m p) := by
  ext k
  rw [zeroSumWeightEquiv_apply, typeABaseChangeRootSystem, root_rootPairingBaseChange,
    piAlgebraMap_apply, root_typeAIndexEquiv]
  simp only [typeAZeroSumVec_apply, eq_comm, algebraMap_int_eq, eq_intCast, Int.cast_sub,
    apply_ite Int.cast, Int.cast_one, Int.cast_zero]
  ring

private lemma zeroSumCoweightEquiv_coroot (m : ℕ) (p : TypeAIndex m) :
    zeroSumCoweightEquiv K m ((typeABaseChangeRootSystem K m).coroot (typeAIndexEquiv m p)) =
      typeAZeroSumVec K p.val.1 p.val.2 := by
  apply (zeroSumCoweightEquiv K m).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext k
  rw [zeroSumCoweightEquiv_symm_apply, ← typeAZeroSumBasis_repr_apply, typeAZeroSumBasis_repr_vec,
    typeABaseChangeRootSystem, coroot_rootPairingBaseChange, piAlgebraMap_apply,
    coroot_typeAIndexEquiv]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_sub, apply_ite Int.cast, Int.cast_one,
    Int.cast_zero]

/-- **The classical sum-zero root system of type `Aₘ` over `K`.** Its weight and coweight spaces
are both the sum-zero hyperplane `singleParityCheckCode K (Fin (m + 1))`, paired by the ambient
dot product, and its roots and coroots indexed by `p : TypeAIndex m` are `e_{p.1} - e_{p.2}`. -/
noncomputable def typeAZeroSumRootPairing (m : ℕ) :
    RootPairing (TypeAIndex m) K
      (singleParityCheckCode K (Fin (m + 1))) (singleParityCheckCode K (Fin (m + 1))) :=
  (typeABaseChangeRootSystem K m).map (typeAIndexEquiv m).symm
    (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m)

/-- `typeAZeroSumRootPairing K m` is a root system. -/
instance instIsRootSystemTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsRootSystem := by
  delta typeAZeroSumRootPairing
  infer_instance

/-- `typeAZeroSumRootPairing K m` is crystallographic. -/
instance instIsCrystallographicTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsCrystallographic := by
  delta typeAZeroSumRootPairing
  infer_instance

/-- `typeAZeroSumRootPairing K m` is reduced. -/
instance instIsReducedTypeAZeroSumRootPairing (m : ℕ) :
    (typeAZeroSumRootPairing K m).IsReduced := by
  delta typeAZeroSumRootPairing
  infer_instance

/-- The canonical root-system equivalence from `typeABaseChangeRootSystem K m` to
`typeAZeroSumRootPairing K m`. -/
noncomputable def typeABaseChangeEquivZeroSum (m : ℕ) :
    (typeABaseChangeRootSystem K m).Equiv (typeAZeroSumRootPairing K m) :=
  (typeABaseChangeRootSystem K m).equivMap (typeAIndexEquiv m).symm
    (zeroSumWeightEquiv K m).symm (zeroSumCoweightEquiv K m)

/-- The Bourbaki-numbered base of `typeAZeroSumRootPairing K m`, transported from
`typeABaseChangeBase K m`. -/
noncomputable def typeAZeroSumBase (m : ℕ) : (typeAZeroSumRootPairing K m).Base :=
  (typeABaseChangeBase K m).map (typeABaseChangeEquivZeroSum K m)

/-- The bilinear pairing of `typeAZeroSumRootPairing K m` is the ambient dot product. -/
@[simp]
theorem toLinearMap_typeAZeroSumRootPairing (m : ℕ)
    (u v : singleParityCheckCode K (Fin (m + 1))) :
    (typeAZeroSumRootPairing K m).toLinearMap u v =
      (u : Fin (m + 1) → K) ⬝ᵥ (v : Fin (m + 1) → K) := by
  rw [typeAZeroSumRootPairing, RootPairing.toLinearMap_map, LinearEquiv.symm_symm,
    typeABaseChangeRootSystem, toLinearMap_rootPairingBaseChange, zeroSumWeightEquiv_dotProduct]

/-- The root of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp]
theorem root_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).root p = typeAZeroSumVec K p.val.1 p.val.2 := by
  rw [typeAZeroSumRootPairing, RootPairing.root_map, Equiv.symm_symm, ← zeroSumWeightEquiv_vec,
    LinearEquiv.symm_apply_apply]

/-- The coroot of `typeAZeroSumRootPairing K m` at `p = (a, b)` is `eₐ - e_b`. -/
@[simp]
theorem coroot_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
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
@[simp]
theorem reflectionPerm_self_typeAZeroSumRootPairing (m : ℕ) (p : TypeAIndex m) :
    (typeAZeroSumRootPairing K m).reflectionPerm p p = ⟨(p.val.2, p.val.1), p.2.symm⟩ := by
  apply Subtype.ext
  rw [reflectionPerm_typeAZeroSumRootPairing_val, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The index equivalence of `typeABaseChangeEquivZeroSum K m` is `(typeAIndexEquiv m).symm`. -/
@[simp]
theorem indexEquiv_typeABaseChangeEquivZeroSum (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).indexEquiv = (typeAIndexEquiv m).symm := by
  rw [typeABaseChangeEquivZeroSum, RootPairing.indexEquiv_equivMap]

/-- The `i`-th consecutive pair `(i, i + 1)` indexing the `i`-th Bourbaki simple root of
`typeAZeroSumRootPairing K m`. -/
def typeAZeroSumSimplePair (m : ℕ) (i : Fin m) : TypeAIndex m :=
  ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ.ne⟩

/-- Unfolding equation for the underlying pair of `typeAZeroSumSimplePair`. -/
@[simp]
theorem typeAZeroSumSimplePair_val (m : ℕ) (i : Fin m) :
    (typeAZeroSumSimplePair m i).val = (i.castSucc, i.succ) :=
  (rfl)

/-- `typeAZeroSumSimplePair m` is injective. -/
theorem typeAZeroSumSimplePair_injective (m : ℕ) : Injective (typeAZeroSumSimplePair m) := by
  intro i j hij
  exact Fin.castSucc_injective m (congrArg (fun p : TypeAIndex m ↦ p.val.1) hij)

/-- `(typeAIndexEquiv m).symm` maps `typeASimpleIndex m i` to `typeAZeroSumSimplePair m i`. -/
theorem typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair (m : ℕ) (i : Fin m) :
    (typeAIndexEquiv m).symm (typeASimpleIndex m i) = typeAZeroSumSimplePair m i := by
  rw [typeAIndexEquiv_symm_typeASimpleIndex]
  rfl

/-- The support of `typeAZeroSumBase K m` consists of the consecutive pairs `(i, i + 1)`. -/
theorem mem_support_typeAZeroSumBase_iff {m : ℕ} {p : TypeAIndex m} :
    p ∈ (typeAZeroSumBase K m).support ↔ ∃ i : Fin m, p = typeAZeroSumSimplePair m i := by
  classical
  rw [typeAZeroSumBase, RootPairing.Base.support_map_eq, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [typeABaseChangeBase, support_rootPairingBaseChangeBase,
      mem_typeASimplyConnectedBase_support] at hk
    refine ⟨⟨k, hk⟩, ?_⟩
    have hk' : k = typeASimpleIndex m ⟨k, hk⟩ := Fin.ext (by simp)
    rw [indexEquiv_typeABaseChangeEquivZeroSum]
    conv_lhs => rw [hk']
    exact typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair m ⟨k, hk⟩
  · rintro ⟨i, rfl⟩
    refine ⟨typeASimpleIndex m i, ?_, ?_⟩
    · rw [typeABaseChangeBase, support_rootPairingBaseChangeBase,
        mem_typeASimplyConnectedBase_support, typeASimpleIndex_val]
      exact i.isLt
    · rw [indexEquiv_typeABaseChangeEquivZeroSum,
        typeAIndexEquiv_symm_typeASimpleIndex_eq_simplePair]

/-- `typeAZeroSumBase K m` has Cartan type `A m`. -/
theorem hasCartanType_typeAZeroSumBase (m : ℕ) :
    HasCartanType (typeAZeroSumRootPairing K m) (typeAZeroSumBase K m) (.A m) :=
  (hasCartanType_typeABaseChangeBase K m).map (typeABaseChangeEquivZeroSum K m)

/-- Bourbaki node equivalence `Fin m ≃ (typeAZeroSumBase K m).support` sending `i` to
`typeAZeroSumSimplePair m i`. -/
noncomputable def typeAZeroSumSimpleEquiv (m : ℕ) :
    Fin m ≃ (typeAZeroSumBase K m).support :=
  Equiv.ofBijective
    (fun i ↦ ⟨typeAZeroSumSimplePair m i, (mem_support_typeAZeroSumBase_iff K).mpr ⟨i, rfl⟩⟩)
    ⟨fun i j h ↦ typeAZeroSumSimplePair_injective m (congrArg Subtype.val h),
      fun ⟨p, hp⟩ ↦ by
        obtain ⟨i, rfl⟩ := (mem_support_typeAZeroSumBase_iff K).mp hp
        exact ⟨i, rfl⟩⟩

/-- Coercing `typeAZeroSumSimpleEquiv K m i` gives `typeAZeroSumSimplePair m i`. -/
@[simp]
theorem coe_typeAZeroSumSimpleEquiv (m : ℕ) (i : Fin m) :
    (typeAZeroSumSimpleEquiv K m i : TypeAIndex m) = typeAZeroSumSimplePair m i :=
  (rfl)

/-- Read through `typeAZeroSumSimpleEquiv K m`, the Cartan matrix of `typeAZeroSumBase K m` is
`CartanMatrix.A m`. -/
@[simp]
theorem cartanMatrix_typeAZeroSumBase (m : ℕ) (i j : Fin m) :
    (typeAZeroSumBase K m).cartanMatrix (typeAZeroSumSimpleEquiv K m i)
      (typeAZeroSumSimpleEquiv K m j) = CartanMatrix.A m i j := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    RootPairing.algebraMap_pairingIn, ← RootPairing.root_coroot'_eq_pairing,
    coe_typeAZeroSumSimpleEquiv, coe_typeAZeroSumSimpleEquiv, coroot'_typeAZeroSumRootPairing,
    root_typeAZeroSumRootPairing]
  have hcast : ∀ a b c d : Fin (m + 1),
      (typeAZeroSumVec K a b : Fin (m + 1) → K) c -
        (typeAZeroSumVec K a b : Fin (m + 1) → K) d =
      algebraMap ℤ K ((typeAZeroSumVec ℤ a b : Fin (m + 1) → ℤ) c -
        (typeAZeroSumVec ℤ a b : Fin (m + 1) → ℤ) d) := by
    intro a b c d
    simp [typeAZeroSumVec_apply, algebraMap_int_eq, apply_ite Int.cast]
  rw [hcast]
  congr 1
  simp only [typeAZeroSumSimplePair_val, typeAZeroSumVec_apply, CartanMatrix.A, Matrix.of_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- A root pair `p = (a, b)` is positive for `typeAZeroSumBase K m` if and only if `a < b`. -/
theorem isPos_typeAZeroSumBase_iff {m : ℕ} {p : TypeAIndex m} :
    (typeAZeroSumBase K m).IsPos p ↔ p.val.1 < p.val.2 := by
  have hbij : Set.BijOn (typeAZeroSumSimplePair m) Set.univ
      ((typeAZeroSumBase K m).support : Set (TypeAIndex m)) :=
    ⟨fun i _ ↦ (mem_support_typeAZeroSumBase_iff K).mpr ⟨i, rfl⟩,
      fun i _ j _ h ↦ typeAZeroSumSimplePair_injective m h,
      fun r hr ↦ by
        obtain ⟨i, rfl⟩ := (mem_support_typeAZeroSumBase_iff K).mp hr
        exact ⟨i, trivial, rfl⟩⟩
  have hfwd : ∀ q : TypeAIndex m, q.val.1 < q.val.2 → (typeAZeroSumBase K m).IsPos q := by
    intro q hlt
    rw [← mem_posRoots, mem_posRoots_iff_root_mem_posRootCone,
      mem_posRootCone_iff_exists_nat_of_bijOn (typeAZeroSumRootPairing K m)
        (typeAZeroSumBase K m) hbij]
    refine ⟨fun i ↦ if q.val.1 ≤ i.castSucc ∧ i.castSucc < q.val.2 then 1 else 0, ?_⟩
    apply (typeAZeroSumBasis K m).repr.injective
    ext k
    rw [root_typeAZeroSumRootPairing, typeAZeroSumBasis_repr_vec, map_sum,
      ← Finsupp.lapply_apply (R := K), map_sum]
    simp_rw [Finsupp.lapply_apply, map_nsmul, Finsupp.coe_smul, Pi.smul_apply,
      root_typeAZeroSumRootPairing, typeAZeroSumSimplePair_val, ← typeAZeroSumSimpleRoot_def,
      ← typeAZeroSumBasis_apply, Module.Basis.repr_self_apply]
    rw [Finset.sum_eq_single k (fun i _ hik ↦ by rw [ite_eq_right hik, nsmul_zero]) (by simp),
      ite_eq_left rfl]
    simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc]
    have : (q.val.1 : ℕ) < (q.val.2 : ℕ) := hlt
    split_ifs <;> first | omega | norm_num
  refine ⟨fun hpos ↦ ?_, hfwd p⟩
  rcases lt_or_gt_of_ne p.2 with hlt | hgt
  · exact hlt
  · exfalso
    have hq : (typeAZeroSumBase K m).IsPos ⟨(p.val.2, p.val.1), p.2.symm⟩ := hfwd _ hgt
    rw [← reflectionPerm_self_typeAZeroSumRootPairing K m p, ← mem_posRoots] at hq
    exact reflectionPerm_self_notMem_posRoots (typeAZeroSumRootPairing K m) (typeAZeroSumBase K m)
      ((mem_posRoots _ _ _).mpr hpos) hq

/-- **The diagram-reversal automorphism of `typeAZeroSumRootPairing K m`.** It acts on weight
space by `typeAZeroSumRevEquiv K m` (`(θ x) a = -x (rev a)`) and permutes root pairs by
`finDistinctPairsRevSwap (m + 1)`. -/
noncomputable def typeAZeroSumRevAut (m : ℕ) :
    RootPairing.Aut (typeAZeroSumRootPairing K m) :=
  RootPairing.Equiv.mk' (typeAZeroSumRootPairing K m) (typeAZeroSumRootPairing K m)
    (typeAZeroSumRevEquiv K m) (finDistinctPairsRevSwap (m + 1)) fun p ↦ by simp

/-- The weight map of `typeAZeroSumRevAut K m` is `typeAZeroSumRevEquiv K m`. -/
@[simp]
theorem weightMap_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).weightMap = (typeAZeroSumRevEquiv K m).toLinearMap :=
  (rfl)

/-- The index permutation of `typeAZeroSumRevAut K m` is `finDistinctPairsRevSwap (m + 1)`. -/
@[simp]
theorem indexEquiv_typeAZeroSumRevAut (m : ℕ) :
    (typeAZeroSumRevAut K m).indexEquiv = finDistinctPairsRevSwap (m + 1) :=
  (rfl)

/-- `typeAZeroSumRevAut K m` reverses the Bourbaki-numbered simple pairs. -/
theorem indexEquiv_typeAZeroSumRevAut_simplePair (m : ℕ) (i : Fin m) :
    (typeAZeroSumRevAut K m).indexEquiv (typeAZeroSumSimplePair m i) =
      typeAZeroSumSimplePair m i.rev := by
  apply Subtype.ext
  rw [indexEquiv_typeAZeroSumRevAut, finDistinctPairsRevSwap_apply_val, typeAZeroSumSimplePair_val,
    typeAZeroSumSimplePair_val, Fin.rev_succ, Fin.rev_castSucc]

/-- `typeAZeroSumRevAut K m` preserves the support of `typeAZeroSumBase K m`. -/
theorem indexEquiv_typeAZeroSumRevAut_mem_support {m : ℕ} {p : TypeAIndex m}
    (hp : p ∈ (typeAZeroSumBase K m).support) :
    (typeAZeroSumRevAut K m).indexEquiv p ∈ (typeAZeroSumBase K m).support := by
  obtain ⟨i, rfl⟩ := (mem_support_typeAZeroSumBase_iff K).mp hp
  rw [indexEquiv_typeAZeroSumRevAut_simplePair]
  exact (mem_support_typeAZeroSumBase_iff K).mpr ⟨i.rev, rfl⟩

/-- Conjugating `typeABaseChangeGraphAut K m` by `typeABaseChangeEquivZeroSum K m` yields
`typeAZeroSumRevAut K m`. -/
theorem autCongr_typeABaseChangeEquivZeroSum_graphAut (m : ℕ) :
    (typeABaseChangeEquivZeroSum K m).autCongr (typeABaseChangeGraphAut K m) =
      typeAZeroSumRevAut K m := by
  apply RootPairing.Equiv.weightHom_injective
  refine LinearEquiv.ext fun x ↦ ?_
  have h1 : ∀ u : singleParityCheckCode K (Fin (m + 1)),
      zeroSumWeightEquiv K m (typeAZeroSumRevEquiv K m u) =
        fun k : Fin m ↦ zeroSumWeightEquiv K m u k.rev := by
    intro u
    ext k
    simp only [zeroSumWeightEquiv_apply, coe_typeAZeroSumRevEquiv_apply, Fin.rev_castSucc,
      Fin.rev_succ]
    ring
  have h2 : (typeABaseChangeEquivZeroSum K m).weightEquiv = (zeroSumWeightEquiv K m).symm :=
    RootPairing.weightEquiv_equivMap ..
  rw [RootPairing.Equiv.weightHom_apply, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.weightEquiv_autCongr_apply,
    RootPairing.Equiv.weightEquiv_apply (typeAZeroSumRevAut K m),
    weightMap_typeAZeroSumRevAut, LinearEquiv.coe_coe, h2, LinearEquiv.symm_symm,
    LinearEquiv.symm_apply_eq]
  ext k
  rw [h1, RootPairing.Equiv.weightEquiv_apply, weightMap_typeABaseChangeGraphAut_apply]

end Field

end TauCeti.DynkinType
