/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.GroupTheory.Complement.Local
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic.FinCases
import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Perfect

/-!
# Subgroup and Sylow structure of `SL(2, ZMod 3)`

Over `ZMod 3`, the two-by-two special linear group has order `24` and centre `{±1}` of order `2`.
The matrices `sl2ZModThreeI = !![0, -1; 1, 0]` and `sl2ZModThreeJ = !![1, 1; 1, -1]` satisfy the
dicyclic relations `sl2ZModThreeJ ^ 2 = sl2ZModThreeI ^ 2 = -1` and
`sl2ZModThreeJ * sl2ZModThreeI * sl2ZModThreeJ⁻¹ = sl2ZModThreeI⁻¹` with
`orderOf sl2ZModThreeI = 4`, so `TauCeti.quaternionHom` embeds `QuaternionGroup 2` onto a subgroup
`TauCeti.sl2ZModThreeQuaternionSubgroup` of order `8` and index `3`.

Conjugation by the upper transvection `sl2ZModThreeT = !![1, 1; 0, 1]` cyclically permutes the
three order-four generators `(I, J, I * J)`, while `I` and `T` generate `SL(2, ZMod 3)`. As a
consequence `sl2ZModThreeQuaternionSubgroup` is normal — hence the unique Sylow `2`-subgroup of
`SL(2, ZMod 3)` — and no element outside it fixes any of its six order-four elements up to sign
(`TauCeti.conj_ne_and_ne_neg_of_notMem_sl2ZModThreeQuaternionSubgroup`).

Because every nontrivial subgroup of `QuaternionGroup 2` contains its centre, the central subgroup
`{±1}` has neither a local complement in `sl2ZModThreeQuaternionSubgroup` nor a global complement
in `SL(2, ZMod 3)`. Moreover `SL(2, ZMod 3)` has no subgroup of order `12`
(`TauCeti.not_exists_subgroup_sl2_zmod_three_card_twelve`), showing that a converse to Lagrange's
theorem fails in this solvable group of order `24`.

## Main definitions

* `TauCeti.sl2ZModThreeI`, `TauCeti.sl2ZModThreeJ`, `TauCeti.sl2ZModThreeT`: the standard order-four
  generators and upper transvection in `SL(2, ZMod 3)`.
* `TauCeti.sl2ZModThreeQuaternionHom`, `TauCeti.sl2ZModThreeQuaternionSubgroup`,
  `TauCeti.sl2ZModThreeQuaternionEquiv`: the injective homomorphism from `QuaternionGroup 2`, its
  image of order `8`, and the resulting isomorphism.
* `TauCeti.sl2ZModThreeSylowTwo`: `sl2ZModThreeQuaternionSubgroup` packaged as the unique
  `Sylow 2 SL(2, ZMod 3)`.

## Main results

* `TauCeti.natCard_sl2_zmod_three`, `TauCeti.not_exists_subgroup_sl2_zmod_three_card_twelve`:
  `SL(2, ZMod 3)` has order `24` and no subgroup of order `12`.
* `TauCeti.sl2ZModThreeQuaternionSubgroup_normal`,
  `TauCeti.conj_ne_and_ne_neg_of_notMem_sl2ZModThreeQuaternionSubgroup`: normality of the `Q₈`
  subgroup and outer conjugation action moving every order-four element across `±`-pairs.
* `TauCeti.not_exists_isLocalComplement_center_sl2ZModThreeQuaternionSubgroup`,
  `TauCeti.not_exists_isComplement'_center_sl2_zmod_three`: `{±1}` has neither a local complement
  in the Sylow `2`-subgroup nor a complement in `SL(2, ZMod 3)`.

## References

* K. Conrad, *Generalized quaternion groups*, expository notes.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

open scoped IsMulCommutative MatrixGroups

namespace TauCeti

/-- `SL(2, ZMod 3)` has cardinality `24`. -/
theorem natCard_sl2_zmod_three : Nat.card SL(2, ZMod 3) = 24 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
  decide

/-- In `SL(2, ZMod 3)`, `-1` is distinct from `1`. -/
theorem sl2_zmod_three_neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide

/-- The centre of `SL(2, ZMod 3)` has cardinality `2`. -/
theorem natCard_center_sl2_zmod_three : Nat.card (Subgroup.center SL(2, ZMod 3)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Matrix.SpecialLinearGroup.card_center_eq_two sl2_zmod_three_neg_one_ne_one

/-- `SL(2, ZMod 3)` has no subgroup of cardinality `12`. -/
theorem not_exists_subgroup_sl2_zmod_three_card_twelve :
    ¬ ∃ H : Subgroup SL(2, ZMod 3), Nat.card H = 12 := by
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨H, hH⟩
  have hmul := H.card_mul_index
  rw [hH, natCard_sl2_zmod_three] at hmul
  exact H.index_specialLinearGroup_ne_two (by omega)

/-! ## Explicit generators and the quaternion subgroup -/

/-- The standard rotation matrix `!![0, -1; 1, 0]` of order `4` in `SL(2, ZMod 3)`. -/
def sl2ZModThreeI : SL(2, ZMod 3) :=
  ⟨!![0, -1; 1, 0], by decide⟩

/-- The symmetric matrix `!![1, 1; 1, -1]` of order `4` in `SL(2, ZMod 3)`. -/
def sl2ZModThreeJ : SL(2, ZMod 3) :=
  ⟨!![1, 1; 1, -1], by decide⟩

/-- The upper unitriangular matrix `!![1, 1; 0, 1]` of order `3` in `SL(2, ZMod 3)`. -/
def sl2ZModThreeT : SL(2, ZMod 3) :=
  ⟨!![1, 1; 0, 1], by decide⟩

/-- `TauCeti.sl2ZModThreeI` squares to `-1`. -/
@[simp]
theorem sl2ZModThreeI_sq : sl2ZModThreeI ^ 2 = -1 := by decide

/-- `TauCeti.sl2ZModThreeJ` squares to `-1`. -/
@[simp]
theorem sl2ZModThreeJ_sq : sl2ZModThreeJ ^ 2 = -1 := by decide

/-- `TauCeti.sl2ZModThreeJ` and `TauCeti.sl2ZModThreeI` have equal squares. -/
theorem sl2ZModThreeJ_sq_eq_I_sq : sl2ZModThreeJ ^ 2 = sl2ZModThreeI ^ 2 := by decide

/-- Conjugation by `TauCeti.sl2ZModThreeJ` inverts `TauCeti.sl2ZModThreeI`. -/
theorem sl2ZModThreeJ_conj_I :
    sl2ZModThreeJ * sl2ZModThreeI * sl2ZModThreeJ⁻¹ = sl2ZModThreeI⁻¹ := by decide

/-- `TauCeti.sl2ZModThreeT` has cube `1`. -/
@[simp]
theorem sl2ZModThreeT_cubed : sl2ZModThreeT ^ 3 = 1 := by decide

/-- Conjugation by `TauCeti.sl2ZModThreeT` sends `I` to `J`. -/
theorem sl2ZModThreeT_conj_I :
    sl2ZModThreeT * sl2ZModThreeI * sl2ZModThreeT⁻¹ = sl2ZModThreeJ := by decide

/-- Conjugation by `TauCeti.sl2ZModThreeT` sends `J` to `I * J`. -/
theorem sl2ZModThreeT_conj_J :
    sl2ZModThreeT * sl2ZModThreeJ * sl2ZModThreeT⁻¹ = sl2ZModThreeI * sl2ZModThreeJ := by decide

/-- Conjugation by `TauCeti.sl2ZModThreeT` sends `I * J` to `I`. -/
theorem sl2ZModThreeT_conj_IJ :
    sl2ZModThreeT * (sl2ZModThreeI * sl2ZModThreeJ) * sl2ZModThreeT⁻¹ = sl2ZModThreeI := by decide

/-- `TauCeti.sl2ZModThreeI` has exact order `4`. -/
@[simp]
theorem orderOf_sl2ZModThreeI : orderOf sl2ZModThreeI = 4 :=
  orderOf_eq_iff (by decide) |>.mpr ⟨by decide, fun m hm hpos => by
    interval_cases m <;> decide⟩

/-- `TauCeti.sl2ZModThreeI` and `TauCeti.sl2ZModThreeT` generate `SL(2, ZMod 3)`. -/
theorem closure_sl2ZModThreeI_T :
    Subgroup.closure ({sl2ZModThreeI, sl2ZModThreeT} : Set SL(2, ZMod 3)) = ⊤ := by
  let φ : SL(2, ℤ) →* SL(2, ZMod 3) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))
  have hS : φ ModularGroup.S = sl2ZModThreeI := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hT : φ ModularGroup.T = sl2ZModThreeT := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hpair : φ '' ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) =
      {sl2ZModThreeI, sl2ZModThreeT} := by
    rw [Set.image_pair, hS, hT]
  rw [← hpair, ← MonoidHom.map_closure, SpecialLinearGroup.SL2Z_generators,
    Subgroup.map_top_of_surjective φ Matrix.SpecialLinearGroup.map_intCast_zmod_surjective]

/-- The injective homomorphism `QuaternionGroup 2 →* SL(2, ZMod 3)` sending `a 1` to
`sl2ZModThreeI` and `xa 0` to `sl2ZModThreeJ`. -/
def sl2ZModThreeQuaternionHom : QuaternionGroup 2 →* SL(2, ZMod 3) :=
  quaternionHom sl2ZModThreeJ_sq_eq_I_sq sl2ZModThreeJ_conj_I

/-- `TauCeti.sl2ZModThreeQuaternionHom` maps `a i` to `sl2ZModThreeI ^ (ZMod.cast i : ℤ)`. -/
@[simp]
theorem sl2ZModThreeQuaternionHom_a (i : ZMod (2 * 2)) :
    sl2ZModThreeQuaternionHom (.a i) = sl2ZModThreeI ^ (ZMod.cast i : ℤ) :=
  quaternionHom_a sl2ZModThreeJ_sq_eq_I_sq sl2ZModThreeJ_conj_I i

/-- `TauCeti.sl2ZModThreeQuaternionHom` maps `xa i` to
`sl2ZModThreeJ * sl2ZModThreeI ^ (ZMod.cast i : ℤ)`. -/
@[simp]
theorem sl2ZModThreeQuaternionHom_xa (i : ZMod (2 * 2)) :
    sl2ZModThreeQuaternionHom (.xa i) = sl2ZModThreeJ * sl2ZModThreeI ^ (ZMod.cast i : ℤ) :=
  quaternionHom_xa sl2ZModThreeJ_sq_eq_I_sq sl2ZModThreeJ_conj_I i

/-- `TauCeti.sl2ZModThreeQuaternionHom` is injective. -/
theorem sl2ZModThreeQuaternionHom_injective : Function.Injective sl2ZModThreeQuaternionHom :=
  quaternionHom_injective sl2ZModThreeJ_sq_eq_I_sq sl2ZModThreeJ_conj_I orderOf_sl2ZModThreeI

/-- `TauCeti.sl2ZModThreeQuaternionHom` sends the central involution `a 2` of `QuaternionGroup 2`
to `-1`. -/
theorem sl2ZModThreeQuaternionHom_a_two :
    sl2ZModThreeQuaternionHom (QuaternionGroup.a 2) = -1 := by
  rw [sl2ZModThreeQuaternionHom_a]
  decide

/-- The quaternion subgroup of order `8` in `SL(2, ZMod 3)`, defined as the range of
`TauCeti.sl2ZModThreeQuaternionHom`. -/
def sl2ZModThreeQuaternionSubgroup : Subgroup SL(2, ZMod 3) :=
  sl2ZModThreeQuaternionHom.range

/-- An element of `SL(2, ZMod 3)` lies in `TauCeti.sl2ZModThreeQuaternionSubgroup` if and only if
it is in the image of `TauCeti.sl2ZModThreeQuaternionHom`. -/
theorem mem_sl2ZModThreeQuaternionSubgroup_iff {g : SL(2, ZMod 3)} :
    g ∈ sl2ZModThreeQuaternionSubgroup ↔ ∃ x : QuaternionGroup 2, sl2ZModThreeQuaternionHom x = g :=
  Iff.rfl

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` is generated by `sl2ZModThreeI` and
`sl2ZModThreeJ`. -/
theorem sl2ZModThreeQuaternionSubgroup_eq_closure :
    sl2ZModThreeQuaternionSubgroup = Subgroup.closure {sl2ZModThreeI, sl2ZModThreeJ} :=
  range_quaternionHom sl2ZModThreeJ_sq_eq_I_sq sl2ZModThreeJ_conj_I

/-- The isomorphism `QuaternionGroup 2 ≃* sl2ZModThreeQuaternionSubgroup`. -/
noncomputable def sl2ZModThreeQuaternionEquiv :
    QuaternionGroup 2 ≃* sl2ZModThreeQuaternionSubgroup :=
  MonoidHom.ofInjective sl2ZModThreeQuaternionHom_injective

/-- Coercing `TauCeti.sl2ZModThreeQuaternionEquiv x` to `SL(2, ZMod 3)` evaluates
`TauCeti.sl2ZModThreeQuaternionHom x`. -/
@[simp]
theorem coe_sl2ZModThreeQuaternionEquiv (x : QuaternionGroup 2) :
    (sl2ZModThreeQuaternionEquiv x : SL(2, ZMod 3)) = sl2ZModThreeQuaternionHom x :=
  MonoidHom.ofInjective_apply sl2ZModThreeQuaternionHom_injective

/-- `TauCeti.sl2ZModThreeI` belongs to `TauCeti.sl2ZModThreeQuaternionSubgroup`. -/
@[simp]
theorem sl2ZModThreeI_mem_quaternionSubgroup :
    sl2ZModThreeI ∈ sl2ZModThreeQuaternionSubgroup := by
  rw [sl2ZModThreeQuaternionSubgroup_eq_closure]
  exact Subgroup.subset_closure (by simp)

/-- `TauCeti.sl2ZModThreeJ` belongs to `TauCeti.sl2ZModThreeQuaternionSubgroup`. -/
@[simp]
theorem sl2ZModThreeJ_mem_quaternionSubgroup :
    sl2ZModThreeJ ∈ sl2ZModThreeQuaternionSubgroup := by
  rw [sl2ZModThreeQuaternionSubgroup_eq_closure]
  exact Subgroup.subset_closure (by simp)

/-- `-1` belongs to `TauCeti.sl2ZModThreeQuaternionSubgroup`. -/
@[simp]
theorem neg_one_mem_sl2ZModThreeQuaternionSubgroup :
    (-1 : SL(2, ZMod 3)) ∈ sl2ZModThreeQuaternionSubgroup :=
  ⟨QuaternionGroup.a 2, sl2ZModThreeQuaternionHom_a_two⟩

/-- The centre of `SL(2, ZMod 3)` lies inside `sl2ZModThreeQuaternionSubgroup`. -/
theorem center_le_sl2ZModThreeQuaternionSubgroup :
    Subgroup.center SL(2, ZMod 3) ≤ sl2ZModThreeQuaternionSubgroup := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Matrix.SpecialLinearGroup.center_eq_zpowers_neg_one, Subgroup.zpowers_le]
  exact neg_one_mem_sl2ZModThreeQuaternionSubgroup

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` has cardinality `8`. -/
@[simp]
theorem natCard_sl2ZModThreeQuaternionSubgroup :
    Nat.card sl2ZModThreeQuaternionSubgroup = 8 := by
  rw [Nat.card_congr sl2ZModThreeQuaternionEquiv.symm.toEquiv, natCard_quaternionGroup]

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` has index `3` in `SL(2, ZMod 3)`. -/
@[simp]
theorem index_sl2ZModThreeQuaternionSubgroup :
    sl2ZModThreeQuaternionSubgroup.index = 3 := by
  have h := sl2ZModThreeQuaternionSubgroup.card_mul_index
  rw [natCard_sl2ZModThreeQuaternionSubgroup, natCard_sl2_zmod_three] at h
  omega

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` is a `2`-group. -/
theorem isPGroup_sl2ZModThreeQuaternionSubgroup :
    IsPGroup 2 sl2ZModThreeQuaternionSubgroup := by
  have hcard : Nat.card sl2ZModThreeQuaternionSubgroup = 2 ^ 3 := by
    rw [natCard_sl2ZModThreeQuaternionSubgroup]
    decide
  exact IsPGroup.of_card hcard

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` is not commutative. -/
theorem not_isMulCommutative_sl2ZModThreeQuaternionSubgroup :
    ¬ IsMulCommutative sl2ZModThreeQuaternionSubgroup := by
  intro h
  have : IsMulCommutative (QuaternionGroup 2) :=
    ⟨⟨fun x y => sl2ZModThreeQuaternionEquiv.injective (by
      rw [map_mul, map_mul, mul_comm'])⟩⟩
  exact not_isMulCommutative_quaternionGroup (by decide) this

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` is normal in `SL(2, ZMod 3)`. -/
instance sl2ZModThreeQuaternionSubgroup_normal : sl2ZModThreeQuaternionSubgroup.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← closure_sl2ZModThreeI_T,
    Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.le_normalizer sl2ZModThreeI_mem_quaternionSubgroup
  · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (le_antisymm ?_ ?_)
    · rw [Subgroup.map_le_iff_le_comap]
      nth_rw 1 [sl2ZModThreeQuaternionSubgroup_eq_closure]
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · simp [MulAut.conj_apply, sl2ZModThreeT_conj_I]
      · simpa [MulAut.conj_apply, sl2ZModThreeT_conj_J] using
          mul_mem sl2ZModThreeI_mem_quaternionSubgroup sl2ZModThreeJ_mem_quaternionSubgroup
    · nth_rw 1 [sl2ZModThreeQuaternionSubgroup_eq_closure]
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨sl2ZModThreeI * sl2ZModThreeJ,
          mul_mem sl2ZModThreeI_mem_quaternionSubgroup sl2ZModThreeJ_mem_quaternionSubgroup,
          by simpa [MulAut.conj_apply] using sl2ZModThreeT_conj_IJ⟩
      · exact ⟨sl2ZModThreeI, sl2ZModThreeI_mem_quaternionSubgroup,
          by simpa [MulAut.conj_apply] using sl2ZModThreeT_conj_I⟩

/-- `TauCeti.sl2ZModThreeQuaternionSubgroup` packaged as a Sylow `2`-subgroup of `SL(2, ZMod 3)`. -/
def sl2ZModThreeSylowTwo : Sylow 2 SL(2, ZMod 3) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isPGroup_sl2ZModThreeQuaternionSubgroup.toSylow
    (by rw [index_sl2ZModThreeQuaternionSubgroup]; decide)

/-- The underlying subgroup of `TauCeti.sl2ZModThreeSylowTwo` is
`TauCeti.sl2ZModThreeQuaternionSubgroup`. -/
@[simp]
theorem coe_sl2ZModThreeSylowTwo :
    (sl2ZModThreeSylowTwo : Subgroup SL(2, ZMod 3)) = sl2ZModThreeQuaternionSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe _ _

/-- `SL(2, ZMod 3)` has a unique Sylow `2`-subgroup. -/
noncomputable instance instUniqueSylowTwoSL2ZModThree : Unique (Sylow 2 SL(2, ZMod 3)) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  sl2ZModThreeSylowTwo.unique_of_normal
    (coe_sl2ZModThreeSylowTwo.symm ▸ sl2ZModThreeQuaternionSubgroup_normal)

/-! ## Outer conjugation on the quaternion subgroup and non-splitting of the centre -/

private theorem conj_eq_or_eq_neg_of_mem_quaternionSubgroup {h q : SL(2, ZMod 3)}
    (hh : h ∈ sl2ZModThreeQuaternionSubgroup) (hq : q ∈ sl2ZModThreeQuaternionSubgroup) :
    h * q * h⁻¹ = q ∨ h * q * h⁻¹ = -q := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨y, rfl⟩ := hq
  have hxy : x * y * x⁻¹ = y ∨ x * y * x⁻¹ = QuaternionGroup.a 2 * y := by
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> decide
  rcases hxy with h1 | h2
  · left
    simpa only [map_mul, map_inv] using congrArg sl2ZModThreeQuaternionHom h1
  · right
    have := congrArg sl2ZModThreeQuaternionHom h2
    simpa only [map_mul, map_inv, sl2ZModThreeQuaternionHom_a_two, neg_one_mul] using this

private theorem mem_quaternionSubgroup_cases {q : SL(2, ZMod 3)}
    (hq : q ∈ sl2ZModThreeQuaternionSubgroup) (hq1 : q ≠ 1) (hqneg : q ≠ -1) :
    q = sl2ZModThreeI ∨ q = -sl2ZModThreeI ∨ q = sl2ZModThreeJ ∨ q = -sl2ZModThreeJ ∨
      q = sl2ZModThreeI * sl2ZModThreeJ ∨ q = -(sl2ZModThreeI * sl2ZModThreeJ) := by
  obtain ⟨x, rfl⟩ := hq
  rcases x with i | i
  · rw [sl2ZModThreeQuaternionHom_a] at hq1 hqneg ⊢
    fin_cases i
    · exact absurd (by decide) hq1
    · exact Or.inl (by decide)
    · exact absurd (by decide) hqneg
    · exact Or.inr (Or.inl (by decide))
  · rw [sl2ZModThreeQuaternionHom_xa]
    fin_cases i
    · exact Or.inr (Or.inr (Or.inl (by decide)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))

private theorem coset_sl2ZModThreeQuaternionSubgroup_mul_mem {x y : SL(2, ZMod 3)}
    (hx : x ∈ sl2ZModThreeQuaternionSubgroup)
    (hy : y ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT⁻¹ * y ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT * y ∈ sl2ZModThreeQuaternionSubgroup) :
    x * y ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT⁻¹ * (x * y) ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT * (x * y) ∈ sl2ZModThreeQuaternionSubgroup := by
  rcases hy with hy0 | hy1 | hy2
  · exact Or.inl (mul_mem hx hy0)
  · refine Or.inr (Or.inl ?_)
    have hconj : sl2ZModThreeT⁻¹ * x * sl2ZModThreeT ∈ sl2ZModThreeQuaternionSubgroup := by
      simpa [inv_inv] using
        sl2ZModThreeQuaternionSubgroup_normal.conj_mem x hx sl2ZModThreeT⁻¹
    have hreassoc :
        (sl2ZModThreeT⁻¹ * x * sl2ZModThreeT) * (sl2ZModThreeT⁻¹ * y) =
          sl2ZModThreeT⁻¹ * (x * y) := by
      group
    simpa only [hreassoc] using mul_mem hconj hy1
  · refine Or.inr (Or.inr ?_)
    have hconj : sl2ZModThreeT * x * sl2ZModThreeT⁻¹ ∈ sl2ZModThreeQuaternionSubgroup :=
      sl2ZModThreeQuaternionSubgroup_normal.conj_mem x hx sl2ZModThreeT
    have hreassoc :
        (sl2ZModThreeT * x * sl2ZModThreeT⁻¹) * (sl2ZModThreeT * y) =
          sl2ZModThreeT * (x * y) := by
      group
    simpa only [hreassoc] using mul_mem hconj hy2

private theorem coset_sl2ZModThreeQuaternionSubgroup (g : SL(2, ZMod 3)) :
    g ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT⁻¹ * g ∈ sl2ZModThreeQuaternionSubgroup ∨
      sl2ZModThreeT * g ∈ sl2ZModThreeQuaternionSubgroup := by
  have hg : g ∈ Subgroup.closure ({sl2ZModThreeI, sl2ZModThreeT} : Set SL(2, ZMod 3)) := by
    rw [closure_sl2ZModThreeI_T]
    exact Subgroup.mem_top g
  have hT_eq : sl2ZModThreeT * sl2ZModThreeT = sl2ZModThreeT⁻¹ := by decide
  have hTinv_eq : sl2ZModThreeT⁻¹ * sl2ZModThreeT⁻¹ = sl2ZModThreeT := by decide
  induction hg using Subgroup.closure_induction_left with
  | one => exact Or.inl (one_mem _)
  | mul_left s hs y _ hy =>
    rcases hs with rfl | rfl
    · exact coset_sl2ZModThreeQuaternionSubgroup_mul_mem sl2ZModThreeI_mem_quaternionSubgroup hy
    · rcases hy with hy0 | hy1 | hy2
      · exact Or.inr (Or.inl (by simpa using hy0))
      · exact Or.inr (Or.inr (by rwa [← mul_assoc, hT_eq]))
      · exact Or.inl hy2
  | inv_mul_cancel s hs y _ hy =>
    rcases hs with rfl | rfl
    · exact coset_sl2ZModThreeQuaternionSubgroup_mul_mem
        (inv_mem sl2ZModThreeI_mem_quaternionSubgroup) hy
    · rcases hy with hy0 | hy1 | hy2
      · exact Or.inr (Or.inr (by simpa using hy0))
      · exact Or.inl hy1
      · exact Or.inr (Or.inl (by rwa [← mul_assoc, hTinv_eq]))

/-- **Outer conjugation moves every order-four quaternion element across `±`-pairs.** If `g` lies
outside `sl2ZModThreeQuaternionSubgroup` and `q` is one of the six elements of
`sl2ZModThreeQuaternionSubgroup` outside `{1, -1}`, then `g * q * g⁻¹` is neither `q` nor `-q`. -/
theorem conj_ne_and_ne_neg_of_notMem_sl2ZModThreeQuaternionSubgroup {g q : SL(2, ZMod 3)}
    (hg : g ∉ sl2ZModThreeQuaternionSubgroup) (hq : q ∈ sl2ZModThreeQuaternionSubgroup)
    (hq1 : q ≠ 1) (hqneg : q ≠ -1) :
    g * q * g⁻¹ ≠ q ∧ g * q * g⁻¹ ≠ -q := by
  rcases coset_sl2ZModThreeQuaternionSubgroup g with hgQ | hTg | hTinvg
  · exact absurd hgQ hg
  · set h := sl2ZModThreeT⁻¹ * g
    have hg_eq : g = sl2ZModThreeT * h := by simp [h]
    have hconj_eq : g * q * g⁻¹ = sl2ZModThreeT * (h * q * h⁻¹) * sl2ZModThreeT⁻¹ := by
      rw [hg_eq]
      group
    rw [hconj_eq]
    rcases conj_eq_or_eq_neg_of_mem_quaternionSubgroup hTg hq with hh | hh <;> rw [hh] <;>
      (rcases mem_quaternionSubgroup_cases hq hq1 hqneg with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · set h := sl2ZModThreeT * g
    have hg_eq : g = sl2ZModThreeT⁻¹ * h := by simp [h]
    have hconj_eq : g * q * g⁻¹ = sl2ZModThreeT⁻¹ * (h * q * h⁻¹) * sl2ZModThreeT := by
      rw [hg_eq]
      group
    rw [hconj_eq]
    rcases conj_eq_or_eq_neg_of_mem_quaternionSubgroup hTinvg hq with hh | hh <;> rw [hh] <;>
      (rcases mem_quaternionSubgroup_cases hq hq1 hqneg with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- The centre `{±1}` of `SL(2, ZMod 3)` has no local complement in the Sylow `2`-subgroup
`sl2ZModThreeQuaternionSubgroup`. -/
theorem not_exists_isLocalComplement_center_sl2ZModThreeQuaternionSubgroup :
    ¬ ∃ K : Subgroup SL(2, ZMod 3),
      (Subgroup.center SL(2, ZMod 3)).IsLocalComplement K sl2ZModThreeQuaternionSubgroup := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨K, hK⟩
  have hmap :
      (Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup 2)).map
        sl2ZModThreeQuaternionEquiv.toMonoidHom =
      (Subgroup.center SL(2, ZMod 3)).subgroupOf sl2ZModThreeQuaternionSubgroup := by
    rw [MonoidHom.map_zpowers, Matrix.SpecialLinearGroup.center_eq_zpowers_neg_one]
    ext y
    rw [Subgroup.mem_subgroupOf]
    have ha2 : sl2ZModThreeQuaternionEquiv (QuaternionGroup.a 2) =
        ⟨-1, neg_one_mem_sl2ZModThreeQuaternionSubgroup⟩ :=
      Subtype.ext sl2ZModThreeQuaternionHom_a_two
    rw [MulEquiv.coe_toMonoidHom, ha2]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, by simpa using congrArg Subtype.val hk⟩,
      fun ⟨k, hk⟩ => ⟨k, Subtype.ext (by simpa using hk)⟩⟩
  have hcomp :
      ((Subgroup.zpowers (QuaternionGroup.a 2 : QuaternionGroup 2)).map
        sl2ZModThreeQuaternionEquiv.toMonoidHom).IsComplement'
        (K.subgroupOf sl2ZModThreeQuaternionSubgroup) :=
    hmap.symm ▸ hK.isComplement'_subgroupOf
  exact not_exists_isComplement'_zpowers_quaternionGroup_a 1
    ⟨_, hcomp.of_map sl2ZModThreeQuaternionEquiv.injective⟩

/-- **Non-splitting of `SL(2, ZMod 3)` over its centre.** The central subgroup `{±1}` has no
complement in `SL(2, ZMod 3)`. -/
theorem not_exists_isComplement'_center_sl2_zmod_three :
    ¬ ∃ D : Subgroup SL(2, ZMod 3), (Subgroup.center SL(2, ZMod 3)).IsComplement' D := by
  rintro ⟨D, hD⟩
  exact not_exists_isLocalComplement_center_sl2ZModThreeQuaternionSubgroup
    ⟨D ⊓ sl2ZModThreeQuaternionSubgroup,
      hD.isLocalComplement_inf center_le_sl2ZModThreeQuaternionSubgroup⟩

end TauCeti
