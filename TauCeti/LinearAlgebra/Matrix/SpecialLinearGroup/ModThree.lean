/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.OrderOf

/-!
# Structure of `SL(2, 3)` and its quaternion Sylow `2`-subgroup

The special linear group `SL(2, 3) = Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)` has order `24`.
Its two traceless matrices `I = !![0, -1; 1, 0]` and `J = !![1, 1; 1, -1]` satisfy
`I ^ 2 = J ^ 2 = -1` and `I * J = -(J * I)`, defining an injective homomorphism from
`QuaternionGroup 2` onto a subgroup `quaternionSubgroup ≤ SL(2, 3)` of order `8` and index `3`.

An element `g ∈ SL(2, 3)` lies in `quaternionSubgroup` if and only if `g = ±1` or `trace g = 0`
(equivalently, `g ^ 4 = 1`). Because trace and `±1` are conjugation-invariant, `quaternionSubgroup`
is normal in `SL(2, 3)` and is therefore its unique Sylow `2`-subgroup. Since the quotient
`SL(2, 3) ⧸ quaternionSubgroup` has prime order `3` (hence is abelian) while the transvection
`T = !![1, 1; 0, 1]` satisfies `⁅T, J⁆ = I` and `⁅T, I⁆ * ⁅T, J⁆ = J`, the derived subgroup of
`SL(2, 3)` is precisely `quaternionSubgroup`. In particular, `SL(2, 3)` has no subgroup of
order `12`, because any index-`2` subgroup would be normal with abelian quotient and hence contain
the order-`8` derived subgroup.

## Main definitions

* `TauCeti.SL2ZModThree.quaternionI`, `TauCeti.SL2ZModThree.quaternionJ`: the standard quaternion
  generators of order `4` in `SL(2, 3)`.
* `TauCeti.SL2ZModThree.quaternionHom`: the injective embedding
  `QuaternionGroup 2 →* SL(2, ZMod 3)`.
* `TauCeti.SL2ZModThree.quaternionSubgroup`: its range, the normal Sylow `2`-subgroup of
  `SL(2, 3)`.
* `TauCeti.SL2ZModThree.quaternionSubgroupMulEquiv`: the isomorphism
  `QuaternionGroup 2 ≃* quaternionSubgroup`.

## Main results

* `TauCeti.SL2ZModThree.card`: `Nat.card SL(2, ZMod 3) = 24`.
* `TauCeti.SL2ZModThree.mem_quaternionSubgroup_iff` and
  `TauCeti.SL2ZModThree.mem_quaternionSubgroup_iff_pow_four`: trace and fourth-power
  characterizations of `quaternionSubgroup`.
* `TauCeti.SL2ZModThree.coe_sylow_two_eq_quaternionSubgroup`: `quaternionSubgroup` is the unique
  Sylow `2`-subgroup of `SL(2, 3)`.
* `TauCeti.SL2ZModThree.commutator_eq_quaternionSubgroup`: the derived subgroup of `SL(2, 3)` is
  `quaternionSubgroup`.
* `TauCeti.SL2ZModThree.not_exists_subgroup_card_eq_twelve`: `SL(2, 3)` has no subgroup of
  order `12`.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement IsMulCommutative

namespace TauCeti.SL2ZModThree

/-- **`SL(2, 3)` has order `24`**, by the finite-field order formula for `SL(n, 𝔽)`. -/
theorem card : Nat.card SL(2, ZMod 3) = 24 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Matrix.card_SL_field (n := 2) (𝔽 := ZMod 3)
  rw [Fin.prod_univ_two, ZMod.card] at h
  norm_num at h
  rwa [Nat.card_eq_fintype_card]

/-- The matrix `!![0, -1; 1, 0]` in `SL(2, 3)`, of order `4`. -/
def quaternionI : SL(2, ZMod 3) :=
  ⟨!![0, -1; 1, 0], by decide⟩

/-- The underlying matrix of `quaternionI` is `!![0, -1; 1, 0]`. -/
@[simp]
theorem coe_quaternionI :
    (quaternionI : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![0, -1; 1, 0] := (rfl)

/-- The matrix `!![1, 1; 1, -1]` in `SL(2, 3)`, of order `4`. -/
def quaternionJ : SL(2, ZMod 3) :=
  ⟨!![1, 1; 1, -1], by decide⟩

/-- The underlying matrix of `quaternionJ` is `!![1, 1; 1, -1]`. -/
@[simp]
theorem coe_quaternionJ :
    (quaternionJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![1, 1; 1, -1] := (rfl)

/-- `quaternionI ^ 2 = -1` in `SL(2, 3)`. -/
@[simp]
theorem quaternionI_sq : quaternionI ^ 2 = -1 := by decide

/-- `quaternionJ ^ 2 = -1` in `SL(2, 3)`. -/
@[simp]
theorem quaternionJ_sq : quaternionJ ^ 2 = -1 := by decide

/-- `quaternionI ^ 4 = 1` in `SL(2, 3)`. -/
@[simp]
theorem quaternionI_pow_four : quaternionI ^ 4 = 1 := by decide

/-- `quaternionI` and `quaternionJ` anticommute: `I * J = -(J * I)`. -/
theorem quaternionI_mul_quaternionJ : quaternionI * quaternionJ = -(quaternionJ * quaternionI) := by
  decide

private theorem quaternionI_pow_mod_four (n : ℕ) : quaternionI ^ (n % 4) = quaternionI ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, quaternionI_pow_four, one_pow, one_mul]

private theorem quaternionI_pow_val_add (i j : ZMod 4) :
    quaternionI ^ (i + j).val = quaternionI ^ i.val * quaternionI ^ j.val := by
  rw [ZMod.val_add, quaternionI_pow_mod_four, pow_add]

private theorem quaternionI_pow_val_mul_quaternionJ (i : ZMod 4) :
    quaternionI ^ i.val * quaternionJ = quaternionJ * quaternionI ^ (-i).val := by
  fin_cases i <;> decide

private theorem quaternionI_pow_val_two_add (j : ZMod 4) :
    quaternionI ^ ((2 : ZMod 4) + j).val = -quaternionI ^ j.val := by
  rw [quaternionI_pow_val_add]
  have h2 : quaternionI ^ (2 : ZMod 4).val = -1 := by decide
  rw [h2, neg_one_mul]

/-- The standard embedding of `QuaternionGroup 2` into `SL(2, 3)`, sending `a 1` to `quaternionI`
and `xa 0` to `quaternionJ`. -/
def quaternionHom : QuaternionGroup 2 →* SL(2, ZMod 3) where
  toFun
    | .a i => quaternionI ^ i.val
    | .xa i => quaternionJ * quaternionI ^ i.val
  map_one' := by
    rw [QuaternionGroup.one_def]
    simp
  map_mul' g h := by
    cases g with
    | a i =>
      cases h with
      | a j =>
        simpa only [QuaternionGroup.a_mul_a] using quaternionI_pow_val_add i j
      | xa j =>
        simp only [QuaternionGroup.a_mul_xa]
        rw [← mul_assoc, quaternionI_pow_val_mul_quaternionJ, mul_assoc,
          ← quaternionI_pow_val_add, neg_add_eq_sub]
    | xa i =>
      cases h with
      | a j =>
        simp only [QuaternionGroup.xa_mul_a]
        rw [mul_assoc, ← quaternionI_pow_val_add]
      | xa j =>
        have hJJ : quaternionJ * quaternionJ = -1 := by decide
        simp only [QuaternionGroup.xa_mul_xa, Nat.cast_ofNat]
        rw [mul_assoc, ← mul_assoc (quaternionI ^ i.val), quaternionI_pow_val_mul_quaternionJ,
          mul_assoc quaternionJ, ← mul_assoc quaternionJ quaternionJ, hJJ, neg_one_mul,
          ← quaternionI_pow_val_add, ← quaternionI_pow_val_two_add, add_sub_assoc, neg_add_eq_sub]

/-- Evaluation of `quaternionHom` on rotation elements `a i`. -/
@[simp]
theorem quaternionHom_a (i : ZMod 4) :
    quaternionHom (QuaternionGroup.a i) = quaternionI ^ i.val := (rfl)

/-- Evaluation of `quaternionHom` on coset elements `xa i`. -/
@[simp]
theorem quaternionHom_xa (i : ZMod 4) :
    quaternionHom (QuaternionGroup.xa i) = quaternionJ * quaternionI ^ i.val := (rfl)

/-- `quaternionHom : QuaternionGroup 2 →* SL(2, 3)` is injective. -/
theorem quaternionHom_injective : Function.Injective quaternionHom := by
  rw [injective_iff_map_eq_one]
  intro q hq
  cases q with
  | a i =>
    fin_cases i
    · exact QuaternionGroup.a_zero
    all_goals exact absurd hq (by decide)
  | xa i =>
    fin_cases i <;> exact absurd hq (by decide)

/-- The quaternion subgroup `Q₈ ≤ SL(2, 3)`, the range of `quaternionHom`. -/
def quaternionSubgroup : Subgroup SL(2, ZMod 3) :=
  quaternionHom.range

/-- `quaternionI` lies in `quaternionSubgroup`. -/
theorem quaternionI_mem_quaternionSubgroup : quaternionI ∈ quaternionSubgroup :=
  ⟨QuaternionGroup.a 1, by decide⟩

/-- `quaternionJ` lies in `quaternionSubgroup`. -/
theorem quaternionJ_mem_quaternionSubgroup : quaternionJ ∈ quaternionSubgroup :=
  ⟨QuaternionGroup.xa 0, by decide⟩

/-- `-1` lies in `quaternionSubgroup`. -/
theorem neg_one_mem_quaternionSubgroup : (-1 : SL(2, ZMod 3)) ∈ quaternionSubgroup :=
  ⟨QuaternionGroup.a 2, by decide⟩

/-- Isomorphism between `QuaternionGroup 2` and `quaternionSubgroup ≤ SL(2, 3)`. -/
noncomputable def quaternionSubgroupMulEquiv : QuaternionGroup 2 ≃* quaternionSubgroup :=
  MulEquiv.ofBijective quaternionHom.rangeRestrict
    ⟨fun _ _ h ↦ quaternionHom_injective (congrArg Subtype.val h),
      quaternionHom.rangeRestrict_surjective⟩

/-- Applying `quaternionSubgroupMulEquiv` coerces to `quaternionHom`. -/
@[simp]
theorem coe_quaternionSubgroupMulEquiv (q : QuaternionGroup 2) :
    (quaternionSubgroupMulEquiv q : SL(2, ZMod 3)) = quaternionHom q := (rfl)

private theorem mem_quaternionSubgroup_of_trace_eq_zero {g : SL(2, ZMod 3)}
    (htr : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = 0) : g ∈ quaternionSubgroup := by
  have hd : g 1 1 = -g 0 0 := eq_neg_of_add_eq_zero_right (by rwa [Matrix.trace_fin_two] at htr)
  have hdet : g 0 0 * (-g 0 0) - g 0 1 * g 1 0 = 1 := by
    simpa [hd] using g.fin_two_mul_sub_mul_eq_one
  have hcases : ∀ a b c : ZMod 3, a * (-a) - b * c = 1 →
      (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 2 ∧ c = 2) ∨
      (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 2 ∧ b = 2 ∧ c = 2) := by decide
  have hmem (q : QuaternionGroup 2)
      (h00 : g 0 0 = quaternionHom q 0 0) (h01 : g 0 1 = quaternionHom q 0 1)
      (h10 : g 1 0 = quaternionHom q 1 0) (h11 : g 1 1 = quaternionHom q 1 1) :
      g ∈ quaternionSubgroup := by
    refine ⟨q, Subtype.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  rcases hcases (g 0 0) (g 0 1) (g 1 0) hdet with
    ⟨h00, h01, h10⟩ | ⟨h00, h01, h10⟩ | ⟨h00, h01, h10⟩ |
    ⟨h00, h01, h10⟩ | ⟨h00, h01, h10⟩ | ⟨h00, h01, h10⟩
  · exact hmem (.a 3) h00 h01 h10 (by rw [hd, h00]; decide)
  · exact hmem (.a 1) h00 h01 h10 (by rw [hd, h00]; decide)
  · exact hmem (.xa 0) h00 h01 h10 (by rw [hd, h00]; decide)
  · exact hmem (.xa 1) h00 h01 h10 (by rw [hd, h00]; decide)
  · exact hmem (.xa 3) h00 h01 h10 (by rw [hd, h00]; decide)
  · exact hmem (.xa 2) h00 h01 h10 (by rw [hd, h00]; decide)

/-- **Trace characterization of `Q₈ ≤ SL(2, 3)`**: a matrix in `SL(2, 3)` belongs to
`quaternionSubgroup` if and only if it is `1`, `-1`, or traceless. -/
theorem mem_quaternionSubgroup_iff {g : SL(2, ZMod 3)} :
    g ∈ quaternionSubgroup ↔
      g = 1 ∨ g = -1 ∨ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    cases q with
    | a i => fin_cases i <;> decide
    | xa i => fin_cases i <;> decide
  · rintro (rfl | rfl | htr)
    · exact quaternionSubgroup.one_mem
    · exact neg_one_mem_quaternionSubgroup
    · exact mem_quaternionSubgroup_of_trace_eq_zero htr

/-- **Fourth-power characterization of `Q₈ ≤ SL(2, 3)`**: `quaternionSubgroup` consists precisely of
the elements of `SL(2, 3)` whose fourth power is `1`. -/
theorem mem_quaternionSubgroup_iff_pow_four {g : SL(2, ZMod 3)} :
    g ∈ quaternionSubgroup ↔ g ^ 4 = 1 := by
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [mem_quaternionSubgroup_iff]
  constructor
  · rintro (rfl | rfl | htr)
    · simp
    · decide
    · have hsq : g ^ 2 = -1 := (sq_eq_neg_one_iff_trace_eq_zero g).mpr htr
      calc g ^ 4 = (g ^ 2) ^ 2 := by rw [← pow_mul]
        _ = 1 := by rw [hsq]; decide
  · intro h4
    have hsq2 : (g ^ 2) ^ 2 = 1 := by rwa [← pow_mul]
    rcases (Matrix.SpecialLinearGroup.sq_eq_one_iff (g ^ 2)).mp hsq2 with hsq | hsq
    · rcases (Matrix.SpecialLinearGroup.sq_eq_one_iff g).mp hsq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ((sq_eq_neg_one_iff_trace_eq_zero g).mp hsq))

/-- **`quaternionSubgroup` is normal in `SL(2, 3)`**, since `1`, `-1`, and trace zero are invariant
under conjugation. -/
instance normal_quaternionSubgroup : quaternionSubgroup.Normal where
  conj_mem g hg h := by
    rw [mem_quaternionSubgroup_iff] at hg ⊢
    rcases hg with rfl | rfl | htr
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (by simp))
    · refine Or.inr (Or.inr ?_)
      rw [coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, inv_mul_cancel, coe_one,
        Matrix.one_mul, htr]

/-- **`quaternionSubgroup` has order `8`.** -/
theorem card_quaternionSubgroup : Nat.card quaternionSubgroup = 8 := by
  rw [← Nat.card_congr quaternionSubgroupMulEquiv.toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

/-- **`quaternionSubgroup` has index `3` in `SL(2, 3)`.** -/
theorem index_quaternionSubgroup : quaternionSubgroup.index = 3 := by
  have h := quaternionSubgroup.card_mul_index
  rw [card_quaternionSubgroup, card] at h
  omega

/-- **`quaternionSubgroup` is a `2`-group.** -/
theorem isPGroup_quaternionSubgroup : IsPGroup 2 quaternionSubgroup :=
  IsPGroup.of_card (n := 3) (by rw [card_quaternionSubgroup]; rfl)

/-- **`quaternionSubgroup` is the unique Sylow `2`-subgroup of `SL(2, 3)`.** -/
theorem coe_sylow_two_eq_quaternionSubgroup (P : Sylow 2 SL(2, ZMod 3)) :
    (P : Subgroup SL(2, ZMod 3)) = quaternionSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 SL(2, ZMod 3) :=
    isPGroup_quaternionSubgroup.toSylow (by rw [index_quaternionSubgroup]; decide)
  have hQ : (Q : Subgroup SL(2, ZMod 3)).Normal := by
    rw [isPGroup_quaternionSubgroup.toSylow_coe]
    infer_instance
  have := Sylow.unique_of_normal Q hQ
  rw [Subsingleton.elim P Q, isPGroup_quaternionSubgroup.toSylow_coe]

/-- **`quaternionSubgroup` is non-abelian**, witnessed by `I * J ≠ J * I`. -/
theorem not_isMulCommutative_quaternionSubgroup : ¬ IsMulCommutative quaternionSubgroup := by
  intro hcomm
  have h := congrArg Subtype.val
    (mul_comm (⟨quaternionI, quaternionI_mem_quaternionSubgroup⟩ : quaternionSubgroup)
      ⟨quaternionJ, quaternionJ_mem_quaternionSubgroup⟩)
  exact (by decide : quaternionI * quaternionJ ≠ quaternionJ * quaternionI) h

/-- **The derived subgroup of `SL(2, 3)` is `quaternionSubgroup`.** The quotient has prime order
`3`, hence is abelian, giving `commutator SL(2, 3) ≤ Q₈`; conversely, conjugating `I` and `J` by
the transvection `!![1, 1; 0, 1]` generates both `I` and `J` inside the derived subgroup. -/
theorem commutator_eq_quaternionSubgroup : commutator SL(2, ZMod 3) = quaternionSubgroup := by
  apply le_antisymm
  · rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card (SL(2, ZMod 3) ⧸ quaternionSubgroup) = 3 := index_quaternionSubgroup
    exact (isCyclic_of_prime_card hcard).isMulCommutative
  · rintro _ ⟨q, rfl⟩
    let T : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩
    have hTJ : ⁅T, quaternionJ⁆ = quaternionI := by decide
    have hTIJ : ⁅T, quaternionI⁆ * ⁅T, quaternionJ⁆ = quaternionJ := by decide
    have hI : quaternionI ∈ commutator SL(2, ZMod 3) :=
      hTJ ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top T) (Subgroup.mem_top quaternionJ)
    have hJ : quaternionJ ∈ commutator SL(2, ZMod 3) :=
      hTIJ ▸ mul_mem
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top T) (Subgroup.mem_top quaternionI))
        (hTJ.symm ▸ hI)
    cases q with
    | a i => exact pow_mem hI i.val
    | xa i => exact mul_mem hJ (pow_mem hI i.val)

/-- **`SL(2, 3)` has no subgroup of order `12`**: any such subgroup would have index `2`, hence be
normal with abelian quotient of order `2`, forcing it to contain the order-`8` derived subgroup
`quaternionSubgroup`, contradicting `8 ∤ 12`. -/
theorem not_exists_subgroup_card_eq_twelve :
    ¬ ∃ K : Subgroup SL(2, ZMod 3), Nat.card K = 12 := by
  rintro ⟨K, hK⟩
  have hidx : K.index = 2 := by
    have h := K.card_mul_index
    rw [hK, card] at h
    omega
  have : K.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative (SL(2, ZMod 3) ⧸ K) :=
    (isCyclic_of_prime_card (h := hidx)).isMulCommutative
  have hle : quaternionSubgroup ≤ K := by
    rw [← commutator_eq_quaternionSubgroup]
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hdvd : Nat.card quaternionSubgroup ∣ Nat.card K := Subgroup.card_dvd_of_le hle
  rw [card_quaternionSubgroup, hK] at hdvd
  omega

end TauCeti.SL2ZModThree
