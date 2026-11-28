/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Uniform
import Mathlib.GroupTheory.Commutator.Basic
import TauCeti.Algebra.Group.Pow
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Congruence levels of the `p`-adic Heisenberg group as uniform pro-`p` groups

For a prime `p` and `m ≥ 1` (with `m ≥ 2` when `p = 2`), the congruence level
`TauCeti.HeisenbergGroup.level p m` of `HeisenbergGroup ℤ_[p]` is a nonabelian uniform pro-`p`
group of dimension `3`, with closed `p`-th power subgroup `level p (m + 1)` of index `p ^ 3`.

At `p = 2`, `level 2 1` is neither powerful nor uniform, showing that the fourth-power condition at
`p = 2` is necessary. Moreover, every uniform level `level p m` contains an open subgroup (the
elements with `z`-coordinate divisible by `p ^ (2 * m)`) that is neither powerful nor uniform,
demonstrating that uniformity and powerfulness do not pass to arbitrary open subgroups.

## Main results

* `TauCeti.HeisenbergGroup.isPowerful_level`, `TauCeti.HeisenbergGroup.isUniform_level`:
  `HeisenbergGroup.level p m` is powerful and uniform for `(if p = 2 then 2 else 1) ≤ m`.
* `TauCeti.HeisenbergGroup.closedPowerSubgroup_level`,
  `TauCeti.HeisenbergGroup.index_closedPowerSubgroup_level`,
  `TauCeti.HeisenbergGroup.topologicalGeneratorRankNat_level`: the closed `p`-th power subgroup
  of `level p m` (`1 ≤ m`) is `level p (m + 1)` of index `p ^ 3`, so each uniform level has
  dimension `3`.
* `TauCeti.HeisenbergGroup.not_isPowerful_level_two_one`,
  `TauCeti.HeisenbergGroup.not_isUniform_level_two_one`: `level 2 1` is neither powerful nor
  uniform.
* `TauCeti.HeisenbergGroup.exists_openSubgroup_not_isPowerful_and_not_isUniform_level`: every
  uniform level `level p m` contains an open subgroup that is neither powerful nor uniform.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

namespace HeisenbergGroup

variable (p : ℕ) [hp : Fact p.Prime]

/-- For every prime `p` and every `m ≥ 1` (with `m ≥ 2` at `p = 2`), the congruence level
`HeisenbergGroup.level p m` is powerful. -/
theorem isPowerful_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsPowerful p (level p m).toSubgroup := by
  set r : ℕ := if p = 2 then 2 else 1
  have hr : p ^ r = if p = 2 then 4 else p := pow_ite_eq_ite_four p
  rw [isPowerful_iff, commutator_def, Subgroup.commutator_le]
  rintro a _ b _
  obtain ⟨⟨xa, hxa⟩, ⟨ya, hya⟩, -⟩ := (mem_level_iff p m).mp a.property
  obtain ⟨⟨xb, hxb⟩, ⟨yb, hyb⟩, -⟩ := (mem_level_iff p m).mp b.property
  let c : (level p m).toSubgroup :=
    ⟨⟨0, 0, (p : ℤ_[p]) ^ (2 * m - r) * (xa * yb - xb * ya)⟩, (mem_level_iff p m).mpr
      ⟨dvd_zero _, dvd_zero _, (pow_dvd_pow (p : ℤ_[p]) (by omega)).trans (dvd_mul_right _ _)⟩⟩
  have hcomm : ⁅a, b⁆ = c ^ (if p = 2 then 4 else p) := Subtype.ext <| by
    rw [Subgroup.coe_commutatorElement, commutatorElement_eq, Subgroup.coe_pow, ← hr, pow_eq]
    refine HeisenbergGroup.ext (by simp [c]) (by simp [c]) ?_
    simp only [c, nsmul_eq_mul, Nat.cast_pow, mul_zero, add_zero, hxa, hya, hxb, hyb]
    have hrm : r + (2 * m - r) = m + m := by omega
    rw [← mul_assoc ((p : ℤ_[p]) ^ r), ← pow_add, hrm, pow_add]
    ring
  exact hcomm ▸ pow_mem_closedPowerSubgroup c

/-- **Nonabelian uniform pro-`p` group of dimension `3`**: for every prime `p` and
`(if p = 2 then 2 else 1) ≤ m`, `HeisenbergGroup.level p m` is uniform. -/
theorem isUniform_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    IsUniform p (level p m).toSubgroup where
  isProP := (isProP_padicInt p).subgroup _
  isTopologicallyFinitelyGenerated :=
    (isTopologicallyFinitelyGenerated_padicInt p).of_openSubgroup (level p m).toOpenSubgroup
  isMulTorsionFree := IsMulTorsionFree.of_not_isOfFinOrder fun _ hne ha ↦
    hne <| Subtype.ext <| eq_one_of_isOfFinOrder_padicInt p <|
      (level p m).toSubgroup.subtype.isOfFinOrder ha
  isPowerful := isPowerful_level p hm

/-- For `1 ≤ m`, the closed `p`-th power subgroup of `HeisenbergGroup.level p m` is precisely
`HeisenbergGroup.level p (m + 1)`. -/
theorem closedPowerSubgroup_level {m : ℕ} (hm : 1 ≤ m) :
    closedPowerSubgroup p (level p m).toSubgroup =
      (level p (m + 1)).toSubgroup.subgroupOf (level p m).toSubgroup := by
  refine le_antisymm ((closedPowerSubgroup_le_iff
    ((level p (m + 1)).isClosed.preimage continuous_subtypeVal)).mpr fun a ↦ ?_) fun a ha ↦ ?_
  · rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_eq]
    obtain ⟨hx, hy, hz⟩ := (mem_level_iff p m).mp a.property
    have hmul : ∀ {w : ℤ_[p]}, (p : ℤ_[p]) ^ m ∣ w → (p : ℤ_[p]) ^ (m + 1) ∣ (p : ℤ_[p]) * w :=
      fun ⟨c, hc⟩ ↦ ⟨c, by rw [hc, pow_succ', mul_assoc]⟩
    have hxy : (p : ℤ_[p]) ^ (m + 1) ∣ (p.choose 2 : ℤ_[p]) * (a.val.x * a.val.y) :=
      ((pow_dvd_pow (p : ℤ_[p]) (by omega : m + 1 ≤ m + m)).trans
        (pow_add_dvd_mul (p : ℤ_[p]) hx hy)).trans (dvd_mul_left _ _)
    exact (mem_level_iff p (m + 1)).mpr ⟨by simpa [nsmul_eq_mul] using hmul hx,
      by simpa [nsmul_eq_mul] using hmul hy,
      by simpa [nsmul_eq_mul] using dvd_add (hmul hz) hxy⟩
  · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
      (mem_level_iff p (m + 1)).mp (Subgroup.mem_subgroupOf.mp ha)
    let u : (level p m).toSubgroup := ⟨⟨(p : ℤ_[p]) ^ m * x, 0, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_mul_right _ _, dvd_zero _, dvd_zero _⟩⟩
    let v : (level p m).toSubgroup := ⟨⟨0, (p : ℤ_[p]) ^ m * y, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_mul_right _ _, dvd_zero _⟩⟩
    let w : (level p m).toSubgroup :=
      ⟨⟨0, 0, (p : ℤ_[p]) ^ m * (z - (p : ℤ_[p]) ^ (m + 1) * (x * y))⟩,
        (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_zero _, dvd_mul_right _ _⟩⟩
    have hprod : w ^ p * u ^ p * v ^ p = a := Subtype.ext <| by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, pow_eq, u, v, w]
      refine HeisenbergGroup.ext ?_ ?_ ?_
      · simp only [mul_x, mul_zero, zero_add, add_zero, nsmul_eq_mul, hx, pow_succ', mul_assoc]
      · simp only [mul_y, mul_zero, zero_add, nsmul_eq_mul, hy, pow_succ', mul_assoc]
      · simp only [mul_z, mul_zero, zero_add, add_zero, nsmul_eq_mul, hz, pow_succ', mul_assoc]
        ring
    exact hprod ▸ mul_mem (mul_mem (pow_mem_closedPowerSubgroup w)
      (pow_mem_closedPowerSubgroup u)) (pow_mem_closedPowerSubgroup v)

/-- For every `1 ≤ m`, `closedPowerSubgroup p (HeisenbergGroup.level p m)` has index `p ^ 3`. -/
@[simp]
theorem index_closedPowerSubgroup_level {m : ℕ} (hm : 1 ≤ m) :
    (closedPowerSubgroup p (level p m).toSubgroup).index = p ^ 3 := by
  have hmul := Subgroup.relIndex_mul_index (level_antitone p (Nat.le_succ m))
  rw [index_level, index_level] at hmul
  rw [closedPowerSubgroup_level p hm]
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (3 * m))
  rw [← Subgroup.relIndex, hmul, ← pow_add]
  congr 1
  omega

/-- For every `(if p = 2 then 2 else 1) ≤ m`, `HeisenbergGroup.level p m` has topological
generator rank `3`. -/
@[simp]
theorem topologicalGeneratorRankNat_level {m : ℕ} (hm : (if p = 2 then 2 else 1) ≤ m) :
    topologicalGeneratorRankNat (level p m).toSubgroup
        (isUniform_level p hm).isTopologicallyFinitelyGenerated = 3 := by
  have hm1 : 1 ≤ m := by split_ifs at hm <;> omega
  rw [(isUniform_level p hm).topologicalGeneratorRankNat_eq_log_index,
    index_closedPowerSubgroup_level p hm1, Nat.log_pow hp.out.one_lt]

/-- At `p = 2`, `HeisenbergGroup.level 2 1` is not powerful: every fourth power lies in `level 2 3`,
whereas `⁅(2, 0, 0), (0, 2, 0)⁆ = (0, 0, 4) ∉ level 2 3`. -/
theorem not_isPowerful_level_two_one : ¬ IsPowerful 2 (level 2 1).toSubgroup := fun hpow ↦ by
  have hchoose : Nat.choose 4 2 = 6 := by decide
  have hle : closedPowerSubgroup 4 (level 2 1).toSubgroup ≤
      (level 2 3).toSubgroup.subgroupOf (level 2 1).toSubgroup :=
    (closedPowerSubgroup_le_iff ((level 2 3).isClosed.preimage continuous_subtypeVal)).mpr
      fun a ↦ by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_eq]
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := (mem_level_iff 2 1).mp a.property
        refine (mem_level_iff 2 3).mpr ⟨⟨x, ?_⟩, ⟨y, ?_⟩, ⟨z + 3 * (x * y), ?_⟩⟩
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one, hx]
          ring
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_one, hy]
          ring
        · simp only [nsmul_eq_mul, Nat.cast_ofNat, hchoose, pow_one, hx, hy, hz]
          ring
  let a : (level 2 1).toSubgroup :=
    ⟨⟨2, 0, 0⟩, (mem_level_iff 2 1).mpr ⟨by simp, dvd_zero _, dvd_zero _⟩⟩
  let b : (level 2 1).toSubgroup :=
    ⟨⟨0, 2, 0⟩, (mem_level_iff 2 1).mpr ⟨dvd_zero _, by simp, dvd_zero _⟩⟩
  have hz := ((mem_level_iff 2 3).mp (Subgroup.mem_subgroupOf.mp <|
    hle ((isPowerful_two_iff.mp hpow) (_root_.commutator_def (level 2 1).toSubgroup ▸
      commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
  rw [Subgroup.coe_commutatorElement, commutatorElement_z_mk_fst_snd, ← sq] at hz
  exact PadicInt.not_pow_p_succ_dvd_pow_p 2 hz

/-- At `p = 2`, `HeisenbergGroup.level 2 1` is not uniform. -/
theorem not_isUniform_level_two_one : ¬ IsUniform 2 (level 2 1).toSubgroup :=
  fun hU ↦ not_isPowerful_level_two_one hU.isPowerful

private def deepCenterSubgroup (m : ℕ) : Subgroup (level p m).toSubgroup where
  carrier := {a | (p : ℤ_[p]) ^ (2 * m) ∣ a.val.z}
  one_mem' := dvd_zero _
  mul_mem' := fun {a b} ha hb ↦ dvd_add (dvd_add ha hb) <|
    pow_two_mul_dvd_mul (p : ℤ_[p])
      ((mem_level_iff p m).mp a.property).1 ((mem_level_iff p m).mp b.property).2.1
  inv_mem' := fun {a} ha ↦ dvd_add (dvd_neg.mpr ha) <|
    pow_two_mul_dvd_mul (p : ℤ_[p])
      ((mem_level_iff p m).mp a.property).1 ((mem_level_iff p m).mp a.property).2.1

private def deepCenterPowerBound (m r : ℕ) (hr1 : 1 ≤ r) : Subgroup (HeisenbergGroup ℤ_[p]) where
  carrier := {a | (p : ℤ_[p]) ^ (m + r) ∣ a.x ∧ (p : ℤ_[p]) ^ (m + r) ∣ a.y ∧
    (p : ℤ_[p]) ^ (2 * m + 1) ∣ a.z}
  one_mem' := ⟨dvd_zero _, dvd_zero _, dvd_zero _⟩
  mul_mem' := fun {a b} ha hb ↦ ⟨dvd_add ha.1 hb.1, dvd_add ha.2.1 hb.2.1,
    dvd_add (dvd_add ha.2.2 hb.2.2) ((pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * m + 1 ≤
      (m + r) + (m + r))).trans (pow_add_dvd_mul (p : ℤ_[p]) ha.1 hb.2.1))⟩
  inv_mem' := fun {a} ha ↦ ⟨dvd_neg.mpr ha.1, dvd_neg.mpr ha.2.1,
    dvd_add (dvd_neg.mpr ha.2.2) ((pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * m + 1 ≤
      (m + r) + (m + r))).trans (pow_add_dvd_mul (p : ℤ_[p]) ha.1 ha.2.1))⟩

private theorem closedPowerSubgroup_deepCenterSubgroup_le {m : ℕ} (r : ℕ) (hr1 : 1 ≤ r)
    (hrm : r ≤ m) (hr : p ^ r = if p = 2 then 4 else p) :
    closedPowerSubgroup (if p = 2 then 4 else p) (deepCenterSubgroup p m) ≤
      ((deepCenterPowerBound p m r hr1).subgroupOf (level p m).toSubgroup).subgroupOf
        (deepCenterSubgroup p m) := by
  set e : ℕ := if p = 2 then 4 else p
  have hdvd_choose : p ∣ e.choose 2 := dvd_choose_two_ite_four hp.out
  have hM_closed : IsClosed (deepCenterPowerBound p m r hr1 : Set (HeisenbergGroup ℤ_[p])) :=
    Subgroup.isClosed_of_isOpen _ <| Subgroup.isOpen_mono (H₁ := (level p (2 * m + 1)).toSubgroup)
      (fun a ha ↦ let ⟨hx, hy, hz⟩ := (mem_level_iff p (2 * m + 1)).mp ha
        ⟨(pow_dvd_pow _ (by omega)).trans hx, (pow_dvd_pow _ (by omega)).trans hy, hz⟩)
      (level p (2 * m + 1)).isOpen
  refine (closedPowerSubgroup_le_iff
    ((hM_closed.preimage continuous_subtypeVal).preimage continuous_subtypeVal)).mpr fun a ↦ ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.coe_pow,
    pow_eq]
  obtain ⟨hax, hay, -⟩ := (mem_level_iff p m).mp a.val.property
  have he_eq : (e : ℤ_[p]) = (p : ℤ_[p]) ^ r := by rw [← hr, Nat.cast_pow]
  have hxy : (p : ℤ_[p]) ^ (2 * m) ∣ a.val.val.x * a.val.val.y :=
    pow_two_mul_dvd_mul (p : ℤ_[p]) hax hay
  obtain ⟨c, hc⟩ := hdvd_choose
  refine ⟨by dsimp only; rw [nsmul_eq_mul, he_eq, add_comm m r]
             exact pow_add_dvd_mul (p : ℤ_[p]) dvd_rfl hax,
    by dsimp only; rw [nsmul_eq_mul, he_eq, add_comm m r]
       exact pow_add_dvd_mul (p : ℤ_[p]) dvd_rfl hay,
    dvd_add ?_ ?_⟩
  · rw [nsmul_eq_mul, he_eq]
    exact (pow_dvd_pow (p : ℤ_[p]) (by omega : 2 * m + 1 ≤ r + 2 * m)).trans
      (pow_add_dvd_mul (p : ℤ_[p]) dvd_rfl a.property)
  · rw [nsmul_eq_mul, hc, Nat.cast_mul, mul_assoc, pow_succ']
    exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right hxy _)

/-- **Uniformity does not pass to arbitrary open subgroups**: for every prime `p` and every
uniform level `HeisenbergGroup.level p m` (with `(if p = 2 then 2 else 1) ≤ m`), there is an open
subgroup of `level p m` that is neither powerful nor uniform. -/
theorem exists_openSubgroup_not_isPowerful_and_not_isUniform_level {m : ℕ}
    (hm : (if p = 2 then 2 else 1) ≤ m) :
    ∃ U : OpenSubgroup (level p m).toSubgroup,
      ¬ IsPowerful p U.toSubgroup ∧ ¬ IsUniform p U.toSubgroup := by
  set r : ℕ := if p = 2 then 2 else 1
  have hr1 : 1 ≤ r := by dsimp [r]; split_ifs <;> omega
  let U : OpenSubgroup (level p m).toSubgroup := ⟨deepCenterSubgroup p m, Subgroup.isOpen_mono
    (H₁ := (level p (2 * m)).toSubgroup.subgroupOf (level p m).toSubgroup)
    (fun _ ha ↦ ((mem_level_iff p (2 * m)).mp (Subgroup.mem_subgroupOf.mp ha)).2.2)
    ((level p (2 * m)).isOpen.preimage continuous_subtypeVal)⟩
  have hnotpow : ¬ IsPowerful p U.toSubgroup := fun hpow ↦ by
    let a : U.toSubgroup := ⟨⟨⟨(p : ℤ_[p]) ^ m, 0, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_rfl, dvd_zero _, dvd_zero _⟩⟩, dvd_zero _⟩
    let b : U.toSubgroup := ⟨⟨⟨0, (p : ℤ_[p]) ^ m, 0⟩,
      (mem_level_iff p m).mpr ⟨dvd_zero _, dvd_rfl, dvd_zero _⟩⟩, dvd_zero _⟩
    have hz := (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp <|
      closedPowerSubgroup_deepCenterSubgroup_le p r hr1 hm (pow_ite_eq_ite_four p)
        ((isPowerful_iff.mp hpow) (_root_.commutator_def U.toSubgroup ▸
          commutator_mem_commutator (mem_top a) (mem_top b))))).2.2
    rw [Subgroup.coe_commutatorElement, Subgroup.coe_commutatorElement,
      commutatorElement_z_mk_fst_snd, ← pow_add, ← two_mul] at hz
    exact PadicInt.not_pow_p_succ_dvd_pow_p (2 * m) hz
  exact ⟨U, hnotpow, fun hU ↦ hnotpow hU.isPowerful⟩

end HeisenbergGroup

end TauCeti
