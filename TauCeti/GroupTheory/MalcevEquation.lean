/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.GroupTheory.CSA
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Vaught's condition and Malcev's equation

A group `H` satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise. By Lyndon's theorem every free group does (`IsFreeGroup.isVaught`, in
`TauCeti.GroupTheory.FreeGroup.Vaught`), while the dihedral group of order `8` does not. In a
torsion-free CSA group satisfying Vaught's condition and containing two noncommuting elements `a`
and `b`, Malcev's equation `x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` has only the trivial
solution `x = y = 1`. Thus the single word `malcevWord a b x y` vanishes exactly when both `x` and
`y` do. In a CSA group, `x = 1 ∨ y = 1` holds exactly when `x` commutes with `y`, `a * y * a⁻¹` and
`b * y * b⁻¹` (`Group.IsCSA.eq_one_or_eq_one_iff_commute_conj`); combining these three
commutators with Malcev's word gives one word `malcevOrWord a b x y` that vanishes exactly when
`x` or `y` does. These words reduce conjunctions and disjunctions of equations to a single
equation; see `TauCeti.GroupTheory.GroupAlgGeom.SingleEquation`.

Two facts about the equation `x ^ 2 * y ^ 2 * z ^ 2 = 1` in arbitrary groups lead to Lyndon's
theorem. If `x * y * z` commutes with `x` and `y` and squares to the identity, then `x`, `y` and
`z` commute pairwise. If the abelianization of the group is torsion-free, then `x * y * z` lies
in the commutator subgroup; since the commutators of the dihedral group of order `8` are central
and square to the identity, every homomorphism to that dihedral group sends `x`, `y` and `z` to
pairwise commuting elements.

## Main definitions

* `Group.IsVaught G`: Vaught's condition `x ^ 2 * y ^ 2 * z ^ 2 = 1 → [x, y] = [x, z] = [y, z] = 1`.
* `TauCeti.malcevWord a b x y`: Malcev's word `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`.
* `TauCeti.malcevOrWord a b x y`: a word vanishing exactly when `x` or `y` does.

## Main results

* `Group.isVaught_iff_commute`: Vaught's condition is equivalent to the quasi-identity
  `x ^ 2 * y ^ 2 * z ^ 2 = 1 → x * y = y * x`.
* `Group.not_isVaught_dihedralGroup_four`: the dihedral group of order `8` does not satisfy
  Vaught's condition.
* `Group.IsVaught.isMulCommutative_closure`: in a group satisfying Vaught's condition, a solution
  of `x ^ 2 * y ^ 2 * z ^ 2 = 1` generates a commutative subgroup.
* `TauCeti.pairwise_commute_of_sq_mul_sq_mul_sq_eq_one_of_commute`: if
  `a ^ 2 * b ^ 2 * c ^ 2 = 1` and `a * b * c` commutes with `a` and `b` and squares to the
  identity, then `a`, `b` and `c` commute pairwise.
* `TauCeti.pairwise_commute_map_dihedralGroup_four_of_sq_mul_sq_mul_sq_eq_one`: in a group with
  torsion-free abelianization, every homomorphism to the dihedral group of order `8` sends a
  solution of `x ^ 2 * y ^ 2 * z ^ 2 = 1` to pairwise commuting elements.
* `Group.IsVaught.malcevWord_eq_one_iff`: Malcev's equation has only the trivial solution.
* `Group.IsVaught.malcevOrWord_eq_one_iff`: the disjunction as a single word.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1, Definition 7, Lemmas 3–4.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemmas 3–4.
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

open scoped commutatorElement

namespace Group

variable (G : Type*) [Group G]

/-- A group satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise. By Lyndon's theorem every free group satisfies it
(`IsFreeGroup.isVaught`). -/
def IsVaught : Prop :=
  ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z

/-- The defining condition for Vaught's condition. -/
theorem isVaught_iff : IsVaught G ↔
    ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z :=
  Iff.rfl

/-- Vaught's condition is equivalent to the quasi-identity
`x ^ 2 * y ^ 2 * z ^ 2 = 1 → x * y = y * x`, which only asks `x` and `y` to commute. -/
theorem isVaught_iff_commute :
    IsVaught G ↔ ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y :=
  ⟨fun hG x y z h => (hG x y z h).1, fun hG x y z h => ⟨hG x y z h,
    -- The other two relations: apply the quasi-identity to the cyclic rotations of `(x, y, z)`.
    (hG z x y (by rwa [mul_assoc, mul_eq_one_comm])).symm,
    hG y z x (by rwa [mul_eq_one_comm, ← mul_assoc])⟩⟩

/-- The dihedral group of order `8` does not satisfy Vaught's condition: for the rotation `r 1` and
the reflection `sr 0`, the product `r 1 ^ 2 * sr 0 ^ 2 * r 1 ^ 2` is trivial although `r 1` and
`sr 0` do not commute. -/
theorem not_isVaught_dihedralGroup_four : ¬IsVaught (DihedralGroup 4) := fun h =>
  absurd (h (DihedralGroup.r 1) (DihedralGroup.sr 0) (DihedralGroup.r 1) (by decide)).1.eq
    (by decide)

variable {G}

/-- In a group satisfying Vaught's condition, elements `x`, `y` and `z` with
`x ^ 2 * y ^ 2 * z ^ 2 = 1` generate a commutative subgroup. -/
theorem IsVaught.isMulCommutative_closure (hG : IsVaught G) {x y z : G}
    (h : x ^ 2 * y ^ 2 * z ^ 2 = 1) : IsMulCommutative (Subgroup.closure ({x, y, z} : Set G)) := by
  obtain ⟨hxy, hxz, hyz⟩ := hG x y z h
  exact Subgroup.isMulCommutative_closure <| by
    simp [Set.pairwise_insert, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm]

end Group

namespace TauCeti

open Group

variable {G H : Type*} [Group G] [Group H]

/-- If `a ^ 2 * b ^ 2 * c ^ 2 = 1` and `a * b * c` commutes with `a` and `b` and squares to the
identity, then `a`, `b` and `c` commute pairwise. -/
theorem pairwise_commute_of_sq_mul_sq_mul_sq_eq_one_of_commute {a b c : G}
    (ha : Commute a (a * b * c)) (hb : Commute b (a * b * c)) (hc2 : (a * b * c) ^ 2 = 1)
    (h : a ^ 2 * b ^ 2 * c ^ 2 = 1) : ({a, b, c} : Set G).Pairwise Commute := by
  have hck : c = (a * b)⁻¹ * (a * b * c) := by group
  have hab : Commute a b := by
    have hc' : c ^ 2 = (a * b)⁻¹ ^ 2 := by
      rw [hck, (ha.mul_left hb).inv_left.mul_pow, hc2, mul_one]
    have : a ^ 2 * b ^ 2 * c ^ 2 = a * ⁅a, b⁆ * a⁻¹ := by
      rw [hc']
      simp only [commutatorElement_def, sq]
      group
    rw [← commutatorElement_eq_one_iff_commute]
    simpa [h] using this.symm
  have hac : Commute a c := hck ▸ ((Commute.refl a).mul_right hab).inv_right.mul_right ha
  have hbc : Commute b c := hck ▸ (hab.symm.mul_right (Commute.refl b)).inv_right.mul_right hb
  simp [Set.pairwise_insert, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

/-- In a group with torsion-free abelianization, every homomorphism to the dihedral group of order
`8` sends a solution of `x ^ 2 * y ^ 2 * z ^ 2 = 1` to pairwise commuting elements. -/
theorem pairwise_commute_map_dihedralGroup_four_of_sq_mul_sq_mul_sq_eq_one
    [IsMulTorsionFree (Group.Abelianization G)] {x y z : G} (h : x ^ 2 * y ^ 2 * z ^ 2 = 1)
    (π : G →* DihedralGroup 4) : ({π x, π y, π z} : Set (DihedralGroup 4)).Pairwise Commute := by
  have h2 : Group.Abelianization.of (x * y * z) ^ 2 = 1 := by
    rw [← map_one Group.Abelianization.of, ← h]
    simp [mul_pow]
  have hk : x * y * z ∈ commutator G :=
    Group.Abelianization.of_eq_one_iff.1 ((pow_eq_one_iff_left two_ne_zero).1 h2)
  have hc : π (x * y * z) ∈ Subgroup.center (DihedralGroup 4) := by
    have := Subgroup.mem_map_of_mem π hk
    rw [map_commutator_eq] at this
    apply commutator_le_center_dihedralGroup_iff.2 dvd_rfl
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top this
  have hc' : π x * π y * π z ∈ Subgroup.center (DihedralGroup 4) := by simpa using hc
  exact pairwise_commute_of_sq_mul_sq_mul_sq_eq_one_of_commute (Subgroup.mem_center_iff.1 hc' _)
    (Subgroup.mem_center_iff.1 hc' _) (by simpa using sq_eq_one_of_mem_center_dihedralGroup hc)
    (by simpa using congrArg π h)

/-- Malcev's word `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`. It vanishes exactly when
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2`, which in a torsion-free CSA group satisfying
Vaught's condition, with `a` and `b` not commuting, means `x = 1` and `y = 1`. -/
def malcevWord (a b x y : G) : G :=
  x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹

/-- A word in `x` and `y` with constants `a` and `b`, built from Malcev's word and the
commutators of `x` with `y`, `a * y * a⁻¹` and `b * y * b⁻¹`. In a torsion-free CSA group
satisfying Vaught's condition, with `a` and `b` not commuting, it vanishes exactly when `x = 1`
or `y = 1`. -/
def malcevOrWord (a b x y : G) : G :=
  malcevWord a b ⁅x, y⁆ (malcevWord a b ⁅x, a * y * a⁻¹⁆ ⁅x, b * y * b⁻¹⁆)

/-- The defining equation of Malcev's word, in every group. -/
theorem malcevWord_def (a b x y : G) :
    malcevWord a b x y = x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹ := (rfl)

/-- The defining equation of `malcevOrWord` in terms of Malcev's word, in every group. -/
theorem malcevOrWord_def (a b x y : G) :
    malcevOrWord a b x y =
      malcevWord a b ⁅x, y⁆ (malcevWord a b ⁅x, a * y * a⁻¹⁆ ⁅x, b * y * b⁻¹⁆) := (rfl)

/-- Malcev's word vanishes exactly when Malcev's equation holds. -/
theorem malcevWord_eq_one_iff_eq {a b x y : G} :
    malcevWord a b x y = 1 ↔ x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2 :=
  mul_inv_eq_one

@[simp]
theorem map_malcevWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevWord a b x y) = malcevWord (f a) (f b) (f x) (f y) := by
  simp [malcevWord]

@[simp]
theorem map_malcevOrWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevOrWord a b x y) = malcevOrWord (f a) (f b) (f x) (f y) := by
  simp [malcevOrWord, map_commutatorElement]

/-- The trivial solution of Malcev's equation, in every group. -/
@[simp]
theorem malcevWord_one_one (a b : G) : malcevWord a b 1 1 = 1 := by
  simp [malcevWord]

/-- `malcevOrWord a b x y` vanishes when `x = 1`, in every group. -/
@[simp]
theorem malcevOrWord_one_left (a b y : G) : malcevOrWord a b 1 y = 1 := by
  simp [malcevOrWord]

/-- `malcevOrWord a b x y` vanishes when `y = 1`, in every group. -/
@[simp]
theorem malcevOrWord_one_right (a b x : G) : malcevOrWord a b x 1 = 1 := by
  simp [malcevOrWord]

/-- **Malcev's equation** (Kharlampovich–Myasnikov, Lemma 3). In a torsion-free CSA group
satisfying Vaught's condition, if `a` and `b` do not commute, then
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` holds only for `x = y = 1`. -/
theorem _root_.Group.IsVaught.malcevWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevWord a b x y = 1 ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h => ?_, fun ⟨hx, hy⟩ => by simp [hx, hy]⟩
  have hT := (isCommTransitive_iff G).1 hG.isCommTransitive
  have := hG.isCommTransitive.hasUniqueRoots
  have hconj := (isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2
  set r := y * b * y * b⁻¹ with hr
  have heq : x ^ 2 * a * x ^ 2 * a⁻¹ = r ^ 2 := malcevWord_eq_one_iff_eq.1 h
  -- Vaught's condition for `x`, `a * x * a⁻¹` and `r⁻¹` makes `x` commute with `a * x * a⁻¹`.
  have h₁ : x ^ 2 * (a * x * a⁻¹) ^ 2 * r⁻¹ ^ 2 = 1 := by
    rw [conj_pow, inv_pow, mul_inv_eq_one, ← heq]
    group
  obtain ⟨hxa, -, -⟩ := hV _ _ _ h₁
  obtain rfl | hx := eq_or_ne x 1
  · -- Then `r ^ 2 = 1`, so `r = 1`, that is `(y * b) ^ 2 = b ^ 2`, and `y * b = b`.
    have hr₁ : y * b * y * b⁻¹ = 1 := (pow_eq_one_iff_left two_ne_zero).1 <| by
      rw [← hr, ← heq]
      group
    have hyb : (y * b) ^ 2 = b ^ 2 :=
      calc (y * b) ^ 2 = y * b * y * b := by rw [sq]; group
        _ = b ^ 2 := by rw [mul_inv_eq_one.1 hr₁, sq]
    exact ⟨rfl, mul_eq_right.1 (pow_left_injective two_ne_zero hyb)⟩
  · -- Otherwise `x` commutes with `a`, so `r ^ 2 = x ^ 4` and `r = x ^ 2`. Vaught's condition for
    -- `y * b`, `b⁻¹` and `x⁻¹` then makes `x` commute with `b`, hence `a` with `b`.
    have hax : Commute a (x ^ 2) := (hconj x a hx hxa).symm.pow_right 2
    have hrx : r = x ^ 2 := pow_left_injective two_ne_zero (by
      rw [← heq, mul_assoc (x ^ 2), hax.eq, ← mul_assoc, mul_inv_cancel_right, sq (x ^ 2)] :
        r ^ 2 = (x ^ 2) ^ 2)
    have h₂ : (y * b) ^ 2 * b⁻¹ ^ 2 * x⁻¹ ^ 2 = 1 := by
      rw [inv_pow, inv_pow, ← hrx, hr, sq (y * b)]
      group
    obtain ⟨-, -, hbx⟩ := hV _ _ _ h₂
    exact (hab (hT a x b hx (hconj x a hx hxa).symm (Commute.inv_inv_iff.1 hbx).symm)).elim

/-- In a torsion-free CSA group satisfying Vaught's condition, if `a` and `b` do not commute,
then `malcevOrWord a b x y` vanishes exactly when `x = 1` or `y = 1`. -/
theorem _root_.Group.IsVaught.malcevOrWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevOrWord a b x y = 1 ↔ x = 1 ∨ y = 1 := by
  rw [hG.eq_one_or_eq_one_iff_commute_conj hab, malcevOrWord, hV.malcevWord_eq_one_iff hG hab,
    hV.malcevWord_eq_one_iff hG hab]
  simp only [commutatorElement_eq_one_iff_commute]

end TauCeti
