/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Quaternion-group infrastructure

Mathlib equips `QuaternionGroup n` with a `Fintype` instance when `n` is nonzero, but converting
that instance to a list is noncomputable.  The Dixon--Schneider character-table algorithm needs a
list whose reduction can be evaluated by the kernel.  `TauCeti.quaternionElements` lists the two
constructors at every index and `TauCeti.mem_quaternionElements` proves that the list is exhaustive.

Two elements `r` and `s` of a group `G` satisfying `s ^ 2 = r ^ n` and `s * r * s⁻¹ = r⁻¹`
automatically satisfy `r ^ (2 * n) = 1` and determine a homomorphism
`TauCeti.quaternionHom : QuaternionGroup n →* G` sending `a i` to `r ^ i` and `xa i` to
`s * r ^ i` (modeled on `TauCeti.dihedralGroupMulEquiv`), injective as soon as
`orderOf r = 2 * n` (`TauCeti.quaternionHom_injective`) and an isomorphism onto `G` when `r` and
`s` generate `G` (`TauCeti.quaternionGroupMulEquiv`).

The elements `a i` form the cyclic rotation subgroup of index two.  Its coordinate equivalence with
`Multiplicative (ZMod (2 * n))` supplies its cyclicity, and conjugation by every `xa i` inverts it.
This is the subgroup from which the two-dimensional representations of a generalized quaternion
group are induced.

For nonzero `n`, `QuaternionGroup.a n` is the unique element of order two
(`TauCeti.orderOf_eq_two_quaternionGroup_iff`), and for `n ≠ 1` the centre is
`Subgroup.zpowers (QuaternionGroup.a n)` (`TauCeti.center_quaternionGroup_eq_zpowers`).  When
`n = 2 ^ k`, `QuaternionGroup (2 ^ k)` is a `2`-group in which every nontrivial subgroup contains
`QuaternionGroup.a (2 ^ k)` (`TauCeti.quaternionGroup_a_two_pow_mem_of_ne_bot`), so no proper
nontrivial subgroup has a complement (`TauCeti.isComplement'_quaternionGroup_two_pow_iff`).  The
file also records the exponent of `QuaternionGroup 2`, the quaternion group of order eight, in the
form used by its explicit Dixon-prime certificate.

## Main definitions

* `TauCeti.quaternionElements`: a computable enumeration of `QuaternionGroup n`.
* `TauCeti.quaternionHom`, `TauCeti.quaternionGroupMulEquiv`: the homomorphism and isomorphism
  out of `QuaternionGroup n` determined by generators `r` and `s` with `s ^ 2 = r ^ n` and
  `s * r * s⁻¹ = r⁻¹`.
* `TauCeti.quaternionRotations`: the cyclic subgroup consisting of the elements `a i`.
* `TauCeti.quaternionRotationsMulEquiv`: its coordinate equivalence with
  `Multiplicative (ZMod (2 * n))`.
* `TauCeti.quaternionQuotientEquiv`: the quotient identification with `Multiplicative (ZMod 2)`.

## Main results

* `TauCeti.mem_quaternionElements`: the enumeration contains every group element.
* `TauCeti.pow_two_mul_eq_one_of_sq_eq_pow_of_conj_eq_inv`, `TauCeti.quaternionHom_injective`,
  `TauCeti.range_quaternionHom`: `s ^ 2 = r ^ n` and `s * r * s⁻¹ = r⁻¹` force `r ^ (2 * n) = 1`,
  `quaternionHom` is injective when `orderOf r = 2 * n`, and its image is `Subgroup.closure {r, s}`.
* `TauCeti.index_quaternionRotations`, `TauCeti.natCard_quaternionRotations`: the rotation subgroup
  has index `2` and cardinality `2 * n`.
* `TauCeti.conj_eq_inv_of_notMem_quaternionRotations`: an element outside the rotation subgroup
  conjugates every rotation to its inverse.
* `TauCeti.sq_eq_one_quaternionGroup_iff`, `TauCeti.orderOf_eq_two_quaternionGroup_iff`,
  `TauCeti.mem_quaternionRotations_of_sq_eq_one`: for nonzero `n`, `QuaternionGroup.a n` is the
  unique element of order two and every element squaring to `1` lies in the rotation subgroup.
* `TauCeti.center_quaternionGroup_eq_zpowers`, `TauCeti.isMulCommutative_quaternionGroup_iff`: for
  `n ≠ 1` the centre is `Subgroup.zpowers (QuaternionGroup.a n)` and `QuaternionGroup n` is
  non-commutative.
* `TauCeti.not_exists_isComplement'_zpowers_quaternionGroup_a`,
  `TauCeti.not_exists_isComplement'_center_quaternionGroup`,
  `TauCeti.not_exists_isComplement'_quaternionRotations`: for nonzero `n`, neither
  `Subgroup.zpowers (QuaternionGroup.a n)`, nor the centre (when `n ≠ 1`), nor the rotation
  subgroup admits a complement in `QuaternionGroup n`.
* `TauCeti.quaternionGroup_a_two_pow_mem_of_ne_bot`,
  `TauCeti.disjoint_subgroup_quaternionGroup_two_pow_iff`,
  `TauCeti.isComplement'_quaternionGroup_two_pow_iff`: every nontrivial subgroup of
  `QuaternionGroup (2 ^ k)` contains `QuaternionGroup.a (2 ^ k)`, so only `⊥` and `⊤` admit
  complements.
* `TauCeti.exponent_quaternionGroup_two`: `QuaternionGroup 2` has exponent four.

## References

* K. Conrad, *Generalized quaternion groups*, expository notes.
-/

public section

namespace TauCeti

/-- The elements `a 0, xa 0, ..., a (2n-1), xa (2n-1)` of `QuaternionGroup n`.  For nonzero
`n` this lists all `4 * n` elements.  The body is exposed so downstream class-data computations
can reduce it in the kernel. -/
@[expose] def quaternionElements (n : ℕ) : List (QuaternionGroup n) :=
  (List.range (2 * n)).flatMap fun i : ℕ =>
    [QuaternionGroup.a (i : ZMod (2 * n)), QuaternionGroup.xa (i : ZMod (2 * n))]

/-- The enumeration `TauCeti.quaternionElements` exhausts `QuaternionGroup n` when `n` is
nonzero. -/
theorem mem_quaternionElements {n : ℕ} [NeZero n] (g : QuaternionGroup n) :
    g ∈ quaternionElements n := by
  cases g with
  | a i | xa i => exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.val_lt, by simp⟩

/-! ## The rotation subgroup -/

variable {n : ℕ}

/-- The parity of a quaternion-group element: `0` on `a i` and `1` on `xa i`. Written
multiplicatively so its kernel is the rotation subgroup. -/
def quaternionCosetParity (n : ℕ) : QuaternionGroup n →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a _ => 1
    | QuaternionGroup.xa _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
        QuaternionGroup.xa_mul_xa] <;>
      decide

@[simp]
theorem quaternionCosetParity_a (i : ZMod (2 * n)) :
    quaternionCosetParity n (QuaternionGroup.a i) = 1 :=
  (rfl)

@[simp]
theorem quaternionCosetParity_xa (i : ZMod (2 * n)) :
    quaternionCosetParity n (QuaternionGroup.xa i) = Multiplicative.ofAdd 1 :=
  (rfl)

/-- The quaternion coset parity is onto. -/
theorem quaternionCosetParity_surjective (n : ℕ) :
    Function.Surjective (quaternionCosetParity n) := by
  intro y
  fin_cases y
  exacts [⟨QuaternionGroup.a 0, rfl⟩, ⟨QuaternionGroup.xa 0, rfl⟩]

/-- The cyclic subgroup of `QuaternionGroup n` consisting of the elements `a i`, the kernel of
the coset parity. It is normal of index `2`, and `TauCeti.quaternionRotationsMulEquiv` identifies
it with `Multiplicative (ZMod (2 * n))`. -/
def quaternionRotations (n : ℕ) : Subgroup (QuaternionGroup n) :=
  (quaternionCosetParity n).ker

instance quaternionRotations_normal (n : ℕ) : (quaternionRotations n).Normal :=
  (quaternionCosetParity n).normal_ker

/-- Membership in the quaternion rotation subgroup is being an element `a i`. Use this
characterization explicitly; the constructor membership lemmas simplify without expanding the
carrier of the subgroup. -/
theorem mem_quaternionRotations_iff {g : QuaternionGroup n} :
    g ∈ quaternionRotations n ↔ ∃ i : ZMod (2 * n), g = QuaternionGroup.a i := by
  cases g with
  | a i => exact iff_of_true (by simp [quaternionRotations, MonoidHom.mem_ker]) ⟨i, rfl⟩
  | xa i =>
    refine iff_of_false (by simp [quaternionRotations, MonoidHom.mem_ker]) ?_
    rintro ⟨j, hj⟩
    simp at hj

/-- Every element `a i` belongs to the quaternion rotation subgroup. -/
@[simp]
theorem a_mem_quaternionRotations (i : ZMod (2 * n)) :
    QuaternionGroup.a i ∈ quaternionRotations n :=
  mem_quaternionRotations_iff.mpr ⟨i, rfl⟩

/-- No element `xa i` belongs to the quaternion rotation subgroup. -/
@[simp]
theorem xa_notMem_quaternionRotations (i : ZMod (2 * n)) :
    QuaternionGroup.xa i ∉ quaternionRotations n := fun h => by
  obtain ⟨j, hj⟩ := mem_quaternionRotations_iff.mp h
  simp at hj

/-- The quaternion rotation subgroup has index two. -/
@[simp]
theorem index_quaternionRotations (n : ℕ) : (quaternionRotations n).index = 2 := by
  rw [quaternionRotations, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (quaternionCosetParity_surjective n)]
  simp

/-- The rotation subgroup has finite index, for every `n` -- including `n = 0`, where
`QuaternionGroup n` is infinite. -/
instance finiteIndex_quaternionRotations (n : ℕ) : (quaternionRotations n).FiniteIndex :=
  ⟨by simp⟩

/-- Conjugation by an element outside the quaternion rotation subgroup inverts every rotation. -/
theorem conj_eq_inv_of_notMem_quaternionRotations {s g : QuaternionGroup n}
    (hs : s ∉ quaternionRotations n) (hg : g ∈ quaternionRotations n) :
    s * g * s⁻¹ = g⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_quaternionRotations_iff.mp hg
  cases s with
  | a j => exact absurd (a_mem_quaternionRotations j) hs
  | xa j =>
    rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq, ← mul_assoc, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, sub_add_cancel]

/-- Conjugation by an element outside the quaternion rotations, read inside the normal
subgroup. -/
@[simp]
theorem conjNormal_eq_inv_of_notMem_quaternionRotations {s : QuaternionGroup n}
    (hs : s ∉ quaternionRotations n) (x : quaternionRotations n) :
    MulAut.conjNormal s x = x⁻¹ :=
  Subtype.ext (by
    rw [MulAut.conjNormal_apply]
    simpa using conj_eq_inv_of_notMem_quaternionRotations hs x.property)

/-- The rotation index of a quaternion-group element: the index `i` of `a i`, and the junk value
`0` on `xa i`. The interface is `TauCeti.quaternionRotationsMulEquiv`, which reads the index off
an element of the rotation subgroup and so never meets the junk value. -/
private def quaternionRotationIndex : QuaternionGroup n → ZMod (2 * n)
  | QuaternionGroup.a i => i
  | QuaternionGroup.xa _ => 0

private theorem a_quaternionRotationIndex {g : QuaternionGroup n}
    (hg : g ∈ quaternionRotations n) :
    QuaternionGroup.a (quaternionRotationIndex g) = g := by
  obtain ⟨i, rfl⟩ := mem_quaternionRotations_iff.mp hg
  rfl

private theorem quaternionRotationIndex_mul {g h : QuaternionGroup n}
    (hg : g ∈ quaternionRotations n) (hh : h ∈ quaternionRotations n) :
    quaternionRotationIndex (g * h) = quaternionRotationIndex g + quaternionRotationIndex h := by
  obtain ⟨i, rfl⟩ := mem_quaternionRotations_iff.mp hg
  obtain ⟨j, rfl⟩ := mem_quaternionRotations_iff.mp hh
  rw [QuaternionGroup.a_mul_a]
  rfl

/-- The quaternion rotation subgroup is `ZMod (2 * n)` written multiplicatively. -/
def quaternionRotationsMulEquiv (n : ℕ) :
    quaternionRotations n ≃* Multiplicative (ZMod (2 * n)) where
  toFun x := Multiplicative.ofAdd (quaternionRotationIndex (x : QuaternionGroup n))
  invFun i := ⟨QuaternionGroup.a (Multiplicative.toAdd i), a_mem_quaternionRotations _⟩
  left_inv x := Subtype.ext (a_quaternionRotationIndex x.property)
  right_inv _ := rfl
  map_mul' x y := congrArg Multiplicative.ofAdd (quaternionRotationIndex_mul x.property y.property)

@[simp]
theorem quaternionRotationsMulEquiv_a (i : ZMod (2 * n)) :
    quaternionRotationsMulEquiv n ⟨QuaternionGroup.a i, a_mem_quaternionRotations i⟩ =
      Multiplicative.ofAdd i :=
  (rfl)

@[simp]
theorem coe_quaternionRotationsMulEquiv_symm (i : Multiplicative (ZMod (2 * n))) :
    ((quaternionRotationsMulEquiv n).symm i : QuaternionGroup n) =
      QuaternionGroup.a (Multiplicative.toAdd i) :=
  (rfl)

/-- The rotation subgroup is cyclic, `Multiplicative (ZMod (2 * n))` being so. -/
instance isCyclic_quaternionRotations (n : ℕ) : IsCyclic (quaternionRotations n) :=
  isCyclic_of_surjective _ (quaternionRotationsMulEquiv n).symm.surjective

/-- The quotient of `QuaternionGroup n` by its rotation subgroup is `Multiplicative (ZMod 2)`,
via the coset parity homomorphism. -/
noncomputable def quaternionQuotientEquiv (n : ℕ) :
    QuaternionGroup n ⧸ quaternionRotations n ≃* Multiplicative (ZMod 2) :=
  QuotientGroup.quotientKerEquivOfSurjective (quaternionCosetParity n)
    (quaternionCosetParity_surjective n)

/-- On a coset representative `g`, `TauCeti.quaternionQuotientEquiv` is the coset parity of `g`. -/
@[simp]
theorem quaternionQuotientEquiv_mk (n : ℕ) (g : QuaternionGroup n) :
    quaternionQuotientEquiv n (g : QuaternionGroup n ⧸ quaternionRotations n) =
      quaternionCosetParity n g :=
  TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk _ _ g

/-- The quaternion group of order eight has exponent four. -/
@[simp]
theorem exponent_quaternionGroup_two : Monoid.exponent (QuaternionGroup 2) = 4 := by
  rw [QuaternionGroup.exponent]
  decide

open scoped IsMulCommutative

/-! ## Involutions, centre, and subgroup complements -/

/-- The inverse of a rotation `QuaternionGroup.a i` is `QuaternionGroup.a (-i)`. -/
@[simp]
theorem inv_quaternionGroup_a (i : ZMod (2 * n)) :
    (QuaternionGroup.a i : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-i) :=
  inv_eq_of_mul_eq_one_left (by simp)

/-- The inverse of `QuaternionGroup.xa i` is `QuaternionGroup.xa (n + i)`. -/
@[simp]
theorem inv_quaternionGroup_xa (i : ZMod (2 * n)) :
    (QuaternionGroup.xa i : QuaternionGroup n)⁻¹ = QuaternionGroup.xa ((n : ZMod (2 * n)) + i) :=
  inv_eq_of_mul_eq_one_left (by simp [sub_self])

/-- `QuaternionGroup n` has cardinality `4 * n` for every `n : ℕ`, including `n = 0` where both
sides are zero. -/
@[simp]
theorem natCard_quaternionGroup (n : ℕ) : Nat.card (QuaternionGroup n) = 4 * n := by
  rcases eq_zero_or_neZero n with rfl | hn
  · rw [Nat.card_congr QuaternionGroup.quaternionGroupZeroEquivDihedralGroupZero.toEquiv,
      DihedralGroup.nat_card]
    rfl
  · rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- The quaternion rotation subgroup has cardinality `2 * n` for every `n : ℕ` (including `n = 0`,
where both sides are zero). -/
@[simp]
theorem natCard_quaternionRotations (n : ℕ) : Nat.card (quaternionRotations n) = 2 * n := by
  have h := (quaternionRotations n).card_mul_index
  rw [index_quaternionRotations, natCard_quaternionGroup] at h
  omega

/-- For nonzero `n`, the half-turn rotation `QuaternionGroup.a n` is not the identity. -/
theorem quaternionGroup_a_self_ne_one [NeZero n] :
    (QuaternionGroup.a n : QuaternionGroup n) ≠ 1 := by
  intro h
  have hpos : 0 < n := NeZero.pos n
  rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
  exact NeZero.ne n hv

/-- The half-turn rotation `QuaternionGroup.a n` squares to the identity for every `n : ℕ`. -/
@[simp]
theorem quaternionGroup_a_self_sq (n : ℕ) :
    (QuaternionGroup.a n : QuaternionGroup n) ^ 2 = 1 := by
  rw [← QuaternionGroup.xa_sq (0 : ZMod (2 * n)), ← pow_mul, QuaternionGroup.xa_pow_four]

/-- For nonzero `n`, the half-turn rotation `QuaternionGroup.a n` has order two. -/
@[simp]
theorem orderOf_quaternionGroup_a_self [NeZero n] :
    orderOf (QuaternionGroup.a n : QuaternionGroup n) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (quaternionGroup_a_self_sq n) quaternionGroup_a_self_ne_one

/-- In `QuaternionGroup n` with `n ≠ 0`, the solutions of `g ^ 2 = 1` are `1` and
`QuaternionGroup.a n`. -/
theorem sq_eq_one_quaternionGroup_iff [NeZero n] {g : QuaternionGroup n} :
    g ^ 2 = 1 ↔ g = 1 ∨ g = QuaternionGroup.a n := by
  refine ⟨fun hg => ?_, ?_⟩
  · cases g with
    | xa i =>
      rw [QuaternionGroup.xa_sq] at hg
      exact absurd hg quaternionGroup_a_self_ne_one
    | a i =>
      rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at hg
      rcases (ZMod.neg_eq_self_iff i).mp (neg_eq_iff_add_eq_zero.mpr hg) with rfl | hi
      · exact Or.inl QuaternionGroup.a_zero
      · right
        have hval : i.val = n := Nat.eq_of_mul_eq_mul_left zero_lt_two hi
        rw [← i.natCast_zmod_val, hval]
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact quaternionGroup_a_self_sq n

/-- Every element of `QuaternionGroup n` (`n ≠ 0`) squaring to `1` belongs to the rotation
subgroup. -/
theorem mem_quaternionRotations_of_sq_eq_one {n : ℕ} [NeZero n] {x : QuaternionGroup n}
    (hx : x ^ 2 = 1) : x ∈ quaternionRotations n := by
  rcases sq_eq_one_quaternionGroup_iff.1 hx with rfl | rfl
  · exact one_mem _
  · exact a_mem_quaternionRotations _

/-- **Unique involution.** For nonzero `n`, `QuaternionGroup.a n` is the unique element of order
two in `QuaternionGroup n`. -/
theorem orderOf_eq_two_quaternionGroup_iff [NeZero n] {g : QuaternionGroup n} :
    orderOf g = 2 ↔ g = QuaternionGroup.a n := by
  refine ⟨fun h => ?_, fun h => h ▸ orderOf_quaternionGroup_a_self⟩
  rcases sq_eq_one_quaternionGroup_iff.mp (h ▸ pow_orderOf_eq_one g) with rfl | rfl
  · simp at h
  · rfl

/-- The element `QuaternionGroup.a n` is central in `QuaternionGroup n` for every `n : ℕ`. -/
theorem quaternionGroup_a_self_mem_center (n : ℕ) :
    (QuaternionGroup.a n : QuaternionGroup n) ∈ Subgroup.center (QuaternionGroup n) := by
  rw [Subgroup.mem_center_iff]
  rintro (i | i)
  · rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  · rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
    congr 1
    calc i + (n : ZMod (2 * n))
        = i - (n : ZMod (2 * n)) + ((2 * n : ℕ) : ZMod (2 * n)) := by push_cast; ring
      _ = i - (n : ZMod (2 * n)) := by rw [ZMod.natCast_self, add_zero]

/-- For `n ≠ 1`, the centre of `QuaternionGroup n` is generated by `QuaternionGroup.a n` (trivial
at `n = 0`, and of order two for `n ≥ 2`). -/
theorem center_quaternionGroup_eq_zpowers {n : ℕ} (hn : n ≠ 1) :
    Subgroup.center (QuaternionGroup n) = Subgroup.zpowers (QuaternionGroup.a n) := by
  refine le_antisymm (fun g hg => ?_)
    (Subgroup.zpowers_le.mpr (quaternionGroup_a_self_mem_center n))
  rw [Subgroup.mem_center_iff] at hg
  cases g with
  | xa i =>
    exfalso
    have h1 := hg (QuaternionGroup.a 1)
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h1
    have h2 : ((2 : ℕ) : ZMod (2 * n)) = (i + 1) - (i - 1) := by push_cast; ring
    rw [h1, sub_self] at h2
    have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp h2
    exact hn (Nat.dvd_one.mp ((mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp (by simpa using hdvd)))
  | a i =>
    have h0 := hg (QuaternionGroup.xa 0)
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, zero_add, zero_sub,
      QuaternionGroup.xa.injEq] at h0
    rcases (ZMod.neg_eq_self_iff i).mp h0.symm with rfl | hi
    · rw [QuaternionGroup.a_zero]
      exact one_mem _
    · rcases eq_zero_or_neZero n with rfl | _
      · have hi0 : i = 0 := i.val_eq_zero.mp (by omega)
        rw [hi0, QuaternionGroup.a_zero]
        exact one_mem _
      · have hval : i.val = n := Nat.eq_of_mul_eq_mul_left zero_lt_two hi
        rw [← i.natCast_zmod_val, hval]
        exact Subgroup.mem_zpowers _

/-- `QuaternionGroup n` is commutative if and only if `n = 1` (where it is cyclic of order four). -/
@[simp]
theorem isMulCommutative_quaternionGroup_iff {n : ℕ} :
    IsMulCommutative (QuaternionGroup n) ↔ n = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hn
    have hmem : (QuaternionGroup.xa 0 : QuaternionGroup n) ∈
        Subgroup.zpowers (QuaternionGroup.a n) := by
      rw [← center_quaternionGroup_eq_zpowers hn, Subgroup.center_eq_top]
      exact Subgroup.mem_top _
    exact xa_notMem_quaternionRotations 0
      (Subgroup.zpowers_le.mpr (a_mem_quaternionRotations n) hmem)
  · rintro rfl
    exact QuaternionGroup.quaternionGroup_one_isCyclic.isMulCommutative

/-- For `n ≠ 1`, `QuaternionGroup n` is not commutative. -/
theorem not_isMulCommutative_quaternionGroup {n : ℕ} (hn : n ≠ 1) :
    ¬ IsMulCommutative (QuaternionGroup n) :=
  mt isMulCommutative_quaternionGroup_iff.mp hn

/-- For nonzero `n`, the subgroup of order two generated by `QuaternionGroup.a n` has no complement
in `QuaternionGroup n`. -/
theorem not_exists_isComplement'_zpowers_quaternionGroup_a (n : ℕ) [NeZero n] :
    ¬ ∃ K : Subgroup (QuaternionGroup n),
      (Subgroup.zpowers (QuaternionGroup.a n)).IsComplement' K := by
  rintro ⟨K, hK⟩
  have hcard := hK.card_mul_card
  rw [Nat.card_zpowers, orderOf_quaternionGroup_a_self, natCard_quaternionGroup] at hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 ⟨n, by omega⟩
  rw [← Subgroup.orderOf_coe, orderOf_eq_two_quaternionGroup_iff] at hk
  exact quaternionGroup_a_self_ne_one
    (Subgroup.disjoint_def.mp hK.disjoint (Subgroup.mem_zpowers _) (hk ▸ k.property))

/-- For `n ≠ 0` and `n ≠ 1`, the centre of `QuaternionGroup n` has no complement in
`QuaternionGroup n`. -/
theorem not_exists_isComplement'_center_quaternionGroup {n : ℕ} [NeZero n] (hn : n ≠ 1) :
    ¬ ∃ K : Subgroup (QuaternionGroup n),
      (Subgroup.center (QuaternionGroup n)).IsComplement' K := by
  rw [center_quaternionGroup_eq_zpowers hn]
  exact not_exists_isComplement'_zpowers_quaternionGroup_a n

/-- For nonzero `n`, the cyclic rotation subgroup of index two in `QuaternionGroup n` has no
complement. -/
theorem not_exists_isComplement'_quaternionRotations (n : ℕ) [NeZero n] :
    ¬ ∃ K : Subgroup (QuaternionGroup n),
      (quaternionRotations n).IsComplement' K := by
  rintro ⟨K, hK⟩
  obtain ⟨⟨⟨r, hr⟩, ⟨k, hk⟩⟩, hrk⟩ := (hK.existsUnique (QuaternionGroup.xa 0)).exists
  cases k with
  | a i => exact xa_notMem_quaternionRotations 0 (hrk ▸ mul_mem hr (a_mem_quaternionRotations i))
  | xa i =>
    have haK : (QuaternionGroup.a n : QuaternionGroup n) ∈ K :=
      QuaternionGroup.xa_sq i ▸ pow_mem hk 2
    exact quaternionGroup_a_self_ne_one
      (Subgroup.disjoint_def.mp hK.disjoint (a_mem_quaternionRotations n) haK)

/-- The generalized quaternion group `QuaternionGroup (2 ^ k)` has cardinality `2 ^ (k + 2)`. -/
theorem natCard_quaternionGroup_two_pow (k : ℕ) :
    Nat.card (QuaternionGroup (2 ^ k)) = 2 ^ (k + 2) := by
  rw [natCard_quaternionGroup]
  ring

/-- The generalized quaternion group `QuaternionGroup (2 ^ k)` is a `2`-group. -/
theorem isPGroup_quaternionGroup_two_pow (k : ℕ) : IsPGroup 2 (QuaternionGroup (2 ^ k)) :=
  IsPGroup.of_card (natCard_quaternionGroup_two_pow k)

/-- **Every nontrivial subgroup of `QuaternionGroup (2 ^ k)` contains `a ((2 ^ k : ℕ) : _)`.** Thus
`Subgroup.zpowers (QuaternionGroup.a ((2 ^ k : ℕ) : _))` is the unique minimal nontrivial subgroup
of `QuaternionGroup (2 ^ k)`. -/
theorem quaternionGroup_a_two_pow_mem_of_ne_bot {k : ℕ}
    {H : Subgroup (QuaternionGroup (2 ^ k))} (hH : H ≠ ⊥) :
    QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card H :=
    ((isPGroup_quaternionGroup_two_pow k).to_subgroup H).card_eq_or_dvd.resolve_left
      (mt Subgroup.card_eq_one.mp hH)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 hdvd
  rw [← Subgroup.orderOf_coe, orderOf_eq_two_quaternionGroup_iff] at hx
  exact hx ▸ x.property

/-- Two subgroups of `QuaternionGroup (2 ^ k)` are disjoint if and only if at least one of them is
trivial. -/
theorem disjoint_subgroup_quaternionGroup_two_pow_iff {k : ℕ}
    {H K : Subgroup (QuaternionGroup (2 ^ k))} :
    Disjoint H K ↔ H = ⊥ ∨ K = ⊥ := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hne
    exact quaternionGroup_a_self_ne_one (Subgroup.disjoint_def.mp h
      (quaternionGroup_a_two_pow_mem_of_ne_bot hne.1)
      (quaternionGroup_a_two_pow_mem_of_ne_bot hne.2))
  · rintro (rfl | rfl) <;> simp

/-- **Subgroup complements in `QuaternionGroup (2 ^ k)`.** Only `⊥` and `⊤` have complements in
`QuaternionGroup (2 ^ k)`. -/
theorem isComplement'_quaternionGroup_two_pow_iff {k : ℕ}
    {H K : Subgroup (QuaternionGroup (2 ^ k))} :
    H.IsComplement' K ↔ (H = ⊥ ∧ K = ⊤) ∨ (H = ⊤ ∧ K = ⊥) := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases disjoint_subgroup_quaternionGroup_two_pow_iff.mp h.disjoint with rfl | rfl
    · exact Or.inl ⟨rfl, Subgroup.isComplement'_bot_left.mp h⟩
    · exact Or.inr ⟨Subgroup.isComplement'_bot_right.mp h, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Subgroup.isComplement'_bot_top
    · exact Subgroup.isComplement'_top_bot

/-! ## Recognizing a generalized quaternion group -/

section Recognition

variable {G : Type*} [Group G] {r s : G}

/-- In any group, the dicyclic relations `s ^ 2 = r ^ n` and `s * r * s⁻¹ = r⁻¹` force
`r ^ (2 * n) = 1`. -/
theorem pow_two_mul_eq_one_of_sq_eq_pow_of_conj_eq_inv
    (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) : r ^ (2 * n) = 1 := by
  -- Conjugating `r ^ n = s ^ 2` by `s` both inverts and fixes `r ^ n`.
  have hconj_pow : s * r ^ n * s⁻¹ = (r ^ n)⁻¹ := by
    simpa [inv_pow] using congrArg (· ^ n) hconj
  have hfix : s * r ^ n * s⁻¹ = r ^ n := by
    rw [← hs, sq]
    group
  have hinv : (r ^ n)⁻¹ = r ^ n := hconj_pow.symm.trans hfix
  rw [two_mul, pow_add]
  nth_rw 1 [← hinv]
  exact inv_mul_cancel _

private def quaternionFun (r s : G) : QuaternionGroup n → G
  | .a i => r ^ (ZMod.cast i : ℤ)
  | .xa i => s * r ^ (ZMod.cast i : ℤ)

private lemma quaternionFun_a (r s : G) (i : ZMod (2 * n)) :
    quaternionFun r s (.a i) = r ^ (ZMod.cast i : ℤ) := rfl

private lemma quaternionFun_xa (r s : G) (i : ZMod (2 * n)) :
    quaternionFun r s (.xa i) = s * r ^ (ZMod.cast i : ℤ) := rfl

private theorem quaternionFun_a_intCast (hr : r ^ (2 * n) = 1) (k : ℤ) :
    quaternionFun r s (.a (k : ZMod (2 * n))) = r ^ k := by
  rw [quaternionFun_a, zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd ((orderOf_dvd_of_pow_eq_one hr).natCast)
  rw [← ZMod.intCast_eq_intCast_iff, ZMod.intCast_zmod_cast]

private theorem quaternionFun_a_props (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) :
    (∀ i j : ZMod (2 * n),
      quaternionFun r s (.a (i + j)) = quaternionFun r s (.a i) * quaternionFun r s (.a j)) ∧
    (∀ i : ZMod (2 * n), quaternionFun r s (.a (-i)) = (quaternionFun r s (.a i))⁻¹) ∧
    quaternionFun r s (.a (n : ZMod (2 * n))) = r ^ n := by
  have hr : r ^ (2 * n) = 1 := pow_two_mul_eq_one_of_sq_eq_pow_of_conj_eq_inv hs hconj
  refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
  · conv_lhs => rw [← ZMod.intCast_zmod_cast i, ← ZMod.intCast_zmod_cast j, ← Int.cast_add]
    rw [quaternionFun_a_intCast hr, zpow_add, quaternionFun_a, quaternionFun_a]
  · conv_lhs => rw [← ZMod.intCast_zmod_cast i, ← Int.cast_neg]
    rw [quaternionFun_a_intCast hr, zpow_neg, quaternionFun_a]
  · rw [← Int.cast_natCast n, quaternionFun_a_intCast hr, zpow_natCast]

private theorem quaternionFun_mul (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (x y : QuaternionGroup n) :
    quaternionFun r s (x * y) = quaternionFun r s x * quaternionFun r s y := by
  obtain ⟨hadd, hneg, hfn⟩ := quaternionFun_a_props hs hconj
  simp only [quaternionFun_a] at hadd hneg hfn
  have hconj' : s⁻¹ * r * s = r⁻¹ := inv_injective (by
    calc (s⁻¹ * r * s)⁻¹ = s⁻¹ * r⁻¹ * s := by group
      _ = s⁻¹ * (s * r * s⁻¹) * s := by rw [hconj]
      _ = (r⁻¹)⁻¹ := by group)
  have hmove (i : ZMod (2 * n)) :
      r ^ (ZMod.cast i : ℤ) * s = s * r ^ (ZMod.cast (-i) : ℤ) := by
    have hkey : s⁻¹ * r ^ (ZMod.cast i : ℤ) * s = (r ^ (ZMod.cast i : ℤ))⁻¹ := by
      simpa only [MulAut.conj_apply, inv_inv, hconj', inv_zpow] using
        map_zpow (MulAut.conj s⁻¹) r (ZMod.cast i : ℤ)
    rw [hneg, ← hkey, ← mul_assoc, mul_inv_cancel_left]
  rcases x with i | i <;> rcases y with j | j
  · rw [QuaternionGroup.a_mul_a, quaternionFun_a, quaternionFun_a, quaternionFun_a, hadd]
  · rw [QuaternionGroup.a_mul_xa, quaternionFun_xa, quaternionFun_a, quaternionFun_xa,
      ← mul_assoc, hmove, mul_assoc, ← hadd, neg_add_eq_sub]
  · rw [QuaternionGroup.xa_mul_a, quaternionFun_xa, quaternionFun_xa, quaternionFun_a,
      mul_assoc, hadd]
  · have hidx : (n : ZMod (2 * n)) + j - i = ((n : ZMod (2 * n)) + -i) + j := by ring
    rw [QuaternionGroup.xa_mul_xa, hidx, quaternionFun_a, quaternionFun_xa, quaternionFun_xa,
      hadd, hadd, hfn, ← hs, sq]
    calc s * s * r ^ (ZMod.cast (-i) : ℤ) * r ^ (ZMod.cast j : ℤ)
        = s * (s * r ^ (ZMod.cast (-i) : ℤ)) * r ^ (ZMod.cast j : ℤ) := by group
      _ = s * (r ^ (ZMod.cast i : ℤ) * s) * r ^ (ZMod.cast j : ℤ) := by rw [hmove]
      _ = s * r ^ (ZMod.cast i : ℤ) * (s * r ^ (ZMod.cast j : ℤ)) := by group

/-- **The homomorphism out of `QuaternionGroup n` determined by dicyclic generators.** Given `r, s`
in a group `G` satisfying `s ^ 2 = r ^ n` and `s * r * s⁻¹ = r⁻¹`, this sends `a i` to
`r ^ (ZMod.cast i : ℤ)` and `xa i` to `s * r ^ (ZMod.cast i : ℤ)`. No separate hypothesis
`r ^ (2 * n) = 1` is needed, as it follows from the two relations; the construction covers `n = 0`
as well. -/
def quaternionHom (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) :
    QuaternionGroup n →* G where
  toFun := quaternionFun r s
  map_one' := by simp only [QuaternionGroup.one_def, quaternionFun_a, ZMod.cast_zero, zpow_zero]
  map_mul' := quaternionFun_mul hs hconj

/-- `TauCeti.quaternionHom` sends the rotation `a i` to `r ^ (ZMod.cast i : ℤ)`. -/
@[simp]
theorem quaternionHom_a (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) (i : ZMod (2 * n)) :
    quaternionHom hs hconj (.a i) = r ^ (ZMod.cast i : ℤ) := (rfl)

/-- `TauCeti.quaternionHom` sends `xa i` to `s * r ^ (ZMod.cast i : ℤ)`. -/
@[simp]
theorem quaternionHom_xa (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) (i : ZMod (2 * n)) :
    quaternionHom hs hconj (.xa i) = s * r ^ (ZMod.cast i : ℤ) := (rfl)

/-- The image of `TauCeti.quaternionHom` is the subgroup generated by `r` and `s`. -/
theorem range_quaternionHom (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹) :
    (quaternionHom hs hconj).range = Subgroup.closure {r, s} := by
  have hr2n : r ^ (2 * n) = 1 := pow_two_mul_eq_one_of_sq_eq_pow_of_conj_eq_inv hs hconj
  have hone : r ^ (ZMod.cast (1 : ZMod (2 * n)) : ℤ) = r := by
    rw [← quaternionFun_a r s, ← Int.cast_one, quaternionFun_a_intCast hr2n, zpow_one]
  have hrmem : r ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsmem : s ∈ Subgroup.closure ({r, s} : Set G) := Subgroup.subset_closure (by simp)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨i | i, rfl⟩
    · simpa only [quaternionHom_a] using zpow_mem hrmem (ZMod.cast i : ℤ)
    · simpa only [quaternionHom_xa] using mul_mem hsmem (zpow_mem hrmem (ZMod.cast i : ℤ))
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨QuaternionGroup.a 1, by rw [quaternionHom_a, hone]⟩
    · exact ⟨QuaternionGroup.xa 0, by simp⟩

/-- **Injectivity of `TauCeti.quaternionHom`.** When `r` has exact order `2 * n`, the homomorphism
`TauCeti.quaternionHom hs hconj` is injective (including at `n = 0` and `n = 1`). -/
theorem quaternionHom_injective (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (hr : orderOf r = 2 * n) : Function.Injective (quaternionHom hs hconj) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) hi
  · rw [quaternionHom_a, ← zpow_zero r, zpow_eq_zpow_iff_modEq, hr,
      ← ZMod.intCast_eq_intCast_iff, ZMod.intCast_zmod_cast, Int.cast_zero] at hi
    rw [hi, QuaternionGroup.a_zero]
  · rw [quaternionHom_xa] at hi
    exfalso
    have hzpow : s = r ^ (-(ZMod.cast i : ℤ)) := by
      rw [zpow_neg, eq_inv_iff_mul_eq_one]
      exact hi
    have hcomm : Commute s r := hzpow ▸ (Commute.refl r).zpow_left _
    have hinv : r⁻¹ = r := by rw [← hconj, hcomm.eq, mul_inv_cancel_right]
    have hr2 : r ^ 2 = 1 := by
      rw [sq]
      nth_rw 1 [← hinv]
      exact inv_mul_cancel _
    have hord_pos : 0 < orderOf r :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, zero_lt_two, hr2⟩)
    have hord_le : orderOf r ≤ 2 := Nat.le_of_dvd zero_lt_two (orderOf_dvd_of_pow_eq_one hr2)
    have hn1 : n = 1 := by omega
    subst hn1
    have hr1 : r = 1 := by
      calc r = s ^ 2 := by simpa using hs.symm
        _ = (r ^ (-(ZMod.cast i : ℤ))) ^ (2 : ℤ) := by rw [hzpow, zpow_two, sq]
        _ = (r ^ (2 : ℤ)) ^ (-(ZMod.cast i : ℤ)) := by rw [← zpow_mul, mul_comm, zpow_mul]
        _ = 1 := by rw [zpow_two, ← sq, hr2, one_zpow]
    rw [hr1, orderOf_one] at hr
    omega

/-- When `r` and `s` generate `G` and `orderOf r = 2 * n`, `TauCeti.quaternionHom` is bijective. -/
theorem quaternionHom_bijective (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (hr : orderOf r = 2 * n) (hgen : Subgroup.closure ({r, s} : Set G) = ⊤) :
    Function.Bijective (quaternionHom hs hconj) :=
  ⟨quaternionHom_injective hs hconj hr,
    MonoidHom.range_eq_top.mp (by rw [range_quaternionHom, hgen])⟩

/-- **Recognizing a generalized quaternion group.** A group generated by `r` and `s` satisfying
`s ^ 2 = r ^ n`, `s * r * s⁻¹ = r⁻¹`, and `orderOf r = 2 * n` is isomorphic to
`QuaternionGroup n` via `TauCeti.quaternionHom`. -/
noncomputable def quaternionGroupMulEquiv (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (hr : orderOf r = 2 * n) (hgen : Subgroup.closure ({r, s} : Set G) = ⊤) :
    QuaternionGroup n ≃* G :=
  MulEquiv.ofBijective (quaternionHom hs hconj) (quaternionHom_bijective hs hconj hr hgen)

/-- `TauCeti.quaternionGroupMulEquiv` agrees with `TauCeti.quaternionHom` on elements. -/
@[simp]
theorem quaternionGroupMulEquiv_apply (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (hr : orderOf r = 2 * n) (hgen : Subgroup.closure ({r, s} : Set G) = ⊤)
    (x : QuaternionGroup n) :
    quaternionGroupMulEquiv hs hconj hr hgen x = quaternionHom hs hconj x :=
  MulEquiv.ofBijective_apply _ _ x

/-- Existential form of `TauCeti.quaternionGroupMulEquiv`. -/
theorem nonempty_quaternionGroup_mulEquiv (hs : s ^ 2 = r ^ n) (hconj : s * r * s⁻¹ = r⁻¹)
    (hr : orderOf r = 2 * n) (hgen : Subgroup.closure ({r, s} : Set G) = ⊤) :
    Nonempty (QuaternionGroup n ≃* G) :=
  ⟨quaternionGroupMulEquiv hs hconj hr hgen⟩

end Recognition

end TauCeti
