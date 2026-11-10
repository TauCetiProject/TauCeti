/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Quaternion-group infrastructure

Mathlib equips `QuaternionGroup n` with a `Fintype` instance when `n` is nonzero, but converting
that instance to a list is noncomputable.  The Dixon--Schneider character-table algorithm needs a
list whose reduction can be evaluated by the kernel.  `TauCeti.quaternionElements` lists the two
constructors at every index and `TauCeti.mem_quaternionElements` proves that the list is exhaustive.

The elements `a i` form the cyclic rotation subgroup of index two.  Its coordinate equivalence with
`Multiplicative (ZMod (2 * n))` supplies its cyclicity, and conjugation by every `xa i` inverts it.
This is the subgroup from which the two-dimensional representations of a generalized quaternion
group are induced.  The file also records the exponent of `QuaternionGroup 2`, the quaternion
group of order eight, in the form used by its explicit Dixon-prime certificate.

## Main definitions

* `TauCeti.quaternionElements`: a computable enumeration of `QuaternionGroup n`.
* `TauCeti.quaternionRotations`: the cyclic subgroup consisting of the elements `a i`.
* `TauCeti.quaternionRotationsMulEquiv`: its coordinate equivalence with
  `Multiplicative (ZMod (2 * n))`.

## Main results

* `TauCeti.mem_quaternionElements`: the enumeration contains every group element.
* `TauCeti.index_quaternionRotations`: the rotation subgroup has index two.
* `TauCeti.conj_eq_inv_of_notMem_quaternionRotations`: an element outside the rotation subgroup
  conjugates every rotation to its inverse.
* `TauCeti.exponent_quaternionGroup_two`: `QuaternionGroup 2` has exponent four.
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
    simpa using conj_eq_inv_of_notMem_quaternionRotations hs x.2)

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
  left_inv x := Subtype.ext (a_quaternionRotationIndex x.2)
  right_inv _ := rfl
  map_mul' x y := congrArg Multiplicative.ofAdd (quaternionRotationIndex_mul x.2 y.2)

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

/-- The quaternion group of order eight has exponent four. -/
@[simp]
theorem exponent_quaternionGroup_two : Monoid.exponent (QuaternionGroup 2) = 4 := by
  rw [QuaternionGroup.exponent]
  decide

end TauCeti
