/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Order.Partition.Finpartition
public import TauCeti.GroupTheory.Perm.Fin
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Data.Finset.Sort
import TauCeti.GroupTheory.Perm.SwapFactors
import TauCeti.Order.Partition.Finpartition

/-!
# The permutation of a finite partition in a linear order

Let `P` be a finite partition of a finite set `s` of points of a linear order. Reading each part
`B = {b₁ < b₂ < ⋯ < bₖ}` of `P` as the cycle `b₁ ↦ b₂ ↦ ⋯ ↦ bₖ ↦ b₁` gives a permutation
`P.formPerm` of the ambient type, which fixes every point outside `s`. This is the permutation
model of a partition used in the combinatorics of free probability: its cycles are the parts of
`P`, each traversed in increasing cyclic order, so the partition can be recovered from it, and
the number of its cycles is the number of parts. For a noncrossing partition the permutation
of its Kreweras complement is obtained from this one by composing with the full cycle through
`s`; that comparison lives in `TauCeti/Combinatorics/NoncrossingPartition/FormPerm.lean`.

The cycle of each part is Mathlib's `List.formPerm` of the increasing enumeration
`Finset.sort` of the part.

## Main definitions

* `Finpartition.formPerm P`: the permutation cycling each part of `P` in increasing order.

## Main results

* `Finpartition.formPerm_apply_mem_part`, `Finpartition.part_formPerm_apply`: the permutation
  maps each part to itself, and so do its inverse and its powers.
* `Finpartition.formPerm_apply_of_notMem`: points outside `s` are fixed.
* `Finpartition.formPerm_apply_eq_iff`: the value of the permutation at a point is the next point
  of its part in increasing cyclic order.
* `Finpartition.formPerm_symm_apply_eq_iff`: the value of the inverse permutation at a point is
  the previous point of its part in increasing cyclic order.
* `Finpartition.formPerm_bot`, `Finpartition.formPerm_top`: the partition into singletons gives
  the identity, and the partition into one part gives the cycle through `s` in increasing order.
* `Finpartition.formPerm_top_eq_finRotate`: on `Fin n` the partition into one part has permutation
  `finRotate n`.
* `Finpartition.formPerm_top_insert`: adjoining a new largest point `m` to `t` inserts it into the
  cycle through `t` after the largest point `m'` of `t`, multiplying by `swap m' m` on the right.
* `Finpartition.orbitCount_formPerm_top_insert_add_one`: adjoining a new largest point to `t`
  merges its cycle into the cycle through `t`, lowering the number of cycles by one.
* `Finpartition.formPerm_apply_eq_self_iff`: the fixed points are the singleton parts and the
  points outside `s`.
* `Finpartition.sameCycle_formPerm_iff`: two points of `s` lie on a common cycle exactly when
  they lie in a common part.
* `Finpartition.formPerm_injective`: the partition is determined by its permutation.
* `Finpartition.ofSetoid_sameCycle_formPerm`: the partition of a finite type into the cycles of
  `P.formPerm` is `P`.
* `Finpartition.fullCycleType_formPerm`, `Finpartition.cycleType_formPerm`,
  `Finpartition.orbitCount_formPerm`: the cycle lengths of `P.formPerm` are the part sizes of
  `P`, and its number of cycles, fixed points included, is the number of parts.

## References

* P. Biane, *Some properties of crossings and partitions*, Discrete Math. 175 (1997), 41–53.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 23.
-/

public section

open Equiv Equiv.Perm Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α} (P : Finpartition s)

/-- The cycle of the part through `x`, read in increasing order, moves `x` within that part;
it fixes `x` when `x ∉ s`, the part being empty. -/
private theorem part_sort_formPerm_apply (x : α) :
    P.part ((P.part x).sort.formPerm x) = P.part x := by
  by_cases hx : x ∈ s
  · have hmem : (P.part x).sort.formPerm x ∈ P.part x := by
      rw [← mem_sort (· ≤ ·), List.formPerm_mem_iff_mem, mem_sort, mem_part_self]
      exact hx
    exact P.part_eq_of_mem (P.part_mem.2 hx) hmem
  · simp [P.part_eq_empty.2 hx]

/-- The inverse form of `part_sort_formPerm_apply`. -/
private theorem part_sort_formPerm_inv_apply (x : α) :
    P.part ((P.part x).sort.formPerm⁻¹ x) = P.part x := by
  by_cases hx : x ∈ s
  · have hmem : (P.part x).sort.formPerm⁻¹ x ∈ P.part x := by
      rw [← mem_sort (· ≤ ·), ← List.formPerm_mem_iff_mem]
      simpa using hx
    exact P.part_eq_of_mem (P.part_mem.2 hx) hmem
  · simp [P.part_eq_empty.2 hx]

/-- The **permutation of a finite partition** `P` of a finite set `s` in a linear order: it
cycles each part `{b₁ < b₂ < ⋯ < bₖ}` of `P` as `b₁ ↦ b₂ ↦ ⋯ ↦ bₖ ↦ b₁`, and fixes every point
outside `s`. Its cycles are the parts of `P` (`Finpartition.sameCycle_formPerm_iff`). -/
def formPerm : Perm α where
  toFun x := (P.part x).sort.formPerm x
  invFun x := (P.part x).sort.formPerm⁻¹ x
  left_inv x := by
    simp only
    rw [P.part_sort_formPerm_apply]
    simp
  right_inv x := by
    simp only
    rw [P.part_sort_formPerm_inv_apply]
    simp

/-- The permutation of `P` moves `x` along the cycle of its part, read in increasing order. -/
theorem formPerm_apply (x : α) : P.formPerm x = (P.part x).sort.formPerm x := (rfl)

/-- The inverse of the permutation of `P` moves `x` backwards along the cycle of its part. -/
theorem formPerm_inv_apply (x : α) : P.formPerm⁻¹ x = (P.part x).sort.formPerm⁻¹ x := (rfl)

/-- The permutation of `P` maps each point to a point of the same part. -/
@[simp]
theorem part_formPerm_apply (x : α) : P.part (P.formPerm x) = P.part x :=
  P.part_sort_formPerm_apply x

/-- The inverse permutation of `P` maps each point to a point of the same part. -/
@[simp]
theorem part_formPerm_symm_apply (x : α) : P.part (P.formPerm.symm x) = P.part x :=
  P.part_sort_formPerm_inv_apply x

/-- Every power of the permutation of `P` maps each point to a point of the same part. -/
@[simp]
theorem part_formPerm_zpow_apply (k : ℤ) (x : α) : P.part ((P.formPerm ^ k) x) = P.part x := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih => rw [zpow_add_one, Perm.mul_apply, ih, part_formPerm_apply]
  | pred k ih => rw [zpow_sub_one, Perm.mul_apply, ih, Perm.coe_inv, part_formPerm_symm_apply]

/-- Every natural power of the permutation of `P` maps each point to a point of the same part. -/
@[simp]
theorem part_formPerm_pow_apply (k : ℕ) (x : α) : P.part ((P.formPerm ^ k) x) = P.part x := by
  simpa using P.part_formPerm_zpow_apply k x

/-- The permutation of `P` maps `s` to itself. -/
@[simp]
theorem formPerm_apply_mem_iff {x : α} : P.formPerm x ∈ s ↔ x ∈ s := by
  rw [← part_nonempty, part_formPerm_apply, part_nonempty]

/-- The inverse permutation of `P` maps `s` to itself. -/
@[simp]
theorem formPerm_symm_apply_mem_iff {x : α} : P.formPerm.symm x ∈ s ↔ x ∈ s := by
  rw [← part_nonempty, part_formPerm_symm_apply, part_nonempty]

/-- Every power of the permutation of `P` maps `s` to itself. -/
@[simp]
theorem formPerm_zpow_apply_mem_iff (k : ℤ) {x : α} : (P.formPerm ^ k) x ∈ s ↔ x ∈ s := by
  rw [← part_nonempty, part_formPerm_zpow_apply, part_nonempty]

/-- The permutation of `P` maps a point of `s` to a point of its part. -/
theorem formPerm_apply_mem_part {x : α} (hx : x ∈ s) : P.formPerm x ∈ P.part x := by
  rw [← part_formPerm_apply, mem_part_self, formPerm_apply_mem_iff]
  exact hx

/-- The inverse permutation of `P` maps a point of `s` to a point of its part. -/
theorem formPerm_symm_apply_mem_part {x : α} (hx : x ∈ s) : P.formPerm.symm x ∈ P.part x := by
  rw [← part_formPerm_symm_apply, mem_part_self, formPerm_symm_apply_mem_iff]
  exact hx

/-- Every power of the permutation of `P` maps a point of `s` to a point of its part. -/
theorem formPerm_zpow_apply_mem_part (k : ℤ) {x : α} (hx : x ∈ s) :
    (P.formPerm ^ k) x ∈ P.part x := by
  rw [← part_formPerm_zpow_apply P k, mem_part_self, formPerm_zpow_apply_mem_iff]
  exact hx

/-- The permutation of `P` fixes every point outside `s`. -/
theorem formPerm_apply_of_notMem {x : α} (hx : x ∉ s) : P.formPerm x = x := by
  simp [formPerm_apply, P.part_eq_empty.2 hx]

/-- A natural power of the permutation of `P` acts on a point as the same power of the cycle of
its part. -/
theorem formPerm_pow_apply (k : ℕ) (x : α) :
    (P.formPerm ^ k) x = ((P.part x).sort.formPerm ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, formPerm_apply, part_formPerm_pow_apply, ih, ← Perm.mul_apply,
      ← pow_succ']

/-- A point is fixed by the permutation of `P` exactly when its part has at most one point:
it is either a singleton part or a point outside `s`. -/
theorem formPerm_apply_eq_self_iff {x : α} : P.formPerm x = x ↔ #(P.part x) ≤ 1 := by
  by_cases hx : x ∈ s
  · rw [formPerm_apply, List.formPerm_apply_mem_eq_self_iff _ (sort_nodup _ _) _
      ((mem_sort _).2 (P.mem_part hx)), length_sort]
  · simp [P.formPerm_apply_of_notMem hx, P.part_eq_empty.2 hx]

/-- Two points of `s` lie on a common cycle of the permutation of `P` exactly when they lie in a
common part of `P`. -/
theorem sameCycle_formPerm_iff {x y : α} (hx : x ∈ s) :
    P.formPerm.SameCycle x y ↔ y ∈ P.part x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact P.formPerm_zpow_apply_mem_part k hx
  · intro hy
    have hxl : x ∈ (P.part x).sort := (mem_sort _).2 (P.mem_part hx)
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxl
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem ((mem_sort _).2 hy : y ∈ (P.part x).sort)
    refine ⟨(j + ((P.part x).sort.length - i) : ℕ), ?_⟩
    have h := List.formPerm_pow_apply_getElem _ (sort_nodup _ _)
      (j + ((P.part x).sort.length - i)) i hi
    rw [hix] at h
    rw [zpow_natCast, formPerm_pow_apply, h, ← hjy]
    have key (L : ℕ) (hiL : i < L) (hjL : j < L) : (i + (j + (L - i))) % L = j := by
      rw [show i + (j + (L - i)) = j + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hjL]
    simp only [key _ hi hj]

/-- The permutation of `P` moves a point `x` of `s` to the next point of its part, or, when `x` is
the last point of its part, to the first point of its part. -/
private theorem formPerm_apply_spec {x : α} (hx : x ∈ s) :
    (x < P.formPerm x → ∀ w ∈ P.part x, x < w → P.formPerm x ≤ w) ∧
      (P.formPerm x ≤ x → ∀ w ∈ P.part x, P.formPerm x ≤ w ∧ w ≤ x) := by
  have hl := sortedLT_sort (P.part x)
  have hxl : x ∈ (P.part x).sort := (mem_sort _).2 (P.mem_part hx)
  simp only [formPerm_apply, ← mem_sort (· ≤ ·) (s := P.part x)]
  generalize (P.part x).sort = l at hl hxl ⊢
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxl
  rw [List.formPerm_apply_getElem _ hl.nodup]
  rcases (Nat.succ_le_of_lt hi).lt_or_eq with hi' | hi'
  · simp only [Nat.mod_eq_of_lt hi', hl.getElem_lt_getElem_iff, hl.getElem_le_getElem_iff]
    refine ⟨fun _ w hw hlt => ?_, fun h => absurd h (by omega)⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    rw [hl.getElem_lt_getElem_iff] at hlt
    rw [hl.getElem_le_getElem_iff]
    omega
  · have h0 : (i + 1) % l.length = 0 := by rw [show i + 1 = l.length from hi', Nat.mod_self]
    simp only [h0, hl.getElem_lt_getElem_iff, hl.getElem_le_getElem_iff]
    refine ⟨fun h => absurd h (by omega), fun _ w hw => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    rw [hl.getElem_le_getElem_iff, hl.getElem_le_getElem_iff]
    omega

/-- The value of the permutation of `P` at a point `x` of `s` is characterized as the point `z`
of the part of `x` that follows `x` in increasing cyclic order: either `x < z` and no point of the
part lies strictly between them, or `z ≤ x` and the part lies between `z` and `x`, so that `x`
is the last and `z` the first point of the part. -/
theorem formPerm_apply_eq_iff {x z : α} (hx : x ∈ s) :
    P.formPerm x = z ↔ z ∈ P.part x ∧ (x < z → ∀ w ∈ P.part x, x < w → z ≤ w) ∧
      (z ≤ x → ∀ w ∈ P.part x, z ≤ w ∧ w ≤ x) := by
  refine ⟨fun h => h ▸ ⟨P.formPerm_apply_mem_part hx, P.formPerm_apply_spec hx⟩,
    fun ⟨hz, hlt, hle⟩ => ?_⟩
  obtain ⟨hylt, hyle⟩ := P.formPerm_apply_spec hx
  have hy := P.formPerm_apply_mem_part hx
  rcases lt_or_ge x z with hxz | hzx <;> rcases lt_or_ge x (P.formPerm x) with hxy | hyx
  · exact le_antisymm (hylt hxy z hz hxz) (hlt hxz _ hy hxy)
  · exact absurd (hyle hyx z hz).2 (not_le.2 hxz)
  · exact absurd (hle hzx _ hy).2 (not_le.2 hxy)
  · exact le_antisymm (hyle hyx z hz).1 (hle hzx _ hy).1

/-- The value of the inverse permutation of `P` at a point `x` of `s` is characterized as the
point `z` of the part of `x` that precedes `x` in increasing cyclic order: either `z < x` and no
point of the part lies strictly between them, or `x ≤ z` and the part lies between `x` and `z`,
so that `x` is the first and `z` the last point of the part. -/
theorem formPerm_symm_apply_eq_iff {x z : α} (hx : x ∈ s) :
    P.formPerm.symm x = z ↔ z ∈ P.part x ∧ (z < x → ∀ w ∈ P.part x, w < x → w ≤ z) ∧
      (x ≤ z → ∀ w ∈ P.part x, x ≤ w ∧ w ≤ z) := by
  by_cases hz : z ∈ P.part x
  swap
  · exact iff_of_false (fun h => hz (h ▸ P.formPerm_symm_apply_mem_part hx)) fun h => hz h.1
  have hzs : z ∈ s := P.part_subset x hz
  rw [Equiv.symm_apply_eq, eq_comm, P.formPerm_apply_eq_iff hzs,
    (P.mem_part_iff_part_eq_part hzs hx).1 hz]
  simp only [P.mem_part hx, hz, true_and]
  refine and_congr_left fun _ => imp_congr_right fun _ => forall₂_congr fun w _ => ?_
  exact ⟨fun h hwx => not_lt.1 fun hzw => (h hzw).not_gt hwx,
    fun h hzw => not_lt.1 fun hwx => (h hwx).not_gt hzw⟩

/-- The partition of `s` into singletons has the identity permutation. -/
@[simp]
theorem formPerm_bot : (⊥ : Finpartition s).formPerm = 1 := by
  ext x
  by_cases hx : x ∈ s
  · simp [formPerm_apply, part_bot hx]
  · exact formPerm_apply_of_notMem _ hx

/-- The partition of `s` into one part has as permutation the cycle through the points of `s` in
increasing order. -/
@[simp]
theorem formPerm_top : (⊤ : Finpartition s).formPerm = s.sort.formPerm := by
  ext x
  by_cases hx : x ∈ s
  · rw [formPerm_apply, part_top hx]
  · rw [formPerm_apply_of_notMem _ hx, List.formPerm_apply_of_notMem (by simpa using hx)]

/-- On `Fin n`, the partition into one part has as permutation the rotation `i ↦ i + 1` modulo
`n`. -/
theorem formPerm_top_eq_finRotate {n : ℕ} :
    (⊤ : Finpartition (univ : Finset (Fin n))).formPerm = finRotate n := by
  rw [formPerm_top, Fin.formPerm_sort_univ]

/-- Adjoining to `t` a point `m` above all of its points inserts `m` into the increasing cycle
through `t` right after the largest point `m'` of `t`. -/
theorem formPerm_top_insert {t : Finset α} {m m' : α} (hm : ∀ x ∈ t, x < m) (hm' : m' ∈ t)
    (hm't : ∀ x ∈ t, x ≤ m') :
    (⊤ : Finpartition (insert m t)).formPerm = (⊤ : Finpartition t).formPerm * swap m' m := by
  have hmt : m ∉ t := fun h => (hm m h).false
  have hm'm : m' ≠ m := (hm m' hm').ne
  ext x
  rw [Perm.mul_apply]
  by_cases hxs : x ∈ insert m t
  swap
  · have hxt : x ∉ t := fun h => hxs (mem_insert_of_mem h)
    have hxm : x ≠ m := by rintro rfl; exact hxs (mem_insert_self _ t)
    have hxm' : x ≠ m' := by rintro rfl; exact hxt hm'
    rw [formPerm_apply_of_notMem _ hxs, swap_apply_of_ne_of_ne hxm' hxm,
      formPerm_apply_of_notMem _ hxt]
  rw [formPerm_apply_eq_iff _ hxs, part_top hxs]
  rcases mem_insert.1 hxs with rfl | hxt
  · -- The swap sends `m` to `m'`, which the cycle through `t` sends to the first point of `t`.
    rw [swap_apply_right]
    obtain ⟨hy, -, hyle⟩ := (formPerm_apply_eq_iff _ hm').1 rfl
    rw [part_top hm'] at hy hyle
    have hyle := hyle (hm't _ hy)
    refine ⟨mem_insert_of_mem hy, fun h => absurd (hm _ hy) (not_lt.2 h.le), fun _ w hw => ?_⟩
    rcases mem_insert.1 hw with rfl | hw
    exacts [⟨(hm _ hy).le, le_rfl⟩, ⟨(hyle w hw).1, (hm w hw).le⟩]
  by_cases hxm' : x = m'
  · -- The swap sends `m'` to `m`, which the cycle through `t` fixes.
    subst hxm'
    rw [swap_apply_left, formPerm_apply_of_notMem _ hmt]
    refine ⟨mem_insert_self m t, fun _ w hw hxw => ?_, fun h => absurd (hm _ hxt) (not_lt.2 h)⟩
    rcases mem_insert.1 hw with rfl | hw
    exacts [le_rfl, absurd (hm't w hw) (not_le.2 hxw)]
  · -- Below `m'`, the cycle through `t` moves `x` up to the next point of `t`.
    rw [swap_apply_of_ne_of_ne hxm' (by rintro rfl; exact hmt hxt)]
    obtain ⟨hy, hylt, hyle⟩ := (formPerm_apply_eq_iff _ hxt).1 rfl
    rw [part_top hxt] at hy hylt hyle
    have hxlt : x < m' := (hm't x hxt).lt_of_ne hxm'
    have hxy : x < (⊤ : Finpartition t).formPerm x :=
      not_le.1 fun h => absurd (hyle h m' hm').2 (not_le.2 hxlt)
    refine ⟨mem_insert_of_mem hy, fun _ w hw hxw => ?_, fun h => absurd hxy (not_lt.2 h)⟩
    rcases mem_insert.1 hw with rfl | hw
    exacts [(hm _ hy).le, hylt hxy w hw hxw]

/-- Adjoining to a nonempty `t` a point `m` above all of its points merges the fixed point `m`
into the increasing cycle through `t`, so the number of cycles, fixed points included, drops by
one. -/
theorem orbitCount_formPerm_top_insert_add_one [Finite α] {t : Finset α} {m m' : α}
    (hm : ∀ x ∈ t, x < m) (hm' : m' ∈ t) (hm't : ∀ x ∈ t, x ≤ m') :
    TauCeti.orbitCount (⊤ : Finpartition (insert m t)).formPerm + 1 =
      TauCeti.orbitCount (⊤ : Finpartition t).formPerm := by
  have hγm : (⊤ : Finpartition t).formPerm m = m :=
    formPerm_apply_of_notMem _ fun h => (hm m h).false
  rw [formPerm_top_insert hm hm' hm't]
  exact TauCeti.orbitCount_mul_swap_add_one_of_not_sameCycle fun hc =>
    (hm m' hm').ne (hc.eq_of_right hγm)

/-- A finite partition is determined by its permutation. -/
theorem formPerm_injective : Function.Injective (formPerm : Finpartition s → Perm α) := by
  intro P Q h
  refine ext_of_part fun x hx => Finset.ext fun y => ?_
  rw [← P.sameCycle_formPerm_iff hx, ← Q.sameCycle_formPerm_iff hx, h]

/-- Finite partitions are equal exactly when their permutations are. -/
@[simp]
theorem formPerm_inj {Q : Finpartition s} : P.formPerm = Q.formPerm ↔ P = Q :=
  formPerm_injective.eq_iff

section Fintype

variable [Fintype α] (P : Finpartition (univ : Finset α))

/-- The partition of a finite type into the cycles of the permutation of `P`, fixed points
included, is `P` itself. -/
theorem ofSetoid_sameCycle_formPerm [DecidableRel (SameCycle.setoid P.formPerm)] :
    ofSetoid (SameCycle.setoid P.formPerm) = P :=
  ext_of_part fun x hx => Finset.ext fun y => by
    rw [mem_part_ofSetoid_iff_rel]
    exact P.sameCycle_formPerm_iff hx

/-- The cycle lengths of the permutation of `P`, one for each fixed point included, are the
sizes of the parts of `P`. -/
theorem fullCycleType_formPerm : P.formPerm.fullCycleType = P.parts.val.map card := by
  rw [fullCycleType_eq_map_card_filter P.formPerm P.part fun x y => by
    rw [P.sameCycle_formPerm_iff (mem_univ x), P.mem_part_iff_part_eq_part (mem_univ y)
      (mem_univ x), eq_comm]]
  refine Multiset.map_congr (congrArg Finset.val ?_) fun B hB => ?_
  · ext B
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ P.part_mem.2 (mem_univ x), fun hB => by
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
      exact ⟨x, P.part_eq_of_mem hB hx⟩⟩
  · congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact P.part_eq_iff_mem hB

/-- The lengths of the nontrivial cycles of the permutation of `P` are the sizes of the parts of
`P` with at least two points. -/
theorem cycleType_formPerm :
    P.formPerm.cycleType = (P.parts.val.map card).filter fun k => 2 ≤ k := by
  rw [← filter_fullCycleType_eq_cycleType, fullCycleType_formPerm]

/-- The number of cycles of the permutation of `P`, fixed points included, is the number of parts
of `P`. -/
@[simp]
theorem orbitCount_formPerm : TauCeti.orbitCount P.formPerm = #P.parts := by
  classical
  rw [orbitCount_eq_card_parts_partition, ← fullCycleType_def, fullCycleType_formPerm,
    Multiset.card_map, card_val]

end Fintype

end Finpartition
