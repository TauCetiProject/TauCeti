/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cycle types that count fixed points

`Equiv.Perm.cycleType σ` lists the lengths of the cycles of `σ` that are at least two, so it
forgets the fixed points and is a partition of `σ.support.card` rather than of the ambient
cardinality. The factorization type of a polynomial modulo a prime is, by contrast, a partition
of the degree that keeps its parts equal to one. The corrected invariant

`σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1`

is already in Mathlib: it is `(Equiv.Perm.partition σ).parts`, the multiset of parts of
`Equiv.Perm.partition`, and `Equiv.Perm.parts_partition` is its defining equation. This file adds
the API that a comparison with a multiset of factor degrees needs, on that multiset.

## Main results

* `fullCycleType` is the canonical name for the complete cycle-length multiset; its bridge to
  Mathlib's partition API and its sum, identity, conjugacy, and transport lemmas are included.
* `Equiv.Perm.count_one_parts_partition`, `Equiv.Perm.count_parts_partition_of_ne_one`: the parts
  equal to one are the fixed points of `σ`, and at every value other than one the multiset counts a
  part as often as `Equiv.Perm.cycleType` does. Together with Mathlib's
  `Equiv.Perm.filter_parts_partition_eq_cycleType` these say that no information is gained or
  lost.
* `Equiv.Perm.parts_partition_eq_cycleType_iff`: the correction is trivial exactly for a
  permutation with no fixed point.
* `Equiv.Perm.parts_partition_conj`: the multiset is constant on conjugacy classes.
* `Equiv.Perm.lcm_parts_partition`, `Equiv.Perm.sign_of_parts_partition`: the order and the sign
  of a permutation, read off the corrected multiset. These are the two invariants that a single
  exhibited factorization type contributes to the group that exhibits it.
* `Equiv.Perm.parts_partition_permCongr`: transport along an equivalence `α ≃ β` of the underlying
  types leaves it unchanged. Its ingredient `Equiv.Perm.cycleType_permCongr` is proved here too,
  since Mathlib records only `Equiv.Perm.sign_permCongr`. The form for `Equiv.permCongrHom`, the
  group isomorphism a relabelling induces, needs no separate lemma: Mathlib's `simp` lemma
  `Equiv.permCongrHom_coe` rewrites it to `Equiv.permCongr`.
* `Equiv.Perm.parts_partition_of_isCycle`, `Equiv.Perm.parts_partition_swap`: the values on a cycle
  and on a transposition, which are the two shapes the low-degree recognition theorems read.
* `Equiv.Perm.cycleType_eq_singleton_iff`: a single cycle length `n` characterizes a cycle moving
  `n` points; through `Equiv.Perm.filter_fullCycleType_eq_cycleType` this reads a cycle off a full
  cycle type.
* `Equiv.Perm.fullCycleType_eq_map_card_filter`: the full cycle type is the multiset of orbit
  sizes, read through any function whose fibres are the orbits.
* `Equiv.Perm.orbitQuotientEquivCycleFactorsSumFixedPoints`: the classes of `Equiv.Perm.SameCycle`
  are the nontrivial cycle factors together with the fixed points, via the point-level map
  `Equiv.Perm.cycleFactorOrFixedPoint`.
* `Equiv.Perm.fullCycleType_eq_map_card_orbit`: the full cycle type is the multiset of the sizes
  of the orbits of `⟨σ⟩` on the carrier, with `Equiv.Perm.sameCycle_iff_mem_orbit_zpowers`,
  `Equiv.Perm.coe_support_cycleOf_eq_orbit_zpowers` and `Equiv.Perm.orbit_zpowers_eq_singleton`
  identifying those orbits with the cycle supports and the fixed points.

## Implementation notes

The definition `fullCycleType σ` below uses the same `[Fintype α] [DecidableEq α]` arguments as
`Equiv.Perm.partition`, so the invariant is a wrapper around its defining expression. The
public `pos_of_mem_fullCycleType` lemma exposes the positivity of its parts
(`Nat.Partition.parts_pos`),
and `count_fullCycleType_of_ne_one` exposes the non-one count comparison. The filter lemma
(`Equiv.Perm.filter_parts_partition_eq_cycleType`) and the completeness of the conjugacy invariant
(`Equiv.Perm.partition_eq_of_isConj`) remain stated for `partition.parts` and are available through
the defining bridge. Downstream statements use `(Equiv.Perm.partition σ).parts`, which is a bare
`Multiset ℕ` and so can be compared with a multiset of factor degrees directly; it is the bundled
`σ.partition`, whose type `Nat.Partition n` is indexed by the ambient cardinality, that cannot.

Since `Equiv.Perm.partition` takes the `DecidableEq α` of its carrier as an instance argument and
is not `noncomputable`, the multiset below is written at the carrier's own instance rather than at
`Classical.propDecidable`, which is what the downstream comparison with a factorization type is
stated with. The invariant and its API are in the `Equiv.Perm` namespace, so permutation
expressions can use dot notation and the statements sit alongside the partition lemmas they
refine.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The cycle lengths of `σ`, including one part for each fixed point.

Unlike `Equiv.Perm.cycleType`, this is a partition of the cardinality of the whole carrier. It
is the permutation-side cycle invariant used to compare a Galois action with factor degrees. -/
def _root_.Equiv.Perm.fullCycleType (σ : Equiv.Perm α) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1

/-! ### The two halves of the multiset -/

/-- The parts of `Equiv.Perm.partition` equal to one are the fixed points of `σ`. Together with
`Equiv.Perm.filter_parts_partition_eq_cycleType`, which recovers the cycle lengths, this says that
the correction neither gains nor loses information. -/
@[simp]
theorem _root_.Equiv.Perm.count_one_parts_partition (σ : Equiv.Perm α) :
    σ.partition.parts.count 1 = Fintype.card α - σ.support.card := by
  rw [parts_partition, Multiset.count_add, Multiset.count_replicate_self,
    Multiset.count_eq_zero_of_notMem fun h => (one_lt_of_mem_cycleType h).false, zero_add]

/-- At every value other than one, `Equiv.Perm.partition` counts a part as often as
`Equiv.Perm.cycleType` does. -/
@[simp]
theorem _root_.Equiv.Perm.count_parts_partition_of_ne_one (σ : Equiv.Perm α) {n : ℕ} (hn : n ≠ 1) :
    σ.partition.parts.count n = σ.cycleType.count n := by
  simp [parts_partition, Multiset.count_replicate, hn.symm]

/-- The number of parts of `Equiv.Perm.partition` is the number of cycles of `σ` of length at
least two together with its fixed points. -/
@[simp]
theorem _root_.Equiv.Perm.card_parts_partition (σ : Equiv.Perm α) :
    Multiset.card σ.partition.parts =
      Multiset.card σ.cycleType + (Fintype.card α - σ.support.card) := by
  rw [parts_partition, Multiset.card_add, Multiset.card_replicate]

/-! ### The correction term -/

/-- The correction is trivial exactly when the permutation has no fixed point. This is the one
place where the parts of `Equiv.Perm.partition` and `Equiv.Perm.cycleType` may be exchanged, and
the hypothesis is about `σ`, not about the ambient type. -/
theorem _root_.Equiv.Perm.parts_partition_eq_cycleType_iff {σ : Equiv.Perm α} :
    σ.partition.parts = σ.cycleType ↔ σ.support = Finset.univ := by
  constructor
  · intro h
    have hsum := σ.partition.parts_sum
    rw [h, sum_cycleType] at hsum
    exact Finset.eq_univ_of_card _ hsum
  · intro h
    rw [parts_partition, h, Finset.card_univ, Nat.sub_self, Multiset.replicate_zero, add_zero]

/-- For a permutation with no fixed point, the parts of `Equiv.Perm.partition` are
`Equiv.Perm.cycleType`. -/
theorem _root_.Equiv.Perm.parts_partition_eq_cycleType {σ : Equiv.Perm α}
    (hσ : σ.support = Finset.univ) : σ.partition.parts = σ.cycleType :=
  parts_partition_eq_cycleType_iff.2 hσ

/-! ### Special values -/

/-- The parts of the identity permutation are all one, with one part for each element of the
underlying finite type. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_one :
    (1 : Equiv.Perm α).partition.parts = Multiset.replicate (Fintype.card α) 1 := by
  rw [parts_partition, cycleType_one, support_one, Finset.card_empty, Nat.sub_zero, zero_add]

/-- The identity is the only permutation all of whose parts are one. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_eq_replicate_one_iff {σ : Equiv.Perm α} :
    σ.partition.parts = Multiset.replicate (Fintype.card α) 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, parts_partition_one]⟩
  rw [← cycleType_eq_zero, ← filter_parts_partition_eq_cycleType, h, Multiset.filter_eq_nil]
  exact fun n hn => by rw [Multiset.eq_of_mem_replicate hn]; omega

/-- The cycle type of a cycle, with its fixed points restored. -/
theorem _root_.Equiv.Perm.parts_partition_of_isCycle {σ : Equiv.Perm α} (hσ : σ.IsCycle) :
    σ.partition.parts =
      σ.support.card ::ₘ Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
  rw [parts_partition, hσ.cycleType, Multiset.singleton_add]

/-- The cycle type of a transposition, with its fixed points restored: on a type with `n` points
a transposition has parts `{2, 1, …, 1}` with `n - 2` parts equal to one. -/
theorem _root_.Equiv.Perm.parts_partition_swap {x y : α} (hxy : x ≠ y) :
    (swap x y).partition.parts = 2 ::ₘ Multiset.replicate (Fintype.card α - 2) 1 := by
  rw [parts_partition_of_isCycle (isCycle_swap hxy), card_support_swap hxy]

/-- On an empty type there is nothing to partition. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_of_isEmpty [IsEmpty α] (σ : Equiv.Perm α) :
    σ.partition.parts = 0 := by
  have hσ : σ = 1 := Equiv.ext fun x => isEmptyElim x
  rw [hσ, parts_partition_one, Fintype.card_eq_zero, Multiset.replicate_zero]

/-- The parts of `Equiv.Perm.partition` are empty exactly on an empty type; in particular they do
not vanish on the identity of a nonempty type, unlike `Equiv.Perm.cycleType`. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_eq_zero_iff {σ : Equiv.Perm α} :
    σ.partition.parts = 0 ↔ Fintype.card α = 0 := by
  refine ⟨fun h => by rw [← σ.partition.parts_sum, h, Multiset.sum_zero], fun h => ?_⟩
  have : IsEmpty α := Fintype.card_eq_zero_iff.1 h
  exact parts_partition_of_isEmpty σ

/-! ### Conjugacy -/

/-- The parts of `Equiv.Perm.partition` are constant on conjugacy classes. This is the unbundled
form of Mathlib's `Equiv.Perm.partition_eq_of_isConj`, which also gives the converse. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_conj (g σ : Equiv.Perm α) :
    (g * σ * g⁻¹).partition.parts = σ.partition.parts :=
  congrArg Nat.Partition.parts (partition_eq_of_isConj.1 (isConj_iff.2 ⟨g, rfl⟩)).symm

/-- Inverting a permutation does not change the parts of its partition. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_inv (σ : Equiv.Perm α) :
    σ⁻¹.partition.parts = σ.partition.parts := by
  rw [parts_partition, parts_partition, cycleType_inv, support_inv]

/-! ### Order and parity

The two invariants that a single exhibited factorization type contributes: the order of the
permutation it exhibits, which divides the order of any group containing it, and its sign. -/

private theorem lcm_replicate_one (k : ℕ) : (Multiset.replicate k 1).lcm = 1 :=
  Nat.dvd_one.1 <| Multiset.lcm_dvd.2 fun _ hb => dvd_of_eq (Multiset.eq_of_mem_replicate hb)

/-- The order of a permutation is the least common multiple of the parts of
`Equiv.Perm.partition`. The parts equal to one contribute nothing, so this agrees with
`Equiv.Perm.lcm_cycleType`; stating it here means that a factorization type can be read as a lower
bound on the order of a group directly, without first discarding its fixed points. -/
@[simp]
theorem _root_.Equiv.Perm.lcm_parts_partition (σ : Equiv.Perm α) :
    σ.partition.parts.lcm = orderOf σ := by
  rw [parts_partition, Multiset.lcm_add, lcm_cycleType, lcm_replicate_one]
  simp

/-- Every part of a permutation's partition divides the order of the permutation. -/
theorem _root_.Equiv.Perm.dvd_of_mem_parts_partition {σ : Equiv.Perm α} {n : ℕ}
    (hn : n ∈ σ.partition.parts) : n ∣ orderOf σ := by
  rw [← lcm_parts_partition]
  exact Multiset.dvd_lcm hn

/-- The sign of a permutation, read off the parts of `Equiv.Perm.partition`: it is the parity of
the number of parts, corrected by the ambient cardinality. This is `Equiv.Perm.sign_of_cycleType`
in the convention that keeps the fixed points, and the parity invariant of a Galois image is
computed from it. -/
theorem _root_.Equiv.Perm.sign_of_parts_partition (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card α + Multiset.card σ.partition.parts) := by
  have hle : σ.support.card ≤ Fintype.card α := by
    simpa using σ.support.card_le_univ
  have h : Fintype.card α + Multiset.card σ.partition.parts =
      σ.cycleType.sum + Multiset.card σ.cycleType + 2 * (Fintype.card α - σ.support.card) := by
    rw [card_parts_partition, sum_cycleType]
    omega
  rw [h, pow_add, pow_mul, sign_of_cycleType]
  simp

/-! ### Transport along an equivalence of the underlying types -/

/-- The cycle type of a permutation does not change when the underlying type is relabelled.
Mathlib has this for `Equiv.Perm.sign` as `Equiv.Perm.sign_permCongr`, and for the extension of a
permutation to a larger type as `Equiv.Perm.cycleType_extendDomain`; relabelling is the case of
the latter in which the predicate cut out is `True`. -/
@[simp]
theorem _root_.Equiv.Perm.cycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  have h : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ : β => trivial)).symm) := by
    ext b
    rw [Perm.extendDomain_apply_subtype _ _ trivial]
    simp
  rw [h, cycleType_extendDomain]

/-- Relabelling the underlying type does not change the number of points that a permutation
moves. -/
@[simp]
theorem _root_.Equiv.Perm.card_support_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [← sum_cycleType, ← sum_cycleType, cycleType_permCongr]

/-- The parts of `Equiv.Perm.partition` are natural in the underlying type: a relabelling
`e : α ≃ β` leaves them unchanged. This is what lets a statement about the roots of a polynomial,
which form a type with no chosen numbering, be compared with a statement about `Fin n`. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).partition.parts = σ.partition.parts := by
  rw [parts_partition, parts_partition, cycleType_permCongr, card_support_permCongr,
    Fintype.card_congr e]

/-! ### The canonical full cycle type API -/

/-- `fullCycleType` is the unbundled parts of Mathlib's permutation partition. -/
theorem _root_.Equiv.Perm.fullCycleType_def (σ : Equiv.Perm α) :
    fullCycleType σ = σ.partition.parts := by
  rw [fullCycleType, Equiv.Perm.parts_partition]

/-! The filter and conjugacy forms of the partition API. -/

/-- Filtering the full cycle type to parts of length at least two recovers the cycle type. -/
@[simp]
theorem _root_.Equiv.Perm.filter_fullCycleType_eq_cycleType {σ : Equiv.Perm α} :
    (fullCycleType σ).filter (fun n => 2 ≤ n) = σ.cycleType := by
  rw [fullCycleType_def]
  exact Equiv.Perm.filter_parts_partition_eq_cycleType

/-- A permutation has a single cycle length `n`, and no other, exactly when it is a cycle
moving `n` points. -/
theorem _root_.Equiv.Perm.cycleType_eq_singleton_iff {σ : Equiv.Perm α} {n : ℕ} :
    σ.cycleType = {n} ↔ σ.IsCycle ∧ σ.support.card = n := by
  refine ⟨fun h => ⟨card_cycleType_eq_one.mp (by rw [h, Multiset.card_singleton]), ?_⟩,
    fun h => by rw [h.1.cycleType, h.2]⟩
  rw [← sum_cycleType, h, Multiset.sum_singleton]

/-- Conjugate permutations have equal full cycle types. -/
theorem _root_.Equiv.Perm.fullCycleType_eq_of_isConj {σ τ : Equiv.Perm α}
    (hστ : IsConj σ τ) : fullCycleType σ = fullCycleType τ := by
  rw [fullCycleType_def, fullCycleType_def]
  exact congrArg Nat.Partition.parts (Equiv.Perm.partition_eq_of_isConj.1 hστ)

/-- The full cycle lengths of a permutation sum to the cardinality of its carrier. -/
@[simp]
theorem _root_.Equiv.Perm.sum_fullCycleType (σ : Equiv.Perm α) :
    (fullCycleType σ).sum = Fintype.card α := by
  rw [fullCycleType_def]
  exact σ.partition.parts_sum

/-- Every part of a permutation's full cycle type is positive. -/
theorem _root_.Equiv.Perm.pos_of_mem_fullCycleType {σ : Equiv.Perm α} {n : ℕ}
    (hn : n ∈ fullCycleType σ) : 0 < n := by
  rw [fullCycleType_def] at hn
  exact σ.partition.parts_pos hn

/-- At every value other than one, `fullCycleType` counts a part as often as
`Equiv.Perm.cycleType` does. -/
@[simp]
theorem _root_.Equiv.Perm.count_fullCycleType_of_ne_one (σ : Equiv.Perm α) {n : ℕ} (hn : n ≠ 1) :
    (fullCycleType σ).count n = σ.cycleType.count n := by
  rw [fullCycleType_def]
  exact Equiv.Perm.count_parts_partition_of_ne_one σ hn

/-- The identity has one full cycle-type part for every point of the carrier. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_one :
    fullCycleType (1 : Equiv.Perm α) = Multiset.replicate (Fintype.card α) 1 := by
  rw [fullCycleType_def, Equiv.Perm.parts_partition_one]

/-- On an empty finite carrier, the full cycle type is empty. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_of_isEmpty [IsEmpty α] (σ : Equiv.Perm α) :
    fullCycleType σ = 0 := by
  rw [fullCycleType_def, Equiv.Perm.parts_partition_of_isEmpty]

/-- The full cycle type is empty exactly when the carrier is empty. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_eq_zero_iff {σ : Equiv.Perm α} :
    fullCycleType σ = 0 ↔ Fintype.card α = 0 := by
  simpa only [fullCycleType_def] using
    (Equiv.Perm.parts_partition_eq_zero_iff (σ := σ))

/-- The full cycle type agrees with the cycle type exactly when there are no fixed points. -/
theorem _root_.Equiv.Perm.fullCycleType_eq_cycleType_iff {σ : Equiv.Perm α} :
    fullCycleType σ = σ.cycleType ↔ σ.support = Finset.univ := by
  simpa only [fullCycleType_def] using
    (Equiv.Perm.parts_partition_eq_cycleType_iff (σ := σ))

/-- A fixed-point-free permutation has no one-parts in its full cycle type. -/
theorem _root_.Equiv.Perm.fullCycleType_eq_cycleType {σ : Equiv.Perm α}
    (hσ : σ.support = Finset.univ) :
    fullCycleType σ = σ.cycleType :=
  fullCycleType_eq_cycleType_iff.2 hσ

/-- Conjugating a permutation does not change its full cycle type. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_conj (g σ : Equiv.Perm α) :
    fullCycleType (g * σ * g⁻¹) = fullCycleType σ := by
  rw [fullCycleType_def, fullCycleType_def,
    Equiv.Perm.parts_partition_conj]

/-- Inverting a permutation does not change its full cycle type. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_inv (σ : Equiv.Perm α) :
    fullCycleType σ⁻¹ = fullCycleType σ := by
  rw [fullCycleType_def, fullCycleType_def,
    Equiv.Perm.parts_partition_inv]

/-- Relabelling the carrier does not change a permutation's full cycle type. -/
@[simp]
theorem _root_.Equiv.Perm.fullCycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    fullCycleType (e.permCongr σ) = fullCycleType σ := by
  rw [fullCycleType_def, fullCycleType_def,
    Equiv.Perm.parts_partition_permCongr]

/-- The parts equal to one in the full cycle type are precisely the fixed points. -/
@[simp]
theorem _root_.Equiv.Perm.count_one_fullCycleType (σ : Equiv.Perm α) :
    (fullCycleType σ).count 1 = Fintype.card α - σ.support.card := by
  rw [fullCycleType_def]
  exact Equiv.Perm.count_one_parts_partition σ

open scoped Classical in
/-- **The full cycle type lists the sizes of the orbits.** If the fibres of `m : α → γ` are
exactly the orbits of `σ`, then the full cycle type of `σ` is the multiset of the sizes of those
fibres, one for each value of `m`. -/
theorem _root_.Equiv.Perm.fullCycleType_eq_map_card_filter {γ : Type*}
    (σ : Equiv.Perm α) (m : α → γ) (hm : ∀ x y, σ.SameCycle x y ↔ m x = m y) :
    fullCycleType σ =
      (Finset.univ.image m).val.map fun c => (Finset.univ.filter fun x => m x = c).card := by
  classical
  set T := Finset.univ.image m
  set fib : γ → ℕ := fun c => (Finset.univ.filter fun x => m x = c).card
  -- A value of `m` is either hit by the support of `σ` or only by fixed points.
  set R : γ → Prop := fun c => ∃ x ∈ σ.support, m x = c
  -- The values hit by the support match the cycle factors, each fibre being a cycle's support.
  have hcycle : (T.filter R).val.map fib = σ.cycleType := by
    rw [cycleType_def, Function.comp_def]
    refine (Multiset.map_eq_map_of_bij_of_nodup _ _ σ.cycleFactorsFinset.nodup
      (T.filter R).nodup
      (fun c hc => m (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose)
      ?_ ?_ ?_ ?_).symm
    · intro c hc
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        _, mem_cycleFactorsFinset_support_le hc hx, rfl⟩
    · intro c hc d hd hcd
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      have hy := (mem_cycleFactorsFinset_iff.mp hd).1.nonempty_support.choose_spec
      rw [cycle_is_cycleOf hx hc, cycle_is_cycleOf hy hd]
      exact ((hm _ _).mpr hcd).cycleOf_eq
    · intro c hc
      obtain ⟨-, x, hx, rfl⟩ := Finset.mem_filter.mp hc
      have hmem : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
        cycleOf_mem_cycleFactorsFinset_iff.mpr hx
      refine ⟨_, hmem, ?_⟩
      have hy := (mem_cycleFactorsFinset_iff.mp hmem).1.nonempty_support.choose_spec
      exact ((hm _ _).mp ((mem_support_cycleOf_iff' (mem_support.mp hx)).mp hy)).symm
    · intro c hc
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      set x := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose
      have hxs : σ x ≠ x := mem_support.mp (mem_cycleFactorsFinset_support_le hc hx)
      rw [cycle_is_cycleOf hx hc]
      congr 1
      ext y
      rw [mem_support_cycleOf_iff' hxs, hm]
      simp [eq_comm]
  -- The remaining values are the images of the fixed points, each with a singleton fibre.
  have hfixed : (T.filter fun c => ¬ R c).val.map fib =
      Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
    have himage : T.filter (fun c => ¬ R c) = σ.supportᶜ.image m := by
      ext c
      simp only [T, R, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_compl, not_exists, not_and]
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        exact ⟨x, fun h => hx x h rfl, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, rfl⟩, fun y hy hxy => mem_support.mp hy
          (((hm y x).mpr hxy).apply_eq_self_iff.mpr (notMem_support.mp hx))⟩
    rw [himage, Multiset.eq_replicate]
    refine ⟨?_, fun n hn => ?_⟩
    · rw [Multiset.card_map, Finset.card_val, Finset.card_image_of_injOn, Finset.card_compl]
      intro x hx y _ hxy
      exact ((hm x y).mpr hxy).eq_of_left (notMem_support.mp (Finset.mem_compl.mp hx))
    · obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      refine Finset.card_eq_one.mpr ⟨x, ?_⟩
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine ⟨fun hxy => ?_, fun h => h ▸ rfl⟩
      exact (((hm x y).mpr hxy.symm).eq_of_left
        (notMem_support.mp (Finset.mem_compl.mp hx))).symm
  rw [fullCycleType, ← hcycle, ← hfixed, ← Multiset.map_add, Finset.filter_val,
    Finset.filter_val, Multiset.filter_add_not]

/-! ### Orbit sizes -/

section OrbitSizes

open MulAction

variable (σ : Equiv.Perm α)

omit [Fintype α] [DecidableEq α] in
/-- Two points lie on the same cycle of `σ` exactly when one is a `⟨σ⟩`-translate of the
other. -/
theorem _root_.Equiv.Perm.sameCycle_iff_mem_orbit_zpowers {x y : α} :
    σ.SameCycle x y ↔ y ∈ orbit (Subgroup.zpowers σ) x := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨⟨σ ^ i, Subgroup.zpow_mem_zpowers σ i⟩, hi⟩
  · rintro ⟨g, hg⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp g.2
    exact ⟨i, by rw [hi]; exact hg⟩

omit [Fintype α] [DecidableEq α] in
/-- The orbit relation of `⟨σ⟩` is the same-cycle relation of `σ`. -/
theorem _root_.Equiv.Perm.orbitRel_zpowers_apply {x y : α} :
    orbitRel (Subgroup.zpowers σ) α x y ↔ σ.SameCycle x y := by
  rw [orbitRel_apply, ← sameCycle_iff_mem_orbit_zpowers]
  exact ⟨SameCycle.symm, SameCycle.symm⟩

/-- The `⟨σ⟩`-orbit of a moved point is the support of its cycle. -/
theorem _root_.Equiv.Perm.coe_support_cycleOf_eq_orbit_zpowers {x : α} (hx : x ∈ σ.support) :
    ((σ.cycleOf x).support : Set α) = orbit (Subgroup.zpowers σ) x := by
  ext y
  rw [Finset.mem_coe, mem_support_cycleOf_iff, ← sameCycle_iff_mem_orbit_zpowers]
  exact and_iff_left hx

omit [Fintype α] [DecidableEq α] in
/-- The `⟨σ⟩`-orbit of a fixed point is a singleton. -/
theorem _root_.Equiv.Perm.orbit_zpowers_eq_singleton {x : α} (hx : σ x = x) :
    orbit (Subgroup.zpowers σ) x = {x} := by
  ext y
  rw [← sameCycle_iff_mem_orbit_zpowers, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact zpow_apply_eq_self_of_apply_eq_self hx i
  · rintro rfl
    exact SameCycle.refl σ y

/-- The fixed points of a permutation are the complement of its support. -/
theorem _root_.Equiv.Perm.card_subtype_apply_eq :
    Fintype.card {x : α // σ x = x} = Fintype.card α - σ.support.card := by
  have hp : (fun x : α => σ x = x) = (fun x => x ∈ σ.supportᶜ) := by
    funext x
    simp [mem_support]
  calc
    _ = Fintype.card {x : α // x ∈ σ.supportᶜ} := Fintype.card_congr (Equiv.subtypeEquivProp hp)
    _ = σ.supportᶜ.card := Fintype.card_coe _
    _ = Fintype.card α - σ.support.card := Finset.card_compl (s := σ.support)

/-- The cycle factor of a moved point, or the point itself when it is fixed: the point-level map
underlying `Equiv.Perm.orbitQuotientEquivCycleFactorsSumFixedPoints`. -/
def _root_.Equiv.Perm.cycleFactorOrFixedPoint (x : α) :
    σ.cycleFactorsFinset ⊕ {x : α // σ x = x} :=
  if hx : σ x = x then Sum.inr ⟨x, hx⟩
  else Sum.inl ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩

@[simp]
theorem _root_.Equiv.Perm.cycleFactorOrFixedPoint_of_apply_eq {x : α} (hx : σ x = x) :
    σ.cycleFactorOrFixedPoint x = Sum.inr ⟨x, hx⟩ :=
  dite_eq_left hx

@[simp]
theorem _root_.Equiv.Perm.cycleFactorOrFixedPoint_of_apply_ne {x : α} (hx : σ x ≠ x) :
    σ.cycleFactorOrFixedPoint x =
      Sum.inl ⟨σ.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩ :=
  dite_eq_right hx

/-- The orbits of a permutation are its nontrivial cycle factors together with its fixed points.
This is the set-level decomposition underlying the full cycle partition: a nontrivial orbit is
sent to the unique member of `cycleFactorsFinset`, while a singleton orbit is sent to its fixed
point. -/
noncomputable def _root_.Equiv.Perm.orbitQuotientEquivCycleFactorsSumFixedPoints :
    Quotient (SameCycle.setoid σ) ≃ σ.cycleFactorsFinset ⊕ {x : α // σ x = x} where
  toFun := Quotient.lift σ.cycleFactorOrFixedPoint fun x y hxy => by
    have hfixed : σ x = x ↔ σ y = y := SameCycle.apply_eq_self_iff hxy
    by_cases hx : σ x = x
    · rw [cycleFactorOrFixedPoint_of_apply_eq σ hx,
        cycleFactorOrFixedPoint_of_apply_eq σ (hfixed.mp hx)]
      exact congrArg Sum.inr (Subtype.ext (hxy.eq_of_left hx))
    · rw [cycleFactorOrFixedPoint_of_apply_ne σ hx,
        cycleFactorOrFixedPoint_of_apply_ne σ (mt hfixed.mpr hx)]
      exact congrArg Sum.inl (Subtype.ext hxy.cycleOf_eq)
  invFun := Sum.elim
    (fun c => Quotient.mk (SameCycle.setoid σ)
      (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1).choose)
    (fun x => Quotient.mk (SameCycle.setoid σ) x.1)
  left_inv q := by
    induction q using Quotient.ind with
    | _ x =>
      by_cases hx : σ x = x
      · rw [Quotient.lift_mk, cycleFactorOrFixedPoint_of_apply_eq σ hx, Sum.elim_inr]
      · rw [Quotient.lift_mk, cycleFactorOrFixedPoint_of_apply_ne σ hx, Sum.elim_inl]
        exact Quotient.sound ((mem_support_cycleOf_iff' hx).mp (IsCycle.nonempty_support
          (mem_cycleFactorsFinset_iff.mp (cycleOf_mem_cycleFactorsFinset_iff.mpr
            (mem_support.mpr hx))).1).choose_spec).symm
  right_inv := by
    rintro (c | x)
    · have hc := (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1).choose_spec
      rw [Sum.elim_inl, Quotient.lift_mk, cycleFactorOrFixedPoint_of_apply_ne σ
        (mem_support.mp (mem_cycleFactorsFinset_support_le c.2 hc))]
      exact congrArg Sum.inl (Subtype.ext (cycle_is_cycleOf hc c.2).symm)
    · rw [Sum.elim_inr, Quotient.lift_mk, cycleFactorOrFixedPoint_of_apply_eq σ x.2]

@[simp]
theorem _root_.Equiv.Perm.orbitQuotientEquivCycleFactorsSumFixedPoints_mk (x : α) :
    σ.orbitQuotientEquivCycleFactorsSumFixedPoints (Quotient.mk (SameCycle.setoid σ) x) =
      σ.cycleFactorOrFixedPoint x :=
  (rfl)

open scoped Classical in
/-- **The full cycle type lists the orbit sizes.** The full cycle type of `σ` is the multiset of
the sizes of the orbits of `⟨σ⟩` on the carrier: the cycles of length at least two are the orbits
of the moved points, and each fixed point is an orbit of size one. -/
theorem _root_.Equiv.Perm.fullCycleType_eq_map_card_orbit :
    fullCycleType σ =
      (Finset.univ : Finset (orbitRel.Quotient (Subgroup.zpowers σ) α)).val.map
        (fun ω => Nat.card ω.orbit) := by
  -- The `⟨σ⟩`-orbit classes are the cycle classes, hence the cycle factors and the fixed points.
  -- The relation of `SameCycle.setoid σ` is `σ.SameCycle` by definition, whence the `Iff.rfl`.
  let e : orbitRel.Quotient (Subgroup.zpowers σ) α ≃ σ.cycleFactorsFinset ⊕ {x : α // σ x = x} :=
    (Quotient.congrRight fun x y => (orbitRel_zpowers_apply σ).trans Iff.rfl).trans
      σ.orbitQuotientEquivCycleFactorsSumFixedPoints
  -- `Quotient.congrRight` and `Quotient.lift` both compute on representatives.
  have he : ∀ x : α, e (Quotient.mk'' x) = σ.cycleFactorOrFixedPoint x := fun _ => rfl
  -- Through `e`, a class of moved points has the size of its cycle, a fixed point has size one.
  have hcard : ∀ ω : orbitRel.Quotient (Subgroup.zpowers σ) α, Nat.card ω.orbit =
      Sum.elim (fun c : σ.cycleFactorsFinset => c.1.support.card) (fun _ => 1) (e ω) := by
    intro ω
    refine Quotient.inductionOn' ω fun x => ?_
    rw [orbitRel.Quotient.orbit_mk, he]
    by_cases hx : σ x = x
    · rw [cycleFactorOrFixedPoint_of_apply_eq σ hx, Sum.elim_inr,
        orbit_zpowers_eq_singleton σ hx, Nat.card_coe_set_eq,
        Set.ncard_singleton]
    · rw [cycleFactorOrFixedPoint_of_apply_ne σ hx, Sum.elim_inl,
        ← coe_support_cycleOf_eq_orbit_zpowers σ (mem_support.mpr hx), Nat.card_coe_set_eq,
        Set.ncard_coe_finset]
  -- Split the sum type into cycles and fixed points, then reindex the classes along `e`.
  calc fullCycleType σ
      = (Finset.univ : Finset (σ.cycleFactorsFinset ⊕ {x : α // σ x = x})).val.map
          (Sum.elim (fun c => c.1.support.card) fun _ => 1) := by
        rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum, Multiset.map_add,
          Multiset.map_map, Multiset.map_map, fullCycleType, cycleType_def]
        congr 1
        · rw [Finset.univ_eq_attach, Finset.attach_val]
          exact (Multiset.attach_map_val' _ _).symm
        · -- `Multiset.map_const'` matches only the literal form `fun _ => 1`; the composite
          -- `Sum.elim _ (fun _ => 1) ∘ Sum.inr` is that function by `rfl` (`Sum.elim_inr`), so
          -- reshape it before rewriting.
          rw [show (Sum.elim (fun c : σ.cycleFactorsFinset => c.1.support.card) (fun _ => 1) ∘
              Sum.inr) = fun _ => 1 from rfl,
            Multiset.map_const', Finset.card_val, Finset.card_univ, card_subtype_apply_eq]
    _ = (Finset.univ.map e.toEmbedding).val.map
          (Sum.elim (fun c => c.1.support.card) fun _ => 1) := by
        rw [Finset.map_univ_equiv]
    _ = _ := by
        rw [Finset.map_val, Multiset.map_map]
        exact Multiset.map_congr rfl fun ω _ => (hcard ω).symm

end OrbitSizes

/-! ### Worked examples

The three shapes that the degree-four recognition theorems read off a factorization type. -/

example : Equiv.Perm.fullCycleType (1 : Equiv.Perm (Fin 4)) = {1, 1, 1, 1} := by decide

example : Equiv.Perm.fullCycleType (swap 0 1 : Equiv.Perm (Fin 4)) = {2, 1, 1} := by decide

example : Equiv.Perm.fullCycleType (finRotate 4) = {4} := by decide

end TauCeti
