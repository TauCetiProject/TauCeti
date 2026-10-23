/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import TauCeti.Combinatorics.NoncrossingPartition.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
public import TauCeti.GroupTheory.Perm.SwapFactors
import TauCeti.Data.Fin.Basic

/-!
# Boundary cycles of one-vertex chord diagrams

A one-vertex chord diagram is a disc with `m` untwisted bands attached along its boundary. Its
`n` attaching points are numbered `0, …, n - 1` counterclockwise around the boundary circle, so
that turning to the next point is `finRotate n`, and the bands form a matching of these points,
an involution `σ` of `Fin n` joining the two ends `a`, `σ a` of each band; fixed points of `σ`
are unused marked points of the circle, which subdivide it without changing anything. The
boundary of the resulting ribbon surface is traversed by `finRotate n * σ`: cross the band at the
current point, then turn to the next point. Its cycles are the boundary cycles of the diagram.

This file proves the boundary-count criterion for planarity of such a diagram. The diagram has
`m = n - orbitCount σ` bands, and

* it has at most `m + 1` boundary cycles: adding one band raises the count by at most one
  (`Equiv.Perm.orbitCount_finRotate_mul_add_orbitCount_le`);
* two interleaved bands have a single boundary cycle
  (`TauCeti.orbitCount_finRotate_mul_swap_mul_swap`), so a diagram containing an interleaved
  pair has at most `m - 1` boundary cycles
  (`TauCeti.orbitCount_finRotate_mul_add_orbitCount_add_two_le`);
* it has exactly `m + 1` boundary cycles if and only if no two bands interleave
  (`Function.Involutive.orbitCount_finRotate_mul_add_orbitCount_eq_iff`). For the converse, a
  noncrossing matching has an innermost band, whose two ends are joined by a boundary arc
  containing no other band (`Equiv.Perm.IsNoncrossingMatching.exists_forall_apply_eq_self`);
  deleting it removes exactly one boundary cycle, and the remaining bands are again noncrossing.

Equivalently, the closed surface obtained by capping the boundary cycles has Euler characteristic
`1 - m + #boundary cycles`, and the diagram is a sphere, that is, planar, exactly when its bands
do not interleave. One-vertex ribbon graphs arise by contracting a spanning tree of a connected
ribbon graph, such as the underlying graph of a link diagram, and this criterion is the
noncrossing consequence of planarity in that one-vertex case. For perfect matchings of
`Fin (2 * m)`, where every boundary point is the end of a band, the criterion reads
`orbitCount (finRotate (2 * m) * σ) = m + 1`
(`TauCeti.IsPerfectMatching.orbitCount_finRotate_mul_eq_iff`).

## Main definitions

* `Equiv.Perm.IsNoncrossingMatching σ`: no two chords `{a, σ a}` and `{b, σ b}` of `σ`
  interleave.

## Main results

* `Function.Involutive.isNoncrossingMatching_iff`: an involution is a noncrossing matching
  exactly when its orbit partition is a noncrossing partition.
* `Equiv.Perm.orbitCount_finRotate_mul_add_orbitCount_le`: the boundary-count bound.
* `TauCeti.orbitCount_finRotate_mul_swap_mul_swap`: two interleaved bands have one boundary
  cycle.
* `TauCeti.orbitCount_finRotate_mul_add_orbitCount_add_two_le`: an interleaved pair of bands
  loses two boundary cycles from the bound.
* `Equiv.Perm.IsNoncrossingMatching.orbitCount_finRotate_mul_add_orbitCount`,
  `Function.Involutive.orbitCount_finRotate_mul_add_orbitCount_eq_iff`: the bound is attained
  exactly by the noncrossing matchings.
* `TauCeti.IsPerfectMatching.orbitCount_finRotate_mul_le`,
  `TauCeti.IsPerfectMatching.orbitCount_finRotate_mul_eq_iff`: the same for perfect matchings.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 (rotation systems and their faces) and §3.4
  (chord diagrams).
* P. Biane, *Some properties of crossings and partitions*, Discrete Math. 175 (1997), 41–53
  (noncrossing permutations as geodesics to the full cycle).
-/

public section

open Equiv TauCeti

namespace Equiv.Perm

section LinearOrder

variable {α : Type*} [LinearOrder α] {σ τ : Perm α}

/-- A permutation `σ` of a linearly ordered type, read as the matching joining each `a` to `σ a`,
is a **noncrossing matching** when no two of its chords interleave: there are no
`a < b < σ a < σ b`. For an involution the chords are the pairs `{a, σ a}` with `σ a ≠ a`, and
the condition says that they are pairwise noninterleaving, so that they can be drawn disjointly
inside a disc whose boundary meets them in the order of `α`. Equivalently, the partition of `α`
into the orbits of the involution is noncrossing in the sense of `Finpartition.IsNoncrossing`
(`Function.Involutive.isNoncrossingMatching_iff`); the condition is stated directly on the
permutation, the form in which chord diagrams arise. -/
def IsNoncrossingMatching (σ : Perm α) : Prop :=
  ∀ ⦃a b : α⦄, a < b → b < σ a → ¬ σ a < σ b

/-- The defining condition of `Equiv.Perm.IsNoncrossingMatching`. -/
theorem isNoncrossingMatching_iff :
    σ.IsNoncrossingMatching ↔ ∀ ⦃a b : α⦄, a < b → b < σ a → ¬ σ a < σ b :=
  Iff.rfl

/-- A matching fails to be noncrossing exactly when two of its chords interleave. -/
theorem not_isNoncrossingMatching_iff :
    ¬ σ.IsNoncrossingMatching ↔ ∃ a b, a < b ∧ b < σ a ∧ σ a < σ b := by
  simp [IsNoncrossingMatching]

/-- The empty matching is noncrossing. -/
@[simp]
theorem isNoncrossingMatching_one : (1 : Perm α).IsNoncrossingMatching :=
  fun _ _ hab hba _ => lt_asymm hab (by simpa using hba)

/-- A matching whose chords are chords of a noncrossing matching is noncrossing: if `τ` agrees
with `σ` away from its fixed points, then `τ` is noncrossing when `σ` is. -/
theorem IsNoncrossingMatching.of_forall_apply_eq_or (hσ : σ.IsNoncrossingMatching)
    (h : ∀ x, τ x = x ∨ τ x = σ x) : τ.IsNoncrossingMatching := by
  intro a b hab hba hlt
  rcases h a with ha | ha
  · exact lt_asymm hab (ha ▸ hba)
  rcases h b with hb | hb
  · exact lt_asymm hba (hb ▸ hlt)
  exact hσ hab (ha ▸ hba) (ha ▸ hb ▸ hlt)

end LinearOrder

end Equiv.Perm

/-- An involution of a finite linear order is a noncrossing matching exactly when the partition
into its orbits, the pairs `{a, σ a}` and the fixed points, is a noncrossing partition. Any
decidability instance for the orbit relation may be used, for instance a classical one. -/
theorem Function.Involutive.isNoncrossingMatching_iff {α : Type*} [Fintype α] [LinearOrder α]
    {σ : Perm α} [DecidableRel (Perm.SameCycle.setoid σ)] (hinv : Function.Involutive σ) :
    σ.IsNoncrossingMatching ↔ (Finpartition.ofSetoid (Perm.SameCycle.setoid σ)).IsNoncrossing := by
  have hsc : ∀ a b, σ.SameCycle a b ↔ a = b ∨ a = σ b := fun a b => by
    simpa [show hinv.toPerm σ = σ from Equiv.ext fun _ => rfl] using
      sameCycle_toPerm_iff σ hinv a b
  simp only [Finpartition.isNoncrossing_iff_part, Finset.mem_univ, true_implies,
    Finpartition.mem_part_ofSetoid_iff_rel]
  refine ⟨fun hσ a b c hac d hbd hab hbc hcd => ?_, fun hP a b hab hba hlt => ?_⟩
  · rcases (hsc a c).1 hac with rfl | rfl
    · exact (lt_asymm hab hbc).elim
    rcases (hsc b d).1 hbd with rfl | rfl
    · exact (lt_asymm hbc hcd).elim
    exact (hσ hab (by rwa [hinv c]) (by rwa [hinv c, hinv d])).elim
  · have := hP a b (σ a) ((hsc a (σ a)).2 (Or.inr (hinv a).symm)) (σ b)
      ((hsc b (σ b)).2 (Or.inr (hinv b).symm)) hab hba hlt
    rcases (hsc a b).1 (Finpartition.mem_part_ofSetoid_iff_rel.1
      (this ▸ (Finpartition.ofSetoid _).mem_part_self.2 (Finset.mem_univ b))) with rfl | h
    · exact lt_irrefl _ hab
    · exact lt_irrefl b (by rwa [h, hinv b] at hba)

/-! ### Boundary cycles -/

namespace TauCeti

variable {n : ℕ}

/-- If the matching `σ` fixes `a` and every point strictly between `a` and `c`, then the boundary
traversal `finRotate n * σ` runs along the boundary circle from `a` to `c`. -/
theorem sameCycle_finRotate_mul_of_forall_apply_eq_self {σ : Perm (Fin n)} {a c : Fin n}
    (hac : a ≤ c) (h : ∀ x, a ≤ x → x < c → σ x = x) :
    (finRotate n * σ).SameCycle a c := by
  have hwalk : ∀ j : ℕ, (a : ℕ) + j ≤ c → (((finRotate n * σ) ^ j) a : ℕ) = a + j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hx := ih (by omega)
      have hσx : σ (((finRotate n * σ) ^ j) a) = ((finRotate n * σ) ^ j) a :=
        h _ (by rw [Fin.le_def, hx]; omega) (by rw [Fin.lt_def, hx]; omega)
      rw [pow_succ', Perm.mul_apply, Perm.mul_apply, hσx,
        Fin.coe_finRotate_of_add_one_lt (by rw [hx]; omega), hx, add_assoc]
  refine ⟨((c : ℕ) - a : ℕ), Fin.ext ?_⟩
  rw [zpow_natCast, hwalk _ (by rw [Fin.le_def] at hac; omega)]
  rw [Fin.le_def] at hac
  omega

/-- **Two interleaved bands have one boundary cycle.** For boundary points `a < b < c < d`, the
chord diagram with the two bands `{a, c}` and `{b, d}` has a single boundary cycle. -/
theorem orbitCount_finRotate_mul_swap_mul_swap {a b c d : Fin n} (hab : a < b) (hbc : b < c)
    (hcd : c < d) : orbitCount (finRotate n * swap a c * swap b d) = 1 := by
  rw [Fin.lt_def] at hab hbc hcd
  have hd := d.isLt
  have hn : n ≠ 0 := by omega
  -- The band `{a, c}` cuts the boundary circle in two cycles.
  have hac : (finRotate n).SameCycle a c := by
    simpa using sameCycle_finRotate_mul_of_forall_apply_eq_self (σ := 1) (a := a) (c := c)
      (Fin.le_def.mpr (by omega)) (fun _ _ _ => rfl)
  have h2 : orbitCount (finRotate n * swap a c) = 2 := by
    rw [orbitCount_mul_swap_of_sameCycle (Fin.ne_of_lt (Fin.lt_def.mpr (by omega))) hac,
      orbitCount_finRotate]
    simp [hn]
  -- One of them runs through the points of `(a, c]`, which contains `b` but not `d`.
  have hmaps : ∀ x : Fin n, (a : ℕ) < x → (x : ℕ) ≤ c →
      (a : ℕ) < (finRotate n * swap a c) x ∧ ((finRotate n * swap a c) x : ℕ) ≤ c := by
    intro x hax hxc
    rcases eq_or_ne x c with rfl | hxc'
    · rw [Perm.mul_apply, swap_apply_right, Fin.coe_finRotate_of_add_one_lt (by omega)]
      omega
    · have hxc'' : (x : ℕ) < c := lt_of_le_of_ne hxc (Fin.val_ne_of_ne hxc')
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Fin.ne_of_gt (Fin.lt_def.mpr hax)) hxc',
        Fin.coe_finRotate_of_add_one_lt (by omega)]
      omega
  have hbd : ¬ (finRotate n * swap a c).SameCycle b d := by
    intro hsc
    obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
    have hiter : ∀ j : ℕ, (a : ℕ) < ((finRotate n * swap a c) ^ j) b ∧
        (((finRotate n * swap a c) ^ j) b : ℕ) ≤ c := by
      intro j
      induction j with
      | zero => simp only [pow_zero, Perm.one_apply]; omega
      | succ j ih =>
        rw [pow_succ', Perm.mul_apply (finRotate n * swap a c)]
        exact hmaps _ ih.1 ih.2
    have := (hiter k).2
    rw [hk] at this
    omega
  have := orbitCount_mul_swap_add_one_of_not_sameCycle hbd
  omega

/-- **An interleaved pair of bands loses two boundary cycles.** If two chords of `σ` interleave,
`a < b < σ a < σ b`, then the chord diagram of `σ`, with `m = n - orbitCount σ` bands, has at
most `m - 1` boundary cycles: the two interleaved bands have one boundary cycle, and each of the
other `m - 2` bands raises the count by at most one. -/
theorem orbitCount_finRotate_mul_add_orbitCount_add_two_le {σ : Perm (Fin n)} {a b : Fin n}
    (hab : a < b) (hb : b < σ a) (hσ : σ a < σ b) :
    orbitCount (finRotate n * σ) + orbitCount σ + 2 ≤ n + 1 := by
  -- Remove the two interleaved chords `{a, σ a}` and `{b, σ b}`, one after the other.
  have h1 : orbitCount (swap a (σ a) * σ) = orbitCount σ + 1 :=
    orbitCount_swap_mul_of_sameCycle (Fin.ne_of_lt (hab.trans hb)) ⟨1, by simp⟩
  have hbd : (swap a (σ a) * σ) b = σ b :=
    swap_apply_of_ne_of_ne (Fin.ne_of_gt ((hab.trans hb).trans hσ)) (Fin.ne_of_gt hσ)
  have h2 : orbitCount (swap b (σ b) * (swap a (σ a) * σ)) = orbitCount σ + 2 := by
    rw [orbitCount_swap_mul_of_sameCycle (Fin.ne_of_lt (hb.trans hσ)) ⟨1, by simp [hbd]⟩, h1]
  have hprod : finRotate n * σ =
      finRotate n * swap a (σ a) * swap b (σ b) * (swap b (σ b) * (swap a (σ a) * σ)) := by
    simp only [mul_assoc, swap_mul_self_mul]
  have hle := Perm.orbitCount_mul_add_orbitCount_le_orbitCount_add_card
    (finRotate n * swap a (σ a) * swap b (σ b)) (swap b (σ b) * (swap a (σ a) * σ))
  rw [← hprod, h2, orbitCount_finRotate_mul_swap_mul_swap hab hb hσ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hle
  omega

end TauCeti

namespace Equiv.Perm

variable {n : ℕ}

/-- **The boundary-count bound.** A chord diagram on `n` boundary points with matching `σ` has
`m = n - orbitCount σ` bands and at most `m + 1` boundary cycles: adding one band raises the
number of boundary cycles by at most one. -/
theorem orbitCount_finRotate_mul_add_orbitCount_le (σ : Perm (Fin n)) :
    orbitCount (finRotate n * σ) + orbitCount σ ≤ n + 1 := by
  have := orbitCount_mul_add_orbitCount_le_orbitCount_add_card (finRotate n) σ
  rw [orbitCount_finRotate, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  split_ifs at this <;> omega

/-- A noncrossing involution other than the identity has an **innermost chord**: a chord
`{a, σ a}` with `a < σ a` whose arc of the boundary circle from `a` to `σ a` contains no end of
another chord. -/
theorem IsNoncrossingMatching.exists_forall_apply_eq_self {σ : Perm (Fin n)}
    (hσ : σ.IsNoncrossingMatching) (hinv : Function.Involutive σ) (h1 : σ ≠ 1) :
    ∃ a, a < σ a ∧ ∀ x, a < x → x < σ a → σ x = x := by
  classical
  -- The left ends of the chords, and among them one whose chord is shortest.
  have hne : (Finset.univ.filter fun a => a < σ a).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra! hcon
      exact h1 (Equiv.ext hcon)
    rcases lt_or_gt_of_ne hx with hlt | hlt
    · exact ⟨σ x, by simpa [hinv x] using hlt⟩
    · exact ⟨x, by simpa using hlt⟩
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image _ (fun a => (σ a : ℕ) - a) hne
  rw [Finset.mem_filter] at ha
  refine ⟨a, ha.2, fun x hax hxa => ?_⟩
  by_contra hx
  have hmin' : ∀ y, y < σ y → (σ a : ℕ) - a ≤ (σ y : ℕ) - y := fun y hy =>
    hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
  rcases lt_trichotomy (σ x) a with hlt | heq | hgt
  · -- The chord `{σ x, x}` would interleave with `{a, σ a}`.
    exact hσ hlt (by rwa [hinv x]) (by rwa [hinv x])
  · exact (ne_of_lt hxa) (by rw [← heq, hinv x])
  rcases lt_trichotomy (σ x) (σ a) with hlt' | heq' | hgt'
  · -- The chord `{x, σ x}` would lie strictly inside `{a, σ a}`, so it would be shorter.
    rw [Fin.lt_def] at hax hxa hgt hlt'
    rcases lt_or_gt_of_ne hx with hlt'' | hlt''
    · have := hmin' (σ x) (by rwa [hinv x])
      rw [hinv x, Fin.lt_def] at *
      omega
    · have := hmin' x hlt''
      rw [Fin.lt_def] at hlt''
      omega
  · exact (ne_of_lt hax) (σ.injective heq').symm
  · exact hσ hax hxa hgt'

/-- **A noncrossing matching attains the boundary-count bound.** A chord diagram whose `m` bands do
not interleave has exactly `m + 1` boundary cycles. -/
theorem IsNoncrossingMatching.orbitCount_finRotate_mul_add_orbitCount [NeZero n]
    {σ : Perm (Fin n)} (hσ : σ.IsNoncrossingMatching) (hinv : Function.Involutive σ) :
    orbitCount (finRotate n * σ) + orbitCount σ = n + 1 := by
  induction hk : n - orbitCount σ using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
  by_cases h1 : σ = 1
  · subst h1
    simp [orbitCount_finRotate, NeZero.ne n, add_comm]
  -- Delete an innermost chord `{a, σ a}`; it joins two points of one boundary cycle.
  obtain ⟨a, ha, hin⟩ := hσ.exists_forall_apply_eq_self hinv h1
  set τ := swap a (σ a) * σ with hτ
  have hτσ : ∀ x, τ x = x ∨ τ x = σ x := fun x => by
    rcases hinv.swap_mul_apply_eq_self_or a x with ⟨-, hx⟩ | ⟨-, -, hx⟩
    exacts [Or.inl hx, Or.inr hx]
  have hsplit : orbitCount τ = orbitCount σ + 1 :=
    orbitCount_swap_mul_of_sameCycle (Fin.ne_of_lt ha) ⟨1, by simp⟩
  have hlt := orbitCount_lt_card_of_ne_one h1
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hlt
  have hih := ih (n - orbitCount τ) (by omega) (hσ.of_forall_apply_eq_or hτσ)
    (hinv.swap_mul a) rfl
  have hsc : (finRotate n * τ).SameCycle a (σ a) := by
    refine sameCycle_finRotate_mul_of_forall_apply_eq_self ha.le fun x hax hxc => ?_
    rcases hinv.swap_mul_apply_eq_self_or a x with ⟨-, hx⟩ | ⟨hxa, -, hx⟩
    · exact hx
    · rw [hx, hin x (lt_of_le_of_ne hax (Ne.symm hxa)) hxc]
  have hrot := orbitCount_mul_swap_of_sameCycle (Fin.ne_of_lt ha) hsc
  rw [mul_assoc, show τ * swap a (σ a) = σ from hinv.swap_mul_mul_swap a] at hrot
  omega

end Equiv.Perm

/-- **The boundary-count criterion for noninterleaving.** A chord diagram on a nonempty boundary
circle, with matching an involution `σ` and `m = n - orbitCount σ` bands, has exactly `m + 1`
boundary cycles if and only if no two of its bands interleave. -/
theorem Function.Involutive.orbitCount_finRotate_mul_add_orbitCount_eq_iff {n : ℕ} [NeZero n]
    {σ : Perm (Fin n)} (hinv : Function.Involutive σ) :
    orbitCount (finRotate n * σ) + orbitCount σ = n + 1 ↔ σ.IsNoncrossingMatching := by
  refine ⟨fun h => ?_, fun hσ => hσ.orbitCount_finRotate_mul_add_orbitCount hinv⟩
  by_contra hσ
  obtain ⟨a, b, hab, hb, hlt⟩ := Perm.not_isNoncrossingMatching_iff.mp hσ
  have := orbitCount_finRotate_mul_add_orbitCount_add_two_le hab hb hlt
  omega

namespace TauCeti.IsPerfectMatching

variable {m : ℕ} {σ : Perm (Fin (2 * m))}

/-- A chord diagram whose `2 * m` boundary points are the ends of `m` bands has at most `m + 1`
boundary cycles. -/
theorem orbitCount_finRotate_mul_le (hσ : IsPerfectMatching σ) :
    orbitCount (finRotate (2 * m) * σ) ≤ m + 1 := by
  have := σ.orbitCount_finRotate_mul_add_orbitCount_le
  have h := hσ.two_mul_orbitCount
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- **The boundary-count criterion for a perfect matching.** A chord diagram whose `2 * m`
boundary points are the ends of `m ≠ 0` bands has `m + 1` boundary cycles exactly when no two
bands interleave. -/
theorem orbitCount_finRotate_mul_eq_iff [NeZero m] (hσ : IsPerfectMatching σ) :
    orbitCount (finRotate (2 * m) * σ) = m + 1 ↔ σ.IsNoncrossingMatching := by
  have h := hσ.two_mul_orbitCount
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have : NeZero (2 * m) := ⟨by simp [NeZero.ne m]⟩
  rw [← hσ.involutive.orbitCount_finRotate_mul_add_orbitCount_eq_iff]
  omega

end TauCeti.IsPerfectMatching
