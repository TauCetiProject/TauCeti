/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Flow
public import TauCeti.Combinatorics.Network.Walk

/-!
# Walk assignments and augmentation along residual walks

Weighting a directed walk `p` by `q : K` gives the arrow assignment `walkAssignment p q`, which
places `n • q` on an arrow that `p` traverses `n` times; natural-number scalar multiplication needs
no multiplicative structure on `K`. A walk from `s` to `t` raises the excess at `t` by `q` and
lowers the excess at `s` by `q`, so a closed walk gives a circulation. A walk that repeats no
arrow, such as a directed path or cycle, places `q` on each arrow it traverses and zero elsewhere.
For `0 ≤ q` it is then an ordinary `s`–`t` flow for any nonnegative capacities that are at least
`q` along the walk.

Applied to the residual arrows of a feasible assignment, this is augmentation. Augmenting an
ordinary `s`–`t` flow between distinct terminals `s ≠ t` along a residual walk that repeats no
arrow, by an amount between zero and the residual capacities along the walk, gives a flow of value
larger by that amount. The largest such amount is the *bottleneck* of the walk, its least residual
capacity, which is positive on an augmenting path, where every residual capacity is positive.
Directed paths and cycles repeat no arrow (`TauCeti.ArrowWalk.IsPath.nodup_arrows`,
`TauCeti.ArrowWalk.IsCycle.nodup_arrows`), so all of this applies to them. Along a closed
residual walk that repeats no arrow, the residual update preserves feasibility for arbitrary lower
and upper bounds and preserves every excess: this is cycle augmentation of bounded circulations.

## Main definitions

* `TauCeti.walkAssignment p q`: the assignment of the walk `p` weighted by `q`.
* `TauCeti.walkFlow`: a walk repeating no arrow, weighted by a feasible amount, as an ordinary
  flow.
* `TauCeti.Flow.augmentWalk`: augmentation of an ordinary flow along a residual walk.
* `TauCeti.Flow.augmentBottleneck`: augmentation by the bottleneck of the residual walk.

## Main results

* `TauCeti.excessAt_walkAssignment`: a walk from `s` to `t` weighted by `q` has excess `q` at `t`
  and `-q` at `s`.
* `TauCeti.walkAssignment_mem_Icc`: a walk repeating no arrow, weighted by `q`, lies between zero
  and any nonnegative capacities that are at least `q` along the walk.
* `TauCeti.Flow.val_augmentWalk` and `TauCeti.Flow.val_augmentBottleneck`: augmentation along a
  residual `s`–`t` walk between distinct terminals `s ≠ t` increases the value by the augmenting
  amount.
* `TauCeti.Flow.val_lt_val_augmentBottleneck`: augmentation along an augmenting `s`–`t` path by its
  bottleneck strictly increases the value.
* `TauCeti.Flow.augmentBottleneck_toFun_mem`: augmentation by the bottleneck preserves arrow values
  in an additive subgroup containing the capacities.
* `TauCeti.residualUpdate_walkAssignment_mem_Icc` and
  `TauCeti.excessAt_residualUpdate_walkAssignment_self`: augmentation along a residual walk
  preserves feasibility, and along a closed walk it also preserves every excess.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canadian J. Math. 8 (1956).
* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993 (augmenting paths and cycles).
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

/-! ### Walk assignments -/

section AddCommMonoid

variable [AddCommMonoid K]

open Classical in
/-- The assignment of the walk `p` weighted by `q`: an arrow traversed `n` times by `p` carries
`n • q`. -/
noncomputable def walkAssignment {s t : V} (p : ArrowWalk Q s t) (q : K) : Assignment Q K :=
  fun _ _ e ↦ p.arrows.count ⟨_, _, e⟩ • q

open Classical in
theorem walkAssignment_apply {s t : V} (p : ArrowWalk Q s t) (q : K) {x y : V} (e : Q x y) :
    walkAssignment p q e = p.arrows.count ⟨_, _, e⟩ • q :=
  (rfl)

@[simp]
theorem walkAssignment_nil (s : V) (q : K) :
    walkAssignment (ArrowWalk.nil s : ArrowWalk Q s s) q = 0 := by
  funext x y e
  simp [walkAssignment_apply]

@[simp]
theorem walkAssignment_zero {s t : V} (p : ArrowWalk Q s t) :
    walkAssignment p (0 : K) = 0 := by
  funext x y e
  simp [walkAssignment_apply]

/-- Extending a walk by an arrow adds the weight on that arrow. -/
@[simp]
theorem walkAssignment_cons {s t x : V} (p : ArrowWalk Q s t) (e : Q t x) (q : K) :
    walkAssignment (p.cons e) q = walkAssignment p q + Assignment.single e q := by
  classical
  funext a b e'
  -- `count_singleton` and `Assignment.single_apply` compare the two arrows in opposite orders.
  simp only [walkAssignment_apply, ArrowWalk.arrows_cons, List.count_append, add_nsmul,
    Pi.add_apply, Assignment.single_apply, List.count_singleton, beq_iff_eq,
    eq_comm (a := (⟨t, x, e⟩ : Σ a b, Q a b))]
  split_ifs <;> simp only [one_nsmul, zero_nsmul, add_zero]

/-- The assignment of a concatenation is the sum of the assignments of its pieces. -/
@[simp]
theorem walkAssignment_comp {s t x : V} (p : ArrowWalk Q s t) (p' : ArrowWalk Q t x) (q : K) :
    walkAssignment (p.comp p') q = walkAssignment p q + walkAssignment p' q := by
  classical
  funext a b e
  simp [walkAssignment_apply, List.count_append, add_nsmul]

/-- The assignment of a walk is zero on an arrow the walk does not traverse. -/
theorem walkAssignment_eq_zero_of_notMem {s t : V} (p : ArrowWalk Q s t) (q : K) {x y : V}
    {e : Q x y} (he : ⟨x, y, e⟩ ∉ p.arrows) : walkAssignment p q e = 0 := by
  classical
  rw [walkAssignment_apply, List.count_eq_zero_of_not_mem he, zero_nsmul]

/-- A walk that traverses no arrow twice carries its weight on each arrow it traverses. -/
theorem walkAssignment_eq_of_mem {s t : V} {p : ArrowWalk Q s t} (hp : p.arrows.Nodup) (q : K)
    {x y : V} {e : Q x y} (he : ⟨x, y, e⟩ ∈ p.arrows) : walkAssignment p q e = q := by
  classical
  rw [walkAssignment_apply, List.count_eq_one_of_mem hp he, one_nsmul]

/-- A walk assignment takes values in any additive submonoid containing the weight. -/
theorem walkAssignment_mem {S : Type*} [SetLike S K] [AddSubmonoidClass S K] {H : S}
    {s t : V} (p : ArrowWalk Q s t) {q : K} (hq : q ∈ H) {x y : V} (e : Q x y) :
    walkAssignment p q e ∈ H := by
  classical
  rw [walkAssignment_apply]
  exact nsmul_mem hq _

section Order

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- A walk weighted by a nonnegative amount gives a nonnegative assignment. -/
theorem walkAssignment_nonneg {s t : V} (p : ArrowWalk Q s t) {q : K} (hq : 0 ≤ q) :
    0 ≤ walkAssignment p q := by
  classical
  intro x y e
  rw [walkAssignment_apply]
  exact nsmul_nonneg hq _

/-- **Feasibility of a walk.** A walk that traverses no arrow twice, weighted by `q ≥ 0`, lies
between zero and any nonnegative capacities that are at least `q` on every arrow it traverses. -/
theorem walkAssignment_mem_Icc {s t : V} {p : ArrowWalk Q s t} (hp : p.arrows.Nodup) {q : K}
    (hq : 0 ≤ q) {cap : Assignment Q K} (hcap : 0 ≤ cap) (hle : ∀ a ∈ p.arrows, q ≤ cap a.2.2) :
    walkAssignment p q ∈ Set.Icc 0 cap := by
  refine ⟨walkAssignment_nonneg p hq, fun x y e ↦ ?_⟩
  by_cases he : ⟨x, y, e⟩ ∈ p.arrows
  · rw [walkAssignment_eq_of_mem hp q he]
    exact hle _ he
  · rw [walkAssignment_eq_zero_of_notMem p q he]
    exact hcap x y e

end Order

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup K] [Fintype V] [∀ x y, Fintype (Q x y)]

/-- **Excess of a walk.** A walk from `s` to `t` weighted by `q` has excess `q` at `t`, excess `-q`
at `s`, and zero excess elsewhere; for a closed walk the two cancel. -/
@[simp]
theorem excessAt_walkAssignment [DecidableEq V] {s t : V} (p : ArrowWalk Q s t) (q : K) (v : V) :
    excessAt (walkAssignment p q) v = (if v = t then q else 0) - (if v = s then q else 0) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [walkAssignment_cons, excessAt_add, ih, excessAt_single]
    abel

/-- A closed walk gives a circulation. -/
theorem isCirculation_walkAssignment {s : V} (c : ArrowWalk Q s s) (q : K) :
    IsCirculation (walkAssignment c q) := by
  classical
  exact (isCirculation_iff _).2 fun v ↦ by rw [excessAt_walkAssignment, sub_self]

section Order

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- A walk from `s` to `t` that traverses no arrow twice, weighted by `q ≥ 0`, as an ordinary
`s`–`t` flow for nonnegative capacities that are at least `q` on every arrow it traverses. -/
noncomputable def walkFlow {cap : Assignment Q K} {s t : V} (p : ArrowWalk Q s t)
    (hp : p.arrows.Nodup) {q : K} (hq : 0 ≤ q) (hcap : 0 ≤ cap)
    (hle : ∀ a ∈ p.arrows, q ≤ cap a.2.2) : Flow cap s t where
  toFun := walkAssignment p q
  mem_Icc := walkAssignment_mem_Icc hp hq hcap hle
  conserve v hvs hvt := by
    classical
    simp [hvs, hvt]
  excessAt_sink_nonneg := by
    classical
    rw [excessAt_walkAssignment]
    split_ifs <;> simp_all

variable {cap : Assignment Q K} {s t : V} {p : ArrowWalk Q s t} {hp : p.arrows.Nodup} {q : K}
  {hq : 0 ≤ q} {hcap : 0 ≤ cap} {hle : ∀ a ∈ p.arrows, q ≤ cap a.2.2}

@[simp]
theorem walkFlow_toFun : (walkFlow p hp hq hcap hle).toFun = walkAssignment p q :=
  (rfl)

/-- A walk between distinct vertices, weighted by `q`, is a flow of value `q`. -/
theorem val_walkFlow (hst : s ≠ t) : (walkFlow p hp hq hcap hle).val = q := by
  classical
  simp [BoundedFlow.val_def, hst.symm]

end Order

end AddCommGroup

/-! ### Augmentation -/

section Augmentation

variable [AddCommGroup K]

/-- **Cycle augmentation.** Updating along a closed residual walk preserves the excess at every
vertex. Together with `residualUpdate_walkAssignment_mem_Icc`, augmenting a bounded circulation
along a residual cycle gives a bounded circulation. -/
theorem excessAt_residualUpdate_walkAssignment_self [Fintype V] [∀ x y, Fintype (Q x y)]
    (f : Assignment Q K) {s : V}
    (c : ArrowWalk (ResidualHom Q) s s) (q : K) (v : V) :
    excessAt (residualUpdate f (walkAssignment c q)) v = excessAt f v :=
  (isCirculation_walkAssignment c q).excessAt_residualUpdate f v

section PartialOrder

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- **Feasibility of augmentation.** Updating a feasible assignment `f` along a residual walk that
traverses no arrow twice, by an amount between zero and the residual capacities along the walk,
gives a feasible assignment. Lower bounds may be negative. For a closed walk, such as a residual
cycle, the update also preserves every excess (`excessAt_residualUpdate_walkAssignment_self`). -/
theorem residualUpdate_walkAssignment_mem_Icc {lo hi f : Assignment Q K} (hf : f ∈ Set.Icc lo hi)
    {s t : V} {p : ArrowWalk (ResidualHom Q) s t} (hp : p.arrows.Nodup) {q : K} (hq : 0 ≤ q)
    (hle : ∀ a ∈ p.arrows, q ≤ residualCapacity lo hi f a.2.2) :
    residualUpdate f (walkAssignment p q) ∈ Set.Icc lo hi :=
  residualUpdate_mem_Icc (walkAssignment_mem_Icc hp hq (residualCapacity_nonneg hf) hle)

variable [Fintype V] [∀ x y, Fintype (Q x y)]

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The *augmentation* of an ordinary `s`–`t` flow `f` along a residual walk from `s` to `t` that
traverses no arrow twice, by an amount `q` between zero and the residual capacities along the walk:
each forward residual arrow of the walk raises its arrow's value by `q`, and each reverse residual
arrow lowers it by `q`. -/
noncomputable def augmentWalk (f : Flow cap s t) (p : ArrowWalk (ResidualHom Q) s t)
    (hp : p.arrows.Nodup) {q : K} (hq : 0 ≤ q)
    (hle : ∀ a ∈ p.arrows, q ≤ residualCapacity 0 cap f.toFun a.2.2) : Flow cap s t :=
  f.augment (walkFlow p hp hq (residualCapacity_nonneg f.mem_Icc) hle)

variable {f : Flow cap s t} {p : ArrowWalk (ResidualHom Q) s t} {hp : p.arrows.Nodup} {q : K}
  {hq : 0 ≤ q} {hle : ∀ a ∈ p.arrows, q ≤ residualCapacity 0 cap f.toFun a.2.2}

@[simp]
theorem augmentWalk_toFun :
    (f.augmentWalk p hp hq hle).toFun = residualUpdate f.toFun (walkAssignment p q) := by
  simp [augmentWalk]

/-- Augmenting along a residual walk between distinct terminals increases the value by the
augmenting amount. -/
@[simp]
theorem val_augmentWalk (hst : s ≠ t) : (f.augmentWalk p hp hq hle).val = f.val + q := by
  rw [augmentWalk, toBoundedFlow_augment, BoundedFlow.val_update, val_walkFlow hst]

end Flow

end PartialOrder

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K] [Fintype V] [∀ x y, Fintype (Q x y)]

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The augmentation of an ordinary `s`–`t` flow `f` along a residual walk from `s` to `t` that
traverses an arrow but no arrow twice, by its bottleneck: the least residual capacity of an arrow
of the walk, which is the largest amount that the residual capacities along the walk allow. -/
noncomputable def augmentBottleneck (f : Flow cap s t) (p : ArrowWalk (ResidualHom Q) s t)
    (hp : p.arrows.Nodup) (hne : p.arrows ≠ []) : Flow cap s t :=
  f.augmentWalk p hp (q := p.bottleneck (residualCapacity 0 cap f.toFun) hne)
    (ArrowWalk.le_bottleneck_iff.2 fun a _ ↦ residualCapacity_nonneg f.mem_Icc _ _ a.2.2)
    (fun _ ha ↦ ArrowWalk.bottleneck_le ha)

variable {f : Flow cap s t} {p : ArrowWalk (ResidualHom Q) s t} {hp : p.arrows.Nodup}
  {hne : p.arrows ≠ []}

@[simp]
theorem augmentBottleneck_toFun :
    (f.augmentBottleneck p hp hne).toFun =
      residualUpdate f.toFun
        (walkAssignment p (p.bottleneck (residualCapacity 0 cap f.toFun) hne)) :=
  augmentWalk_toFun

/-- Augmentation by the bottleneck preserves arrow values in an additive subgroup `H` that
contains the capacities: residual capacities, and hence the bottleneck, lie in `H`. -/
theorem augmentBottleneck_toFun_mem (H : AddSubgroup K)
    (hcap : ∀ ⦃x y⦄ (e : Q x y), cap e ∈ H) (hf : ∀ ⦃x y⦄ (e : Q x y), f.toFun e ∈ H) {x y : V}
    (e : Q x y) : (f.augmentBottleneck p hp hne).toFun e ∈ H := by
  have hres : ∀ ⦃v w⦄ (e : ResidualHom Q v w), residualCapacity 0 cap f.toFun e ∈ H :=
    fun _ _ ↦ residualCapacity_mem H (fun _ _ _ ↦ H.zero_mem) hcap hf
  obtain ⟨a, -, ha⟩ := ArrowWalk.exists_mem_bottleneck_eq
    (c := residualCapacity 0 cap f.toFun) (hne := hne)
  rw [augmentBottleneck_toFun]
  exact residualUpdate_mem H hf (fun _ _ _ ↦ walkAssignment_mem p (ha ▸ hres a.2.2) _) e

/-- Augmenting along a residual walk between distinct terminals by its bottleneck increases the
value by the bottleneck. -/
@[simp]
theorem val_augmentBottleneck (hst : s ≠ t) :
    (f.augmentBottleneck p hp hne).val =
      f.val + p.bottleneck (residualCapacity 0 cap f.toFun) hne :=
  val_augmentWalk hst

/-- **Augmentation along an augmenting path.** If every arrow of a residual walk between distinct
terminals has positive residual capacity, as on an augmenting path, then augmenting by the
bottleneck strictly increases the value of the flow. -/
theorem val_lt_val_augmentBottleneck (hst : s ≠ t)
    (hpos : ∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) :
    f.val < (f.augmentBottleneck p hp hne).val := by
  rw [val_augmentBottleneck hst, lt_add_iff_pos_right]
  exact ArrowWalk.lt_bottleneck_iff.2 hpos

end Flow

end LinearOrder

end Augmentation

end TauCeti
