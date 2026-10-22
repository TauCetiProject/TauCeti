/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.Network.AugmentingPath

/-!
# Shortest-path augmentation and the existence of maximum flows

A *shortest augmentation step* augments an ordinary `s`–`t` flow by its bottleneck along an
augmenting walk of least length, that is, a residual walk from `s` to `t` of arrows of positive
residual capacity whose length is the positive distance from `s` to `t` for the residual
capacities. This is the rule of Edmonds and Karp. Unlike arbitrary augmentation, it terminates over
every linearly ordered additive commutative group of coefficients: there is no infinite sequence of
shortest augmentation steps, whatever the capacities and the initial flow, and whatever shortest
augmenting walk each step chooses.

Consequently, starting from any flow, finitely many shortest augmentation steps lead to a flow
with no augmenting walk, which is maximum by the augmenting-path optimality criterion. This gives
the existence of a maximum flow for any nonnegative capacities, hence the max-flow/min-cut
theorem; since each step keeps the arrow values in any additive subgroup containing the
capacities, the maximum flow can be chosen with values in such a subgroup.

## Main definitions

* `TauCeti.Flow.ShortestAugmentsTo`: one shortest augmentation step.

## Main results

* `TauCeti.Flow.exists_shortestAugmentsTo` and
  `TauCeti.Flow.isMaximum_iff_forall_not_shortestAugmentsTo`: a shortest augmentation step starts
  from a flow between distinct terminals exactly when it is not maximum.
* `TauCeti.Flow.ShortestAugmentsTo.positiveEdist_le`: shortest augmentation does not decrease
  residual distances from the source.
* `TauCeti.Flow.wellFounded_shortestAugmentsTo`: every sequence of shortest augmentation steps is
  finite.
* `TauCeti.Flow.exists_isMaximum_mem`: for nonnegative capacities in an additive subgroup and
  distinct terminals, some maximum flow has its arrow values in the subgroup.
* `TauCeti.Flow.exists_isMaximum` and `TauCeti.Flow.exists_val_eq_arrowSum`: **max-flow/min-cut**,
  a maximum flow exists and its value equals the capacity of some cut.

## Implementation notes

The proof tracks the positive residual distances `d v` from the source. An augmentation along a
walk can only create residual capacity on the reverses of the arrows of the walk, and along a
shortest walk `d` grows by one across every arrow, so across its reverse `d` drops by one. Hence
after the step the old distances still grow by at most one along every residual arrow of positive
capacity, and the residual distances never decrease. When they stay the same, the arrows of
positive residual capacity across which `d` grows form a strictly smaller set: a reversed arrow
never belongs to it, and the arrow realizing the bottleneck is saturated. Since the distances are
less than the number of vertices or infinite, the pair of these two quantities decreases
lexicographically.

## References

* J. Edmonds, R. M. Karp, *Theoretical improvements in algorithmic efficiency for network flow
  problems*, J. ACM 19 (1972).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 10.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)]
variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-! ### Shortest augmentation steps -/

/-- `f.ShortestAugmentsTo g` when the flow `g` arises from `f` by one shortest augmentation step:
augmentation by its bottleneck along a shortest augmenting walk of `f`, a residual walk from `s` to
`t` that traverses at least one arrow, traverses no arrow twice, has positive residual capacity on
every arrow, and has length the positive distance from `s` to `t` for the residual capacities. -/
def ShortestAugmentsTo (f g : Flow cap s t) : Prop :=
  ∃ (p : ArrowWalk (ResidualHom Q) s t) (hp : p.arrows.Nodup) (hne : p.arrows ≠ []),
    (∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) ∧
      p.length = positiveEdist (residualCapacity 0 cap f.toFun) s t ∧
        f.augmentBottleneck p hp hne = g

theorem shortestAugmentsTo_iff {f g : Flow cap s t} :
    f.ShortestAugmentsTo g ↔ ∃ (p : ArrowWalk (ResidualHom Q) s t) (hp : p.arrows.Nodup)
      (hne : p.arrows ≠ []), (∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2) ∧
        p.length = positiveEdist (residualCapacity 0 cap f.toFun) s t ∧
          f.augmentBottleneck p hp hne = g :=
  Iff.rfl

/-- A shortest augmentation step is an augmentation step. -/
theorem ShortestAugmentsTo.augmentsTo {f g : Flow cap s t} (h : f.ShortestAugmentsTo g) :
    f.AugmentsTo g :=
  let ⟨p, hp, hne, hpos, _, hg⟩ := h
  augmentsTo_iff.2 ⟨p, hp, hne, hpos, hg⟩

/-- A shortest augmentation step starts from every flow between distinct terminals that has an
augmenting walk. -/
theorem exists_shortestAugmentsTo (hst : s ≠ t) {f : Flow cap s t}
    (h : PositiveReachable (residualCapacity 0 cap f.toFun) s t) : ∃ g, f.ShortestAugmentsTo g :=
  let ⟨p, hp, hpos, hlen⟩ := h.exists_isPath_length_eq_positiveEdist
  ⟨_, p, hp.nodup_arrows, p.arrows_ne_nil hst, hpos, hlen, rfl⟩

/-- An ordinary flow between distinct terminals is maximum exactly when no shortest augmentation
step starts from it. -/
theorem isMaximum_iff_forall_not_shortestAugmentsTo (hst : s ≠ t) (f : Flow cap s t) :
    f.IsMaximum ↔ ∀ g, ¬f.ShortestAugmentsTo g := by
  refine ⟨fun hf g hg ↦ (isMaximum_iff_forall_not_augmentsTo hst f).1 hf g hg.augmentsTo,
    fun h ↦ (isMaximum_iff_not_positiveReachable hst f).2 fun hr ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_shortestAugmentsTo hst hr
  exact h g hg

/-! ### Residual distances under shortest augmentation -/

/-- After a shortest augmentation step, every residual arrow of positive capacity either already had
positive residual capacity, or is the reverse of an arrow of the augmenting walk, across which the
old positive distance from the source drops. -/
private theorem ShortestAugmentsTo.pos_or_lt {f g : Flow cap s t}
    {p : ArrowWalk (ResidualHom Q) s t} {hp : p.arrows.Nodup} {hne : p.arrows ≠ []}
    (hpos : ∀ a ∈ p.arrows, 0 < residualCapacity 0 cap f.toFun a.2.2)
    (hlen : p.length = positiveEdist (residualCapacity 0 cap f.toFun) s t)
    (hg : f.augmentBottleneck p hp hne = g) {x y : V} (a : ResidualHom Q x y)
    (ha : 0 < residualCapacity 0 cap g.toFun a) :
    0 < residualCapacity 0 cap f.toFun a ∨
      positiveEdist (residualCapacity 0 cap f.toFun) s y <
        positiveEdist (residualCapacity 0 cap f.toFun) s x := by
  subst hg
  rw [augmentBottleneck_toFun] at ha
  refine (pos_residualCapacity_or_mem_arrows_of_pos_residualCapacity_residualUpdate
    (ArrowWalk.le_bottleneck_iff.2 fun a _ ↦ (hpos a ‹_›).le) a ha).imp_right fun h ↦ ?_
  exact positiveEdist_lt_of_mem_arrows hpos hlen h

/-- **Shortest augmentation does not decrease residual distances.** After a shortest augmentation
step, the positive distance from the source to every vertex for the residual capacities is at least
what it was before. -/
theorem ShortestAugmentsTo.positiveEdist_le {f g : Flow cap s t} (h : f.ShortestAugmentsTo g)
    (v : V) :
    positiveEdist (residualCapacity 0 cap f.toFun) s v ≤
      positiveEdist (residualCapacity 0 cap g.toFun) s v := by
  obtain ⟨p, hp, hne, hpos, hlen, hg⟩ := h
  refine le_positiveEdist_of_forall_le_add_one (positiveEdist_self _ s) (fun x y a ha ↦ ?_) v
  rcases pos_or_lt hpos hlen hg a ha with ha | ha
  exacts [positiveEdist_le_add_one a ha, ha.le.trans le_self_add]

open Classical in
/-- The residual arrows of positive capacity across which the positive distance from the source
grows. -/
private noncomputable def levelArrows (f : Flow cap s t) : Finset (Σ x y, ResidualHom Q x y) :=
  univ.filter fun a ↦ 0 < residualCapacity 0 cap f.toFun a.2.2 ∧
    positiveEdist (residualCapacity 0 cap f.toFun) s a.1 <
      positiveEdist (residualCapacity 0 cap f.toFun) s a.2.1

/-- A shortest augmentation step that does not change the residual distances strictly shrinks the
set of residual arrows of positive capacity across which the distance grows: no new such arrow
appears, and the arrow realizing the bottleneck loses its residual capacity. -/
private theorem ShortestAugmentsTo.levelArrows_ssubset {f g : Flow cap s t}
    (h : f.ShortestAugmentsTo g)
    (hd : positiveEdist (residualCapacity 0 cap g.toFun) s =
      positiveEdist (residualCapacity 0 cap f.toFun) s) :
    levelArrows g ⊂ levelArrows f := by
  classical
  obtain ⟨p, hp, hne, hpos, hlen, hg⟩ := h
  refine (ssubset_iff_of_subset fun a ha ↦ ?_).2 ?_
  · simp only [levelArrows, mem_filter, mem_univ, true_and, hd] at ha ⊢
    refine ⟨(pos_or_lt hpos hlen hg a.2.2 ha.1).resolve_right fun h ↦ ?_, ha.2⟩
    exact h.not_gt ha.2
  -- the bottleneck arrow `b` is saturated, since its reverse is not on the shortest walk
  obtain ⟨b, hb, hbeq⟩ := ArrowWalk.exists_mem_bottleneck_eq (c := residualCapacity 0 cap f.toFun)
    (hne := hne)
  refine ⟨b, ?_, fun hb' ↦ ?_⟩
  · simp only [levelArrows, mem_filter, mem_univ, true_and]
    exact ⟨hpos b hb, positiveEdist_lt_of_mem_arrows hpos hlen hb⟩
  have hrev : (⟨b.2.1, b.1, b.2.2.swap⟩ : Σ x y, ResidualHom Q x y) ∉ p.arrows := fun h ↦
    (positiveEdist_lt_of_mem_arrows hpos hlen h).not_gt
      (positiveEdist_lt_of_mem_arrows hpos hlen hb)
  simp only [levelArrows, mem_filter, mem_univ, true_and, ← hg, augmentBottleneck_toFun,
    residualCapacity_residualUpdate, walkAssignment_eq_of_mem hp _ hb,
    walkAssignment_eq_zero_of_notMem p _ hrev, hbeq, sub_self, add_zero, lt_self_iff_false,
    false_and] at hb'

/-- **Termination of shortest-path augmentation.** There is no infinite sequence of shortest
augmentation steps, from any flow, for any capacities over any linearly ordered additive
commutative group, whatever shortest augmenting walk each step chooses. -/
theorem wellFounded_shortestAugmentsTo :
    WellFounded fun g f : Flow cap s t ↦ f.ShortestAugmentsTo g := by
  classical
  -- the residual distances, measured from above by `card V`, then the number of level arrows
  let μ : Flow cap s t → ℕ ×ₗ ℕ := fun f ↦ toLex
    (∑ v, ((Fintype.card V : ℕ∞) - positiveEdist (residualCapacity 0 cap f.toFun) s v).toNat,
      (levelArrows f).card)
  refine Subrelation.wf (fun {g f} h ↦ ?_) (InvImage.wf μ wellFounded_lt)
  have hle := h.positiveEdist_le
  by_cases hd : positiveEdist (residualCapacity 0 cap g.toFun) s =
      positiveEdist (residualCapacity 0 cap f.toFun) s
  · refine Prod.Lex.toLex_lt_toLex.2 (.inr ⟨by simp only [hd], card_lt_card ?_⟩)
    exact h.levelArrows_ssubset hd
  have hne (x : ℕ∞) : (Fintype.card V : ℕ∞) - x ≠ ⊤ :=
    (tsub_le_self.trans_lt (ENat.natCast_lt_top _)).ne
  refine Prod.Lex.toLex_lt_toLex.2 (.inl ?_)
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hd
  have hlt := (hle v).lt_of_ne' hv
  refine sum_lt_sum (fun w _ ↦ ENat.toNat_le_toNat (tsub_le_tsub_left (hle w) _) (hne _))
    ⟨v, mem_univ v, ?_⟩
  -- the old distance to `v` is finite, hence less than `card V`
  have hfin := positiveEdist_lt_card (positiveEdist_lt_top_iff.1 (hlt.trans_le le_top))
  generalize positiveEdist (residualCapacity 0 cap f.toFun) s v = a at hlt hfin
  generalize positiveEdist (residualCapacity 0 cap g.toFun) s v = b at hlt
  lift a to ℕ using (hlt.trans_le le_top).ne
  induction b using ENat.recTopCoe with
  | top => simpa [← ENat.natCast_sub] using ENat.natCast_lt_natCast.1 hfin
  | coe b =>
    simp only [← ENat.natCast_sub, ENat.toNat_natCast, ENat.natCast_lt_natCast] at hlt hfin ⊢
    omega

/-- From every flow between distinct terminals, finitely many shortest augmentation steps lead to a
maximum flow. -/
theorem exists_reflTransGen_shortestAugmentsTo_isMaximum (hst : s ≠ t) (f : Flow cap s t) :
    ∃ g, Relation.ReflTransGen ShortestAugmentsTo f g ∧ g.IsMaximum := by
  induction f using (wellFounded_shortestAugmentsTo (cap := cap) (s := s) (t := t)).induction with
  | _ f ih =>
    by_cases hmax : f.IsMaximum
    · exact ⟨f, .refl, hmax⟩
    · obtain ⟨g, hg⟩ := not_forall_not.1
        (mt (isMaximum_iff_forall_not_shortestAugmentsTo hst f).2 hmax)
      obtain ⟨g', hg', hmax'⟩ := ih g hg
      exact ⟨g', .head hg hg', hmax'⟩

/-! ### Existence of maximum flows -/

/-- **Integrality of maximum flows.** For nonnegative capacities in an additive subgroup `H` and
distinct terminals, some maximum flow has all its arrow values in `H`. -/
theorem exists_isMaximum_mem (hst : s ≠ t) (hcap₀ : 0 ≤ cap) {H : AddSubgroup K}
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H) :
    ∃ f : Flow cap s t, f.IsMaximum ∧ ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H := by
  let f₀ : Flow cap s t :=
    ⟨⟨0, ⟨le_rfl, hcap₀⟩, fun v _ _ ↦ excessAt_zero v⟩, (excessAt_zero t).ge⟩
  obtain ⟨f, hf, hmax⟩ := exists_reflTransGen_shortestAugmentsTo_isMaximum hst f₀
  refine ⟨f, hmax, ?_⟩
  clear hmax
  induction hf with
  | refl => exact fun _ _ _ ↦ zero_mem H
  | tail _ hg ih => exact fun _ _ ↦ hg.augmentsTo.mem hcap ih

/-- For nonnegative capacities and distinct terminals, a maximum flow exists. -/
theorem exists_isMaximum (hst : s ≠ t) (hcap₀ : 0 ≤ cap) : ∃ f : Flow cap s t, f.IsMaximum :=
  (exists_isMaximum_mem hst hcap₀ (H := ⊤) fun _ _ _ ↦ AddSubgroup.mem_top _).imp fun _ ↦ And.left

/-- **Max-flow/min-cut.** For nonnegative capacities and distinct terminals, some flow has value
equal to the capacity of the arrows leaving some vertex set containing `s` but not `t`. By weak
duality this flow is maximum and this cut is minimum. -/
theorem exists_val_eq_arrowSum [DecidableEq V] (hst : s ≠ t) (hcap₀ : 0 ≤ cap) :
    ∃ (f : Flow cap s t) (S : Finset V), s ∈ S ∧ t ∉ S ∧ f.val = arrowSum cap S Sᶜ :=
  let ⟨f, hf⟩ := exists_isMaximum hst hcap₀
  ⟨f, hf.exists_val_eq_arrowSum hst⟩

end Flow

end TauCeti
