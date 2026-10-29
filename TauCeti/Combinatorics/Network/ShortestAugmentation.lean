/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import TauCeti.Combinatorics.Network.AugmentingPath
public import TauCeti.Combinatorics.Network.Distance

/-!
# Shortest augmenting paths and the existence of maximum flows

A step of *shortest-path augmentation* takes a bounded `s`–`t` assignment `f` to the residual
update of `f` along an augmenting walk of least length, by the bottleneck of that walk. This file
proves that the relation is well-founded in the direction of successive steps, from any feasible
assignment, over every linearly ordered additive commutative group of coefficients. Combined with
the augmenting-path optimality criterion, this gives the existence of maximum assignments whenever
a feasible one exists, and in particular of maximum ordinary flows for nonnegative capacities, so
the max-flow/min-cut theorem. Since each step preserves values in an additive subgroup containing
the bounds, it also gives integrality: for nonnegative capacities in an additive subgroup, some
maximum flow takes its values in that subgroup.

The argument is that of Edmonds and Karp, and of Dinitz. Write `d` for the positive distance from
`s` in the residual network of `f`, and `d'` for that of the augmented assignment. A residual arrow
that becomes positive is the reverse of an arrow of the augmenting walk, so along it `d` decreases
by one. Hence `d` rises by at most one along every positive residual arrow of the new assignment,
and `d ≤ d'` (`TauCeti.BoundedFlow.ShortestAugmentationStep.positiveEDist_le`). When `d' = d`, the
positive residual arrows `u → v` with `d v = d u + 1` after the step are among those before it,
and the arrow of the walk attaining the bottleneck is no longer positive. Since distances are
bounded by the number of vertices, the distances and then the number of these arrows give a
lexicographic measure that decreases at every step. The coefficients need not be discrete or
Archimedean; augmentation along arbitrary augmenting paths need not terminate in that
generality.

## Main definitions

* `TauCeti.BoundedFlow.ShortestAugmentationStep f g`: `g` arises from `f` by one step of
  shortest-path augmentation.

## Main results

* `TauCeti.BoundedFlow.exists_shortestAugmentationStep_iff`: for distinct terminals, a step exists
  exactly when there is an augmenting walk, and
  `TauCeti.BoundedFlow.isMaximum_iff_forall_not_shortestAugmentationStep`: an assignment is maximum
  exactly when no step starts from it.
* `TauCeti.BoundedFlow.ShortestAugmentationStep.val_lt`: each step strictly increases the value.
* `TauCeti.BoundedFlow.ShortestAugmentationStep.positiveEDist_le`: residual distances from the
  source do not decrease.
* `TauCeti.BoundedFlow.wellFounded_shortestAugmentationStep`: shortest-path augmentation
  terminates.
* `TauCeti.BoundedFlow.exists_reflTransGen_shortestAugmentationStep_isMaximum`: finitely many steps
  lead from any bounded `s`–`t` assignment to a maximum one.
* `TauCeti.BoundedFlow.exists_val_eq_cutBound`: the max-flow/min-cut theorem for bounded
  assignments.
* `TauCeti.Flow.exists_isMaximum_mem` and `TauCeti.Flow.exists_val_eq_arrowSum`: integrality and
  the max-flow/min-cut theorem for ordinary flows with nonnegative capacities.

## References

* J. Edmonds, R. M. Karp, *Theoretical improvements in algorithmic efficiency for network flow
  problems*, J. ACM 19 (1972).
* E. A. Dinic, *Algorithm for solution of a problem of maximum flow in a network with power
  estimation*, Soviet Math. Dokl. 11 (1970).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 10.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] [LinearOrder K]
  [IsOrderedAddMonoid K]

namespace BoundedFlow

variable {lo hi : Assignment Q K} {s t : V}

/-- One step of *shortest-path augmentation*: `g` is the residual update of `f` along an
augmenting walk `p` from `s` to `t` of least length, by the bottleneck of `p`. The walk traverses
only residual arrows of positive capacity, its length is the positive distance from `s` to `t` in
the residual network of `f`, and it traverses at least one arrow. -/
def ShortestAugmentationStep (f g : BoundedFlow lo hi s t) : Prop :=
  ∃ (p : ArrowWalk (ResidualHom Q) s t) (hne : p.arrows ≠ []),
    (∀ a ∈ p.arrows, 0 < residualCapacity lo hi f.toFun a.2.2) ∧
    (p.length : ℕ∞) = positiveEDist (residualCapacity lo hi f.toFun) s t ∧
    g.toFun = residualUpdate f.toFun
      (walkAssignment p (p.bottleneck (residualCapacity lo hi f.toFun) hne))

omit [IsOrderedAddMonoid K] in
theorem shortestAugmentationStep_def {f g : BoundedFlow lo hi s t} :
    f.ShortestAugmentationStep g ↔
      ∃ (p : ArrowWalk (ResidualHom Q) s t) (hne : p.arrows ≠ []),
        (∀ a ∈ p.arrows, 0 < residualCapacity lo hi f.toFun a.2.2) ∧
        (p.length : ℕ∞) = positiveEDist (residualCapacity lo hi f.toFun) s t ∧
        g.toFun = residualUpdate f.toFun
          (walkAssignment p (p.bottleneck (residualCapacity lo hi f.toFun) hne)) :=
  Iff.rfl

omit [IsOrderedAddMonoid K] in
/-- A step of shortest-path augmentation traverses at least one arrow, so its terminals are
distinct. -/
private theorem ShortestAugmentationStep.source_ne_sink {f g : BoundedFlow lo hi s t}
    (h : f.ShortestAugmentationStep g) : s ≠ t := by
  rintro rfl
  obtain ⟨p, hne, -, hlen, -⟩ := h
  rw [positiveEDist_self] at hlen
  exact hne (ArrowWalk.arrows_eq_nil_iff.2 (by exact_mod_cast hlen))

/-- For distinct terminals, a step of shortest-path augmentation starts from `f` exactly when `f`
has an augmenting walk. -/
theorem exists_shortestAugmentationStep_iff (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    (∃ g, f.ShortestAugmentationStep g) ↔
      PositiveReachable (residualCapacity lo hi f.toFun) s t := by
  refine ⟨fun ⟨_, p, _, hpos, _⟩ ↦ positiveReachable_def.2 ⟨p, hpos⟩, fun h ↦ ?_⟩
  obtain ⟨p, hpos, hlen⟩ := h.exists_length_eq_positiveEDist
  have hp := ArrowWalk.isPath_of_length_eq_positiveEDist hpos hlen
  have hne : p.arrows ≠ [] := p.arrows_ne_nil hst
  have hq : 0 < p.bottleneck (residualCapacity lo hi f.toFun) hne :=
    ArrowWalk.lt_bottleneck_iff.2 hpos
  exact ⟨f.update (walkFlow p hp.nodup_arrows hq.le (residualCapacity_nonneg f.mem_Icc)
    fun _ ha ↦ ArrowWalk.bottleneck_le ha).toBoundedFlow, p, hne, hpos, hlen, by simp⟩

/-- A bounded `s`–`t` assignment is maximum exactly when no step of shortest-path augmentation
starts from it. -/
theorem isMaximum_iff_forall_not_shortestAugmentationStep (f : BoundedFlow lo hi s t) :
    f.IsMaximum ↔ ∀ g, ¬f.ShortestAugmentationStep g := by
  obtain rfl | hst := eq_or_ne s t
  · exact iff_of_true (isMaximum_of_eq rfl f) fun _ h ↦ h.source_ne_sink rfl
  rw [isMaximum_iff_not_positiveReachable hst, ← exists_shortestAugmentationStep_iff hst,
    not_exists]

namespace ShortestAugmentationStep

variable {f g : BoundedFlow lo hi s t}

/-- A step of shortest-path augmentation strictly increases the value. -/
theorem val_lt (h : f.ShortestAugmentationStep g) : f.val < g.val := by
  classical
  have hst := h.source_ne_sink
  obtain ⟨p, hne, hpos, -, hg⟩ := h
  simpa [val_def, hg, hst.symm] using ArrowWalk.lt_bottleneck_iff.2 hpos

omit [IsOrderedAddMonoid K] in
/-- **Integrality of shortest-path augmentation.** If the bounds and `f` take values in an additive
subgroup `H`, then so does the result of a step of shortest-path augmentation. -/
theorem toFun_mem (H : AddSubgroup K) (hlo : ∀ ⦃v w⦄ (e : Q v w), lo e ∈ H)
    (hhi : ∀ ⦃v w⦄ (e : Q v w), hi e ∈ H) (h : f.ShortestAugmentationStep g)
    (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H) {v w : V} (e : Q v w) : g.toFun e ∈ H := by
  obtain ⟨p, hne, -, -, hg⟩ := h
  obtain ⟨a, -, ha⟩ :=
    ArrowWalk.exists_mem_bottleneck_eq (c := residualCapacity lo hi f.toFun) (hne := hne)
  rw [hg]
  exact residualUpdate_mem H hf (fun _ _ e' ↦ walkAssignment_mem p
    (ha ▸ residualCapacity_mem H hlo hhi hf a.2.2) e') e

/-- A residual arrow whose reverse is not traversed by the augmenting walk loses residual
capacity in a step of shortest-path augmentation, or keeps it. -/
private theorem residualCapacity_le_of_swap_notMem {p : ArrowWalk (ResidualHom Q) s t}
    {hne : p.arrows ≠ []} (hpos : ∀ a ∈ p.arrows, 0 < residualCapacity lo hi f.toFun a.2.2)
    (hg : g.toFun = residualUpdate f.toFun
      (walkAssignment p (p.bottleneck (residualCapacity lo hi f.toFun) hne)))
    {u v : V} (a : ResidualHom Q u v) (ha : ⟨v, u, a.swap⟩ ∉ p.arrows) :
    residualCapacity lo hi g.toFun a ≤ residualCapacity lo hi f.toFun a := by
  rw [hg, residualCapacity_residualUpdate, walkAssignment_eq_zero_of_notMem p _ ha, add_zero,
    sub_le_self_iff]
  exact walkAssignment_nonneg p (ArrowWalk.lt_bottleneck_iff.2 hpos).le u v a

/-- **Monotonicity of residual distances.** A step of shortest-path augmentation does not decrease
the positive distance from the source in the residual network. -/
theorem positiveEDist_le (h : f.ShortestAugmentationStep g) (v : V) :
    positiveEDist (residualCapacity lo hi f.toFun) s v ≤
      positiveEDist (residualCapacity lo hi g.toFun) s v := by
  obtain ⟨p, hne, hpos, hlen, hg⟩ := h
  refine le_positiveEDist (positiveEDist_self _ s) (fun x y a ha ↦ ?_) v
  by_cases hmem : ⟨y, x, a.swap⟩ ∈ p.arrows
  · -- the reverse of `a` lies on the shortest walk, so the distance drops by one along `a`
    have hxy : positiveEDist (residualCapacity lo hi f.toFun) s x =
        positiveEDist (residualCapacity lo hi f.toFun) s y + 1 :=
      positiveEDist_eq_add_one_of_mem_arrows hpos hlen hmem
    rw [hxy]
    exact le_self_add.trans le_self_add
  · exact positiveEDist_le_add_one a
      (ha.trans_le (residualCapacity_le_of_swap_notMem hpos hg a hmem))

end ShortestAugmentationStep

/-! ### Termination -/

open Classical in
/-- The *admissible arrows*: the residual arrows `u → v` of positive capacity with `d v = d u + 1`,
for the positive distance `d` from `s`. -/
private noncomputable def admissibleArrows (c : Assignment (ResidualHom Q) K) (s : V) :
    Finset (Σ x y, ResidualHom Q x y) :=
  univ.filter fun a ↦ 0 < c a.2.2 ∧ positiveEDist c s a.2.1 = positiveEDist c s a.1 + 1

open Classical in
/-- The pairs `(v, k)` with `k` less than the number of vertices and the positive distance from `s`
to `v` at most `k`. It shrinks strictly when finite distances increase. -/
private noncomputable def distancePairs (c : Assignment (ResidualHom Q) K) (s : V) :
    Finset (V × Fin (Fintype.card V)) :=
  univ.filter fun x ↦ positiveEDist c s x.1 ≤ x.2

/-- A step of shortest-path augmentation strictly decreases the number of admissible arrows when
it leaves all residual distances from the source unchanged. -/
private theorem card_admissibleArrows_lt {f g : BoundedFlow lo hi s t}
    (h : f.ShortestAugmentationStep g)
    (heq : positiveEDist (residualCapacity lo hi g.toFun) s =
      positiveEDist (residualCapacity lo hi f.toFun) s) :
    #(admissibleArrows (residualCapacity lo hi g.toFun) s) <
      #(admissibleArrows (residualCapacity lo hi f.toFun) s) := by
  obtain ⟨p, hne, hpos, hlen, hg⟩ := h
  have hlt {a : Σ x y, ResidualHom Q x y} (ha : a ∈ p.arrows) :=
    positiveEDist_lt_of_mem_arrows hpos hlen ha
  refine card_lt_card ((ssubset_iff_of_subset fun a ha ↦ ?_).2 ?_)
  · -- an admissible arrow after the step was admissible before it
    simp only [admissibleArrows, mem_filter, mem_univ, true_and, heq] at ha ⊢
    refine ⟨ha.1.trans_le (ShortestAugmentationStep.residualCapacity_le_of_swap_notMem hpos hg _
      fun hmem ↦ ?_), ha.2⟩
    have hlt' : positiveEDist (residualCapacity lo hi f.toFun) s a.2.1 <
        positiveEDist (residualCapacity lo hi f.toFun) s a.1 := hlt hmem
    rw [ha.2] at hlt'
    exact hlt'.not_ge le_self_add
  · -- the arrow attaining the bottleneck is admissible before the step but not after it
    obtain ⟨a, ha, hδ⟩ :=
      ArrowWalk.exists_mem_bottleneck_eq (c := residualCapacity lo hi f.toFun) (hne := hne)
    have hswap : (⟨a.2.1, a.1, a.2.2.swap⟩ : Σ x y, ResidualHom Q x y) ∉ p.arrows :=
      fun hmem ↦ (hlt ha).not_gt (hlt hmem)
    have hp := ArrowWalk.isPath_of_length_eq_positiveEDist hpos hlen
    refine ⟨a, ?_, ?_⟩
    · simpa [admissibleArrows] using
        ⟨hpos a ha, positiveEDist_eq_add_one_of_mem_arrows hpos hlen ha⟩
    · simp only [admissibleArrows, mem_filter, mem_univ, true_and, not_and]
      intro hcap
      rw [hg, residualCapacity_residualUpdate, walkAssignment_eq_of_mem hp.nodup_arrows _ ha,
        walkAssignment_eq_zero_of_notMem p _ hswap, hδ, sub_self, add_zero] at hcap
      exact absurd hcap (lt_irrefl 0)

/-- A step of shortest-path augmentation shrinks the set of distance pairs. -/
private theorem distancePairs_subset {f g : BoundedFlow lo hi s t}
    (h : f.ShortestAugmentationStep g) :
    distancePairs (residualCapacity lo hi g.toFun) s ⊆
      distancePairs (residualCapacity lo hi f.toFun) s := by
  intro x hx
  simp only [distancePairs, mem_filter, mem_univ, true_and] at hx ⊢
  exact (h.positiveEDist_le x.1).trans hx

/-- A step of shortest-path augmentation shrinks the set of distance pairs strictly when some
residual distance from the source changes. -/
private theorem distancePairs_ssubset {f g : BoundedFlow lo hi s t}
    (h : f.ShortestAugmentationStep g)
    (hne : positiveEDist (residualCapacity lo hi g.toFun) s ≠
      positiveEDist (residualCapacity lo hi f.toFun) s) :
    distancePairs (residualCapacity lo hi g.toFun) s ⊂
      distancePairs (residualCapacity lo hi f.toFun) s := by
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hlt := (h.positiveEDist_le v).lt_of_ne' hv
  have hreach : PositiveReachable (residualCapacity lo hi f.toFun) s v :=
    positiveEDist_ne_top_iff.1 hlt.ne_top
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hlt.ne_top
  have hkcard : k < Fintype.card V := by
    exact_mod_cast hk ▸ positiveEDist_lt_card hreach
  refine (ssubset_iff_of_subset (distancePairs_subset h)).2 ⟨(v, ⟨k, hkcard⟩), ?_, ?_⟩
  · simp [distancePairs, hk]
  · simpa [distancePairs, ← hk] using hlt

/-- The termination measure of shortest-path augmentation: the number of distance pairs, which
decreases when a residual distance from the source changes, then the number of admissible arrows,
which decreases otherwise. -/
private noncomputable def terminationMeasure (f : BoundedFlow lo hi s t) : ℕ ×ₗ ℕ :=
  toLex (#(distancePairs (residualCapacity lo hi f.toFun) s),
    #(admissibleArrows (residualCapacity lo hi f.toFun) s))

private theorem terminationMeasure_lt {f g : BoundedFlow lo hi s t}
    (h : f.ShortestAugmentationStep g) : terminationMeasure g < terminationMeasure f := by
  rw [terminationMeasure, terminationMeasure, Prod.Lex.toLex_lt_toLex]
  by_cases heq : positiveEDist (residualCapacity lo hi g.toFun) s =
    positiveEDist (residualCapacity lo hi f.toFun) s
  · exact .inr ⟨by simp only [distancePairs, heq], card_admissibleArrows_lt h heq⟩
  · exact .inl (card_lt_card (distancePairs_ssubset h heq))

/-- **Termination of shortest-path augmentation.** There is no infinite sequence of steps of
shortest-path augmentation: the relation is well-founded in the direction of successive steps, from
any bounded `s`–`t` assignment, whatever the coefficients. -/
theorem wellFounded_shortestAugmentationStep :
    WellFounded fun g f : BoundedFlow lo hi s t ↦ f.ShortestAugmentationStep g :=
  Subrelation.wf terminationMeasure_lt (InvImage.wf terminationMeasure wellFounded_lt)

/-- From any bounded `s`–`t` assignment, finitely many steps of shortest-path augmentation lead to
a maximum one. -/
theorem exists_reflTransGen_shortestAugmentationStep_isMaximum (f : BoundedFlow lo hi s t) :
    ∃ g, Relation.ReflTransGen ShortestAugmentationStep f g ∧ g.IsMaximum := by
  refine wellFounded_shortestAugmentationStep.induction
    (C := fun f ↦ ∃ g, Relation.ReflTransGen ShortestAugmentationStep f g ∧ g.IsMaximum) f
    fun f ih ↦ ?_
  by_cases hf : f.IsMaximum
  · exact ⟨f, .refl, hf⟩
  · obtain ⟨g, hfg⟩ := not_forall_not.1 <|
      (isMaximum_iff_forall_not_shortestAugmentationStep f).not.1 hf
    obtain ⟨g', hgg', hg'⟩ := ih g hfg
    exact ⟨g', .head hfg hgg', hg'⟩

/-- **Existence of maximum assignments.** If some bounded `s`–`t` assignment exists, then a maximum
one exists. -/
theorem exists_isMaximum (f : BoundedFlow lo hi s t) : ∃ g : BoundedFlow lo hi s t, g.IsMaximum :=
  let ⟨g, _, hg⟩ := exists_reflTransGen_shortestAugmentationStep_isMaximum f
  ⟨g, hg⟩

/-- **Max-flow/min-cut theorem for bounded assignments.** If some bounded `s`–`t` assignment
between distinct terminals exists, then some bounded `s`–`t` assignment has value equal to the cut
bound of some vertex set containing `s` but not `t`. By weak duality
(`TauCeti.BoundedFlow.val_le_cutBound`) this assignment is maximum and this cut bound is
minimum. -/
theorem exists_val_eq_cutBound [DecidableEq V] (hst : s ≠ t) (f : BoundedFlow lo hi s t) :
    ∃ g : BoundedFlow lo hi s t, ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ g.val = cutBound lo hi S :=
  let ⟨g, hg⟩ := exists_isMaximum f
  ⟨g, hg.exists_val_eq_cutBound hst⟩

/-- **Integrality.** If the bounds lie in an additive subgroup `H` and some bounded `s`–`t`
assignment takes values in `H`, then some maximum bounded `s`–`t` assignment takes values in
`H`. -/
theorem exists_isMaximum_mem (H : AddSubgroup K)
    (hlo : ∀ ⦃v w⦄ (e : Q v w), lo e ∈ H) (hhi : ∀ ⦃v w⦄ (e : Q v w), hi e ∈ H)
    (f : BoundedFlow lo hi s t) (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H) :
    ∃ g : BoundedFlow lo hi s t, g.IsMaximum ∧ ∀ ⦃v w⦄ (e : Q v w), g.toFun e ∈ H := by
  obtain ⟨g, hfg, hg⟩ := exists_reflTransGen_shortestAugmentationStep_isMaximum f
  refine ⟨g, hg, ?_⟩
  clear hg
  induction hfg with
  | refl => exact hf
  | tail _ hstep ih => exact fun _ _ e ↦ hstep.toFun_mem H hlo hhi ih e

end BoundedFlow

/-! ### Ordinary flows -/

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- **Integrality of maximum flows.** For nonnegative capacities in an additive subgroup `H`, some
maximum ordinary flow takes values in `H`. For distinct terminals, its value is the capacity of
some cut by `TauCeti.Flow.IsMaximum.exists_val_eq_arrowSum`. -/
theorem exists_isMaximum_mem (hcap : 0 ≤ cap) (H : AddSubgroup K)
    (hcapH : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H) :
    ∃ f : Flow cap s t, f.IsMaximum ∧ ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ H := by
  obtain ⟨g, hg, hgH⟩ := (zero hcap : Flow cap s t).toBoundedFlow.exists_isMaximum_mem H
    (fun _ _ _ ↦ H.zero_mem) hcapH fun _ _ _ ↦ by simp
  have hval : 0 ≤ excessAt g.toFun t := by
    rw [← BoundedFlow.val_def]
    simpa using BoundedFlow.isMaximum_iff.1 hg (zero hcap).toBoundedFlow
  exact ⟨⟨g, hval⟩, (isMaximum_toBoundedFlow _).1 hg, hgH⟩

/-- For nonnegative capacities, a maximum ordinary flow exists. -/
theorem exists_isMaximum (hcap : 0 ≤ cap) : ∃ f : Flow cap s t, f.IsMaximum :=
  let ⟨f, hf, _⟩ := exists_isMaximum_mem hcap ⊤ fun _ _ _ ↦ AddSubgroup.mem_top _
  ⟨f, hf⟩

/-- **Max-flow/min-cut theorem.** For nonnegative capacities and distinct terminals, some ordinary
flow has value equal to the capacity of the arrows leaving some vertex set containing `s` but not
`t`. By weak duality (`TauCeti.Flow.val_le_arrowSum`) this flow is maximum and this cut is
minimum. -/
theorem exists_val_eq_arrowSum [DecidableEq V] (hst : s ≠ t) (hcap : 0 ≤ cap) :
    ∃ f : Flow cap s t, ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = arrowSum cap S Sᶜ :=
  let ⟨f, hf⟩ := exists_isMaximum hcap
  ⟨f, hf.exists_val_eq_arrowSum hst⟩

end Flow

end TauCeti
