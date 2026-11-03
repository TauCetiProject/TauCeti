/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.UpperLower.CompleteLattice
public import TauCeti.Combinatorics.Network.CutSubmodular
public import TauCeti.Combinatorics.Network.MinimumCut.Residual
public import TauCeti.Combinatorics.Quiver.StronglyConnectedComponent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Tactic.FinCases

/-!
# The poset of all minimum cuts

Let `f` be a maximum bounded `s`–`t` assignment between distinct terminals. Keep only the residual
arrows of positive capacity, and collapse each strongly connected component of the resulting
quiver to a point: these *residual components* are partially ordered by reachability. The
minimum cuts are exactly the terminal-separating vertex sets closed under positive residual
reachability. So every minimum cut contains the components reachable from the component of the
source, and avoids those from which the component of the sink is reachable; these two families of
components are disjoint because `f` admits no augmenting walk. A minimum cut is then determined
by the remaining *free* components it contains, and these form an arbitrary upper set of the free
components.

This identifies the lattice of minimum cuts, ordered by inclusion, with the lattice of upper sets
of the finite poset of free components, also ordered by inclusion. Since Mathlib orders
`UpperSet` by reverse inclusion, the target of the order isomorphism is `(UpperSet _)ᵒᵈ`. Unions
and intersections of minimum cuts correspond to unions and intersections of upper sets, the
smallest and largest minimum cuts to the empty and the full upper set, and the minimum cut is
unique exactly when there is no free component.

The bounds may be negative and the value of `f` may have either sign; the ordinary-flow
statements follow by specialization.

## Main definitions

* `TauCeti.BoundedFlow.ResidualComponent`: the strongly connected components of the positive
  residual quiver of `f`, partially ordered by reachability.
* `TauCeti.BoundedFlow.FreeComponent`: the residual components neither reachable from the
  component of the source nor reaching the component of the sink.
* `TauCeti.BoundedFlow.IsMaximum.minimizersOrderIso`: the order isomorphism between the minimum
  cuts and the upper sets of free components, ordered by inclusion.

## Main results

* `TauCeti.BoundedFlow.IsMaximum.disjoint_Ici_Iic`: no residual component is both reachable from
  the source and reaches the sink.
* `TauCeti.BoundedFlow.IsMaximum.mem_of_residualComponent_le` and
  `TauCeti.BoundedFlow.IsMaximum.notMem_of_residualComponent_le`: the forced components.
* `TauCeti.BoundedFlow.IsMaximum.mem_minimizersOrderIso_symm_iff`: the vertex-membership formula
  for the minimum cut of an upper set of free components.
* `TauCeti.BoundedFlow.IsMaximum.coe_minimizersOrderIso_sup` and
  `TauCeti.BoundedFlow.IsMaximum.coe_minimizersOrderIso_inf`: unions and intersections correspond.
* `TauCeti.BoundedFlow.IsMaximum.minimizersOrderIso_symm_top` and
  `TauCeti.BoundedFlow.IsMaximum.minimizersOrderIso_symm_bot`: the empty and full upper sets give
  the smallest and largest minimum cuts.
* `TauCeti.BoundedFlow.IsMaximum.existsUnique_isMinimum_iff_isEmpty`: the minimum cut is unique
  exactly when there is no free component.
* `TauCeti.Flow.IsMaximum.minimizersOrderIso`: the ordinary-flow specialization, with
  `TauCeti.Flow.IsMaximum.minimizersOrderIso_symm_top` and
  `TauCeti.Flow.IsMaximum.minimizersOrderIso_symm_bot` identifying its smallest and largest
  minimum cuts.

## References

* J.-C. Picard, M. Queyranne, *On the structure of all minimum cuts in a network and
  applications*, Math. Programming Stud. 13 (1980), 8–16.
-/

public section

namespace TauCeti

open Finset TerminalCut OrderDual

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]

namespace BoundedFlow

section Component

variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
variable {lo hi : Assignment Q K} {s t : V} (f : BoundedFlow lo hi s t)

/-- The *residual components* of a bounded `s`–`t` assignment `f`: the strongly connected
components of the quiver of residual arrows of positive capacity for `f`. They are partially
ordered by reachability along such arrows. -/
abbrev ResidualComponent : Type u :=
  @Quiver.StronglyConnectedComponent V ⟨PositiveHom (residualCapacity lo hi f.toFun)⟩

/-- The residual component of `f` containing a vertex. -/
def residualComponent (v : V) : f.ResidualComponent :=
  @Quiver.StronglyConnectedComponent.mk V ⟨PositiveHom (residualCapacity lo hi f.toFun)⟩ v

/-- The *free* residual components of `f`: those not reachable from the component of the source
and from which the component of the sink is not reachable, with the induced partial order. -/
abbrev FreeComponent : Type u :=
  {C : f.ResidualComponent // ¬f.residualComponent s ≤ C ∧ ¬C ≤ f.residualComponent t}

variable {f}

omit [DecidableEq V] [IsOrderedAddMonoid K] in
/-- The residual component of `v` is below that of `w` exactly when `w` is positively reachable
from `v` for the residual capacities. -/
@[simp]
theorem residualComponent_le_residualComponent {v w : V} :
    f.residualComponent v ≤ f.residualComponent w ↔
      PositiveReachable (residualCapacity lo hi f.toFun) v w := by
  rw [positiveReachable_iff_nonempty_arrowWalk]
  exact @Quiver.StronglyConnectedComponent.mk_le_mk V
    ⟨PositiveHom (residualCapacity lo hi f.toFun)⟩ v w

omit [DecidableEq V] [IsOrderedAddMonoid K] in
/-- Two vertices have the same residual component exactly when each is positively reachable from
the other for the residual capacities. -/
@[simp]
theorem residualComponent_eq_residualComponent {v w : V} :
    f.residualComponent v = f.residualComponent w ↔
      PositiveReachable (residualCapacity lo hi f.toFun) v w ∧
        PositiveReachable (residualCapacity lo hi f.toFun) w v := by
  rw [le_antisymm_iff, residualComponent_le_residualComponent,
    residualComponent_le_residualComponent]

omit [DecidableEq V] [IsOrderedAddMonoid K] in
/-- Every residual component contains a vertex. -/
theorem residualComponent_surjective : Function.Surjective f.residualComponent :=
  @Quiver.StronglyConnectedComponent.mk_surjective V ⟨PositiveHom (residualCapacity lo hi f.toFun)⟩

end Component

namespace IsMaximum

variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
variable {lo hi : Assignment Q K} {s t : V} {f : BoundedFlow lo hi s t}

omit [DecidableEq V] in
/-- For a maximum bounded `s`–`t` assignment between distinct terminals, no residual component is
both reachable from the component of the source and reaches the component of the sink. -/
theorem disjoint_Ici_Iic (hst : s ≠ t) (hf : f.IsMaximum) :
    Disjoint (Set.Ici (f.residualComponent s)) (Set.Iic (f.residualComponent t)) := by
  rw [Set.Ici_disjoint_Iic, residualComponent_le_residualComponent]
  exact hf.not_positiveReachable hst

/-- Every minimum cut contains the vertices whose residual component is reachable from the
component of the source. -/
theorem mem_of_residualComponent_le (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) {v : V}
    (hv : f.residualComponent s ≤ f.residualComponent v) : v ∈ S :=
  (hf.forall_isMinimum_mem_iff hst).2 (residualComponent_le_residualComponent.1 hv) S hS

/-- No minimum cut contains a vertex whose residual component reaches the component of the sink. -/
theorem notMem_of_residualComponent_le (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) {v : V}
    (hv : f.residualComponent v ≤ f.residualComponent t) : v ∉ S :=
  (hf.forall_isMinimum_notMem_iff hst).2 (residualComponent_le_residualComponent.1 hv) S hS

/-- A minimum cut contains every vertex of a residual component above that of one of its members.
-/
private theorem mem_of_le (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) {v w : V}
    (hvw : f.residualComponent v ≤ f.residualComponent w) (hv : v ∈ S) : w ∈ S :=
  hf.mem_of_positiveReachable hst hS (residualComponent_le_residualComponent.1 hvw) hv

/-- The source side determined by a set of free components: the vertices whose residual
component is reachable from the component of the source or is one of the given free components. -/
private noncomputable def sourceSide (f : BoundedFlow lo hi s t) (U : Set f.FreeComponent) :
    Finset V := by
  classical
  exact univ.filter fun v ↦ f.residualComponent s ≤ f.residualComponent v ∨
    ∃ h, (⟨f.residualComponent v, h⟩ : f.FreeComponent) ∈ U

omit [DecidableEq V] [IsOrderedAddMonoid K] in
private theorem mem_sourceSide {U : Set f.FreeComponent} {v : V} :
    v ∈ sourceSide f U ↔ f.residualComponent s ≤ f.residualComponent v ∨
      ∃ h, (⟨f.residualComponent v, h⟩ : f.FreeComponent) ∈ U := by
  classical
  simp [sourceSide]

/-- The source side of an upper set of free components is a minimum cut. -/
private theorem isMinimum_sourceSide (hst : s ≠ t) (hf : f.IsMaximum)
    {U : Set f.FreeComponent} (hU : IsUpperSet U) :
    TerminalCut.IsMinimum (cutBound lo hi) {s} {t} (sourceSide f U) := by
  have hdisj := Set.disjoint_left.1 (hf.disjoint_Ici_Iic hst)
  refine (hf.isMinimum_cutBound_iff_forall_positiveReachable hst).2
    ⟨mem_sourceSide.2 (.inl le_rfl), fun ht ↦ ?_, fun v hv w hvw ↦ ?_⟩
  · rcases mem_sourceSide.1 ht with h | ⟨h, -⟩
    exacts [hdisj (Set.mem_Ici.2 h) (Set.mem_Iic.2 le_rfl), h.2 le_rfl]
  · rw [← residualComponent_le_residualComponent] at hvw
    rw [mem_sourceSide] at hv ⊢
    by_cases hsw : f.residualComponent s ≤ f.residualComponent w
    · exact .inl hsw
    rcases hv with hsv | ⟨h, hvU⟩
    · exact .inl (hsv.trans hvw)
    exact .inr ⟨⟨hsw, fun hwt ↦ h.2 (hvw.trans hwt)⟩, hU (Subtype.mk_le_mk.2 hvw) hvU⟩

/-- The free components all of whose vertices lie in a minimum cut form an upper set. -/
private theorem isUpperSet_freeSet (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) :
    IsUpperSet {C : f.FreeComponent | ∀ v, f.residualComponent v = C.1 → v ∈ S} := by
  intro C D hCD hC w hw
  obtain ⟨v, hv⟩ := residualComponent_surjective C.1
  exact mem_of_le hst hf hS (hv.trans_le ((Subtype.coe_le_coe.2 hCD).trans_eq hw.symm)) (hC v hv)

/-- **The poset of minimum cuts.** For a maximum bounded `s`–`t` assignment `f` between distinct
terminals, the minimum cuts, ordered by inclusion, are order isomorphic to the upper sets of the
poset of free residual components, ordered by inclusion. A minimum cut corresponds to the free
components contained in it, and an upper set to the vertices of its components together with the
vertices forced onto the source side. -/
noncomputable def minimizersOrderIso (hst : s ≠ t) (hf : f.IsMaximum) :
    minimizers (isSubmodular_cutBound lo hi (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t} ≃o
      (UpperSet f.FreeComponent)ᵒᵈ :=
  Equiv.toOrderIso
    { toFun S := toDual ⟨{C | ∀ v, f.residualComponent v = C.1 → v ∈ (S : Finset V)},
        isUpperSet_freeSet hst hf ((mem_minimizers _ _ _).1 S.2)⟩
      invFun U := ⟨sourceSide f ↑(ofDual U),
        (mem_minimizers _ _ _).2 (isMinimum_sourceSide hst hf (ofDual U).upper)⟩
      left_inv S := by
        have hS := (mem_minimizers _ _ _).1 S.2
        refine Subtype.ext (Finset.ext fun v ↦ ?_)
        simp only [mem_sourceSide, ofDual_toDual]
        refine ⟨fun h ↦ h.elim (hf.mem_of_residualComponent_le hst hS) fun ⟨_, h⟩ ↦ h v rfl,
          fun hv ↦ ?_⟩
        by_cases hsv : f.residualComponent s ≤ f.residualComponent v
        · exact .inl hsv
        exact .inr ⟨⟨hsv, fun hvt ↦ hf.notMem_of_residualComponent_le hst hS hvt hv⟩,
          fun w hw ↦ mem_of_le hst hf hS hw.ge hv⟩
      right_inv U := by
        refine ofDual.injective (UpperSet.ext (Set.ext fun ⟨C, hC⟩ ↦ ?_))
        simp only [ofDual_toDual, UpperSet.coe_mk, Set.mem_ofPred_eq, SetLike.mem_coe]
        refine ⟨fun h ↦ ?_, fun h v hv ↦ ?_⟩
        · obtain ⟨v, rfl⟩ := residualComponent_surjective C
          rcases mem_sourceSide.1 (h v rfl) with hsv | ⟨_, hv⟩
          exacts [(hC.1 hsv).elim, hv]
        · subst hv
          exact mem_sourceSide.2 (.inr ⟨hC, h⟩) }
    (fun S T hST ↦ UpperSet.coe_subset_coe.1 fun _ hC v hv ↦ hST (hC v hv))
    (fun U U' hUU' v hv ↦ by
      rcases mem_sourceSide.1 hv with h | ⟨h, hU⟩
      exacts [mem_sourceSide.2 (.inl h), mem_sourceSide.2 (.inr ⟨h, hUU' hU⟩)])

/-- A free component belongs to the upper set of a minimum cut exactly when all of its vertices
lie in the cut. -/
theorem mem_minimizersOrderIso_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {S : minimizers (isSubmodular_cutBound lo hi (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}}
    {C : f.FreeComponent} :
    C ∈ ofDual (hf.minimizersOrderIso hst S) ↔
      ∀ v, f.residualComponent v = C.1 → v ∈ (S : Finset V) :=
  Iff.rfl

/-- The free residual component of a vertex belongs to the upper set of a minimum cut exactly when
the vertex lies in the cut. -/
@[simp]
theorem residualComponent_mem_minimizersOrderIso_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {S : minimizers (isSubmodular_cutBound lo hi (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}}
    {v : V} (h : ¬f.residualComponent s ≤ f.residualComponent v ∧
      ¬f.residualComponent v ≤ f.residualComponent t) :
    ⟨f.residualComponent v, h⟩ ∈ ofDual (hf.minimizersOrderIso hst S) ↔ v ∈ (S : Finset V) :=
  ⟨fun hv ↦ hv v rfl, fun hv _ hw ↦ mem_of_le hst hf ((mem_minimizers _ _ _).1 S.2) hw.ge hv⟩

/-- **Vertex-membership formula.** A vertex lies in the minimum cut of an upper set of free
components exactly when its residual component is reachable from the component of the source or
is a member of the upper set. -/
@[simp]
theorem mem_minimizersOrderIso_symm_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {U : (UpperSet f.FreeComponent)ᵒᵈ} {v : V} :
    v ∈ ((hf.minimizersOrderIso hst).symm U : Finset V) ↔
      f.residualComponent s ≤ f.residualComponent v ∨
        ∃ h, (⟨f.residualComponent v, h⟩ : f.FreeComponent) ∈ ofDual U :=
  mem_sourceSide

/-- The free components contained in the union of two minimum cuts are the union of those
contained in each. -/
theorem coe_minimizersOrderIso_sup (hst : s ≠ t) (hf : f.IsMaximum)
    (S T : minimizers (isSubmodular_cutBound lo hi (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}) :
    (↑(ofDual (hf.minimizersOrderIso hst (S ⊔ T))) : Set f.FreeComponent) =
      ↑(ofDual (hf.minimizersOrderIso hst S)) ∪ ↑(ofDual (hf.minimizersOrderIso hst T)) := by
  rw [map_sup, _root_.ofDual_sup, UpperSet.coe_inf]

/-- The free components contained in the intersection of two minimum cuts are the intersection of
those contained in each. -/
theorem coe_minimizersOrderIso_inf (hst : s ≠ t) (hf : f.IsMaximum)
    (S T : minimizers (isSubmodular_cutBound lo hi (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}) :
    (↑(ofDual (hf.minimizersOrderIso hst (S ⊓ T))) : Set f.FreeComponent) =
      ↑(ofDual (hf.minimizersOrderIso hst S)) ∩ ↑(ofDual (hf.minimizersOrderIso hst T)) := by
  rw [map_inf, _root_.ofDual_inf, UpperSet.coe_sup]

/-- The empty upper set of free components gives the smallest minimum cut. -/
theorem minimizersOrderIso_symm_top (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) :
    ((hf.minimizersOrderIso hst).symm (toDual ⊤) : Finset V) =
      smallest hsub (disjoint_singleton.2 hst) := by
  ext v
  rw [mem_minimizersOrderIso_symm_iff, hf.mem_smallest_iff hst hsub,
    ← residualComponent_le_residualComponent]
  simp [UpperSet.notMem_top]

/-- The full upper set of free components gives the largest minimum cut. -/
theorem minimizersOrderIso_symm_bot (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) :
    ((hf.minimizersOrderIso hst).symm (toDual ⊥) : Finset V) =
      largest hsub (disjoint_singleton.2 hst) := by
  ext v
  rw [mem_minimizersOrderIso_symm_iff, hf.mem_largest_iff hst hsub,
    ← residualComponent_le_residualComponent]
  simp only [ofDual_toDual, UpperSet.mem_bot, exists_const_iff, and_true]
  refine ⟨fun h hvt ↦ ?_, fun h ↦ (em _).imp_right fun hsv ↦ ⟨hsv, h⟩⟩
  rcases h with hsv | ⟨-, h⟩
  exacts [Set.disjoint_left.1 (hf.disjoint_Ici_Iic hst) (Set.mem_Ici.2 hsv) (Set.mem_Iic.2 hvt),
    h hvt]

/-- The minimum cut is unique exactly when no residual component is free. -/
theorem existsUnique_isMinimum_iff_isEmpty (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, TerminalCut.IsMinimum (cutBound lo hi) {s} {t} S) ↔ IsEmpty f.FreeComponent := by
  rw [hf.existsUnique_isMinimum_iff hst, isEmpty_subtype]
  simp only [← residualComponent_le_residualComponent, not_and_or, not_not]
  exact ⟨fun h C ↦ by obtain ⟨v, rfl⟩ := residualComponent_surjective C; exact h v,
    fun h v ↦ h _⟩

end IsMaximum

end BoundedFlow

/-! ### Ordinary flows -/

namespace Flow.IsMaximum

variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
variable {cap : Assignment Q K} {s t : V} {f : Flow cap s t}

/-- **The poset of minimum cuts of an ordinary flow.** For a maximum ordinary `s`–`t` flow `f`
between distinct terminals, the minimum cuts for the capacity of the arrows leaving a set, ordered
by inclusion, are order isomorphic to the upper sets of the poset of free residual components,
ordered by inclusion. -/
noncomputable def minimizersOrderIso (hst : s ≠ t) (hf : f.IsMaximum) :
    minimizers (isSubmodular_outgoingArrowSum cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t} ≃o
      (UpperSet f.FreeComponent)ᵒᵈ :=
  ({ toEquiv := Equiv.subtypeEquivRight fun S ↦ by
      simp only [mem_minimizers, ← funext (cutBound_zero_left cap)]
     map_rel_iff' := Iff.rfl } :
    minimizers (isSubmodular_outgoingArrowSum cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t} ≃o
      minimizers (isSubmodular_cutBound 0 cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}).trans
    (((isMaximum_toBoundedFlow f).2 hf).minimizersOrderIso hst)

/-- The free residual component of a vertex belongs to the upper set of a minimum cut of a maximum
ordinary flow exactly when the vertex lies in the cut. -/
@[simp]
theorem residualComponent_mem_minimizersOrderIso_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {S : minimizers (isSubmodular_outgoingArrowSum cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}}
    {v : V} (h : ¬f.residualComponent s ≤ f.residualComponent v ∧
      ¬f.residualComponent v ≤ f.residualComponent t) :
    ⟨f.residualComponent v, h⟩ ∈ ofDual (hf.minimizersOrderIso hst S) ↔ v ∈ (S : Finset V) :=
  BoundedFlow.IsMaximum.residualComponent_mem_minimizersOrderIso_iff hst
    ((isMaximum_toBoundedFlow f).2 hf) h

/-- A vertex lies in the minimum cut of an upper set of free components exactly when its residual
component is reachable from the component of the source or is a member of the upper set. -/
@[simp]
theorem mem_minimizersOrderIso_symm_iff (hst : s ≠ t) (hf : f.IsMaximum)
    {U : (UpperSet f.FreeComponent)ᵒᵈ} {v : V} :
    v ∈ ((hf.minimizersOrderIso hst).symm U : Finset V) ↔
      f.residualComponent s ≤ f.residualComponent v ∨
        ∃ h, (⟨f.residualComponent v, h⟩ : f.FreeComponent) ∈ ofDual U :=
  BoundedFlow.IsMaximum.mem_minimizersOrderIso_symm_iff hst ((isMaximum_toBoundedFlow f).2 hf)

/-- The free components contained in the union of two minimum cuts of a maximum ordinary flow are
the union of those contained in each. -/
theorem coe_minimizersOrderIso_sup (hst : s ≠ t) (hf : f.IsMaximum)
    (S T : minimizers (isSubmodular_outgoingArrowSum cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}) :
    (↑(ofDual (hf.minimizersOrderIso hst (S ⊔ T))) : Set f.FreeComponent) =
      ↑(ofDual (hf.minimizersOrderIso hst S)) ∪ ↑(ofDual (hf.minimizersOrderIso hst T)) := by
  rw [map_sup, _root_.ofDual_sup, UpperSet.coe_inf]

/-- The free components contained in the intersection of two minimum cuts of a maximum ordinary
flow are the intersection of those contained in each. -/
theorem coe_minimizersOrderIso_inf (hst : s ≠ t) (hf : f.IsMaximum)
    (S T : minimizers (isSubmodular_outgoingArrowSum cap (f.mem_Icc.1.trans f.mem_Icc.2)) {s} {t}) :
    (↑(ofDual (hf.minimizersOrderIso hst (S ⊓ T))) : Set f.FreeComponent) =
      ↑(ofDual (hf.minimizersOrderIso hst S)) ∩ ↑(ofDual (hf.minimizersOrderIso hst T)) := by
  rw [map_inf, _root_.ofDual_inf, UpperSet.coe_sup]

/-- The empty upper set of free components gives the smallest minimum cut of a maximum ordinary
flow. -/
theorem minimizersOrderIso_symm_top (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) :
    ((hf.minimizersOrderIso hst).symm (toDual ⊤) : Finset V) =
      smallest hsub (disjoint_singleton.2 hst) := by
  have hf' := (isMaximum_toBoundedFlow f).2 hf
  have hsub' := isSubmodular_cutBound 0 cap (f.mem_Icc.1.trans f.mem_Icc.2)
  ext v
  rw [mem_minimizersOrderIso_symm_iff, hf.mem_smallest_iff hst hsub,
    ← hf'.mem_smallest_iff hst hsub', ← hf'.minimizersOrderIso_symm_top hst hsub',
    BoundedFlow.IsMaximum.mem_minimizersOrderIso_symm_iff]

/-- The full upper set of free components gives the largest minimum cut of a maximum ordinary
flow. -/
theorem minimizersOrderIso_symm_bot (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) :
    ((hf.minimizersOrderIso hst).symm (toDual ⊥) : Finset V) =
      largest hsub (disjoint_singleton.2 hst) := by
  have hf' := (isMaximum_toBoundedFlow f).2 hf
  have hsub' := isSubmodular_cutBound 0 cap (f.mem_Icc.1.trans f.mem_Icc.2)
  ext v
  rw [mem_minimizersOrderIso_symm_iff, hf.mem_largest_iff hst hsub,
    ← hf'.mem_largest_iff hst hsub', ← hf'.minimizersOrderIso_symm_bot hst hsub',
    BoundedFlow.IsMaximum.mem_minimizersOrderIso_symm_iff]

/-- The minimum cut is unique exactly when no residual component of a maximum ordinary flow is
free. -/
theorem existsUnique_isMinimum_iff_isEmpty (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S) ↔ IsEmpty f.FreeComponent := by
  rw [← funext (cutBound_zero_left cap)]
  exact ((isMaximum_toBoundedFlow f).2 hf).existsUnique_isMinimum_iff_isEmpty hst

end Flow.IsMaximum

/-!
## Example

On the vertices `s = 0`, `a = 1`, `b = 2` and `t = 3`, take unit capacities on the arrows
`s → a`, `a → t`, `s → b`, `b → t` and `a → b`, and capacity zero on one arrow for every other
ordered pair, loops included. The flow sending one unit along each of `s → a → t` and `s → b → t`
and nothing along `a → b` has value `2`, the capacity of `{s}`, so it is maximum. Its residual
arrows of positive capacity are the reverse arrows `a → s`, `b → s`, `t → a` and `t → b`, and the
forward arrow `a → b`. So the free residual components are those of `a` and `b`, with the
component of `a` below that of `b`. The upper sets of free components are the empty set, the
component of `b`, and both components, and the minimum cuts are `{s}`, `{s, b}` and `{s, a, b}`:
choosing `a` forces choosing `b`.
-/

private abbrev ExHom (_ _ : Fin 4) : Type := Unit

private def exCap : Assignment ExHom ℤ := fun v w _ ↦
  ![![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]] v w

private def exFlow : Flow exCap (0 : Fin 4) 3 where
  toFun v w _ := ![![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]] v w
  mem_Icc := ⟨fun v w _ ↦ by revert v w; decide, fun v w _ ↦ by revert v w; decide⟩
  conserve v h0 h3 := by
    fin_cases v <;> simp_all [excessAt_def, Fin.sum_univ_four]
  excessAt_sink_nonneg := by simp [excessAt_def, Fin.sum_univ_four]

private theorem exFlow_isMaximum : exFlow.IsMaximum :=
  (Flow.isMaximum_toBoundedFlow exFlow).1 <|
    exFlow.isMaximum_of_val_eq_cutBound (S := {0}) (by decide) (by decide) (by
      simp [BoundedFlow.val_def, excessAt_def, cutBound_def, arrowSum_eq_sum_ite,
        Fin.sum_univ_four, exCap, exFlow])

/-- In the example, no residual arrow of positive capacity leaves `C`: every arrow leaving `C` is
saturated and every arrow entering `C` carries nothing. -/
private def ExClosed (C : Finset (Fin 4)) : Prop :=
  ∀ v ∈ C, ∀ w ∉ C, (∀ e : ExHom v w, exCap e = exFlow.toFun e) ∧
    ∀ e : ExHom w v, exFlow.toFun e = 0

private instance (C : Finset (Fin 4)) : Decidable (ExClosed C) := by
  unfold ExClosed
  infer_instance

private theorem exClosed_iff {C : Finset (Fin 4)} :
    (∀ v ∈ C, ∀ w ∉ C, ∀ e : ResidualHom ExHom v w,
      residualCapacity 0 exCap exFlow.toFun e = 0) ↔ ExClosed C := by
  simp [ExClosed, Sum.forall, sub_eq_zero]

private theorem not_positiveReachable_ex {C : Finset (Fin 4)} (hC : ExClosed C) {v w : Fin 4}
    (hv : v ∈ C) (hw : w ∉ C) : ¬PositiveReachable (residualCapacity 0 exCap exFlow.toFun) v w :=
  fun h ↦ hw (h.mem_of_mem (C := (C : Set (Fin 4))) hv fun x y e hx he ↦
    by_contra fun hy ↦ he.ne' (exClosed_iff.2 hC x hx y hy e))

private theorem exFlow_free {v : Fin 4} (hv : v = 1 ∨ v = 2) :
    ¬exFlow.residualComponent 0 ≤ exFlow.residualComponent v ∧
      ¬exFlow.residualComponent v ≤ exFlow.residualComponent 3 := by
  simp only [BoundedFlow.residualComponent_le_residualComponent]
  rcases hv with rfl | rfl <;>
    exact ⟨not_positiveReachable_ex (C := {0}) (by decide) (by decide) (by decide),
      not_positiveReachable_ex (C := {0, 1, 2}) (by decide) (by decide) (by decide)⟩

-- The two free residual components are those of `a` and `b`, and the first lies below the second.
example : ∀ C : exFlow.FreeComponent,
    C.1 = exFlow.residualComponent 1 ∨ C.1 = exFlow.residualComponent 2 := by
  rintro ⟨C, hs, ht⟩
  obtain ⟨v, rfl⟩ := BoundedFlow.residualComponent_surjective C
  fin_cases v
  exacts [(hs le_rfl).elim, .inl rfl, .inr rfl, (ht le_rfl).elim]

example : (⟨_, exFlow_free (.inl rfl)⟩ : exFlow.FreeComponent) < ⟨_, exFlow_free (.inr rfl)⟩ := by
  refine lt_of_le_not_ge ?_ ?_ <;>
    simp only [Subtype.mk_le_mk, BoundedFlow.residualComponent_le_residualComponent]
  · exact .single (Q := ResidualHom ExHom) (Sum.inl ()) (by simp [exCap, exFlow])
  · exact not_positiveReachable_ex (C := {0, 2}) (by decide) (by decide) (by decide)

-- The minimum cuts are exactly `{s}`, `{s, b}` and `{s, a, b}`.
example (S : Finset (Fin 4)) :
    IsMinimum (fun S ↦ arrowSum exCap S Sᶜ) {0} {3} S ↔ S = {0} ∨ S = {0, 2} ∨ S = {0, 1, 2} := by
  rw [exFlow_isMaximum.isMinimum_iff (by decide), exClosed_iff]
  revert S
  decide

end TauCeti
