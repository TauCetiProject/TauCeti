/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.UpperLower.CompleteLattice
public import TauCeti.Combinatorics.Network.MinimumCut.Residual
public import TauCeti.Combinatorics.Network.PositiveComponent
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The poset of all minimum cuts

Let `f` be a maximum bounded `s`–`t` assignment between distinct terminals, and order the
strongly connected components of its positive-capacity residual arrows by residual reachability,
as `TauCeti.PositiveComponent`. The components reachable from the component of `s` lie on the
source side of every minimum cut, and those reaching the component of `t` on the source side of
none. The remaining, *free*, components parametrize all minimum cuts: a minimum cut is determined
by the free components it contains, and these form an upper set; conversely every upper set of
free components, together with the vertices reachable from `s`, is a minimum cut.

This gives an order isomorphism between the lattice of minimum cuts under inclusion and the upper
sets of the finite poset of free components under inclusion, written `(UpperSet _)ᵒᵈ` because
Mathlib orders `UpperSet` by reverse inclusion. Union and intersection of minimum cuts correspond
to union and intersection of upper sets; the empty and the full upper set give the smallest and
the largest minimum cuts, and the minimum cut is unique exactly when there are no free components.
The bounds may be negative and the value of `f` may have either sign; the ordinary-flow statements
follow by specialization.

## Main definitions

* `TauCeti.BoundedFlow.IsMaximum.minimumCutOrderIso`: the order isomorphism between the minimum
  cuts and the upper sets of free components.
* `TauCeti.Flow.IsMaximum.minimumCutOrderIso`: the same for ordinary flows.

## Main results

* `TauCeti.BoundedFlow.IsMaximum.mem_minimumCutOrderIso` and
  `TauCeti.BoundedFlow.IsMaximum.mem_minimumCutOrderIso_symm`: the isomorphism and its inverse on
  components and on vertices.
* `TauCeti.BoundedFlow.IsMaximum.coe_minimumCutOrderIso_symm_bot` and
  `TauCeti.BoundedFlow.IsMaximum.coe_minimumCutOrderIso_symm_top`: the empty and the full upper set
  give the smallest and the largest minimum cuts.
* `TauCeti.BoundedFlow.IsMaximum.existsUnique_isMinimum_iff_isEmpty`: the minimum cut is unique
  exactly when there are no free components.

## References

* J.-C. Picard, M. Queyranne, *On the structure of all minimum cuts in a network and
  applications*, Math. Programming Stud. 13 (1980), 8–16.
-/

public section

namespace TauCeti

open Finset TerminalCut OrderDual PositiveComponent

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]
variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

namespace BoundedFlow.IsMaximum

variable {lo hi : Assignment Q K} {s t : V} {f : BoundedFlow lo hi s t}

/-- The free components contained in a minimum cut form an upper set. -/
private theorem isUpperSet_setOf_forall_mem (hst : s ≠ t) (hf : f.IsMaximum) {S : Finset V}
    (hS : IsMinimum (cutBound lo hi) {s} {t} S) :
    IsUpperSet {C : Free (residualCapacity lo hi f.toFun) s t |
      ∀ v, PositiveComponent.mk (residualCapacity lo hi f.toFun) v = C.1 → v ∈ S} := by
  intro C D hCD hC w hw
  obtain ⟨v, hv⟩ := mk_surjective C.1
  have hvw : PositiveComponent.mk (residualCapacity lo hi f.toFun) v ≤
      PositiveComponent.mk _ w := by
    rw [hv, hw]
    exact hCD
  exact hf.mem_of_positiveReachable hst hS (mk_le_mk.1 hvw) (hC v hv)

variable (f) in
/-- The vertices positively reachable from the source together with the vertices of the free
components in `U`. -/
private noncomputable def cutOfUpperSet
    (U : UpperSet (Free (residualCapacity lo hi f.toFun) s t)) : Finset V := by
  classical
  exact univ.filter fun v ↦ PositiveReachable (residualCapacity lo hi f.toFun) s v ∨
    ∃ C ∈ U, PositiveComponent.mk (residualCapacity lo hi f.toFun) v = C.1

omit [DecidableEq V] [IsOrderedAddMonoid K] in
private theorem mem_cutOfUpperSet {U : UpperSet (Free (residualCapacity lo hi f.toFun) s t)}
    {v : V} : v ∈ cutOfUpperSet f U ↔ PositiveReachable (residualCapacity lo hi f.toFun) s v ∨
      ∃ C ∈ U, PositiveComponent.mk (residualCapacity lo hi f.toFun) v = C.1 := by
  classical
  simp [cutOfUpperSet]

/-- The vertices reachable from the source together with the vertices of an upper set of free
components form a minimum cut. -/
private theorem isMinimum_cutOfUpperSet (hst : s ≠ t) (hf : f.IsMaximum)
    (U : UpperSet (Free (residualCapacity lo hi f.toFun) s t)) :
    IsMinimum (cutBound lo hi) {s} {t} (cutOfUpperSet f U) := by
  rw [hf.isMinimum_cutBound_iff hst]
  refine ⟨mem_cutOfUpperSet.2 (.inl (.refl _ _)), fun ht ↦ ?_, fun v hv w hw e ↦ ?_⟩
  · rcases mem_cutOfUpperSet.1 ht with h | ⟨C, -, hC⟩
    · exact hf.not_positiveReachable hst h
    · exact C.2.2 (hC ▸ le_rfl)
  refine ((residualCapacity_nonneg f.mem_Icc v w e).eq_or_lt.resolve_right fun he ↦ ?_).symm
  have hvw := PositiveReachable.single e he
  rw [mem_cutOfUpperSet, not_or, not_exists] at hw
  rcases mem_cutOfUpperSet.1 hv with hv | ⟨C, hCU, hC⟩
  · exact hw.1 (hv.trans hvw)
  · have hCw : C.1 ≤ PositiveComponent.mk _ w := hC ▸ mk_le_mk.2 hvw
    exact hw.2 ⟨PositiveComponent.mk _ w, mt mk_le_mk.1 hw.1, fun h ↦ C.2.2 (hCw.trans h)⟩
      ⟨U.upper hCw hCU, rfl⟩

/-- **The poset of all minimum cuts.** For a maximum bounded `s`–`t` assignment `f` between
distinct terminals, the minimum cuts for the cut bound, ordered by inclusion, are order isomorphic
to the upper sets of free components of the positive-capacity residual arrows, ordered by
inclusion. A minimum cut is sent to the free components it contains, and an upper set to the
vertices of its components together with the vertices positively reachable from the source. -/
noncomputable def minimumCutOrderIso (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) :
    minimizers hsub {s} {t} ≃o (UpperSet (Free (residualCapacity lo hi f.toFun) s t))ᵒᵈ :=
  Equiv.toOrderIso
    { toFun S := toDual ⟨_, isUpperSet_setOf_forall_mem hst hf ((mem_minimizers _ _ _).1 S.2)⟩
      invFun U := ⟨cutOfUpperSet f (ofDual U),
        (mem_minimizers _ _ _).2 (isMinimum_cutOfUpperSet hst hf _)⟩
      left_inv S := by
        have hS := (mem_minimizers _ _ _).1 S.2
        refine Subtype.ext (Finset.ext fun v ↦ mem_cutOfUpperSet.trans ⟨?_, fun hv ↦ ?_⟩)
        · rintro (h | ⟨C, hC, hvC⟩)
          exacts [(hf.forall_isMinimum_mem_iff hst).2 h _ hS, hC v hvC]
        by_cases h : PositiveReachable (residualCapacity lo hi f.toFun) s v
        · exact .inl h
        refine .inr ⟨⟨PositiveComponent.mk _ v, mt mk_le_mk.1 h, fun h' ↦
          (hf.forall_isMinimum_notMem_iff hst).2 (mk_le_mk.1 h') _ hS hv⟩, fun w hw ↦ ?_, rfl⟩
        exact hf.mem_of_positiveReachable hst hS (mk_eq_mk.1 hw.symm).1 hv
      right_inv U := by
        refine congrArg toDual (SetLike.ext fun C ↦ ⟨fun hC ↦ ?_, fun hC v hv ↦
          mem_cutOfUpperSet.2 (.inr ⟨C, hC, hv⟩)⟩)
        obtain ⟨v, hv⟩ := mk_surjective C.1
        rcases mem_cutOfUpperSet.1 (hC v hv) with h | ⟨D, hD, hvD⟩
        · exact (C.2.1 (hv ▸ mk_le_mk.2 h)).elim
        · rwa [Subtype.ext (hvD.symm.trans hv)] at hD }
    (fun S T hST ↦ UpperSet.coe_subset_coe.1 fun _ hC v hv ↦ hST (hC v hv))
    fun U U' hUU' v hv ↦ by
      rcases mem_cutOfUpperSet.1 hv with h | ⟨C, hC, hvC⟩
      exacts [mem_cutOfUpperSet.2 (.inl h),
        mem_cutOfUpperSet.2 (.inr ⟨C, UpperSet.coe_subset_coe.2 hUU' hC, hvC⟩)]

/-- A free component corresponds to a minimum cut `S` exactly when all its vertices lie in `S`. -/
@[simp]
theorem mem_minimumCutOrderIso (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) (S : minimizers hsub {s} {t})
    {C : Free (residualCapacity lo hi f.toFun) s t} :
    C ∈ ofDual (hf.minimumCutOrderIso hst hsub S) ↔
      ∀ v, PositiveComponent.mk (residualCapacity lo hi f.toFun) v = C.1 → v ∈ (S : Finset V) :=
  Iff.rfl

/-- The minimum cut of an upper set `U` of free components consists of the vertices positively
reachable from the source and the vertices of the components in `U`. -/
@[simp]
theorem mem_minimumCutOrderIso_symm (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi))
    (U : (UpperSet (Free (residualCapacity lo hi f.toFun) s t))ᵒᵈ) {v : V} :
    v ∈ ((hf.minimumCutOrderIso hst hsub).symm U : Finset V) ↔
      PositiveReachable (residualCapacity lo hi f.toFun) s v ∨
        ∃ C ∈ ofDual U, PositiveComponent.mk (residualCapacity lo hi f.toFun) v = C.1 :=
  mem_cutOfUpperSet

/-- The free components contained in the union of two minimum cuts are those contained in one of
them. -/
theorem coe_ofDual_minimumCutOrderIso_sup (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) (S T : minimizers hsub {s} {t}) :
    SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub (S ⊔ T))) =
      SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub S)) ∪
        SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub T)) := by
  rw [map_sup, _root_.ofDual_sup, UpperSet.coe_inf]

/-- The free components contained in the intersection of two minimum cuts are those contained in
both. -/
theorem coe_ofDual_minimumCutOrderIso_inf (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) (S T : minimizers hsub {s} {t}) :
    SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub (S ⊓ T))) =
      SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub S)) ∩
        SetLike.coe (ofDual (hf.minimumCutOrderIso hst hsub T)) := by
  rw [map_inf, _root_.ofDual_inf, UpperSet.coe_sup]

/-- The empty upper set of free components gives the smallest minimum cut. -/
theorem coe_minimumCutOrderIso_symm_bot (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) :
    ((hf.minimumCutOrderIso hst hsub).symm ⊥ : Finset V) =
      smallest hsub (disjoint_singleton.2 hst) := by
  ext v
  rw [mem_minimumCutOrderIso_symm, hf.mem_smallest_iff hst hsub]
  simp

/-- The full upper set of free components gives the largest minimum cut. -/
theorem coe_minimumCutOrderIso_symm_top (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular (cutBound lo hi)) :
    ((hf.minimumCutOrderIso hst hsub).symm ⊤ : Finset V) =
      largest hsub (disjoint_singleton.2 hst) := by
  ext v
  rw [mem_minimumCutOrderIso_symm, hf.mem_largest_iff hst hsub]
  simp only [ofDual_top, UpperSet.mem_bot, true_and]
  refine ⟨?_, fun hvt ↦ ?_⟩
  · rintro (h | ⟨C, hC⟩) hvt
    · exact hf.not_positiveReachable hst (h.trans hvt)
    · exact C.2.2 (hC ▸ mk_le_mk.2 hvt)
  by_cases h : PositiveReachable (residualCapacity lo hi f.toFun) s v
  · exact .inl h
  · exact .inr ⟨⟨PositiveComponent.mk _ v, mt mk_le_mk.1 h, mt mk_le_mk.1 hvt⟩, rfl⟩

/-- The minimum cut is unique exactly when there are no free components of the positive-capacity
residual arrows of a maximum bounded `s`–`t` assignment. -/
theorem existsUnique_isMinimum_iff_isEmpty (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, IsMinimum (cutBound lo hi) {s} {t} S) ↔
      IsEmpty (Free (residualCapacity lo hi f.toFun) s t) :=
  (hf.existsUnique_isMinimum_iff hst).trans isEmpty_free_iff.symm

end BoundedFlow.IsMaximum

/-! ### Ordinary flows -/

namespace Flow.IsMaximum

variable {cap : Assignment Q K} {s t : V} {f : Flow cap s t}

omit [IsOrderedAddMonoid K] in
/-- Submodularity of the capacity of the arrows leaving a set, as submodularity of the cut bound
with zero lower bounds. -/
private theorem isSubmodular_cutBound_zero
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) :
    IsSubmodular (cutBound 0 cap) :=
  funext (cutBound_zero_left cap) ▸ hsub

/-- The minimum cuts for the capacity of the arrows leaving a set are those for the cut bound
with zero lower bounds. -/
private def minimizersCutBoundZero (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (hsub' : IsSubmodular (cutBound 0 cap)) :
    minimizers hsub {s} {t} ≃o minimizers hsub' {s} {t} where
  toEquiv := Equiv.subtypeEquivRight fun S ↦ by
    rw [mem_minimizers, mem_minimizers, funext (cutBound_zero_left cap)]
  map_rel_iff' := Iff.rfl

/-- `minimizersCutBoundZero` keeps each minimum cut; this holds by its definition through
`Equiv.subtypeEquivRight`. -/
private theorem coe_minimizersCutBoundZero
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (hsub' : IsSubmodular (cutBound 0 cap)) (S : minimizers hsub {s} {t}) :
    (minimizersCutBoundZero hsub hsub' S : Finset V) = S :=
  rfl

/-- The inverse of `minimizersCutBoundZero` keeps each minimum cut; this holds by its definition
through `Equiv.subtypeEquivRight`. -/
private theorem coe_minimizersCutBoundZero_symm
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (hsub' : IsSubmodular (cutBound 0 cap)) (S : minimizers hsub' {s} {t}) :
    ((minimizersCutBoundZero hsub hsub').symm S : Finset V) = S :=
  rfl

/-- **The poset of all minimum cuts for ordinary flows.** For a maximum ordinary `s`–`t` flow `f`
between distinct terminals, the minimum cuts for the capacity of the arrows leaving a set,
ordered by inclusion, are order isomorphic to the upper sets of free components of the
positive-capacity residual arrows, ordered by inclusion. -/
noncomputable def minimumCutOrderIso (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) :
    minimizers hsub {s} {t} ≃o (UpperSet (Free (residualCapacity 0 cap f.toFun) s t))ᵒᵈ :=
  (minimizersCutBoundZero hsub (isSubmodular_cutBound_zero hsub)).trans
    (((isMaximum_toBoundedFlow f).2 hf).minimumCutOrderIso hst (isSubmodular_cutBound_zero hsub))

/-- The ordinary-flow isomorphism sends a minimum cut to the free components that the
bounded-assignment isomorphism assigns to the same cut. -/
theorem minimumCutOrderIso_apply (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (hsub' : IsSubmodular (cutBound 0 cap)) (S : minimizers hsub {s} {t}) :
    hf.minimumCutOrderIso hst hsub S =
      ((isMaximum_toBoundedFlow f).2 hf).minimumCutOrderIso hst hsub'
        ⟨S, by
          rw [mem_minimizers, funext (cutBound_zero_left cap)]
          exact (mem_minimizers hsub _ _).1 S.2⟩ := by
  rw [minimumCutOrderIso, OrderIso.trans_apply]
  exact congrArg _ (Subtype.ext (coe_minimizersCutBoundZero _ _ S))

/-- The inverse ordinary-flow isomorphism sends an upper set of free components to the minimum cut
that the inverse bounded-assignment isomorphism assigns to it. -/
theorem coe_minimumCutOrderIso_symm (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (hsub' : IsSubmodular (cutBound 0 cap))
    (U : (UpperSet (Free (residualCapacity 0 cap f.toFun) s t))ᵒᵈ) :
    ((hf.minimumCutOrderIso hst hsub).symm U : Finset V) =
      ((((isMaximum_toBoundedFlow f).2 hf).minimumCutOrderIso hst hsub').symm U : Finset V) := by
  rw [minimumCutOrderIso, OrderIso.symm_trans_apply, coe_minimizersCutBoundZero_symm]

/-- A free component corresponds to a minimum cut `S` exactly when all its vertices lie in `S`. -/
@[simp]
theorem mem_minimumCutOrderIso (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ) (S : minimizers hsub {s} {t})
    {C : Free (residualCapacity 0 cap f.toFun) s t} :
    C ∈ ofDual (hf.minimumCutOrderIso hst hsub S) ↔
      ∀ v, PositiveComponent.mk (residualCapacity 0 cap f.toFun) v = C.1 → v ∈ (S : Finset V) := by
  rw [minimumCutOrderIso_apply hst hf hsub (isSubmodular_cutBound_zero hsub),
    BoundedFlow.IsMaximum.mem_minimumCutOrderIso]

/-- The minimum cut of an upper set `U` of free components consists of the vertices positively
reachable from the source and the vertices of the components in `U`. -/
@[simp]
theorem mem_minimumCutOrderIso_symm (hst : s ≠ t) (hf : f.IsMaximum)
    (hsub : IsSubmodular fun S : Finset V ↦ arrowSum cap S Sᶜ)
    (U : (UpperSet (Free (residualCapacity 0 cap f.toFun) s t))ᵒᵈ) {v : V} :
    v ∈ ((hf.minimumCutOrderIso hst hsub).symm U : Finset V) ↔
      PositiveReachable (residualCapacity 0 cap f.toFun) s v ∨
        ∃ C ∈ ofDual U, PositiveComponent.mk (residualCapacity 0 cap f.toFun) v = C.1 := by
  rw [coe_minimumCutOrderIso_symm hst hf hsub (isSubmodular_cutBound_zero hsub),
    BoundedFlow.IsMaximum.mem_minimumCutOrderIso_symm]

/-- The minimum cut is unique exactly when there are no free components of the positive-capacity
residual arrows of a maximum ordinary `s`–`t` flow. -/
theorem existsUnique_isMinimum_iff_isEmpty (hst : s ≠ t) (hf : f.IsMaximum) :
    (∃! S, IsMinimum (fun S ↦ arrowSum cap S Sᶜ) {s} {t} S) ↔
      IsEmpty (Free (residualCapacity 0 cap f.toFun) s t) :=
  (hf.existsUnique_isMinimum_iff hst).trans isEmpty_free_iff.symm

end Flow.IsMaximum

/-!
## Example

On the vertices `s = 0`, `a = 1`, `b = 2` and `t = 3`, take unit capacities on the arrows
`s → a`, `s → b`, `a → b`, `a → t` and `b → t`, and one arrow of capacity zero for every other
ordered pair, loops included. The flow sending one unit along `s → a → t` and one along
`s → b → t` has value `2`, the capacity of `{s}`, so it is maximum. In its residual network the
only arrows of positive capacity are `a → s`, `b → s`, `t → a`, `t → b` and `a → b`, so every
positive component is a single vertex. The free components are those of `a` and `b`, with
`a < b`, and the minimum cuts are exactly `{s}`, `{s, b}` and `{s, a, b}`: choosing `a` forces
choosing `b`.
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
  (Flow.isMaximum_toBoundedFlow _).1 <| exFlow.isMaximum_of_val_eq_cutBound (S := {0}) (by decide)
    (by decide) (by
      simp [BoundedFlow.val_def, excessAt_def, cutBound_def, arrowSum_eq_sum_ite,
        Fin.sum_univ_four, exCap, exFlow])

/-- No vertex outside a set that no positive-capacity residual arrow leaves is reachable from
inside it. -/
private theorem not_positiveReachable_ex {S : Finset (Fin 4)} {v w : Fin 4} (hv : v ∈ S)
    (hw : w ∉ S) (hS : ∀ x ∈ S, ∀ y ∉ S, ∀ e : ResidualHom ExHom x y,
      ¬0 < residualCapacity 0 exCap exFlow.toFun e) :
    ¬PositiveReachable (residualCapacity 0 exCap exFlow.toFun) v w := fun h ↦
  hw (h.mem_of_mem (C := (S : Set (Fin 4))) hv fun x y e hx he ↦ by
    by_contra hy
    exact hS x hx y hy e he)

private theorem not_positiveReachable_ex_source {w : Fin 4} (hw : w ≠ 0) :
    ¬PositiveReachable (residualCapacity 0 exCap exFlow.toFun) 0 w :=
  not_positiveReachable_ex (S := {0}) (by decide) (by simpa using hw) (by
    simp only [Sum.forall, residualCapacity_inl, residualCapacity_inr]
    decide)

private theorem not_positiveReachable_ex_sink {v : Fin 4} (hv : v ≠ 3) :
    ¬PositiveReachable (residualCapacity 0 exCap exFlow.toFun) v 3 :=
  not_positiveReachable_ex (S := {0, 1, 2}) (by fin_cases v <;> simp_all) (by decide) (by
    simp only [Sum.forall, residualCapacity_inl, residualCapacity_inr]
    decide)

private theorem not_positiveReachable_ex_two_one :
    ¬PositiveReachable (residualCapacity 0 exCap exFlow.toFun) 2 1 :=
  not_positiveReachable_ex (S := {0, 2}) (by decide) (by decide) (by
    simp only [Sum.forall, residualCapacity_inl, residualCapacity_inr]
    decide)

-- The free components are those of `a` and `b`.
example (C : PositiveComponent (residualCapacity 0 exCap exFlow.toFun)) :
    (¬mk _ 0 ≤ C ∧ ¬C ≤ mk _ 3) ↔ C = mk _ 1 ∨ C = mk _ 2 := by
  induction C using PositiveComponent.ind with
  | h v =>
    have h01 := not_positiveReachable_ex_source (w := 1) (by decide)
    have h02 := not_positiveReachable_ex_source (w := 2) (by decide)
    have h13 := not_positiveReachable_ex_sink (v := 1) (by decide)
    have h23 := not_positiveReachable_ex_sink (v := 2) (by decide)
    fin_cases v <;> simp [mk_eq_mk, h01, h02, h13, h23, not_positiveReachable_ex_two_one]

-- The free component of `a` lies strictly below that of `b`.
example : mk (residualCapacity 0 exCap exFlow.toFun) 1 < mk _ 2 :=
  lt_of_le_not_ge (mk_le_mk.2 (.single (Q := ResidualHom ExHom) (Sum.inl ()) (by
    simp [exCap, exFlow]))) (mt mk_le_mk.1 not_positiveReachable_ex_two_one)

-- The minimum cuts are exactly `{s}`, `{s, b}` and `{s, a, b}`.
example (S : Finset (Fin 4)) :
    IsMinimum (fun S ↦ arrowSum exCap S Sᶜ) {0} {3} S ↔ S = {0} ∨ S = {0, 2} ∨ S = {0, 1, 2} := by
  rw [exFlow_isMaximum.isMinimum_iff (by decide)]
  simp only [Sum.forall, residualCapacity_inl, residualCapacity_inr]
  revert S
  decide

end TauCeti
