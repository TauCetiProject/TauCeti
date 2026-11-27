/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Extremal bounded flows as residual maximum flows

Starting from any feasible bounded terminal assignment, maximizing its value is an ordinary
maximum-flow problem in the forward residual direction. Minimizing its value is the corresponding
maximum-flow problem with the terminals exchanged. The resulting augmentation and diminution add
or subtract the residual-flow value, respectively.

These reductions let results about ordinary maximum flows be applied to networks with signed lower
and upper bounds without first normalizing the bounds.

## References

* J. Bang-Jensen and G. Gutin, *Digraphs: Theory, Algorithms and Applications*, Theorem 3.4.2.
* D. P. Bertsekas, *Linear Network Optimization*, Section 1.1.3.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K]

namespace BoundedFlow

variable {lo hi : Assignment Q K} {s t : V}

section Ordered

variable [Preorder K] [AddLeftMono K]

/-- Augment a bounded terminal assignment by an ordinary flow in its residual network. -/
def augment (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) s t) : BoundedFlow lo hi s t :=
  f.update r.toBoundedFlow

/-- Residual augmentation uses the residual update on the underlying assignments. -/
@[simp]
theorem augment_toFun (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) s t) :
    (f.augment r).toFun = residualUpdate f.toFun r.toFun :=
  f.update_toFun r.toBoundedFlow

/-- Residual augmentation adds the value of the residual flow. -/
@[simp]
theorem val_augment (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) s t) :
    (f.augment r).val = f.val + r.val :=
  f.val_update r.toBoundedFlow

/-- Diminish a bounded terminal assignment by augmenting toward its source in the residual
network. -/
def diminish (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) t s) : BoundedFlow lo hi s t :=
  f.update r.toBoundedFlow.swap

/-- Residual diminution uses the residual update on the underlying assignments. -/
@[simp]
theorem diminish_toFun (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) t s) :
    (f.diminish r).toFun = residualUpdate f.toFun r.toFun := by
  rw [diminish, update_toFun, swap_toFun]

/-- Residual diminution subtracts the value of the reverse residual flow. -/
@[simp]
theorem val_diminish (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) t s) :
    (f.diminish r).val = f.val - r.val := by
  rw [diminish, val_update, val_swap]
  abel

end Ordered

section LinearOrder

variable [LinearOrder K] [IsOrderedAddMonoid K]

/-- Augmenting a bounded assignment gives a maximum assignment exactly when the residual flow is
maximum. -/
@[simp]
theorem isMaximum_augment_iff (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) s t) :
    (f.augment r).IsMaximum ↔ r.IsMaximum := by
  rw [isMaximum_iff, Flow.isMaximum_iff]
  constructor
  · intro h q
    have hq := h (f.augment q)
    simpa only [val_augment, add_le_add_iff_left] using hq
  · intro hr g
    by_cases hgf : g.val ≤ f.val
    · rw [val_augment]
      exact hgf.trans (le_add_of_nonneg_right r.val_nonneg)
    · have hfg : f.val ≤ g.val := le_of_not_ge hgf
      obtain ⟨q, hq⟩ := f.exists_update_eq g
      have hqval : f.val + q.val = g.val := by
        rw [← val_update, hq]
      have hqnonneg : 0 ≤ q.val := by
        rw [← add_le_add_iff_left f.val, add_zero, hqval]
        exact hfg
      let q' : Flow (residualCapacity lo hi f.toFun) s t := ⟨q, by
        rw [← BoundedFlow.val_def]
        exact hqnonneg⟩
      rw [← hqval, val_augment, add_le_add_iff_left]
      simpa [q'] using hr q'

/-- Diminishing a bounded assignment gives a minimum assignment exactly when the reverse residual
flow is maximum. -/
@[simp]
theorem isMinimum_diminish_iff (f : BoundedFlow lo hi s t)
    (r : Flow (residualCapacity lo hi f.toFun) t s) :
    (f.diminish r).IsMinimum ↔ r.IsMaximum := by
  rw [isMinimum_iff, Flow.isMaximum_iff]
  constructor
  · intro h q
    have hq := h (f.diminish q)
    simpa only [val_diminish, sub_le_sub_iff_left, neg_le_neg_iff] using hq
  · intro hr g
    by_cases hfg : f.val ≤ g.val
    · rw [val_diminish]
      exact (sub_le_self f.val r.val_nonneg).trans hfg
    · have hgf : g.val ≤ f.val := le_of_not_ge hfg
      obtain ⟨q, hq⟩ := f.exists_update_eq g
      have hqval : f.val + q.val = g.val := by
        rw [← val_update, hq]
      have hqnonpos : q.val ≤ 0 := by
        rw [← add_le_add_iff_left f.val, add_zero, hqval]
        exact hgf
      let q' : Flow (residualCapacity lo hi f.toFun) t s := ⟨q.swap, by
        rw [← BoundedFlow.val_def, val_swap]
        exact neg_nonneg.mpr hqnonpos⟩
      calc
        (f.diminish r).val = f.val - r.val := val_diminish f r
        _ ≤ f.val - q'.val := sub_le_sub_left (hr q') f.val
        _ = g.val := by simp [q', hqval]

/-- A maximum bounded assignment is obtained by augmenting any feasible starting assignment by a
maximum ordinary flow in its residual network. -/
theorem exists_isMaximum_augment (f : BoundedFlow lo hi s t) :
    ∃ r : Flow (residualCapacity lo hi f.toFun) s t,
      r.IsMaximum ∧ (f.augment r).IsMaximum := by
  obtain ⟨r, hr⟩ := Flow.exists_isMaximum (residualCapacity_nonneg f.mem_Icc)
  exact ⟨r, hr, (isMaximum_augment_iff f r).2 hr⟩

/-- A minimum bounded assignment is obtained by diminishing any feasible starting assignment by a
maximum ordinary flow from sink to source in its residual network. -/
theorem exists_isMinimum_diminish (f : BoundedFlow lo hi s t) :
    ∃ r : Flow (residualCapacity lo hi f.toFun) t s,
      r.IsMaximum ∧ (f.diminish r).IsMinimum := by
  obtain ⟨r, hr⟩ := Flow.exists_isMaximum (residualCapacity_nonneg f.mem_Icc)
  exact ⟨r, hr, (isMinimum_diminish_iff f r).2 hr⟩

end LinearOrder

end BoundedFlow

end TauCeti
