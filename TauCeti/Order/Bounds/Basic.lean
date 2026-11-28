/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Directed

/-!
# Tail bounds of monotone and antitone families

In a directed preorder, the greatest lower bound of an antitone family indexed by `{r // r₀ ≤ r}`
agrees with the greatest lower bound of any tail `{r // s ≤ r}` with `r₀ ≤ s`
(`TauCeti.isGLB_antitone_tail_iff`). Dually, the least upper bound of a monotone family agrees with
the least upper bound of any tail (`TauCeti.isLUB_monotone_tail_iff`).

## Main results

* `TauCeti.isGLB_antitone_tail_iff`: the greatest lower bound of an antitone family over `r ≥ r₀`
  coincides with that over any tail `r ≥ s` (`r₀ ≤ s`).
* `TauCeti.isLUB_monotone_tail_iff`: the least upper bound of a monotone family over `r ≥ r₀`
  coincides with that over any tail `r ≥ s` (`r₀ ≤ s`).
-/

public section

namespace TauCeti

/-- An antitone family indexed by `{r : ι // r₀ ≤ r}` in a directed preorder has greatest lower
bound `a` if and only if its restriction to any tail `{r : ι // s ≤ r}` (`r₀ ≤ s`) has greatest
lower bound `a`. -/
theorem isGLB_antitone_tail_iff {ι α : Type*} [Preorder ι] [IsDirectedOrder ι] [Preorder α]
    {r₀ s : ι} (hs : r₀ ≤ s) (f : ∀ r : ι, r₀ ≤ r → α)
    (hf : ∀ {r r'} (hr : r₀ ≤ r) (hrr' : r ≤ r'), f r' (hr.trans hrr') ≤ f r hr) (a : α) :
    IsGLB (Set.range fun r : {r : ι // r₀ ≤ r} ↦ f r.val r.property) a ↔
      IsGLB (Set.range fun r : {r : ι // s ≤ r} ↦ f r.val (hs.trans r.property)) a := by
  have hsub : (Set.range fun r : {r : ι // s ≤ r} ↦ f r.val (hs.trans r.property)) ⊆
      Set.range fun r : {r : ι // r₀ ≤ r} ↦ f r.val r.property :=
    fun _ ⟨⟨r, hr⟩, hEq⟩ ↦ ⟨⟨r, hs.trans hr⟩, hEq⟩
  have hco : IsCoinitialFor
      (Set.range fun r : {r : ι // r₀ ≤ r} ↦ f r.val r.property)
      (Set.range fun r : {r : ι // s ≤ r} ↦ f r.val (hs.trans r.property)) := by
    rintro _ ⟨⟨r, hr⟩, hEq⟩
    obtain ⟨m, hrm, hsm⟩ := exists_ge_ge r s
    exact ⟨f m (hs.trans hsm), ⟨⟨m, hsm⟩, rfl⟩, hEq ▸ hf hr hrm⟩
  exact isGLB_congr (le_antisymm (lowerBounds_mono_set hsub)
    (lowerBounds_mono_of_isCoinitialFor hco))

/-- A monotone family indexed by `{r : ι // r₀ ≤ r}` in a directed preorder has least upper
bound `a` if and only if its restriction to any tail `{r : ι // s ≤ r}` (`r₀ ≤ s`) has least
upper bound `a`. -/
theorem isLUB_monotone_tail_iff {ι α : Type*} [Preorder ι] [IsDirectedOrder ι] [Preorder α]
    {r₀ s : ι} (hs : r₀ ≤ s) (f : ∀ r : ι, r₀ ≤ r → α)
    (hf : ∀ {r r'} (hr : r₀ ≤ r) (hrr' : r ≤ r'), f r hr ≤ f r' (hr.trans hrr')) (a : α) :
    IsLUB (Set.range fun r : {r : ι // r₀ ≤ r} ↦ f r.val r.property) a ↔
      IsLUB (Set.range fun r : {r : ι // s ≤ r} ↦ f r.val (hs.trans r.property)) a :=
  isGLB_antitone_tail_iff (α := αᵒᵈ) hs (fun r hr ↦ OrderDual.toDual (f r hr))
    (fun hr hrr' ↦ (hf hr hrr').dual) (OrderDual.toDual a)

end TauCeti
