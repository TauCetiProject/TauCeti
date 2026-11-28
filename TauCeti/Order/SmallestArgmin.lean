/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

/-!
# Smallest index attaining the minimum on a finite linear order

Given `c : ι → α` on a finite nonempty linear order `ι`, `TauCeti.smallestArgmin c` returns the
least index at which `c` attains its minimum, giving canonical deterministic tie-breaking.
-/

public section

namespace TauCeti

variable {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder ι] [LinearOrder α]

omit [LinearOrder ι] in
private theorem nonempty_min_filter (c : ι → α) :
    (Finset.univ.filter fun j ↦ ∀ i, c j ≤ c i).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.univ.exists_min_image c Finset.univ_nonempty
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i ↦ hj i (Finset.mem_univ _)⟩⟩

/-- The least index in a finite nonempty linear order `ι` minimizing `c : ι → α`. -/
def smallestArgmin (c : ι → α) : ι :=
  (Finset.univ.filter fun j ↦ ∀ i, c j ≤ c i).min' (nonempty_min_filter c)

/-- `smallestArgmin c` attains the global minimum of `c`. -/
theorem smallestArgmin_le (c : ι → α) (i : ι) : c (smallestArgmin c) ≤ c i :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (nonempty_min_filter c))).2 i

/-- Every minimizer of `c` is at least `smallestArgmin c`. -/
theorem smallestArgmin_le_of_forall_le {c : ι → α} {j : ι} (hj : ∀ i, c j ≤ c i) :
    smallestArgmin c ≤ j :=
  Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)

/-- Every index strictly smaller than `smallestArgmin c` has strictly larger value under `c`. -/
theorem lt_of_lt_smallestArgmin (c : ι → α) {i : ι} (h : i < smallestArgmin c) :
    c (smallestArgmin c) < c i :=
  lt_of_not_ge fun hle ↦
    not_le_of_gt h (smallestArgmin_le_of_forall_le fun k ↦ hle.trans (smallestArgmin_le c k))

/-- Exact characterization of the least minimizer `smallestArgmin c`. -/
theorem smallestArgmin_eq_iff {c : ι → α} {j : ι} :
    smallestArgmin c = j ↔ (∀ i, c j ≤ c i) ∧ ∀ i < j, c j < c i := by
  refine ⟨fun h ↦ h ▸ ⟨smallestArgmin_le c, fun _ hi ↦ lt_of_lt_smallestArgmin c hi⟩, ?_⟩
  rintro ⟨hmin, hlt⟩
  exact le_antisymm (smallestArgmin_le_of_forall_le hmin)
    (le_of_not_gt fun h ↦ not_le_of_gt (hlt _ h) (smallestArgmin_le c j))

/-- If some index strictly beats `i`, then `i` cannot be `smallestArgmin c`. -/
theorem smallestArgmin_ne_of_lt {c : ι → α} {i j : ι} (h : c j < c i) :
    smallestArgmin c ≠ i :=
  fun heq ↦ not_le_of_gt h (heq ▸ smallestArgmin_le c j)

/-- If every index `i ≤ j₀` is strictly beaten by some index `j`, then `j₀ < smallestArgmin c`. -/
theorem lt_smallestArgmin_of_forall_lt {c : ι → α} {j₀ : ι}
    (h : ∀ i ≤ j₀, ∃ j, c j < c i) : j₀ < smallestArgmin c :=
  lt_of_not_ge fun hle ↦ let ⟨j, hj⟩ := h _ hle; not_le_of_gt hj (smallestArgmin_le c j)

/-- On a constant function, `smallestArgmin` returns the least element of `ι`. -/
@[simp]
theorem smallestArgmin_const (a : α) :
    smallestArgmin (fun _ : ι ↦ a) = Finset.univ.min' Finset.univ_nonempty :=
  smallestArgmin_eq_iff.2
    ⟨fun _ ↦ le_rfl, fun i hi ↦ (not_le_of_gt hi (Finset.min'_le _ i (Finset.mem_univ i))).elim⟩

/-- Post-composing with a strictly monotone map preserves `smallestArgmin`. -/
theorem smallestArgmin_comp_strictMono {β : Type*} [LinearOrder β] {f : α → β}
    (hf : StrictMono f) (c : ι → α) :
    smallestArgmin (f ∘ c) = smallestArgmin c :=
  smallestArgmin_eq_iff.2
    ⟨fun i ↦ hf.monotone (smallestArgmin_le c i), fun _ hi ↦ hf (lt_of_lt_smallestArgmin c hi)⟩

/-- Pointwise equal functions have the same `smallestArgmin`. -/
theorem smallestArgmin_congr {c₁ c₂ : ι → α} (h : ∀ i, c₁ i = c₂ i) :
    smallestArgmin c₁ = smallestArgmin c₂ :=
  congrArg smallestArgmin (funext h)

end TauCeti
