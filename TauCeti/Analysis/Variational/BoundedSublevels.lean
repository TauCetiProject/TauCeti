/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Bounded sublevels of an energy

`HasBoundedSublevelsOn E S` is the boundedness condition used to obtain compactness in the
direct method: every sublevel of the real energy `E`, relative to the admissible set `S`,
is bounded. It is stable under restriction, increasing the energy, positive scaling, and
addition of an energy bounded below. In a seminormed group it is equivalent to boundedness
of every admissible sequence whose energies are bounded above.
-/

public section

open Set Bornology

namespace TauCeti

/-- Every sublevel of `E` relative to `S` is bounded. No lower bound on `E` is required. -/
def HasBoundedSublevelsOn {X : Type*} [Bornology X] (E : X → ℝ) (S : Set X) : Prop :=
  ∀ b : ℝ, IsBounded {x ∈ S | E x ≤ b}

/-- Characterization of bounded sublevels by the boundedness of each relative sublevel. -/
theorem hasBoundedSublevelsOn_iff {X : Type*} [Bornology X] {E : X → ℝ} {S : Set X} :
    HasBoundedSublevelsOn E S ↔ ∀ b : ℝ, IsBounded {x ∈ S | E x ≤ b} :=
  Iff.rfl

namespace HasBoundedSublevelsOn

variable {X : Type*} [Bornology X] {E F : X → ℝ} {S T : Set X}

/-- Each relative sublevel of an energy with bounded sublevels is bounded. -/
theorem isBounded_sublevel (h : HasBoundedSublevelsOn E S) (b : ℝ) :
    IsBounded {x ∈ S | E x ≤ b} :=
  h b

/-- Bounded sublevels are inherited by smaller admissible sets. -/
theorem mono (h : HasBoundedSublevelsOn E S) (hTS : T ⊆ S) :
    HasBoundedSublevelsOn E T :=
  fun b ↦ (h b).subset fun _ hx ↦ ⟨hTS hx.1, hx.2⟩

/-- Increasing an energy preserves bounded sublevels. -/
theorem of_le (h : HasBoundedSublevelsOn E S) (hEF : ∀ x ∈ S, E x ≤ F x) :
    HasBoundedSublevelsOn F S :=
  fun b ↦ (h b).subset fun x hx ↦ ⟨hx.1, (hEF x hx.1).trans hx.2⟩

/-- Adding an energy bounded below preserves bounded sublevels. -/
theorem add_of_bddBelow (h : HasBoundedSublevelsOn E S) (hF : BddBelow (F '' S)) :
    HasBoundedSublevelsOn (fun x ↦ E x + F x) S := by
  obtain ⟨a, ha⟩ := hF
  intro b
  refine (h (b - a)).subset fun x hx ↦ ⟨hx.1, ?_⟩
  have := ha (mem_image_of_mem F hx.1)
  linarith [hx.2]

/-- Positive scaling preserves bounded sublevels. -/
theorem const_mul (h : HasBoundedSublevelsOn E S) {c : ℝ} (hc : 0 < c) :
    HasBoundedSublevelsOn (fun x ↦ c * E x) S := by
  intro b
  exact (h (b / c)).subset fun x hx ↦ ⟨hx.1, (le_div_iff₀ hc).2 (by
    simpa [mul_comm] using hx.2)⟩

/-- An admissible sequence with bounded-above energies has bounded range. -/
theorem isBounded_range (h : HasBoundedSublevelsOn E S) {u : ℕ → X}
    (hu : ∀ n, u n ∈ S) (hE : BddAbove (range (E ∘ u))) : IsBounded (range u) := by
  obtain ⟨b, hb⟩ := hE
  exact (h b).subset (range_subset_iff.2 fun n ↦ ⟨hu n, hb (mem_range_self n)⟩)

end HasBoundedSublevelsOn

section Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] {E : V → ℝ} {S : Set V}

/-- Bounded sublevels are equivalent to boundedness of every admissible sequence with
bounded-above energies. -/
theorem hasBoundedSublevelsOn_iff_seq : HasBoundedSublevelsOn E S ↔
    ∀ u : ℕ → V, (∀ n, u n ∈ S) → BddAbove (range (E ∘ u)) → IsBounded (range u) := by
  classical
  refine ⟨fun h _ hu hE ↦ h.isBounded_range hu hE, fun h b ↦ ?_⟩
  by_contra hb
  have hunbounded : ∀ R : ℝ, ∃ x, (x ∈ S ∧ E x ≤ b) ∧ R < ‖x‖ := by
    simpa only [isBounded_iff_forall_norm_le, not_exists, not_forall, not_le,
      exists_prop, mem_ofPred_eq] using hb
  choose u hu using fun n : ℕ ↦ hunbounded n
  have hbound : IsBounded (range u) := h u (fun n ↦ (hu n).1.1)
    ⟨b, by rintro _ ⟨n, rfl⟩; exact (hu n).1.2⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbound
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact (not_lt_of_ge (hR _ (mem_range_self n))) (hn.trans (hu n).2)

/-- A quantitative norm lower bound outside a ball gives bounded sublevels. -/
theorem hasBoundedSublevelsOn_of_norm_coercive
    (h : ∀ b : ℝ, ∃ R : ℝ, ∀ x ∈ S, R ≤ ‖x‖ → b < E x) :
    HasBoundedSublevelsOn E S := by
  intro b
  obtain ⟨R, hR⟩ := h b
  exact isBounded_iff_forall_norm_le.2 ⟨R, fun x hx ↦
    (lt_of_not_ge fun hnorm ↦ (hR x hx.1 hnorm).not_ge hx.2).le⟩

end Seminormed

end TauCeti
