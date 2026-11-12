/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import TauCeti.Order.Filter.Extr

/-!
# Bounded sublevels of an energy

`HasBoundedSublevelsOn E S` is the boundedness condition used to obtain compactness in the
direct method: every sublevel of the real energy `E`, relative to the admissible set `S`,
is bounded. It is stable under restriction, increasing the energy, positive scaling, and
addition of an energy bounded below. In a pseudometric space it is equivalent to boundedness
of every admissible sequence whose energies are bounded above.
-/

public section

open Set Bornology Filter

namespace TauCeti

/-- Every sublevel of `E` relative to `S` is bounded. No lower bound on `E` is required. -/
def HasBoundedSublevelsOn {X : Type*} [Bornology X] (E : X → ℝ) (S : Set X) : Prop :=
  ∀ b : ℝ, IsBounded {x ∈ S | E x ≤ b}

/-- Characterization of bounded sublevels by the boundedness of each relative sublevel. -/
theorem hasBoundedSublevelsOn_iff {X : Type*} [Bornology X] {E : X → ℝ} {S : Set X} :
    HasBoundedSublevelsOn E S ↔ ∀ b : ℝ, IsBounded {x ∈ S | E x ≤ b} :=
  Iff.rfl

/-- Every energy has bounded sublevels on a bounded admissible set. -/
theorem _root_.Bornology.IsBounded.hasBoundedSublevelsOn {X : Type*} [Bornology X]
    {S : Set X} (hS : IsBounded S) (E : X → ℝ) : HasBoundedSublevelsOn E S :=
  fun _ ↦ hS.subset fun _ hx ↦ hx.1

/-- Bounded sublevels depend only on the energy on the admissible set. -/
theorem hasBoundedSublevelsOn_congr {X : Type*} [Bornology X]
    {E F : X → ℝ} {S : Set X} (h : EqOn E F S) :
    HasBoundedSublevelsOn E S ↔ HasBoundedSublevelsOn F S := by
  simp only [hasBoundedSublevelsOn_iff]
  have heq : ∀ b, {x ∈ S | E x ≤ b} = {x ∈ S | F x ≤ b} := fun b ↦
    Subset.antisymm (fun x hx ↦ ⟨hx.1, by simpa only [← h hx.1] using hx.2⟩)
      (fun x hx ↦ ⟨hx.1, by simpa only [h hx.1] using hx.2⟩)
  simp only [heq]

/-- Bounded sublevels express divergence to infinity along admissible points escaping
all bounded sets. -/
theorem hasBoundedSublevelsOn_iff_tendsto {X : Type*} [Bornology X]
    {E : X → ℝ} {S : Set X} :
    HasBoundedSublevelsOn E S ↔ Tendsto E (cobounded X ⊓ 𝓟 S) atTop := by
  rw [tendsto_atTop]
  constructor
  · intro h b
    rw [eventually_iff, mem_inf_principal]
    exact mem_of_superset (h b) fun x hx hS ↦ le_of_not_ge (fun hE ↦ hx ⟨hS, hE⟩)
  · intro h b
    have hb := h (b + 1)
    rw [eventually_iff, mem_inf_principal] at hb
    have hbound : IsBounded {x | ¬(x ∈ S → b + 1 ≤ E x)} := by
      simpa only [isBounded_def, compl_ofPred, not_not, mem_ofPred_eq] using hb
    exact hbound.subset fun x hx hle ↦
      (not_le_of_gt (lt_add_one b)) ((hle hx.1).trans hx.2)

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

/-- Bounded sublevels on two admissible sets give bounded sublevels on their union. -/
theorem union (hS : HasBoundedSublevelsOn E S) (hT : HasBoundedSublevelsOn E T) :
    HasBoundedSublevelsOn E (S ∪ T) := by
  intro b
  convert (hS b).union (hT b) using 1
  ext x
  simp only [mem_ofPred_eq, mem_union]
  tauto

/-- Adding a bounded-sublevel energy to a bounded-below energy preserves bounded sublevels. -/
theorem bddBelow_add (h : HasBoundedSublevelsOn E S) (hF : BddBelow (F '' S)) :
    HasBoundedSublevelsOn (fun x ↦ F x + E x) S := by
  simpa only [add_comm] using h.add_of_bddBelow hF

/-- Subtracting an energy bounded above preserves bounded sublevels. -/
theorem sub_of_bddAbove (h : HasBoundedSublevelsOn E S) (hF : BddAbove (F '' S)) :
    HasBoundedSublevelsOn (fun x ↦ E x - F x) S := by
  obtain ⟨a, ha⟩ := hF
  intro b
  refine (h (b + a)).subset fun x hx ↦ ⟨hx.1, ?_⟩
  have := ha (mem_image_of_mem F hx.1)
  linarith [hx.2]

/-- An admissible family with bounded-above energies has bounded range. -/
theorem isBounded_range (h : HasBoundedSublevelsOn E S) {ι : Sort*} {u : ι → X}
    (hu : ∀ n, u n ∈ S) (hE : BddAbove (range (E ∘ u))) : IsBounded (range u) := by
  obtain ⟨b, hb⟩ := hE
  exact (h b).subset (range_subset_iff.2 fun n ↦ ⟨hu n, hb (mem_range_self n)⟩)

/-- The minimizers of an energy with bounded sublevels form a bounded set. -/
theorem isBounded_minimizers (h : HasBoundedSublevelsOn E S) :
    IsBounded {x ∈ S | IsMinOn E S x} := by
  by_cases hne : S.Nonempty
  · obtain ⟨u, hu⟩ := hne
    exact (h (E u)).subset fun x hx ↦ ⟨hx.1, hx.2 hu⟩
  · simp [Set.not_nonempty_iff_eq_empty.1 hne]

end HasBoundedSublevelsOn

section NormalForms

variable {X : Type*} [Bornology X] {E : X → ℝ} {S T : Set X}

/-- The empty set has bounded sublevels for every energy. -/
@[simp] theorem hasBoundedSublevelsOn_empty : HasBoundedSublevelsOn E ∅ :=
  isBounded_empty.hasBoundedSublevelsOn E

/-- A singleton has bounded sublevels for every energy. -/
@[simp] theorem hasBoundedSublevelsOn_singleton (x : X) : HasBoundedSublevelsOn E {x} :=
  isBounded_singleton.hasBoundedSublevelsOn E

/-- Bounded sublevels on a union are equivalent to bounded sublevels on both sets. -/
@[simp] theorem hasBoundedSublevelsOn_union :
    HasBoundedSublevelsOn E (S ∪ T) ↔ HasBoundedSublevelsOn E S ∧ HasBoundedSublevelsOn E T :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- Inserting one admissible point does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_insert (x : X) :
    HasBoundedSublevelsOn E (insert x S) ↔ HasBoundedSublevelsOn E S := by
  rw [← singleton_union, hasBoundedSublevelsOn_union]
  simp

/-- A constant energy has bounded sublevels exactly on bounded sets. -/
@[simp] theorem hasBoundedSublevelsOn_const (c : ℝ) :
    HasBoundedSublevelsOn (fun _ : X ↦ c) S ↔ IsBounded S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.hasBoundedSublevelsOn _⟩
  simpa using h.isBounded_sublevel c

/-- Adding a constant does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_add_const (c : ℝ) :
    HasBoundedSublevelsOn (fun x ↦ E x + c) S ↔ HasBoundedSublevelsOn E S := by
  constructor
  · intro h b
    exact (h.isBounded_sublevel (b + c)).subset fun x hx ↦
      ⟨hx.1, by linarith [hx.2]⟩
  · intro h
    exact h.add_of_bddBelow ⟨c, by rintro _ ⟨x, _, rfl⟩; exact le_rfl⟩

/-- Adding a constant on the left does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_const_add (c : ℝ) :
    HasBoundedSublevelsOn (fun x ↦ c + E x) S ↔ HasBoundedSublevelsOn E S := by
  simpa only [add_comm] using hasBoundedSublevelsOn_add_const (E := E) (S := S) c

/-- Subtracting a constant does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_sub_const (c : ℝ) :
    HasBoundedSublevelsOn (fun x ↦ E x - c) S ↔ HasBoundedSublevelsOn E S := by
  simpa only [sub_eq_add_neg] using hasBoundedSublevelsOn_add_const (E := E) (S := S) (-c)

/-- Positive scaling does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_const_mul {c : ℝ} (hc : 0 < c) :
    HasBoundedSublevelsOn (fun x ↦ c * E x) S ↔ HasBoundedSublevelsOn E S := by
  refine ⟨fun h b ↦ ?_, fun h ↦ h.const_mul hc⟩
  exact (h.isBounded_sublevel (c * b)).subset fun x hx ↦
    ⟨hx.1, mul_le_mul_of_nonneg_left hx.2 hc.le⟩

/-- Positive right scaling does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_mul_const {c : ℝ} (hc : 0 < c) :
    HasBoundedSublevelsOn (fun x ↦ E x * c) S ↔ HasBoundedSublevelsOn E S := by
  simpa only [mul_comm] using hasBoundedSublevelsOn_const_mul (E := E) (S := S) hc

/-- Dividing by a positive constant does not affect bounded sublevels. -/
@[simp] theorem hasBoundedSublevelsOn_div_const {c : ℝ} (hc : 0 < c) :
    HasBoundedSublevelsOn (fun x ↦ E x / c) S ↔ HasBoundedSublevelsOn E S := by
  simpa only [div_eq_mul_inv] using
    hasBoundedSublevelsOn_mul_const (E := E) (S := S) (inv_pos.2 hc)

end NormalForms

section PseudoMetric

variable {V : Type*} [PseudoMetricSpace V] {E : V → ℝ} {S : Set V}

/-- Bounded sublevels are equivalent to boundedness of every admissible sequence with
bounded-above energies. -/
theorem hasBoundedSublevelsOn_iff_seq : HasBoundedSublevelsOn E S ↔
    ∀ u : ℕ → V, (∀ n, u n ∈ S) → BddAbove (range (E ∘ u)) → IsBounded (range u) := by
  classical
  refine ⟨fun h _ hu hE ↦ h.isBounded_range hu hE, fun h b ↦ ?_⟩
  by_contra hb
  obtain ⟨v, _⟩ := nonempty_of_not_isBounded hb
  have hunbounded : ∀ R : ℝ, ∃ x, (x ∈ S ∧ E x ≤ b) ∧ R < dist x v := by
    simpa only [Metric.isBounded_iff_subset_closedBall v, subset_def,
      Metric.mem_closedBall, not_exists, not_forall, not_le, exists_prop,
      mem_ofPred_eq] using hb
  choose u hu using fun n : ℕ ↦ hunbounded n
  have hbound : IsBounded (range u) := h u (fun n ↦ (hu n).1.1)
    ⟨b, by rintro _ ⟨n, rfl⟩; exact (hu n).1.2⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall v).1 hbound
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact (not_lt_of_ge (hR (mem_range_self n))) (hn.trans (hu n).2)

end PseudoMetric

section Seminormed

variable {V : Type*} [SeminormedAddGroup V] {E : V → ℝ} {S : Set V}

/-- Bounded sublevels are equivalent to a quantitative energy lower bound outside
sufficiently large norm balls. -/
theorem hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm :
    HasBoundedSublevelsOn E S ↔
      ∀ b : ℝ, ∃ R : ℝ, ∀ x ∈ S, R ≤ ‖x‖ → b ≤ E x := by
  constructor
  · intro h b
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (h.isBounded_sublevel b)
    refine ⟨R + 1, fun x hx hnorm ↦ le_of_not_ge fun hE ↦ ?_⟩
    have := hR x ⟨hx, hE⟩
    linarith
  · intro h b
    obtain ⟨R, hR⟩ := h (b + 1)
    exact isBounded_iff_forall_norm_le.2 ⟨R, fun x hx ↦
      (lt_of_not_ge fun hnorm ↦ (not_le_of_gt (lt_add_one b))
        ((hR x hx.1 hnorm).trans hx.2)).le⟩

/-- The norm has bounded sublevels on every admissible set. -/
theorem hasBoundedSublevelsOn_norm : HasBoundedSublevelsOn (fun x : V ↦ ‖x‖) S :=
  hasBoundedSublevelsOn_iff_forall_exists_le_of_le_norm.2 fun b ↦
    ⟨b, fun _ _ hx ↦ hx⟩

end Seminormed

end TauCeti
