/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Order statistics of finite tuples

The `k`-th order statistic of a tuple `x : Fin n → α` in a linear order is the entry in
position `k` once the entries of `x` are sorted increasingly, keeping repeated values with their
multiplicity. Positions are counted from `0`, so position `0` holds the minimum and position
`Fin.last _` the maximum. The sort is `Tuple.sort`, and the order statistics of `x` are the
entries of the sorted tuple `x ∘ Tuple.sort x`.

The order statistics are characterized by counting: `orderStatistic k x ≤ t` exactly
when more than `k` entries of `x` are at most `t`. They commute with monotone maps and are
measurable whenever the binary minimum and maximum operations are measurable.

## Main definitions

* `TauCeti.orderStatistic` — the `k`-th order statistic of a finite tuple.

## Main results

* `TauCeti.orderStatistic_comp_of_monotoneOn`, `TauCeti.orderStatistic_comp_of_monotone` — order
  statistics commute with maps that are monotone on the entries of the tuple;
* `TauCeti.orderStatistic_le_iff`, `TauCeti.orderStatistic_lt_iff` — the counting
  characterizations;
* `TauCeti.orderStatistic_zero`, `TauCeti.orderStatistic_last` — the extreme order statistics
  are the minimum and the maximum;
* `TauCeti.measurable_orderStatistic` — measurability.
-/

public section

noncomputable section

open MeasureTheory Set Finset

namespace TauCeti

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- The `k`-th **order statistic** of a tuple `x : Fin n → α`: the entry in position `k` once the
entries of `x` are sorted increasingly, repeated values kept with their multiplicity. Positions
are counted from `0`, so `orderStatistic 0 x` is the least entry of `x` and
`orderStatistic (Fin.last _) x` the greatest. -/
def orderStatistic (k : Fin n) (x : Fin n → α) : α :=
  x (Tuple.sort x k)

theorem orderStatistic_def (k : Fin n) (x : Fin n → α) :
    orderStatistic k x = x (Tuple.sort x k) := (rfl)

/-- Applying a map that is monotone on every entry of a tuple commutes with taking an order
statistic. No behavior is required away from those entries. -/
theorem orderStatistic_comp_of_monotoneOn {β : Type*} [LinearOrder β] {s : Set α} (f : α → β)
    (hf : MonotoneOn f s) (hx : ∀ i, x i ∈ s) (k : Fin n) :
    orderStatistic k (f ∘ x) = f (orderStatistic k x) := by
  rw [orderStatistic_def, orderStatistic_def]
  have hmono : Monotone (f ∘ x ∘ Tuple.sort x) := by
    intro i j hij
    exact hf (hx _) (hx _) (Tuple.monotone_sort x hij)
  exact congrFun (Tuple.unique_monotone (Tuple.monotone_sort (f ∘ x))
    hmono) k

/-- Applying a monotone map to every entry commutes with taking an order statistic. -/
theorem orderStatistic_comp_of_monotone {β : Type*} [LinearOrder β] (f : α → β)
    (hf : Monotone f) (k : Fin n) (x : Fin n → α) :
    orderStatistic k (f ∘ x) = f (orderStatistic k x) :=
  orderStatistic_comp_of_monotoneOn f (hf.monotoneOn (s := Set.univ))
    (fun _ ↦ Set.mem_univ _) k

/-- The order statistics of a tuple do not depend on the order in which its entries are
listed. -/
@[simp]
theorem orderStatistic_comp_perm (k : Fin n) (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    orderStatistic k (x ∘ σ) = orderStatistic k x := by
  simpa only [orderStatistic_def, Function.comp_apply] using
    congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := x) (σ := σ)) k

/-- **The counting characterization of order statistics.** The `k`-th order statistic of `x` is
at most `t` exactly when more than `k` entries of `x` are at most `t`. -/
@[simp]
theorem orderStatistic_le_iff (k : Fin n) (x : Fin n → α) (t : α) :
    orderStatistic k x ≤ t ↔ (k : ℕ) < #{i | x i ≤ t} := by
  have hcard : #{i | x (Tuple.sort x i) ≤ t} = #{i | x i ≤ t} :=
    Finset.card_equiv (Tuple.sort x) (by simp)
  rw [← hcard]
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort x)).symm

/-- The strict form of `TauCeti.orderStatistic_le_iff`: the `k`-th order statistic of `x` is
below `t` exactly when more than `k` entries of `x` are below `t`. -/
@[simp]
theorem orderStatistic_lt_iff (k : Fin n) (x : Fin n → α) (t : α) :
    orderStatistic k x < t ↔ (k : ℕ) < #{i | x i < t} := by
  have hcard : #{i | x (Tuple.sort x i) < t} = #{i | x i < t} :=
    Finset.card_equiv (Tuple.sort x) (by simp)
  rw [← hcard]
  exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone (Tuple.monotone_sort x)).symm

/-- The least order statistic is the minimum of the entries. -/
@[simp]
theorem orderStatistic_zero (x : Fin (n + 1) → α) :
    orderStatistic 0 x = Finset.univ.inf' Finset.univ_nonempty x := by
  refine eq_of_forall_ge_iff fun t => ?_
  simp [Finset.card_pos, Finset.filter_nonempty_iff]

/-- The greatest order statistic is the maximum of the entries. -/
@[simp]
theorem orderStatistic_last (x : Fin (n + 1) → α) :
    orderStatistic (Fin.last n) x = Finset.univ.sup' Finset.univ_nonempty x := by
  refine eq_of_forall_ge_iff fun t => ?_
  have hcard : n < #{i | x i ≤ t} ↔ ({i | x i ≤ t} : Finset _) = Finset.univ := by
    have := Finset.card_le_univ (Finset.univ.filter fun i => x i ≤ t)
    rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin] at *
    omega
  simp [hcard, Finset.filter_eq_self]

/-- The sublevel sets of an order statistic, by the counting characterization
`TauCeti.orderStatistic_le_iff`. -/
theorem preimage_orderStatistic_Iic (k : Fin n) (t : α) :
    orderStatistic k ⁻¹' Iic t = {x | (k : ℕ) < #{i | x i ≤ t}} := by
  ext x
  simp

variable [MeasurableSpace α] [MeasurableInf₂ α] [MeasurableSup₂ α]

/-- Each order statistic is a measurable function of the tuple. -/
@[fun_prop]
theorem measurable_orderStatistic (k : Fin n) :
    Measurable (orderStatistic k : (Fin n → α) → α) := by
  let p := (Finset.univ : Finset (Fin n)).powersetCard ((k : ℕ) + 1)
  have hp : p.Nonempty := Finset.powersetCard_nonempty.mpr (by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega)
  have hpa : p.attach.Nonempty := by simpa using hp
  have hs : ∀ s : p, s.1.Nonempty := fun s => Finset.card_pos.mp (by
    rw [(Finset.mem_powersetCard.mp s.2).2]
    omega)
  have hrepr : (orderStatistic k : (Fin n → α) → α) =
      p.attach.inf' hpa fun s =>
        s.1.sup' (hs s) fun i (x : Fin n → α) => x i := by
    funext x
    simp only [Finset.inf'_apply, Finset.sup'_apply]
    refine eq_of_forall_ge_iff fun t => ?_
    rw [orderStatistic_le_iff, Nat.lt_iff_add_one_le]
    simp only [Finset.inf'_le_iff, Finset.sup'_le_iff]
    constructor
    · intro h
      obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq h
      have hsp : s ∈ p := Finset.mem_powersetCard.mpr ⟨by simp, hcard⟩
      refine ⟨⟨s, hsp⟩, by simp, fun i hi => ?_⟩
      exact (Finset.mem_filter.mp (hsub hi)).2
    · rintro ⟨s, -, hsle⟩
      rw [← (Finset.mem_powersetCard.mp s.2).2]
      exact Finset.card_le_card fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsle i hi⟩
  rw [hrepr]
  refine Finset.inf'_induction hpa
    (fun s => s.1.sup' (hs s) fun i (x : Fin n → α) => x i)
    (p := fun f => Measurable f) (fun (_ : (Fin n → α) → α) hf _ hg => hf.inf hg) ?_
  intro s _
  exact Finset.measurable_sup' (hs s) fun i _ =>
    measurable_pi_apply (X := fun _ : Fin n => α) i

end TauCeti
