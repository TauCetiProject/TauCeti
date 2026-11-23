/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Basic.Finite.Sigma

/-!
# Convergence along the cofinite filter

If a function tending to `atTop` along the cofinite filter takes all its values strictly above `b`,
then they are bounded below by a single `c > b` (`Filter.Tendsto.exists_gt_forall_le`); for
instance, positive periods tending to infinity are bounded below by a positive constant. This
complements Mathlib's `Filter.Tendsto.exists_forall_le`, which needs a nonempty domain. That such a
function takes only finitely many values below each bound is Mathlib's Northcott property
(`northcott_iff_tendsto`, `Northcott.finite_le`).

In an order with finite lower sets `Iic a` and a truncated subtraction, subtracting a constant has
finite fibres, so it maps the cofinite filter into itself (`Filter.tendsto_tsub_const_cofinite`);
for instance, shifting the multi-indices `n : σ →₀ ℕ` down by a fixed `d`.

Extending a function along any map by a constant preserves convergence along the cofinite filter
to a limit that the constant lies in (`Filter.Tendsto.extend_cofinite`); for instance, the extension
by zero of a function vanishing at infinity on a subgroup vanishes at infinity on the whole group.

On a sigma type with finitely many components, convergence along the cofinite filter can be checked
on each component (`Filter.tendsto_cofinite_sigma_iff`); for instance, the row norms of an operator
into a finite sum of coefficient models tend to zero when they do on each summand.
-/

public section

open Filter

/-- In an order whose lower sets `Iic a` are finite, subtracting a constant `d` has finite fibres
(`n - d = m` forces `n ≤ m + d`), so it maps the cofinite filter into itself. -/
theorem Filter.tendsto_tsub_const_cofinite {α : Type*} [Preorder α] [Add α] [Sub α]
    [OrderedSub α] [LocallyFiniteOrderBot α] (d : α) : Tendsto (· - d) cofinite cofinite :=
  Tendsto.cofinite_of_finite_preimage_singleton fun m ↦
    ((Set.finite_Iic (m + d)).subset fun _ hn ↦ tsub_le_iff_right.1 (le_of_eq hn)).to_subtype

namespace Filter.Tendsto

variable {α β : Type*} {f : α → β}

/-- If a function tending to `atTop` along the cofinite filter takes all its values above `b`, it
is bounded below by some `c > b`. -/
theorem exists_gt_forall_le [LinearOrder β] [NoMaxOrder β] (hf : Tendsto f cofinite atTop)
    {b : β} (hb : ∀ a, b < f a) : ∃ c, b < c ∧ ∀ a, c ≤ f a := by
  cases isEmpty_or_nonempty α
  · obtain ⟨c, hc⟩ := exists_gt b
    exact ⟨c, hc, isEmptyElim⟩
  · obtain ⟨a₀, ha₀⟩ := hf.exists_forall_le
    exact ⟨f a₀, hb a₀, ha₀⟩

/-- Extending `φ : α → γ` along any map `f : α → β` by a constant `e` preserves convergence along
the cofinite filter to any filter `l` with `pure e ≤ l`. -/
theorem extend_cofinite {γ : Type*} {l : Filter γ} {φ : α → γ} (hφ : Tendsto φ cofinite l)
    (f : α → β) {e : γ} (he : pure e ≤ l) :
    Tendsto (Function.extend f φ fun _ ↦ e) cofinite l := by
  classical
  intro s hs
  rw [mem_map, mem_cofinite]
  refine ((mem_cofinite.mp (hφ hs)).image f).subset fun b hb ↦ ?_
  rw [Set.mem_compl_iff, Set.mem_preimage, Function.extend_def] at hb
  by_cases h : ∃ a, f a = b
  · rw [dite_eq_left h] at hb
    exact ⟨h.choose, hb, h.choose_spec⟩
  · rw [dite_eq_right h] at hb
    exact absurd (he hs) hb

end Filter.Tendsto

namespace Filter

/-- Over finitely many components, a function on a sigma type tends to `l` along the cofinite
filter exactly when its restriction to each component does. -/
theorem tendsto_cofinite_sigma_iff {ι β : Type*} [Finite ι] {α : ι → Type*}
    {f : (Σ i, α i) → β} {l : Filter β} :
    Tendsto f cofinite l ↔ ∀ i, Tendsto (fun a ↦ f ⟨i, a⟩) cofinite l := by
  refine ⟨fun hf i ↦ hf.comp sigma_mk_injective.tendsto_cofinite, fun hf s hs ↦ ?_⟩
  rw [mem_map, mem_cofinite]
  exact (Set.finite_univ.sigma fun i _ ↦ mem_cofinite.mp (hf i hs)).subset
    fun _ hx ↦ ⟨Set.mem_univ _, hx⟩

end Filter
