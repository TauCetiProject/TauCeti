/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators

/-!
# Combinatorics of signed staircase partitions and layer counts

This file provides elementary combinatorial identities for signed staircase indexings used to
construct joint highest-weight minor products on `n × r` variable matrices:

* `TauCeti.sum_sigma_filter_eq_sum_mul_sum_Ioo`: counting layers of each label `η : ι` and
  size `p < N` that contain a given position `m η`.
* `TauCeti.sign_eq_of_ne_zero_of_lt`: if layers of opposite signs fit inside `N`
  (`N < i + j → k 1 i = 0 ∨ k (-1) j = 0`), then no position belongs to active layers of both
  signs when `-η` reverses the order.
* `TauCeti.exists_equiv_fin_eq_card_filter_lt`: for an injective `ℤ`-valued weight `l` on a
  finite signed set `r`, the rank of each element among those of the same sign in decreasing
  order of `s c * l c` defines a bijection onto `Fin (Fintype.card {c : r // s c = η})`.

## Provenance

Adapted from `New.sum_sigma_filter_eq_sum_mul_sum_Ioo`, `New.sign_eq_of_ne_zero_of_lt`, and
`New.exists_equiv_fin_eq_card_filter_lt` in `src/Lib/Weil/Lift.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), generalizing `sum_sigma_filter_eq_sum_mul_sum_Ioo`
from `ℤˣ` to an arbitrary finite index type `ι`.
-/

public section

open Finset Function

namespace TauCeti

/-- Counting layers in a staircase indexed by a finite type `ι`: for each `η : ι` and size
`p < N`, take `k η p` layers with positions `0, …, p - 1`. The layers for `η` containing
position `m η` are precisely those of size `p > m η`, so summing `w η` over all matching layers
yields `∑ η, w η * ∑ j ∈ Ioo (m η) N, (k η j : ℤ)`. -/
theorem sum_sigma_filter_eq_sum_mul_sum_Ioo {ι : Type*} [Fintype ι] (N : ℕ)
    (k : ι → ℕ → ℕ) (m : ι → ℕ) (w : ι → ℤ) :
    ∑ t : (Σ η : ι, Σ p : Fin N, Fin (k η p)),
        ∑ i : Fin t.snd.fst with m t.fst = i.val, w t.fst =
      ∑ η : ι, w η * ∑ j ∈ Ioo (m η) N, (k η j : ℤ) := by
  have h_card (a p : ℕ) : #{i : Fin p | a = i.val} = if a < p then 1 else 0 := by
    by_cases h : a < p
    · rw [ite_eq_left h, Finset.card_eq_one]
      exact ⟨⟨a, h⟩, Finset.ext fun i ↦ by simp [Fin.ext_iff, eq_comm]⟩
    · rw [ite_eq_right h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _; omega
  have h_Ioo (a : ℕ) : Ioo a N = map Fin.valEmbedding {j : Fin N | a < j.val} := by
    ext x
    simp only [mem_Ioo, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨⟨x, h2⟩, h1, rfl⟩, fun ⟨j, h1, h2⟩ ↦ h2 ▸ ⟨h1, j.isLt⟩⟩
  simp only [Fintype.sum_sigma, Finset.sum_const, nsmul_eq_mul, h_card, h_Ioo,
    Finset.sum_map, Fin.valEmbedding_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun η _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  split_ifs <;> simp [mul_comm]

/-- Layers of opposite signs share no position: if `x : ℤˣ → Fin N` reverses order under
negation (`x (-η) = (x η).rev`) and `k 1 i = 0 ∨ k (-1) j = 0` whenever `N < i + j`, then
`k η p ≠ 0`, `k μ q ≠ 0`, `x η < p`, and `x μ < q` force `η = μ`. -/
theorem sign_eq_of_ne_zero_of_lt {N : ℕ} {k : ℤˣ → ℕ → ℕ}
    (hk_fit : ∀ i j : ℕ, N < i + j → k 1 i = 0 ∨ k (-1) j = 0) {x : ℤˣ → Fin N}
    (hx : ∀ η : ℤˣ, x (-η) = (x η).rev) {η μ : ℤˣ} {p q : ℕ} (hp : k η p ≠ 0) (hq : k μ q ≠ 0)
    (hxp : x η < p) (hxq : x μ < q) : η = μ := by
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or μ with rfl | rfl
  · rfl
  · exfalso
    have hrev := hx 1
    have hlt : N < p + q := by
      have h2 : (x (-1)).val < q := hxq
      rw [hrev, Fin.val_rev] at h2
      omega
    rcases hk_fit p q hlt with h | h
    · exact hp h
    · exact hq h
  · exfalso
    have hrev := hx 1
    have hlt : N < q + p := by
      have h2 : (x (-1)).val < p := hxp
      rw [hrev, Fin.val_rev] at h2
      omega
    rcases hk_fit q p hlt with h | h
    · exact hq h
    · exact hp h
  · rfl

/-- For an injective `l : r → ℤ` on a finite type `r` with signs `s : r → ℤˣ`, counting the
elements of the same sign with strictly larger `s c * l c` defines a bijection from
`{c : r // s c = η}` onto `Fin (Fintype.card {c : r // s c = η})`. -/
theorem exists_equiv_fin_eq_card_filter_lt {r : Type*} [Fintype r]
    {s : r → ℤˣ} {l : r → ℤ} (hl : Injective l) {o : r → ℕ}
    (ho : ∀ c : r, o c = #{d : r | s d = s c ∧ (s c : ℤ) * l c < (s c : ℤ) * l d}) (η : ℤˣ) :
    ∃ f : {c : r // s c = η} ≃ Fin (Fintype.card {c : r // s c = η}),
      ∀ c : {c : r // s c = η}, (f c).val = o c := by
  classical
  let g : {c : r // s c = η} → ℤ := fun c ↦ -((η : ℤ) * l c.val)
  have hg : Injective g := fun a b h ↦ Subtype.ext <| hl <|
    mul_left_cancel₀ (Units.ne_zero η) (neg_inj.mp h)
  let e₀ := Fintype.equivFin {c : r // s c = η}
  let σ := Tuple.sort (g ∘ e₀.symm)
  let e : {c : r // s c = η} ≃ Fin (Fintype.card {c : r // s c = η}) := e₀.trans σ.symm
  refine ⟨e, fun c ↦ ?_⟩
  have hcard : (e c).val = #{d : {c : r // s c = η} | g d < g c} := by
    have hmono : StrictMono ((g ∘ e₀.symm) ∘ σ) :=
      (Tuple.monotone_sort _).strictMono_of_injective
        ((hg.comp e₀.symm.injective).comp σ.injective)
    have hlt_iff (d : {c : r // s c = η}) : g d < g c ↔ e d < e c := by
      have h1 : g d = ((g ∘ e₀.symm) ∘ σ) (e d) := by simp [e, Function.comp_apply]
      have h2 : g c = ((g ∘ e₀.symm) ∘ σ) (e c) := by simp [e, Function.comp_apply]
      rw [h1, h2, hmono.lt_iff_lt]
    rw [← Fin.card_Iio (e c)]
    refine (Finset.card_bij (fun d _ ↦ e d) (fun d hd ↦ ?_) (fun _ _ _ _ h ↦ e.injective h)
      (fun j hj ↦ ⟨e.symm j, ?_, by simp⟩)).symm
    · simp only [mem_filter, mem_univ, true_and, mem_Iio] at hd ⊢
      exact (hlt_iff d).mp hd
    · simp only [mem_filter, mem_univ, true_and, mem_Iio] at hj ⊢
      exact (hlt_iff (e.symm j)).mpr (by simpa using hj)
  rw [hcard, ho c.val]
  refine Finset.card_bij (fun d _ ↦ d.val) (fun d hd ↦ ?_) (fun _ _ _ _ h ↦ Subtype.ext h)
    (fun d hd ↦ ?_)
  · simp only [mem_filter, mem_univ, true_and, g, neg_lt_neg_iff] at hd ⊢
    exact ⟨d.property.trans c.property.symm, c.property.symm ▸ hd⟩
  · simp only [mem_filter, mem_univ, true_and] at hd
    have hc : s c.val = η := c.property
    rw [hc] at hd
    refine ⟨⟨d, hd.left⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and, g, neg_lt_neg_iff]
    exact hd.right

end TauCeti
