/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Sums over the parallel hyperplanes of a finite field

Let `F` be a finite field with `q` elements and `a : ι → F`. The level sets of the linear form
`u ↦ ∑ᵢ aᵢ uᵢ` on `F ^ ι` are `q` parallel hyperplanes. If `aⱼ ≠ 0`, translation of the `j`-th
coordinate permutes them transitively, so a function invariant under that translation has the same
sum over each of them, and its sum over all of `F ^ ι` is `q` times its sum over any one of them.

## Main results

* `TauCeti.card_smul_sum_filter_sum_mul_eq`: if `aⱼ ≠ 0` and `g` is invariant under translation of
  the `j`-th coordinate, then `q • ∑_{∑ᵢ aᵢ uᵢ = b} g(u) = ∑_u g(u)`.
* `TauCeti.sum_filter_sum_mul_eq_prod_eq_ite`: if every `aᵢ ≠ 0` and every `fᵢ` sums to `0`, then
  over `∑ᵢ aᵢ uᵢ = b` the product `∏_{i ∈ T} fᵢ(uᵢ)` over a proper subset `T` of the coordinates
  sums to `q ^ (r - 1)` when `T` is empty and to `0` otherwise.
-/

public section

open Finset

namespace TauCeti

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]

/-- If `aⱼ ≠ 0` and `g` is invariant under translation of the `j`-th coordinate, then summing `g`
over all tuples is summing it over the `q` parallel hyperplanes `∑ᵢ aᵢ uᵢ = c`, on each of which
it has the same sum. -/
theorem card_smul_sum_filter_sum_mul_eq {M : Type*} [AddCommMonoid M] {a : ι → F} {j : ι}
    (hj : a j ≠ 0) {g : (ι → F) → M} (hg : ∀ u c, g (u + Pi.single j c) = g u) (b : F) :
    Fintype.card F • ∑ u : ι → F with ∑ i, a i * u i = b, g u = ∑ u, g u := by
  have key : ∀ c, ∑ u : ι → F with ∑ i, a i * u i = c, g u =
      ∑ u : ι → F with ∑ i, a i * u i = b, g u := by
    intro c
    rw [sum_filter, sum_filter, ← Equiv.sum_comp (Equiv.addRight (Pi.single j ((c - b) / a j)))]
    refine sum_congr rfl fun u _ ↦ ?_
    have hsum : ∑ i, a i * (u i + Pi.single (M := fun _ ↦ F) j ((c - b) / a j) i) =
        ∑ i, a i * u i + (c - b) := by
      simp [mul_add, sum_add_distrib, Pi.single_apply, mul_div_cancel₀ _ hj]
    have hiff : ∑ i, a i * u i + (c - b) = c ↔ ∑ i, a i * u i = b := by
      constructor <;> intro h <;> linear_combination h
    simp only [Equiv.coe_addRight, Pi.add_apply, hsum, hg, hiff]
  rw [← sum_fiberwise univ (fun u : ι → F ↦ ∑ i, a i * u i) g]
  simp [key, card_univ]

/-- Over a hyperplane `∑ᵢ aᵢ uᵢ = b` with nonzero `aᵢ`, a product `∏_{i ∈ T} fᵢ(uᵢ)` over a proper
subset `T` of the coordinates, of functions with `∑_y fᵢ(y) = 0`, sums to `q ^ (r - 1)` when `T`
is empty and to `0` otherwise. -/
theorem sum_filter_sum_mul_eq_prod_eq_ite {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {f : ι → F → R} (hf : ∀ i, ∑ y, f i y = 0) {T : Finset ι}
    (hT : T ≠ univ) (b : F) :
    ∑ u : ι → F with ∑ i, a i * u i = b, ∏ i ∈ T, f i (u i) =
      if T = ∅ then (Fintype.card F : R) ^ (Fintype.card ι - 1) else 0 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ T := by simpa [eq_univ_iff_forall] using hT
  have hq : (Fintype.card F : R) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := card_smul_sum_filter_sum_mul_eq (ha j) (g := fun u ↦ ∏ i ∈ T, f i (u i))
    (fun u c ↦ prod_congr rfl fun i hi ↦ by
      rw [Pi.add_apply, Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj), add_zero]) b
  have hall : ∑ u : ι → F, ∏ i ∈ T, f i (u i) = ∏ i, ∑ y, if i ∈ T then f i y else 1 := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
    exact sum_congr rfl fun u _ ↦ by rw [prod_ite_mem, univ_inter]
  rw [nsmul_eq_mul, hall] at h
  split_ifs with hT0
  · have hι : Fintype.card ι = Fintype.card ι - 1 + 1 :=
      (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨j⟩)).symm
    refine mul_left_cancel₀ hq (h.trans ?_)
    simp [hT0, card_univ, ← pow_succ', ← hι]
  · obtain ⟨i, hi⟩ := ne_empty_iff_nonempty.mp hT0
    refine (mul_eq_zero.mp (h.trans (prod_eq_zero (mem_univ i) ?_))).resolve_left hq
    simpa [hi] using hf i

end TauCeti
