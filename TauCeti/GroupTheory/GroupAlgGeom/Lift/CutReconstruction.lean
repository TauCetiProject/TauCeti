/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.Basic

/-!
# Stable windows in the cut-equation reconstruction

In the proof of the implicit function theorem for a regular orientable quadratic equation
(Kharlampovich–Myasnikov, §7.4, the proof of Theorem 9), a cut equation `Π_L` is transformed rank
by rank into a sequence `Π_L → Π_{L-1} → ⋯ → Π_1`. The complexity `Comp(Π_j)` of these cut equations
is monotone in `j` (Claim 5) and takes at most `κ(Π)` values (Claim 7), and the pigeonhole principle
then gives three consecutive blocks of `K` ranks on which it is constant (Claim 9): the sequence
*stabilizes* at `K (r + 2)`, and the pieces of the stabilized cut equations are then split and
reconstructed.

This file contains this pigeonhole step, for an arbitrary sequence `c : ℕ → α` with values in a
partial order. The source's alternative `Comp(Π_{K (r + 1)}) = 0` is not needed: a monotone sequence
with few values always has a stable window, provided the depth `L` is large compared with the number
of values. The depth cannot be fixed before the sequence: the identity of `ℕ`, which takes `L + 1`
values on `[0, L]`, is constant on no window `[K (r - 1), K (r + 2)]` with `K > 0`.

## Main results

* `TauCeti.GroupAlgGeom.Lift.exists_stable_window`: a monotone sequence with values in a finite set
  `s` is constant on a window `[K (r - 1), K (r + 2)]` with `r ≥ r₀` and `K (r + 2) ≤ L`, as soon as
  `K (r₀ + 3 |s|) ≤ L + K` (Claim 9).

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §7.4: Definition 42, Claims 5, 7 and 9.
-/

public section

namespace TauCeti.GroupAlgGeom.Lift

section Window

variable {α : Type*} [PartialOrder α] {c : ℕ → α} {K r₀ L : ℕ}

/-- **Stabilization** (Kharlampovich–Myasnikov, Claim 9). Let `c` be monotone on
`[K (r₀ - 1), L]`, with values in a finite set `s`. If `K (r₀ + 3 |s|) ≤ L + K`, then for some
`r ≥ r₀` with `K (r + 2) ≤ L` the sequence is constant on `[K (r - 1), K (r + 2)]` (three blocks
of `K` steps, or two when `r = 0`). The source's bound `K r₀ + 4 K |s| ≤ L` implies this one. -/
theorem exists_stable_window {s : Finset α} (hc : MonotoneOn c (Set.Icc (K * (r₀ - 1)) L))
    (hs : ∀ j ∈ Set.Icc (K * (r₀ - 1)) L, c j ∈ s) (hL : K * (r₀ + 3 * s.card) ≤ L + K) :
    ∃ r, r₀ ≤ r ∧ K * (r + 2) ≤ L ∧
      ∀ j ∈ Set.Icc (K * (r - 1)) (K * (r + 2)), c j = c (K * (r + 2)) := by
  -- The window of `r = r₀ + 3 t` is `[e t, e (t + 1)]`, where `e t = K (r₀ + 3 t - 1)`; the
  -- windows of `t < |s|` lie in `[e 0, e |s|]`.
  obtain ⟨e, he, he_mono⟩ : ∃ e : ℕ → ℕ, (∀ t, e t = K * (r₀ + 3 * t - 1)) ∧ Monotone e :=
    ⟨fun t => K * (r₀ + 3 * t - 1), fun _ => rfl, fun a b hab => Nat.mul_le_mul_left _ (by lia)⟩
  have hlast : e s.card ≤ L := by rw [he, Nat.mul_sub_one]; lia
  have hsub : Set.Icc (e 0) (e s.card) ⊆ Set.Icc (K * (r₀ - 1)) L :=
    Set.Icc_subset_Icc (by simp [he]) hlast
  have hD : ∀ t ≤ s.card, e t ∈ Set.Icc (K * (r₀ - 1)) L := fun t ht =>
    hsub ⟨he_mono t.zero_le, he_mono ht⟩
  -- By the pigeonhole principle two of the `|s| + 1` values `c (e t)`, `t ≤ |s|`, coincide.
  obtain ⟨x, hx, y, hy, hxy, hcxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (s.card + 1)) (f := c ∘ e) (by simp)
    (fun t ht => hs _ (hD t (Finset.mem_range_succ_iff.1 ht)))
  simp only [Finset.mem_range] at hx hy
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm hcxy.symm hy hx (by lia)
  -- Then `c` is constant on `[e x, e y]`, in particular on the window of `t = x`.
  have htop : K * (r₀ + 3 * x + 2) = e (x + 1) := by
    rw [he, show r₀ + 3 * (x + 1) - 1 = r₀ + 3 * x + 2 by lia]
  refine ⟨r₀ + 3 * x, by lia, htop ▸ (he_mono (by lia)).trans hlast, fun j hj => ?_⟩
  rw [htop, ← he] at hj
  rw [htop]
  have hjD : j ∈ Set.Icc (K * (r₀ - 1)) L :=
    hsub ⟨(he_mono x.zero_le).trans hj.1, hj.2.trans (he_mono (by lia))⟩
  refine le_antisymm (hc hjD (hD _ (by lia)) hj.2) ?_
  calc c (e (x + 1)) ≤ c (e y) := hc (hD _ (by lia)) (hD _ (by lia)) (he_mono (by lia))
    _ = c (e x) := hcxy.symm
    _ ≤ c j := hc (hD _ (by lia)) hjD hj.1

/-- The identity of `ℕ`, a monotone sequence with `L + 1` values on `[0, L]`, is constant on no
window `[K (r - 1), K (r + 2)]` with `K > 0`: in `exists_stable_window` the depth `L` has to grow
with the number of values, and cannot be fixed before the sequence. -/
example (hK : 0 < K) : ¬∃ r, r₀ ≤ r ∧ K * (r + 2) ≤ L ∧
    ∀ j ∈ Set.Icc (K * (r - 1)) (K * (r + 2)), j = K * (r + 2) := by
  rintro ⟨r, -, -, h⟩
  have := h (K * (r - 1)) ⟨le_rfl, Nat.mul_le_mul_left _ (by lia)⟩
  have h2 : K * (r - 1) < K * (r + 2) := Nat.mul_lt_mul_of_pos_left (by lia) hK
  lia

end Window

end TauCeti.GroupAlgGeom.Lift
