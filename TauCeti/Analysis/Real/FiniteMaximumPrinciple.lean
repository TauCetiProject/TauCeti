/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# A maximum principle for finite weighted sums

Let `r i : G → G` be arbitrary maps and let `c i` be nonnegative real weights whose sum is
strictly smaller than `l`. A real function `v` bounded above and satisfying
`l * v x ≤ ∑ i ∈ s, c i * v (r i x)` is nonpositive. The supremum need not be attained, and
no topology, group structure, or finiteness assumption on `G` is required.

The comparison form only requires the difference of a subsolution and a supersolution to be
bounded above. In particular, the supersolution itself can be unbounded. This permits comparing
a matrix coefficient with a sum of absolute values of zero terms. The inhomogeneous form gives
the uniform bound `b / (l - ∑ i ∈ s, c i)` for a subsolution with constant error `b`.

The maximum principle is the real-weight form of the statement named
`New.SiegelWeil.maximum_principle` in `src/Lib/Weil/Unramified/HeckeTransfer.lean` of grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
The proofs here use the least-upper-bound property of the real numbers.
-/

public section

open Finset Set

namespace TauCeti

variable {G ι : Type*} {s : Finset ι} {c : ι → ℝ} {l : ℝ} {r : ι → G → G}

/-- **Finite weighted maximum principle.** If the total nonnegative weight is less than `l`,
a bounded-above subsolution of `l * v ≤ ∑ i ∈ s, c i * v ∘ r i` is nonpositive. -/
theorem nonpos_of_mul_le_sum (hc : ∀ i ∈ s, 0 ≤ c i) (hl : ∑ i ∈ s, c i < l)
    {v : G → ℝ} (hv : BddAbove (range v))
    (hsub : ∀ x, l * v x ≤ ∑ i ∈ s, c i * v (r i x)) (x : G) : v x ≤ 0 := by
  have : Nonempty G := ⟨x⟩
  have hlpos : 0 < l := (sum_nonneg hc).trans_lt hl
  let M := sSup (range v)
  have hM (y : G) : v y ≤ M := le_csSup hv (mem_range_self y)
  have hbound (y : G) : v y ≤ (∑ i ∈ s, c i) * M / l := by
    apply (le_div_iff₀ hlpos).2
    calc v y * l = l * v y := mul_comm _ _
      _ ≤ ∑ i ∈ s, c i * v (r i y) := hsub y
      _ ≤ ∑ i ∈ s, c i * M := sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left (hM _) (hc i hi)
      _ = (∑ i ∈ s, c i) * M := (sum_mul ..).symm
  have hsup : M ≤ (∑ i ∈ s, c i) * M / l :=
    csSup_le (range_nonempty v) (by rintro _ ⟨y, rfl⟩; exact hbound y)
  have hmul := (le_div_iff₀ hlpos).1 hsup
  have hMnonpos : M ≤ 0 := by nlinarith
  exact (hM x).trans hMnonpos

/-- **Comparison for finite weighted sums.** A subsolution lies below a supersolution if their
difference is bounded above and the total nonnegative weight is strictly less than `l`.
Neither function needs to be bounded individually. -/
theorem le_of_mul_sub_sum_le (hc : ∀ i ∈ s, 0 ≤ c i) (hl : ∑ i ∈ s, c i < l)
    {v w : G → ℝ} (hvw : BddAbove (range (fun x ↦ v x - w x)))
    (hsub : ∀ x, l * v x - ∑ i ∈ s, c i * v (r i x) ≤
      l * w x - ∑ i ∈ s, c i * w (r i x)) (x : G) : v x ≤ w x := by
  have h := nonpos_of_mul_le_sum (r := r) hc hl hvw (fun y ↦ ?_) x
  · exact sub_nonpos.1 h
  · simp only [mul_sub, sum_sub_distrib]
    linarith [hsub y]

/-- **Uniform error bound.** A bounded-above function with
`l * v x ≤ ∑ i ∈ s, c i * v (r i x) + b` is at most `b / (l - ∑ i ∈ s, c i)`.
The error `b` may have either sign. -/
theorem le_div_sub_sum_of_mul_le_sum_add (hc : ∀ i ∈ s, 0 ≤ c i)
    (hl : ∑ i ∈ s, c i < l) {v : G → ℝ} (hv : BddAbove (range v)) {b : ℝ}
    (hsub : ∀ x, l * v x ≤ ∑ i ∈ s, c i * v (r i x) + b) (x : G) :
    v x ≤ b / (l - ∑ i ∈ s, c i) := by
  let B := b / (l - ∑ i ∈ s, c i)
  have hB : l * B - (∑ i ∈ s, c i) * B = b := by
    rw [← sub_mul, mul_div_cancel₀ _ (sub_pos.2 hl).ne']
  obtain ⟨C, hC⟩ := hv
  apply le_of_mul_sub_sum_le (r := r) hc hl (w := fun _ ↦ B)
    ⟨C - B, by rintro _ ⟨y, rfl⟩; exact sub_le_sub_right (hC (mem_range_self y)) B⟩
    (fun y ↦ ?_) x
  rw [← sum_mul, hB]
  linarith [hsub y]

end TauCeti
