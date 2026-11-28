/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.BumpFunction.LatticePartition

/-!
# Periodization in the second variable

For a map `h : X × ℝ → W`, the periodization `TauCeti.periodizeSnd h` is the sum
`(x, t) ↦ Σₖ h (x, t + k)` of the integer translates of `h` in the second variable
(`TauCeti.periodizeSnd_apply`). It has period one in `t` (`TauCeti.periodizeSnd_add_one`).

When `h` is supported in a band `X × (a, b)`, near every point only finitely many translates are
nonzero (`TauCeti.periodizeSnd_eq_sum`), so the periodization of a `C^n` map is `C^n`
(`TauCeti.contDiff_periodizeSnd`). For `h` supported in `X × (-1, 2)`, on `X × [0, 1]` only the
translates by `-1`, `0` and `1` contribute (`TauCeti.periodizeSnd_eq_of_mem_Icc`).

A `C^n` map which already has period one in the second variable over a set `s` of first
coordinates agrees on `s × ℝ` with a `C^n` map of period one everywhere
(`TauCeti.exists_contDiff_eqOn_prod_univ_of_periodic`): periodize its product with a cutoff whose
integer translates sum to one.

Periodizing by `fract` instead (`TauCeti.apply_fract_snd_eventuallyEq`) needs a map that is already
periodic near the seam; summing translates produces periodic maps from arbitrary ones supported in
a band, for instance from mollifications of sections of the strip.
-/

public section

noncomputable section

open Set

namespace TauCeti

variable {X W : Type*} [AddCommMonoid W] [TopologicalSpace W]

/-- The periodization `z ↦ Σₖ h(z.1, z.2 + k)` of a map on `X × ℝ` in the second variable. -/
def periodizeSnd (h : X × ℝ → W) (z : X × ℝ) : W :=
  ∑' k : ℤ, h (z.1, z.2 + k)

/-- The periodization is the sum of the integer translates in the second variable. -/
theorem periodizeSnd_apply (h : X × ℝ → W) (z : X × ℝ) :
    periodizeSnd h z = ∑' k : ℤ, h (z.1, z.2 + k) := by
  rw [periodizeSnd]

/-- The periodization has period one in the second variable. -/
theorem periodizeSnd_add_one (h : X × ℝ → W) (x : X) (t : ℝ) :
    periodizeSnd h (x, t + 1) = periodizeSnd h (x, t) := by
  have := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ ↦ h (x, t + k))
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one] at this
  rw [periodizeSnd, periodizeSnd, ← this]
  exact tsum_congr fun k ↦ by rw [add_assoc, add_comm (1 : ℝ)]

/-- Near a point with second coordinate `t₀`, the periodization of a map supported in the band
`X × (a, b)` is a sum over a fixed finite set of translates. -/
theorem periodizeSnd_eq_sum {h : X × ℝ → W} {a b : ℝ} (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo a b)
    {t₀ : ℝ} {z : X × ℝ} (hz : |z.2 - t₀| < 1) :
    periodizeSnd h z = ∑ k ∈ Finset.Ioo ⌊a - 1 - t₀⌋ ⌈b + 1 - t₀⌉, h (z.1, z.2 + k) := by
  refine tsum_eq_sum fun k hk ↦ ?_
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hh _ hne
  obtain ⟨hz₁, hz₂⟩ := abs_lt.1 hz
  have hfl := Int.floor_le (a - 1 - t₀)
  have hce := Int.le_ceil (b + 1 - t₀)
  refine hk (Finset.mem_Ioo.2 ⟨?_, ?_⟩)
  · exact_mod_cast (show ((⌊a - 1 - t₀⌋ : ℤ) : ℝ) < k by simp only at h₁; linarith)
  · exact_mod_cast (show (k : ℝ) < ⌈b + 1 - t₀⌉ by simp only at h₂; linarith)

/-- On `X × [0, 1]`, the periodization of a map supported in `X × (-1, 2)` only sees the map and
its two translates by `±1` in the second variable. -/
theorem periodizeSnd_eq_of_mem_Icc {h : X × ℝ → W}
    (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 2) {x : X} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    periodizeSnd h (x, t) = h (x, t + 1) + h (x, t) + h (x, t - 1) := by
  rw [periodizeSnd, tsum_eq_sum (s := {1, 0, -1}) fun k hk ↦ ?_]
  · simp [add_assoc, sub_eq_add_neg]
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hh _ hne
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rcases (by omega : k ≤ -2 ∨ 2 ≤ k) with hk' | hk'
  · have : (k : ℝ) ≤ -2 := by exact_mod_cast hk'
    simp only at h₁
    linarith [ht.2]
  · have : (2 : ℝ) ≤ k := by exact_mod_cast hk'
    simp only at h₂
    linarith [ht.1]

/-- The periodization of a `C^n` map supported in a band `E × (a, b)` is `C^n`. -/
theorem contDiff_periodizeSnd {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : WithTop ℕ∞} {h : E × ℝ → W} {a b : ℝ}
    (hc : ContDiff ℝ n h) (hh : ∀ z, h z ≠ 0 → z.2 ∈ Ioo a b) :
    ContDiff ℝ n (periodizeSnd h) := by
  refine contDiff_iff_contDiffAt.2 fun z₀ ↦ ?_
  have hev : periodizeSnd h =ᶠ[nhds z₀]
      fun z ↦ ∑ k ∈ Finset.Ioo ⌊a - 1 - z₀.2⌋ ⌈b + 1 - z₀.2⌉, h (z.1, z.2 + k) := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] at hz
    exact periodizeSnd_eq_sum hh ((le_max_right _ _).trans_lt hz)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun k _ ↦
    hc.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))).contDiffAt

/-- **Periodic extension.** A `C^n` map `h` with period one in the second variable over a set `s`
of first coordinates agrees on `s × ℝ` with a `C^n` map of period one in the second variable
everywhere. -/
theorem exists_contDiff_eqOn_prod_univ_of_periodic {E W : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ∞} {h : E × ℝ → W}
    (hc : ContDiff ℝ n h) {s : Set E} (hs : ∀ x ∈ s, Function.Periodic (fun t ↦ h (x, t)) 1) :
    ∃ g : E × ℝ → W, ContDiff ℝ n g ∧ EqOn g h (s ×ˢ univ) ∧
      ∀ x, Function.Periodic (fun t ↦ g (x, t)) 1 := by
  set k : E × ℝ → W := fun z ↦ latticeBump₁ z.2 • h z
  have hk : ∀ z, k z ≠ 0 → z.2 ∈ Ioo (-1 : ℝ) 1 := fun z hz ↦
    abs_lt.1 (abs_lt_one_of_latticeBump₁_ne_zero (left_ne_zero_of_smul hz))
  refine ⟨periodizeSnd k, contDiff_periodizeSnd ((contDiff_latticeBump₁.comp contDiff_snd).smul hc)
    hk, ?_, periodizeSnd_add_one k⟩
  rintro ⟨x, t⟩ ⟨hx, -⟩
  -- Over `x ∈ s` every translate `h (x, t + j)` is `h (x, t)`, and the bumps sum to one.
  have hsum : HasSum (fun j : ℤ ↦ latticeBump₁ (t + j)) 1 := by
    simpa [Function.comp_def] using (Equiv.neg ℤ).hasSum_iff.2 (hasSum_latticeBump₁_sub t)
  have hj (j : ℤ) : h (x, t + j) = h (x, t) := by simpa using (hs x hx).int_mul j t
  rw [periodizeSnd_apply]
  simp only [k, hj]
  rw [(hsum.smul_const (h (x, t))).tsum_eq, one_smul]

end TauCeti
