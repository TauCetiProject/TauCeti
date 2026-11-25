/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Certificate
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# Certified zero-counting rectangles for the completed Riemann zeta function

A `TauCeti.HasZerosInRects` certificate requires the certified function to have nonnegative divisor
throughout the outer rectangle and order `0` along its frontier. For the Riemann zeta function this
distinguishes the meromorphic completion `completedRiemannZeta` from the pole-cleared entire
completion `TauCeti.LFunctions.zetaEntireCompletion`:

* Because `completedRiemannZeta` has simple poles at `0` and `1`, no `HasZerosInRects` certificate
  for `completedRiemannZeta` on `Set.univ` can cover a rectangle containing `0` or `1`
  (`TauCeti.not_hasZerosInRects_completedRiemannZeta_of_mem`). Certificates for
  `completedRiemannZeta` across the critical strip must therefore stay strictly away from the real
  axis, while certificates reaching `Im s = 0` work with `zetaEntireCompletion`.
* Because `zetaEntireCompletion` is entire and vanishes nowhere on `ℝ`, every degenerate real
  rectangle `Complex.Rectangle (a : ℂ) (b : ℂ)` (`a b : ℝ`), and in particular `[0, 1]`, is
  certified zero-free with the empty subrectangle list
  (`TauCeti.hasZerosInRects_zetaEntireCompletion_ofReal`,
  `TauCeti.hasZerosInRects_zetaEntireCompletion_zero_one`).
-/

public section

open Complex Set TauCeti.LFunctions

namespace TauCeti

/-- Because `completedRiemannZeta` has poles of order `-1` at `0` and `1`, no `HasZerosInRects`
certificate for `completedRiemannZeta` on `univ` can cover a rectangle containing `0` or `1`. -/
theorem not_hasZerosInRects_completedRiemannZeta_of_mem {z w : ℂ}
    {Bs : List (ℂ × ℂ)} {ms : List ℕ}
    (hpole : (0 : ℂ) ∈ Rectangle z w ∨ (1 : ℂ) ∈ Rectangle z w) :
    ¬HasZerosInRects completedRiemannZeta univ z w Bs ms := by
  intro h
  rcases hpole with h0 | h1
  · have := h.divisor_nonneg 0 h0
    rw [divisor_completedRiemannZeta_zero] at this
    omega
  · have := h.divisor_nonneg 1 h1
    rw [divisor_completedRiemannZeta_one] at this
    omega

/-- **Unconditional zero-free certificate on any real segment.** Because `zetaEntireCompletion` is
entire and vanishes nowhere on `ℝ` (`zetaEntireCompletion_ofReal_ne_zero`), the empty rectangle list
certifies `zetaEntireCompletion` on `Rectangle (a : ℂ) (b : ℂ)` for all `a b : ℝ`. -/
theorem hasZerosInRects_zetaEntireCompletion_ofReal (a b : ℝ) :
    HasZerosInRects zetaEntireCompletion univ a b [] [] where
  meromorphicOn := fun z _ ↦ (differentiable_zetaEntireCompletion.analyticAt z).meromorphicAt
  rectangle_subset := subset_univ _
  divisor_nonneg s _ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z) s
  subset_rectangle := by simp
  pairwise_disjoint_interior := List.Pairwise.nil
  meromorphicOrderAt_frontier s hs := by
    have hsR : s ∈ Rectangle (a : ℂ) (b : ℂ) := (isClosed_rectangle _ _).frontier_subset hs
    have him : s.im = 0 := by simpa [Rectangle] using hsR.2
    have hs_real : s = (s.re : ℂ) := by apply Complex.ext <;> simp [him]
    have ha := differentiable_zetaEntireCompletion.analyticAt s
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (hs_real ▸ zetaEntireCompletion_ofReal_ne_zero s.re)]
    rfl
  meromorphicOrderAt_frontier_of_mem := by simp
  map_zeroCount := rfl
  zeroCount_eq_sum := by
    rw [List.sum_nil, zeroCount_def]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun s hs ↦ ?_
    have him : s.im = 0 := by simpa [Rectangle] using hs.2
    have hs_real : s = (s.re : ℂ) := by apply Complex.ext <;> simp [him]
    have ha := differentiable_zetaEntireCompletion.analyticAt s
    have hmer : MeromorphicOn zetaEntireCompletion univ :=
      fun z _ ↦ (differentiable_zetaEntireCompletion.analyticAt z).meromorphicAt
    rw [hmer.divisor_apply (mem_univ s), ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (hs_real ▸ zetaEntireCompletion_ofReal_ne_zero s.re)]
    rfl

/-- **Unconditional zero-free certificate on `[0, 1]`.** -/
theorem hasZerosInRects_zetaEntireCompletion_zero_one :
    HasZerosInRects zetaEntireCompletion univ 0 1 [] [] := by
  simpa using hasZerosInRects_zetaEntireCompletion_ofReal 0 1

end TauCeti
