/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Real boundary values of compensated Dirichlet series

A Dirichlet series with real coefficients still has real boundary values after subtracting a
real counterterm. This works even if the two terms do not separately have finite limits, as
when the counterterm is the principal part at a real pole. The proof uses `LSeries_star` and
uniqueness of the right-hand limit.
-/

public section

open Complex Filter
open scoped ComplexConjugate Topology

/-- A right-hand limit of a real-coefficient Dirichlet series on the real axis, after subtracting
an arbitrary real counterterm, is real. -/
theorem Filter.Tendsto.im_eq_zero_of_LSeries_sub_ofReal {a : ℕ → ℝ} {C : ℝ → ℝ} {b : ℝ} {z : ℂ}
    (h : Tendsto (fun x : ℝ ↦ _root_.LSeries (fun n ↦ (a n : ℂ)) x - (C x : ℂ))
      (𝓝[>] b) (𝓝 z)) : z.im = 0 := by
  have hreal (x : ℝ) : conj (_root_.LSeries (fun n ↦ (a n : ℂ)) x) =
      _root_.LSeries (fun n ↦ (a n : ℂ)) x := by
    simpa only [Pi.star_def, Complex.star_def, conj_ofReal] using
      (TauCeti.LSeries.LSeries_star (fun n ↦ (a n : ℂ)) (x : ℂ)).symm
  apply Complex.conj_eq_iff_im.mp
  refine tendsto_nhds_unique_of_forall (continuous_conj.continuousAt.tendsto.comp h) h ?_
  intro x
  simp only [Function.comp_apply, map_sub, hreal, conj_ofReal]

/-- A continuous extension at a real point is real there if it agrees to the right on the real
axis with a real-coefficient Dirichlet series less a real counterterm. -/
theorem ContinuousAt.im_eq_zero_of_eventuallyEq_LSeries_sub_ofReal
    {a : ℕ → ℝ} {C : ℝ → ℝ} {b : ℝ} {G : ℂ → ℂ} (hG : ContinuousAt G (b : ℂ))
    (h : ∀ᶠ x : ℝ in 𝓝[>] b, G x = _root_.LSeries (fun n ↦ (a n : ℂ)) x - (C x : ℂ)) :
    (G b).im = 0 := by
  have hlim := ((hG.comp continuous_ofReal.continuousAt).mono_left nhdsWithin_le_nhds).congr' h
  exact hlim.im_eq_zero_of_LSeries_sub_ofReal
