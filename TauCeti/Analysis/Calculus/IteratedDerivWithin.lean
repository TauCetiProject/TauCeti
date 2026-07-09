/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Generic lemmas for iterated derivatives within sets

This file records calculus lemmas about `iteratedDerivWithin` and interval integrals that are
independent of any completely-monotone or Bernstein-function structure.

## Main declarations

* `TauCeti.ContDiffOn.hasDerivAt_iteratedDerivWithin`: differentiability of an
  `iteratedDerivWithin` on a neighbourhood inside a unique-differentiability set.
* `TauCeti.ContDiffOn.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici`: transfer of the
  first-derivative interval integral from the `T`-dependent set `Icc x T` to the fixed
  half-line `Ici a`.
* `TauCeti.ContDiffOn.tendsto_integral_neg_iteratedDerivWithin_one_Icc_atTop`: convergence of
  the finite-interval primitive under convergence at infinity.

For the plain fundamental-theorem identity on a compact interval use Mathlib's
`intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc` together with
`iteratedDerivWithin_one`.
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}

/-- At a point `x` in the interior of a unique-differentiability set `s` (`s ∈ 𝓝 x`),
the derivative of the `k`-th iterated derivative-within-`s` of a `C^(k+1)` function is the
`(k+1)`-th iterated derivative-within-`s`. -/
theorem ContDiffOn.hasDerivAt_iteratedDerivWithin
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {g : 𝕜 → E} {s : Set 𝕜} {k : ℕ}
    (hf : ContDiffOn 𝕜 ((k + 1 : ℕ) : WithTop ℕ∞) g s)
    (hs : UniqueDiffOn 𝕜 s) {x : 𝕜} (hx : s ∈ nhds x) :
    HasDerivAt (iteratedDerivWithin k g s) (iteratedDerivWithin (k + 1) g s x) x := by
  rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx]
  exact (hf.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast Nat.lt_succ_self k) hs).hasDerivAt hx

private lemma ContDiffAt.iteratedDerivWithin_eq_of_mem_uniqueDiffOn {n : ℕ} {s u : Set ℝ}
    {t : ℝ} (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f t) (hs : UniqueDiffOn ℝ s)
    (hu : UniqueDiffOn ℝ u) (hts : t ∈ s) (htu : t ∈ u) :
    iteratedDerivWithin n f s t = iteratedDerivWithin n f u t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv hs hf hts,
    iteratedDerivWithin_eq_iteratedDeriv hu hf htu]

/-- The interval integral of `-f'` with the `T`-dependent set `Icc x T` equals the integral with
the fixed set `Ici a`, under local smoothness at the strict interior points. The derivative is
represented as `iteratedDerivWithin 1`. -/
lemma ContDiffOn.integral_neg_iteratedDerivWithin_one_Icc_eq_Ici
    {a x T : ℝ} (hf : ∀ t ∈ Ioo x T, ContDiffAt ℝ 1 f t) (hax : a ≤ x) (hxT : x ≤ T) :
    ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t =
    ∫ t in x..T, -iteratedDerivWithin 1 f (Ici a) t := by
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  rw [uIoo_of_le hxT] at ht
  exact congrArg Neg.neg
    (ContDiffAt.iteratedDerivWithin_eq_of_mem_uniqueDiffOn (hf t ht)
      (uniqueDiffOn_Icc (lt_trans ht.1 ht.2)) (uniqueDiffOn_Ici a)
      ⟨ht.1.le, ht.2.le⟩ (mem_Ici.mpr (le_trans hax ht.1.le)))

/-- The integral `∫ₐᵀ (-f') dt → f(a) - L` as `T → ∞`, assuming smoothness on
`[a, ∞)` and convergence of `f` to `L` at infinity. The derivative is represented as
`iteratedDerivWithin 1`. -/
lemma ContDiffOn.tendsto_integral_neg_iteratedDerivWithin_one_Icc_atTop
    [CompleteSpace E] {a : ℝ} (hf : ContDiffOn ℝ 1 f (Ici a)) {L : E}
    (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in a..T, -iteratedDerivWithin 1 f (Icc a T) t) atTop
        (nhds (f a - L)) := by
  refine Tendsto.congr' (EventuallyEq.symm ?_) (Tendsto.sub tendsto_const_nhds hL)
  filter_upwards [eventually_ge_atTop a] with T hT
  simpa [iteratedDerivWithin_one, intervalIntegral.integral_neg, neg_sub] using
    congrArg Neg.neg (intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
      (hf.mono Icc_subset_Ici_self) hT)

end TauCeti
