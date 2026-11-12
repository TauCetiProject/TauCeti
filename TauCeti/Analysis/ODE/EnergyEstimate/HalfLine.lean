/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Square integrability of linear solutions near an end

Let `A(s)` be a family of bounded operators on a real inner product space `E` converging, as
`s → +∞`, to a symmetric operator `B` with `α ‖v‖ ≤ ‖B v‖` for some `α > 0`. Along a solution of
`w' = -A(s) w`, the quadratic form `V(s) = ⟪w s, B (w s)⟫` is a Lyapunov function at the end: once
`‖A(s) - B‖ ≤ α / 2`, it satisfies `V' ≤ -α² ‖w‖²`, so

`V(s) + α² ∫ₜˢ ‖w‖² ≤ V(T)` for `T ≤ s` (`TauCeti.inner_apply_add_integral_le`).

This splits the solutions by the sign of `V` near the end.

* If `V` is eventually nonnegative, then `∫ₜ^∞ ‖w‖² ≤ V(T) / α²`, so `w` is square integrable
  on every half-line `[a, ∞)` (`TauCeti.memLp_restrict_Ici_of_eventually_inner_nonneg`).
* If `V(T) < 0` at a late enough time `T`, then `V` stays below `V(T)`, so `‖w‖²` stays above
  `-V(T) / ‖B‖`, and `w` is not square integrable on any half-line `[a, ∞)`
  (`TauCeti.eventually_not_memLp_restrict_Ici_of_inner_neg`).

For a symmetric invertible `B` on a finite-dimensional space, `V` is positive definite on the
positive spectral subspace of `B` and negative definite on the negative one, so these are the
two halves of the exponential dichotomy of `w' = -A(s) w` at `+∞`, read off from a single
quadratic form without a fundamental solution. Reflecting time gives the same statements at
`-∞` with the signs of `V` exchanged (`TauCeti.memLp_restrict_Iic_of_eventually_inner_nonpos`,
`TauCeti.eventually_not_memLp_restrict_Iic_of_inner_pos`). They identify the solutions of the
linearized gradient equation along a trajectory that decay at one end, and hence the tangent
spaces of stable and unstable manifolds, with spaces of half-line square-integrable solutions.

## References

* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, §2.2 (asymptotic analysis of the linearized
  trajectory equation).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §3.
-/

public section

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : ℝ → E →L[ℝ] E} {B : E →L[ℝ] E} {w : ℝ → E} {α T : ℝ}

/-- The pointwise decay of the Lyapunov function: if `‖C - B‖ ≤ α / 2` and `α ‖v‖ ≤ ‖B v‖`, then
`2 ⟪-C u, B u⟫ + α² ‖u‖² ≤ 0`. -/
private theorem two_mul_inner_neg_apply_add_le (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖) {C : E →L[ℝ] E}
    (hCB : ‖C - B‖ ≤ α / 2) (u : E) :
    2 * ⟪-C u, B u⟫ + α ^ 2 * ‖u‖ ^ 2 ≤ 0 := by
  have h₁ : ⟪-C u, B u⟫ = -‖B u‖ ^ 2 - ⟪(C - B) u, B u⟫ := by
    rw [sub_apply, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq]
    ring
  have h₂ : -⟪(C - B) u, B u⟫ ≤ ‖(C - B) u‖ * ‖B u‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have h₃ : ‖(C - B) u‖ ≤ α / 2 * ‖u‖ :=
    ((C - B).le_opNorm u).trans (mul_le_mul_of_nonneg_right hCB (norm_nonneg u))
  have h₄ := hBα u
  have hα : 0 ≤ α := by linarith [norm_nonneg (C - B)]
  have h₅ : ‖(C - B) u‖ * ‖B u‖ ≤ α / 2 * ‖u‖ * ‖B u‖ :=
    mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)
  have h₆ : α * ‖u‖ * ‖B u‖ ≤ ‖B u‖ * ‖B u‖ := mul_le_mul_of_nonneg_right h₄ (norm_nonneg _)
  have h₇ : (α * ‖u‖) ^ 2 ≤ ‖B u‖ ^ 2 := pow_le_pow_left₀ (by positivity) h₄ 2
  rw [h₁]
  nlinarith

/-- **The Lyapunov inequality near the end.** Let `B` be symmetric with `α ‖v‖ ≤ ‖B v‖`. If
`‖A(s) - B‖ ≤ α / 2` for `s ≥ T`, then along a solution of `w' = -A(s) w`,
`⟪w s, B (w s)⟫ + α² ∫ₜˢ ‖w‖² ≤ ⟪w T, B (w T)⟫` for `s ≥ T`. -/
theorem inner_apply_add_integral_le (hBsym : (B : E →ₗ[ℝ] E).IsSymmetric)
    (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖) (hAB : ∀ s, T ≤ s → ‖A s - B‖ ≤ α / 2)
    (hw : ∀ s, HasDerivAt w (-A s (w s)) s) {s : ℝ} (hs : T ≤ s) :
    ⟪w s, B (w s)⟫ + α ^ 2 * ∫ τ in T..s, ‖w τ‖ ^ 2 ≤ ⟪w T, B (w T)⟫ := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  set G : ℝ → ℝ := fun s ↦ ⟪w s, B (w s)⟫ + α ^ 2 * ∫ τ in T..s, ‖w τ‖ ^ 2 with hGdef
  have hG (s : ℝ) : HasDerivAt G
      (⟪w s, B (-A s (w s))⟫ + ⟪-A s (w s), B (w s)⟫ + α ^ 2 * ‖w s‖ ^ 2) s := by
    have hB : HasDerivAt (fun s ↦ B (w s)) (B (-A s (w s))) s :=
      B.hasFDerivAt.comp_hasDerivAt s (hw s)
    have hint := ((hwc.norm.pow 2).integral_hasStrictDerivAt T s).hasDerivAt
    convert ((hw s).inner ℝ hB).add (hint.const_mul (α ^ 2)) using 1
  have hanti : AntitoneOn G (Ici T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici T)
      (fun s _ ↦ (hG s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hG s).differentiableAt.differentiableWithinAt) fun s hs ↦ ?_
    rw [interior_Ici] at hs
    rw [(hG s).deriv]
    -- `B` is symmetric, so the two terms of the derivative of `⟪w, B w⟫` agree.
    have hsym : ⟪w s, B (-A s (w s))⟫ = ⟪-A s (w s), B (w s)⟫ := by
      rw [real_inner_comm]
      exact hBsym _ _
    have := two_mul_inner_neg_apply_add_le hBα (hAB s (le_of_lt hs)) (w s)
    linarith
  simpa [hGdef] using hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs

/-- **Solutions with an eventually nonnegative Lyapunov function are square integrable at
`+∞`.** Let `A(s) → B` as `s → +∞`, with `B` symmetric and `α ‖v‖ ≤ ‖B v‖` for some `α > 0`. If
a solution of `w' = -A(s) w` has `⟪w s, B (w s)⟫ ≥ 0` for all large `s`, then `w` is square
integrable on every half-line `[a, ∞)`. -/
theorem memLp_restrict_Ici_of_eventually_inner_nonneg (hA : Tendsto A atTop (𝓝 B))
    (hBsym : (B : E →ₗ[ℝ] E).IsSymmetric) (hα : 0 < α) (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖)
    (hw : ∀ s, HasDerivAt w (-A s (w s)) s) (hV : ∀ᶠ s in atTop, 0 ≤ ⟪w s, B (w s)⟫) (a : ℝ) :
    MemLp w 2 (volume.restrict (Ici a)) := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((eventually_forall_ge_atTop.2
    ((tendsto_iff_norm_sub_tendsto_zero.1 hA).eventually (eventually_le_nhds (half_pos hα)))).and
    (eventually_forall_ge_atTop.2 hV))
  obtain ⟨hAB, hVT⟩ := hT T le_rfl
  have hsq : Continuous fun s ↦ ‖w s‖ ^ 2 := hwc.norm.pow 2
  -- On `(T, ∞)` the integrals of `‖w‖²` are bounded by `V(T) / α²`.
  have hIoi : IntegrableOn (fun s ↦ ‖w s‖ ^ 2) (Ioi T) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (⟪w T, B (w T)⟫ / α ^ 2) T
      (fun i ↦ hsq.integrableOn_Ioc) tendsto_id ?_
    filter_upwards [eventually_ge_atTop T] with i hi
    have hle := inner_apply_add_integral_le hBsym hBα hAB hw hi
    have hnorm : (∫ x in T..i, ‖‖w x‖ ^ 2‖) = ∫ x in T..i, ‖w x‖ ^ 2 := by simp
    rw [id, hnorm, le_div_iff₀ (by positivity)]
    nlinarith [hVT i hi]
  have hIci : IntegrableOn (fun s ↦ ‖w s‖ ^ 2) (Ici a) :=
    (hsq.integrableOn_Icc.union hIoi).mono_set fun s hs ↦ by
      rcases le_or_gt s T with h | h
      exacts [Or.inl ⟨hs, h⟩, Or.inr h]
  exact (memLp_two_iff_integrable_sq_norm hwc.aestronglyMeasurable).2 hIci

/-- **Solutions with a negative Lyapunov function at a late time are not square integrable at
`+∞`.** Let `A(s) → B` as `s → +∞`, with `B` symmetric and `α ‖v‖ ≤ ‖B v‖` for some `α > 0`. For
all large `T`, every solution of `w' = -A(s) w` with `⟪w T, B (w T)⟫ < 0` fails to be square
integrable on every half-line `[a, ∞)`: its norm stays bounded below after time `T`. -/
theorem eventually_not_memLp_restrict_Ici_of_inner_neg (hA : Tendsto A atTop (𝓝 B))
    (hBsym : (B : E →ₗ[ℝ] E).IsSymmetric) (hα : 0 < α) (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖) (a : ℝ) :
    ∀ᶠ T in atTop, ∀ w : ℝ → E, (∀ s, HasDerivAt w (-A s (w s)) s) →
      ⟪w T, B (w T)⟫ < 0 → ¬ MemLp w 2 (volume.restrict (Ici a)) := by
  filter_upwards [eventually_forall_ge_atTop.2 ((tendsto_iff_norm_sub_tendsto_zero.1 hA).eventually
    (eventually_le_nhds (half_pos hα)))] with T hAB w hw hneg hmem
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s ↦ (hw s).continuousAt
  set d := -⟪w T, B (w T)⟫
  have hd : 0 < d := neg_pos.2 hneg
  -- After time `T`, the Lyapunov function stays below `V(T) = -d`, so `‖w‖²` stays above
  -- `d / (‖B‖ + 1)`.
  have hlow : ∀ s, T ≤ s → d / (‖B‖ + 1) ≤ ‖‖w s‖ ^ 2‖ := fun s hs ↦ by
    have hle := inner_apply_add_integral_le hBsym hBα hAB hw hs
    have hint : 0 ≤ ∫ τ in T..s, ‖w τ‖ ^ 2 :=
      intervalIntegral.integral_nonneg hs fun _ _ ↦ by positivity
    have hinner : -⟪w s, B (w s)⟫ ≤ ‖B‖ * ‖w s‖ ^ 2 := by
      have h₁ := neg_le_abs ⟪w s, B (w s)⟫
      have h₂ := abs_real_inner_le_norm (w s) (B (w s))
      have h₃ := mul_le_mul_of_nonneg_left (B.le_opNorm (w s)) (norm_nonneg (w s))
      nlinarith
    rw [norm_pow, norm_norm, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖w s‖, sq_nonneg α]
  have hfin := ((memLp_two_iff_integrable_sq_norm hwc.aestronglyMeasurable).1 hmem
    ).measure_norm_ge_lt_top (div_pos hd (by positivity : (0 : ℝ) < ‖B‖ + 1))
  refine hfin.ne (top_unique ?_)
  rw [Measure.restrict_apply' measurableSet_Ici, ← Real.volume_Ici (a := max a T)]
  exact measure_mono fun s hs ↦
    ⟨hlow s ((le_max_right a T).trans hs), (le_max_left a T).trans hs⟩

/-- Reflecting time turns a solution of `w' = -A(s) w` into one of `w' = -A'(s) w` for
`A'(s) = -A(-s)`. -/
private theorem hasDerivAt_comp_neg (hw : ∀ s, HasDerivAt w (-A s (w s)) s) (s : ℝ) :
    HasDerivAt (fun s ↦ w (-s)) (-(-A (-s)) (w (-s))) s := by
  have h := (hw (-s)).scomp s (hasDerivAt_neg s)
  simpa [Function.comp_def] using h

/-- **Solutions with an eventually nonpositive Lyapunov function are square integrable at
`-∞`.** Let `A(s) → B` as `s → -∞`, with `B` symmetric and `α ‖v‖ ≤ ‖B v‖` for some `α > 0`. If
a solution of `w' = -A(s) w` has `⟪w s, B (w s)⟫ ≤ 0` for all large negative `s`, then `w` is
square integrable on every half-line `(-∞, a]`. -/
theorem memLp_restrict_Iic_of_eventually_inner_nonpos (hA : Tendsto A atBot (𝓝 B))
    (hBsym : (B : E →ₗ[ℝ] E).IsSymmetric) (hα : 0 < α) (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖)
    (hw : ∀ s, HasDerivAt w (-A s (w s)) s) (hV : ∀ᶠ s in atBot, ⟪w s, B (w s)⟫ ≤ 0) (a : ℝ) :
    MemLp w 2 (volume.restrict (Iic a)) := by
  have hmem := memLp_restrict_Ici_of_eventually_inner_nonneg (A := fun s ↦ -A (-s)) (B := -B)
    ((hA.comp tendsto_neg_atTop_atBot).neg)
    (by simpa using LinearMap.IsSymmetric.zero.sub hBsym) hα (by simpa using hBα)
    (hasDerivAt_comp_neg hw) (by
      filter_upwards [tendsto_neg_atTop_atBot.eventually hV] with s hs
      simpa using hs) (-a)
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ici (a := -a))
  rw [show Neg.neg ⁻¹' Ici (-a) = Iic a by ext; simp] at hneg
  simpa [Function.comp_def] using hmem.comp_measurePreserving hneg

/-- **Solutions with a positive Lyapunov function at an early time are not square integrable at
`-∞`.** Let `A(s) → B` as `s → -∞`, with `B` symmetric and `α ‖v‖ ≤ ‖B v‖` for some `α > 0`. For
all large negative `T`, every solution of `w' = -A(s) w` with `0 < ⟪w T, B (w T)⟫` fails to be
square integrable on every half-line `(-∞, a]`. -/
theorem eventually_not_memLp_restrict_Iic_of_inner_pos (hA : Tendsto A atBot (𝓝 B))
    (hBsym : (B : E →ₗ[ℝ] E).IsSymmetric) (hα : 0 < α) (hBα : ∀ v, α * ‖v‖ ≤ ‖B v‖) (a : ℝ) :
    ∀ᶠ T in atBot, ∀ w : ℝ → E, (∀ s, HasDerivAt w (-A s (w s)) s) →
      0 < ⟪w T, B (w T)⟫ → ¬ MemLp w 2 (volume.restrict (Iic a)) := by
  have h := eventually_not_memLp_restrict_Ici_of_inner_neg (A := fun s ↦ -A (-s)) (B := -B)
    ((hA.comp tendsto_neg_atTop_atBot).neg)
    (by simpa using LinearMap.IsSymmetric.zero.sub hBsym) hα (by simpa using hBα) (-a)
  filter_upwards [tendsto_neg_atBot_atTop.eventually h] with T hT w hw hpos hmem
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Iic (a := a))
  rw [show Neg.neg ⁻¹' Iic a = Ici (-a) by ext; simp] at hneg
  refine hT (fun s ↦ w (-s)) (hasDerivAt_comp_neg hw) (by simpa using hpos) ?_
  simpa [Function.comp_def] using hmem.comp_measurePreserving hneg

end TauCeti
