/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.Analysis.Convex.Segment
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity
import TauCeti.Analysis.Contour.AbsolutelyContinuous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.Compact

/-!
# Proximity invariance of the winding number

Two closed curves that stay closer to each other than the first one stays to `w` have the same
winding number about `w`. This is the "dog on a leash" principle: the leash from `γ₀ t` to `γ₁ t`
is too short to reach `w`, so the two walks encircle `w` the same number of times.

Continuous curves with integrable derivatives and countably many differentiability exceptions
are absolutely continuous. Their proximity invariance follows from the absolutely continuous
winding-number theorem.

The application is homotopy invariance of the winding number off the curve.
`Contour.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` deduces invariance
along the straight-line homotopy `s ↦ (1 - s) • γ₀ + s • γ₁` from the purely geometric hypothesis
that the segment `[γ₀ t, γ₁ t]` misses `w` for every parameter `t`: the intermediate curves are
piecewise `C¹` because that predicate is stable under affine combinations, and a compactness
estimate lets finitely many of them be chained together by the leash lemma.

## Main results

* `Contour.windingNumber_eq_of_dist_lt_dist` — the raw-hypothesis form: closed curves that are
  continuous, differentiable off a countable set, and have interval-integrable derivatives, with
  `dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w` throughout, have equal winding numbers about `w`.
* `Contour.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist` — the same for closed piecewise-`C¹`
  curves, whose regularity supplies the raw hypotheses on its own.
* `Contour.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints` — the common-endpoint
  version for paths that need not be closed.
* `Contour.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` — invariance along the
  straight-line homotopy: if `w ∉ [γ₀ t, γ₁ t]` for every `t`, the winding numbers agree.

## Provenance

The comparison-quotient argument is the standard proof of the "dog on a leash" lemma (equivalently,
the homotopy form of Rouché's theorem); see L. Ahlfors, *Complex Analysis*, Ch. 4.
No formal source is vendored.
-/

public section

noncomputable section

open Bornology MeasureTheory Set

namespace TauCeti.Contour

variable {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- **Proximity invariance of the winding number** (the "dog on a leash" lemma). Let `γ₀` and `γ₁`
be closed curves on the oriented interval with endpoints `a`, `b`, each continuous on
`Set.uIcc a b`, differentiable off a common countable set `P`, and with interval-integrable
derivative. If at every parameter the two curves are closer to each other than `γ₀` is to `w`,
then they have the same winding number about `w`. -/
theorem windingNumber_eq_of_dist_lt_dist {P : Set ℝ} (hP : P.Countable)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (h₀cont : ContinuousOn γ₀ (uIcc a b)) (h₁cont : ContinuousOn γ₁ (uIcc a b))
    (h₀diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₀ t)
    (h₁diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₁ t)
    (h₀int : IntervalIntegrable (fun t => deriv γ₀ t) volume a b)
    (h₁int : IntervalIntegrable (fun t => deriv γ₁ t) volume a b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact (h₀cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (h₀diff t ht).hasDerivAt) h₀int).windingNumber_eq_of_dist_lt_dist
    (h₁cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
      (fun t ht ↦ (h₁diff t ht).hasDerivAt) h₁int) h₀closed h₁closed hlt

/-- **Proximity invariance for closed piecewise-`C¹` curves.** If two closed piecewise-`C¹` curves
stay closer to each other than the first stays to `w`, they have the same winding number about `w`.
Piecewise-`C¹` regularity supplies the continuity, differentiability and integrability hypotheses
of `windingNumber_eq_of_dist_lt_dist`. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist (h₀ : IsPiecewiseC1On γ₀ a b)
    (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist
    h₁.absolutelyContinuousOnInterval h₀closed h₁closed hlt

/-- **Proximity invariance for paths with common endpoints.** If two piecewise-`C¹` paths agree at
both endpoints and stay closer to each other than the first stays to `w`, then they have the same
winding number about `w`. Unlike `IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist`, the paths need
not be closed; their common endpoints make the comparison quotient a closed curve. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints
    (h₀ : IsPiecewiseC1On γ₀ a b) (h₁ : IsPiecewiseC1On γ₁ a b)
    (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints
    h₁.absolutelyContinuousOnInterval ha hb hlt

/-- The stage at time `s` of the straight-line homotopy `(1 - s) • γ₀ + s • γ₁`. -/
private def lineHomotopy (γ₀ γ₁ : ℝ → ℂ) (s : ℝ) : ℝ → ℂ := fun t => (1 - s) • γ₀ t + s • γ₁ t

private theorem lineHomotopy_apply (γ₀ γ₁ : ℝ → ℂ) (s t : ℝ) :
    lineHomotopy γ₀ γ₁ s t = (1 - s) • γ₀ t + s • γ₁ t := rfl

/-- Two stages of the straight-line homotopy differ by the scaled displacement of its ends. -/
private theorem lineHomotopy_sub (γ₀ γ₁ : ℝ → ℂ) (s s' t : ℝ) :
    lineHomotopy γ₀ γ₁ s' t - lineHomotopy γ₀ γ₁ s t = (s' - s) • (γ₁ t - γ₀ t) := by
  simp only [lineHomotopy_apply]
  module

/-- Chaining the leash lemma along a uniform subdivision. If every step of the straight-line
homotopy moves each point by less than the clearance `m` between the whole homotopy and `w`, then
every stage `k / N` has the same winding number about `w` as the initial curve. -/
private theorem windingNumber_lineHomotopy_div_eq_of_norm_div_lt (h₀ : IsPiecewiseC1On γ₀ a b)
    (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    {m : ℝ} {N : ℕ} (hNpos : (0 : ℝ) < N)
    (hlt : ∀ t ∈ uIcc a b, ‖γ₁ t - γ₀ t‖ / N < m)
    (hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, m ≤ ‖lineHomotopy γ₀ γ₁ s t - w‖) :
    ∀ k : ℕ, k ≤ N → windingNumber (lineHomotopy γ₀ γ₁ (k / N)) a b w =
      windingNumber (lineHomotopy γ₀ γ₁ 0) a b w := by
  have hHpw : ∀ s : ℝ, IsPiecewiseC1On (lineHomotopy γ₀ γ₁ s) a b := fun s =>
    (h₀.const_smul (1 - s)).add (h₁.const_smul s)
  have hHclosed : ∀ s : ℝ, lineHomotopy γ₀ γ₁ s a = lineHomotopy γ₀ γ₁ s b := fun s => by
    rw [lineHomotopy_apply, lineHomotopy_apply, h₀closed, h₁closed]
  intro k
  induction k with
  | zero => intro _; norm_num
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := Nat.le_of_succ_le hk
    rw [← ih hkN]
    refine IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist (hHpw _) (hHpw _)
      (hHclosed _) (hHclosed _) fun t ht => ?_
    have hmem : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      exact_mod_cast hkN
    -- one stage of the subdivision advances the parameter by exactly `1 / N`
    have hgap : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by push_cast; ring
    have hdisp : ‖lineHomotopy γ₀ γ₁ ((k + 1 : ℕ) / N) t
        - lineHomotopy γ₀ γ₁ ((k : ℝ) / N) t‖ = ‖γ₁ t - γ₀ t‖ / N := by
      rw [lineHomotopy_sub, norm_smul, Real.norm_eq_abs, hgap, abs_of_pos (by positivity)]
      ring
    rw [dist_eq_norm, dist_eq_norm, hdisp]
    exact lt_of_lt_of_le (hlt t ht) (hmle _ hmem t ht)

/-- **Invariance of the winding number along a straight-line homotopy.** If for every parameter `t`
the segment from `γ₀ t` to `γ₁ t` misses `w`, then the two closed piecewise-`C¹` curves have the
same winding number about `w`.

No regularity of the homotopy is assumed. The intermediate curves `(1 - s) • γ₀ + s • γ₁` are
piecewise `C¹` because that predicate is stable under affine combinations; a compactness argument
bounds their distance to `w` below by a positive `m` and the displacement `‖γ₁ - γ₀‖` above by
some `M`; and the `N + 1` stages `k / N` with `M / N < m` are then chained together by
`IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist`. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_notMem_segment (h₀ : IsPiecewiseC1On γ₀ a b)
    (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  have hHne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b, lineHomotopy γ₀ γ₁ s t - w ≠ 0 := by
    intro s hs t ht
    refine sub_ne_zero.mpr fun heq => hseg t ht ?_
    exact heq ▸ ⟨1 - s, s, by linarith [hs.2], hs.1, by ring, rfl⟩
  -- A positive lower bound for the distance from the homotopy to `w`, by compactness.
  have hKcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := isCompact_Icc.prod isCompact_uIcc
  have hKne : (Icc (0 : ℝ) 1 ×ˢ uIcc a b).Nonempty := ⟨(0, a), ⟨by norm_num, left_mem_uIcc⟩⟩
  have hcont₀ : ContinuousOn (fun p : ℝ × ℝ => γ₀ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₀.continuousOn.comp continuousOn_snd fun p hp => hp.2
  have hcont₁ : ContinuousOn (fun p : ℝ × ℝ => γ₁ p.2) (Icc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    h₁.continuousOn.comp continuousOn_snd fun p hp => hp.2
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => ‖lineHomotopy γ₀ γ₁ p.1 p.2 - w‖)
      (Icc (0 : ℝ) 1 ×ˢ uIcc a b) := by
    simp only [lineHomotopy_apply]
    exact ((((continuousOn_const.sub continuousOn_fst).smul hcont₀).add
      (continuousOn_fst.smul hcont₁)).sub continuousOn_const).norm
  obtain ⟨q, hqK, hqmin⟩ := hKcompact.exists_isMinOn hKne hcontF
  have hm : 0 < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ :=
    norm_pos_iff.mpr (hHne q.1 hqK.1 q.2 hqK.2)
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ uIcc a b,
      ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ ≤ ‖lineHomotopy γ₀ γ₁ s t - w‖ :=
    fun s hs t ht => isMinOn_iff.mp hqmin (s, t) ⟨hs, ht⟩
  -- An upper bound for the displacement between the two curves.
  obtain ⟨M, hM⟩ :=
    isCompact_uIcc.exists_bound_of_continuousOn (h₁.continuousOn.sub h₀.continuousOn)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a left_mem_uIcc)
  obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hstep : M / N < ‖lineHomotopy γ₀ γ₁ q.1 q.2 - w‖ := by
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact (div_lt_iff₀ hm).mp hN
  -- Chain the stages `k / N` together with the leash lemma.
  have key := windingNumber_lineHomotopy_div_eq_of_norm_div_lt h₀ h₁ h₀closed h₁closed hNpos
    (fun t ht => lt_of_le_of_lt (by gcongr; exact hM t ht) hstep) hmle
  have hfinal := key N le_rfl
  rw [div_self (ne_of_gt hNpos)] at hfinal
  have hH0 : lineHomotopy γ₀ γ₁ 0 = γ₀ := by
    funext t; rw [lineHomotopy_apply]; simp
  have hH1 : lineHomotopy γ₀ γ₁ 1 = γ₁ := by
    funext t; rw [lineHomotopy_apply]; simp
  rwa [hH0, hH1] at hfinal

end TauCeti.Contour

end

end
