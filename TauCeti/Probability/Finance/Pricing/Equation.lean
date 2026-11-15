/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Probability.Process.ContinuousAE

/-!
# From trajectory identities to the pointwise pricing equation

For a classical price `C(s,t)`, the pricing residual is

`C_t + σ(s,t)² s² / 2 C_ss + r(t) (s C_s - C)`.

If this residual vanishes Lebesgue-time times probability almost everywhere along a
continuous positive process started at `(s,t)`, its continuity implies that it vanishes at
`(s,t)`. Having such a process from every deterministic starting point therefore gives the
pointwise pricing equation on the entire pricing domain, including calendar time zero.
Time derivatives are taken within `[0,∞)`, so at time zero they are right derivatives.
The half-open time intervals impose no continuity of derivatives at maturity.

This is only the continuity step in deriving a classical pricing equation. The along-path
a.e. identity is an explicit input; this file neither derives it from self-financing nor
constructs an asset process, a martingale measure, or a replicating strategy. A single
initial trajectory cannot supply the all-start hypothesis of the final theorem.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §4.5 and §6.4.
-/

public section

open MeasureTheory Set

namespace TauCeti.Finance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] [NeZero P]
  {C σ : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {T : ℝ}

/-- Continuous price derivatives and continuous coefficients upgrade an along-path a.e.
pricing equation to the equation at the deterministic starting point. Volatility may vanish:
this lemma only propagates an already established drift identity. -/
theorem pde_eq_zero_of_ae_eq_zero_along_process {S : ℝ → Ω → ℝ} {s t : ℝ}
    (ht : t ∈ Ico 0 T)
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Ico 0 T))
    (hCs : ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun x ↦ C x p.2) p.1)
      (Ioi 0 ×ˢ Ico 0 T))
    (hCss : ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv fun x ↦ C x p.2) p.1)
      (Ioi 0 ×ˢ Ico 0 T))
    (hCt : ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (C p.1) (Ici 0) p.2) (Ioi 0 ×ˢ Ico 0 T))
    (hσ : ContinuousOn (Function.uncurry σ) (Ioi 0 ×ˢ Ico 0 T))
    (hr : ContinuousOn r (Ico 0 T))
    (hS : ∀ᵐ ω ∂P, ContinuousOn (fun u ↦ S u ω) (Ico t T))
    (hpos : ∀ᵐ ω ∂P, ∀ u ∈ Ico t T, 0 < S u ω)
    (hstart : ∀ᵐ ω ∂P, S t ω = s)
    (hpde : ∀ᵐ p ∂(volume.restrict (Ico t T)).prod P,
      derivWithin (C (S p.1 p.2)) (Ici 0) p.1 +
        σ (S p.1 p.2) p.1 ^ 2 * S p.1 p.2 ^ 2 / 2 *
          deriv (deriv fun x ↦ C x p.1) (S p.1 p.2) +
        r p.1 * (S p.1 p.2 * deriv (fun x ↦ C x p.1) (S p.1 p.2) - C (S p.1 p.2) p.1) = 0) :
    derivWithin (C s) (Ici 0) t + σ s t ^ 2 * s ^ 2 / 2 * deriv (deriv fun x ↦ C x t) s +
      r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0 := by
  have hr' : ContinuousOn (fun p : ℝ × ℝ ↦ r p.2) (Ioi 0 ×ˢ Ico 0 T) :=
    hr.comp continuousOn_snd (fun _ hp ↦ hp.2)
  have hD : ∀ᵐ ω ∂P, ∀ u ∈ Ico t T, (S u ω, u) ∈ Ioi 0 ×ˢ Ico 0 T := by
    filter_upwards [hpos] with ω hpos u hu
    exact ⟨hpos u hu, ht.1.trans hu.1, hu.2⟩
  exact eq_of_ae_eq_along_process ht.2
    ((hCt.add ((((hσ.pow 2).mul (continuousOn_fst.pow 2)).div_const 2).mul hCss)).add
      (hr'.mul ((continuousOn_fst.mul hCs).sub hC)))
    continuousOn_const hS hD hstart hpde

/-- If the along-path pricing equation holds from every positive deterministic spot and every
calendar time before maturity, then the classical pricing equation holds pointwise throughout
the pricing domain. Each start may have its own sample-null set; no intersection over the
uncountable set of starting points is required. -/
theorem pde_eq_zero_of_ae_eq_zero_along_all_starts
    (S : ℝ → ℝ → ℝ → Ω → ℝ)
    (hC : ContinuousOn (Function.uncurry C) (Ioi 0 ×ˢ Ico 0 T))
    (hCs : ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun x ↦ C x p.2) p.1)
      (Ioi 0 ×ˢ Ico 0 T))
    (hCss : ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv fun x ↦ C x p.2) p.1)
      (Ioi 0 ×ˢ Ico 0 T))
    (hCt : ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (C p.1) (Ici 0) p.2)
      (Ioi 0 ×ˢ Ico 0 T))
    (hσ : ContinuousOn (Function.uncurry σ) (Ioi 0 ×ˢ Ico 0 T))
    (hr : ContinuousOn r (Ico 0 T))
    (hS : ∀ s > 0, ∀ t ∈ Ico 0 T,
      ∀ᵐ ω ∂P, ContinuousOn (fun u ↦ S s t u ω) (Ico t T))
    (hpos : ∀ s > 0, ∀ t ∈ Ico 0 T, ∀ᵐ ω ∂P, ∀ u ∈ Ico t T, 0 < S s t u ω)
    (hstart : ∀ s > 0, ∀ t ∈ Ico 0 T, ∀ᵐ ω ∂P, S s t t ω = s)
    (hpde : ∀ s > 0, ∀ t ∈ Ico 0 T,
      ∀ᵐ p ∂(volume.restrict (Ico t T)).prod P,
        derivWithin (C (S s t p.1 p.2)) (Ici 0) p.1 +
          σ (S s t p.1 p.2) p.1 ^ 2 * S s t p.1 p.2 ^ 2 / 2 *
            deriv (deriv fun x ↦ C x p.1) (S s t p.1 p.2) +
          r p.1 * (S s t p.1 p.2 * deriv (fun x ↦ C x p.1) (S s t p.1 p.2) -
            C (S s t p.1 p.2) p.1) = 0) :
    ∀ s > 0, ∀ t ∈ Ico 0 T,
      derivWithin (C s) (Ici 0) t + σ s t ^ 2 * s ^ 2 / 2 *
        deriv (deriv fun x ↦ C x t) s + r t * (s * deriv (fun x ↦ C x t) s - C s t) = 0 := by
  intro s hs t ht
  exact pde_eq_zero_of_ae_eq_zero_along_process ht hC hCs hCss hCt hσ hr
    (hS s hs t ht) (hpos s hs t ht) (hstart s hs t ht) (hpde s hs t ht)

end TauCeti.Finance
