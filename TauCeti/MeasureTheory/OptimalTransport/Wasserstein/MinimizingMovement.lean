/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.MinimizingMovement
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Metric convergence of the Jordan–Kinderlehrer–Otto scheme

Let `E` be a complete separable real inner product space and `Φ : P₂(E) → EReal` a lower
semicontinuous energy on the quadratic Wasserstein space `TauCeti.WassersteinSpace 2 E` that never
takes the value `⊥` and is `λ`-convex along generalized geodesics based at every law
(`TauCeti.GeneralizedGeodesicallyConvex`), for some `λ : ℝ` of arbitrary sign.

In `TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex`, convexity along
generalized geodesics is shown to imply both coercivity
(`TauCeti.moreauYosida_ne_bot_of_generalizedGeodesicallyConvex`) and penalized convexity for small
time steps (`TauCeti.eventually_penalizedConvex_of_generalizedGeodesicallyConvex`), without
properness of `E` or compactness of energy sublevels. Feeding both ingredients into the metric
generation theorem `TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex` yields the
metric convergence of the Jordan–Kinderlehrer–Otto scheme
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`): for every `μ₀` with
`Φ μ₀ ≠ ⊤`, an `EVI_λ` solution `u` starts from `μ₀`, and along any positive time steps `τ j → 0`
and any JKO sequences whose initial laws converge to `μ₀` in `W₂` with uniformly bounded energy, the
piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` converge to `u` in `W₂`, uniformly on every
bounded interval `[0, T]`. Moreover, the domain of the `EVI_λ` semiflow is `closure {μ | Φ μ ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_generalizedGeodesicallyConvex`).

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`: existence of the `EVI_λ`
  flow from `μ₀` and locally uniform `W₂` convergence of JKO interpolants.
* `TauCeti.eviDomain_eq_closure_of_generalizedGeodesicallyConvex`: the `EVI_λ` domain equals
  `closure {μ | Φ μ ≠ ⊤}`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4, Lemma 9.2.7 and Theorem 11.2.1.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Math. 2062,
  Springer 2013, Assumption 3.24 and Theorem 3.25.
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*,
  SIAM J. Math. Anal. 29 (1998), 1--17.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- **Convergence of the Jordan–Kinderlehrer–Otto scheme** (Ambrosio–Gigli–Savaré, Theorem 4.0.4;
Ambrosio–Gigli, Theorem 3.25). Let `Φ : P₂(E) → EReal` be `W₂`-lower semicontinuous, never `⊥`, and
`lam`-convex along generalized geodesics with every base, and let `Φ μ₀ ≠ ⊤`. Then an `EVI_lam`
solution `u` of `Φ` starts from `μ₀`, and for all positive time steps `τ j → 0` and all sequences of
JKO steps `J j` whose initial laws converge to `μ₀` in `W₂` with uniformly bounded energy, the
piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` converge to `u` in `W₂`, uniformly on `[0, T]`
for every `T`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ)
    {μ₀ : WassersteinSpace 2 E} (hμ₀ : Φ μ₀ ≠ ⊤) :
    ∃ u : ℝ → WassersteinSpace 2 E,
      u 0 = μ₀ ∧ IsEVISolution lam Φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → WassersteinSpace 2 E),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) →
        Tendsto (fun j ↦ J j 0) atTop (𝓝 μ₀) → (∃ S : ℝ, ∀ j, Φ (J j 0) ≤ S) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent Φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hΦ_lsc hτ₀
    (moreauYosida_ne_bot_of_generalizedGeodesicallyConvex hΦ_lsc hΦ_bot
      (fun ν _ ↦ hΦ_conv ν) hmτ₀ μ₀)
    (eventually_penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv) hμ₀

/-- Under the hypotheses of
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`, the domain of the `EVI_lam`
flow on `P₂(E)` equals `closure {μ | Φ μ ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_generalizedGeodesicallyConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ) :
    eviDomain lam Φ = closure {μ | Φ μ ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {μ : WassersteinSpace 2 E | Φ μ ≠ ⊤} with hemp | ⟨μ₁, -⟩
  · exact Subset.antisymm (eviDomain_subset_closure.trans (by simp [hemp])) (by simp [hemp])
  obtain ⟨τ₀, hτ₀, hmτ₀⟩ := exists_pos_one_add_mul_pos lam
  exact eviDomain_eq_closure_of_penalizedConvex hΦ_lsc hτ₀
    (moreauYosida_ne_bot_of_generalizedGeodesicallyConvex hΦ_lsc hΦ_bot
      (fun ν _ ↦ hΦ_conv ν) hmτ₀ μ₁)
    (eventually_penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv)

end TauCeti
