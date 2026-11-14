/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.MinimizingMovement
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Metric convergence of the Jordan–Kinderlehrer–Otto scheme

Let `E` be a complete separable real inner product space and `Φ : P₂(E) → EReal` a lower
semicontinuous energy on the quadratic Wasserstein space `TauCeti.WassersteinSpace 2 E` that never
takes the value `⊥` and is `λ`-convex along generalized geodesics based at every law
(`TauCeti.GeneralizedGeodesicallyConvex`), for some `λ : ℝ` of arbitrary sign.

When the base law of a generalized-geodesic plan `γ` from `ν₀` to `ν₁` is chosen to be `ν₀`
itself, the `2`-convexity inequality `TauCeti.IsGeneralizedGeodesicPlan.dist_sq_add_le` reads

`W₂(ν₀, ν_t)² + t (1 - t) ∫ ‖y₀ - y₁‖² dγ ≤ t W₂(ν₀, ν₁)²`.

Dividing by `t > 0` and letting `t → 0⁺` shows that the coupling cost `∫ ‖y₀ - y₁‖² dγ` equals
`W₂(ν₀, ν₁)²` and hence `W₂(ν₀, ν_t) ≤ t W₂(ν₀, ν₁)` for all `t ∈ [0, 1]`. Consequently `Φ` is
`λ`-convex along connecting curves with linear initial speed bound for every `λ ∈ ℝ` (including
`λ < 0`), so `TauCeti.moreauYosida_ne_bot_of_convexAlong` supplies coercivity `Φ_τ(μ) > -∞` as
soon as `1 + λ τ > 0` (`TauCeti.moreauYosida_ne_bot_of_generalizedGeodesicallyConvex`). Together
with `TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex` and completeness of `P₂(E)`, every
Jordan–Kinderlehrer–Otto step `TauCeti.moreauYosidaResolvent Φ τ μ` exists and is unique when
`τ > 0`, `1 + λ τ > 0`, and `Φ` is finite somewhere
(`TauCeti.existsUnique_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex`), without
properness of `E` or compactness of energy sublevels.

Feeding both coercivity and penalized convexity into the metric generation theorem
`TauCeti.exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex` yields the convergence of the
Jordan–Kinderlehrer–Otto scheme
(`TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`): for every `μ₀` with
`Φ μ₀ ≠ ⊤`, an `EVI_λ` solution `u` starts from `μ₀`, and along any positive time steps `τ j → 0`
and any JKO sequences from `μ₀` the piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` converge
to `u` in `W₂`, uniformly on every bounded interval `[0, T]`. Moreover, the domain of the `EVI_λ`
semiflow is `closure {μ | Φ μ ≠ ⊤}`
(`TauCeti.eviDomain_eq_closure_of_generalizedGeodesicallyConvex`).

## Main results

* `TauCeti.moreauYosida_ne_bot_of_generalizedGeodesicallyConvex`: coercivity `Φ_τ(μ) > -∞` on
  `P₂(E)` whenever `1 + λ τ > 0`.
* `TauCeti.moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex` and
  `TauCeti.existsUnique_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex`: existence and
  uniqueness of the JKO step on `P₂(E)` when `τ > 0` and `1 + λ τ > 0`.
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

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Along a generalized-geodesic plan from `ν₀` to `ν₁` based at `ν₀` itself, the coupling cost
equals `W₂(ν₀, ν₁)²`, so the generalized geodesic satisfies `W₂(ν₀, c t) ≤ t W₂(ν₀, ν₁)` and
`ConvexAlong lam Φ c` for every `lam : ℝ`. -/
private theorem exists_convexAlong_of_generalizedGeodesicallyConvex_self
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ} {ν₀ ν₁ : WassersteinSpace 2 E}
    (hconv₀ : GeneralizedGeodesicallyConvex lam Φ ν₀) (hν₀ : Φ ν₀ ≠ ⊤) (hν₁ : Φ ν₁ ≠ ⊤) :
    ∃ c : ℝ → WassersteinSpace 2 E, c 0 = ν₀ ∧ c 1 = ν₁ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, dist ν₀ (c t) ≤ t * dist ν₀ ν₁) ∧ ConvexAlong lam Φ c := by
  obtain ⟨γ, hγ, hφγ⟩ := generalizedGeodesicallyConvex_def.1 hconv₀ hν₀ hν₁
  have hπ := hγ.isCoupling_snd
  choose c hc using exists_coe_eq_generalizedGeodesic hπ
  have hc₀ : c 0 = ν₀ := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
    rw [hc, generalizedGeodesic_zero, hπ.fst_eq]
  have hc₁ : c 1 = ν₁ := WassersteinSpace.ext <| ProbabilityMeasure.toMeasure_injective <| by
    rw [hc, generalizedGeodesic_one, hπ.snd_eq]
  have hI_eq : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd = dist ν₀ ν₁ ^ 2 := by
    set I : ℝ := ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ.snd
    refine le_antisymm ?_ (WassersteinSpace.dist_sq_le_integral hπ)
    by_contra! hlt
    have hI_pos : 0 < I := (sq_nonneg _).trans_lt hlt
    set δ : ℝ := I - dist ν₀ ν₁ ^ 2
    have hδ : 0 < δ := sub_pos.2 hlt
    set t : ℝ := min (1 / 2) (δ / (2 * I))
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hd := hγ.dist_sq_add_le ⟨ht0.le, ht1.le⟩ (hc t)
    rw [dist_self] at hd
    have h1t : (1 - t) * I ≤ dist ν₀ ν₁ ^ 2 :=
      le_of_mul_le_mul_left (by nlinarith [sq_nonneg (dist ν₀ (c t)), hd]) ht0
    have htI : t * I ≤ δ / 2 := calc
      t * I ≤ δ / (2 * I) * I := mul_le_mul_of_nonneg_right (min_le_right _ _) hI_pos.le
      _ = δ / 2 := by have := hI_pos.ne'; field_simp
    linarith [h1t, htI, show (1 - t) * I = I - t * I by ring]
  refine ⟨c, hc₀, hc₁, fun t ht ↦ ?_, convexAlong_def.2 fun t ht ↦ ?_⟩
  · have hd := hγ.dist_sq_add_le ht (hc t)
    rw [dist_self, hI_eq] at hd
    have hsq : dist ν₀ (c t) ^ 2 ≤ (t * dist ν₀ ν₁) ^ 2 := by
      linarith [hd,
        show (1 - t) * 0 ^ 2 + t * dist ν₀ ν₁ ^ 2 - t * (1 - t) * dist ν₀ ν₁ ^ 2 =
          (t * dist ν₀ ν₁) ^ 2 by ring]
    exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg ht.1 dist_nonneg) two_ne_zero).1 hsq
  · have hle := convexAlongGeneralizedGeodesicPlan_def.1 hφγ t ht (c t) (hc t)
    simpa only [hc₀, hc₁, hI_eq] using hle

/-- **Coercivity of energies convex along generalized geodesics.** If `Φ : P₂(E) → EReal` is
`W₂`-lower semicontinuous, never takes the value `⊥`, and is `lam`-convex along generalized
geodesics based at every law of its effective domain, then `Φ_τ(μ) > -∞` for every `μ` and every
time step `τ` with `1 + lam * τ > 0`. -/
theorem moreauYosida_ne_bot_of_generalizedGeodesicallyConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ} {τ : ℝ≥0}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, Φ μ ≠ ⊤ → GeneralizedGeodesicallyConvex lam Φ μ)
    (hmτ : 0 < 1 + lam * τ) (μ : WassersteinSpace 2 E) :
    moreauYosida Φ τ μ ≠ ⊥ :=
  moreauYosida_ne_bot_of_convexAlong hΦ_lsc hΦ_bot
    (fun ν₀ _ h₀ h₁ ↦
      exists_convexAlong_of_generalizedGeodesicallyConvex_self (hΦ_conv ν₀ h₀) h₀ h₁)
    hmτ μ

/-- **Existence of the JKO step under convexity along generalized geodesics.** If
`Φ : P₂(E) → EReal` is `W₂`-lower semicontinuous, never takes the value `⊥`, is finite somewhere,
and is `lam`-convex along generalized geodesics based at every law, then for every `τ > 0` with
`1 + lam * τ > 0` and every `μ : P₂(E)` the JKO resolvent `TauCeti.moreauYosidaResolvent Φ τ μ` is
nonempty. -/
theorem moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ} {τ : ℝ≥0}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + lam * τ) (hdom : ∃ ν, Φ ν ≠ ⊤)
    (μ : WassersteinSpace 2 E) :
    (moreauYosidaResolvent Φ τ μ).Nonempty :=
  (penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv hτ
    hmτ.le).moreauYosidaResolvent_nonempty hΦ_lsc hτ hmτ
    (moreauYosida_ne_bot_of_generalizedGeodesicallyConvex hΦ_lsc hΦ_bot (fun ν _ ↦ hΦ_conv ν) hmτ μ)
    hdom

/-- **Existence and uniqueness of the JKO step under convexity along generalized geodesics.** Under
the hypotheses of `TauCeti.moreauYosidaResolvent_nonempty_of_generalizedGeodesicallyConvex`, every
law `μ : P₂(E)` has a unique JKO step `ν ∈ TauCeti.moreauYosidaResolvent Φ τ μ`. -/
theorem existsUnique_mem_moreauYosidaResolvent_of_generalizedGeodesicallyConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ} {τ : ℝ≥0}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ)
    (hτ : 0 < τ) (hmτ : 0 < 1 + lam * τ) (hdom : ∃ ν, Φ ν ≠ ⊤)
    (μ : WassersteinSpace 2 E) :
    ∃! ν, ν ∈ moreauYosidaResolvent Φ τ μ :=
  (penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv hτ
    hmτ.le).existsUnique_mem_moreauYosidaResolvent hΦ_lsc hτ hmτ
    (moreauYosida_ne_bot_of_generalizedGeodesicallyConvex hΦ_lsc hΦ_bot (fun ν _ ↦ hΦ_conv ν) hmτ μ)
    hdom

/-- Helper packaging coercivity at a small positive step `τ₀` and `PenalizedConvex lam τ Φ` for all
sufficiently small `τ > 0` from convexity along generalized geodesics. -/
private theorem exists_moreauYosida_ne_bot_and_eventually_penalizedConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ) (μ₁ : WassersteinSpace 2 E) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida Φ τ₀ μ₁ ≠ ⊥ ∧
      ∀ᶠ τ in 𝓝[>] (0 : ℝ≥0), PenalizedConvex lam τ Φ := by
  set τ₀ : ℝ≥0 := ⟨1 / (2 * (|lam| + 1)), by positivity⟩
  have hτ₀ : 0 < τ₀ := NNReal.coe_pos.1 (div_pos one_pos (by positivity))
  have hmτ₀ : 0 < 1 + lam * τ₀ := by
    have habs : -(lam * (τ₀ : ℝ)) ≤ |lam| * (τ₀ : ℝ) := by
      simpa [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)] using neg_le_abs (lam * (τ₀ : ℝ))
    have hlt : |lam| * (τ₀ : ℝ) < 1 := by
      change |lam| * (1 / (2 * (|lam| + 1))) < 1
      rw [mul_one_div, div_lt_one (by positivity)]; linarith [abs_nonneg lam]
    linarith
  refine ⟨τ₀, hτ₀, moreauYosida_ne_bot_of_generalizedGeodesicallyConvex hΦ_lsc hΦ_bot
    (fun ν _ ↦ hΦ_conv ν) hmτ₀ μ₁, ?_⟩
  refine Metric.mem_nhdsWithin_iff.2 ⟨1 / (|lam| + 1), by positivity, fun τ ⟨hball, hτ_pos⟩ ↦ ?_⟩
  have hτ_lt : (τ : ℝ) < 1 / (|lam| + 1) := by
    simpa [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (NNReal.coe_nonneg _)] using hball
  have habs : -(lam * (τ : ℝ)) ≤ |lam| * (τ : ℝ) := by
    simpa [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)] using neg_le_abs (lam * (τ : ℝ))
  have hlt : |lam| * (1 / (|lam| + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith [abs_nonneg lam]
  have hmτ : 0 ≤ 1 + lam * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hτ_lt.le (abs_nonneg lam), habs, hlt]
  exact penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv hτ_pos hmτ

/-- **Convergence of the Jordan–Kinderlehrer–Otto scheme** (Ambrosio–Gigli–Savaré, Theorem 4.0.4;
Ambrosio–Gigli, Theorem 3.25). Let `Φ : P₂(E) → EReal` be `W₂`-lower semicontinuous, never `⊥`, and
`lam`-convex along generalized geodesics with every base, and let `Φ μ₀ ≠ ⊤`. Then an `EVI_lam`
solution `u` of `Φ` starts from `μ₀`, and for all positive time steps `τ j → 0` and all sequences of
JKO steps `J j` from `μ₀` with step `τ j`, the piecewise constant interpolants
`t ↦ J j ⌈t / τ j⌉₊` converge to `u` in `W₂`, uniformly on `[0, T]` for every `T`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ)
    {μ₀ : WassersteinSpace 2 E} (hμ₀ : Φ μ₀ ≠ ⊤) :
    ∃ u : ℝ → WassersteinSpace 2 E,
      u 0 = μ₀ ∧ IsEVISolution lam Φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → WassersteinSpace 2 E),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = μ₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent Φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, hne_bot, hpen⟩ :=
    exists_moreauYosida_ne_bot_and_eventually_penalizedConvex hΦ_lsc hΦ_bot hΦ_conv μ₀
  obtain ⟨u, hu0, hevi, hunif⟩ :=
    exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hΦ_lsc hτ₀ hne_bot hpen hμ₀
  refine ⟨u, hu0, hevi, fun τ J hτ_ne hτ0 hJ0 hJ T ↦ hunif τ J hτ_ne hτ0 ?_ ?_ hJ T⟩
  · simpa only [hJ0] using tendsto_const_nhds
  · exact ⟨(Φ μ₀).toReal, fun j ↦ by rw [hJ0 j, EReal.coe_toReal hμ₀ (hΦ_bot μ₀)]⟩

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
  obtain ⟨τ₀, hτ₀, hne_bot, hpen⟩ :=
    exists_moreauYosida_ne_bot_and_eventually_penalizedConvex hΦ_lsc hΦ_bot hΦ_conv μ₁
  exact eviDomain_eq_closure_of_penalizedConvex hΦ_lsc hτ₀ hne_bot hpen

end TauCeti
