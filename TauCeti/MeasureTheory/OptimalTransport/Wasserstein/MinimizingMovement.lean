/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.GeneralizedGeodesic.Convex
import TauCeti.Analysis.GradientFlow.EVI.MinimizingMovement
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Complete

/-!
# Convergence of the Jordan–Kinderlehrer–Otto scheme to Wasserstein `EVI_λ` flows

Let `E` be a separable real Hilbert space and let `Φ : P₂(E) → (-∞, ∞]` be an energy on the
quadratic Wasserstein space `TauCeti.WassersteinSpace 2 E` that is lower semicontinuous for the `W₂`
topology and `λ`-convex along generalized geodesics based at every law
(`TauCeti.GeneralizedGeodesicallyConvex lam Φ μ`).

By `TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`, `Φ` satisfies the metric penalized
convexity assumption `TauCeti.PenalizedConvex lam τ Φ` for all positive time steps `τ` with
`1 + λ τ ≥ 0`, and by `TauCeti.GeneralizedGeodesicallyConvex.moreauYosida_ne_bot` it is coercive
whenever `1 + λ τ > 0`. Since `P₂(E)` is a complete metric space
(`TauCeti.WassersteinSpace.instCompleteSpace`), the metric minimizing movement convergence theorem
of Ambrosio–Gigli–Savaré (`TauCeti.Analysis.GradientFlow.EVI.MinimizingMovement`) applies directly:

* From every initial law `μ₀ ∈ P₂(E)` of finite energy (`Φ μ₀ ≠ ⊤`) there starts a unique `EVI_λ`
  gradient flow `u : ℝ → P₂(E)` (`TauCeti.IsEVISolution lam Φ u`) with `u 0 = μ₀`, and for every
  sequence of positive time steps `τ j → 0` and every family of Jordan–Kinderlehrer–Otto chains
  `J j (k + 1) ∈ moreauYosidaResolvent Φ (τ j) (J j k)` starting at `μ₀`, the piecewise constant
  interpolants `t ↦ J j ⌈t / τ j⌉₊` converge to `u` uniformly in `W₂` on `[0, T]` for every `T`
  (`TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`).
* The domain `TauCeti.eviDomain lam Φ` of initial laws from which an `EVI_λ` flow starts coincides
  with `closure {μ | Φ μ ≠ ⊤}` in `P₂(E)` (`TauCeti.WassersteinSpace.eviDomain_eq_closure`), so
  `TauCeti.eviDomainSemigroup` equips `closure {μ | Φ μ ≠ ⊤}` with a `λ`-contracting semigroup.

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`: locally uniform `W₂`
  convergence of Jordan–Kinderlehrer–Otto schemes to `EVI_λ` gradient flows on `P₂(E)`.
* `TauCeti.WassersteinSpace.eviDomain_eq_closure`: `eviDomain lam Φ = closure {μ | Φ μ ≠ ⊤}` on
  `P₂(E)` under lower semicontinuity and generalized geodesic convexity.

## References

* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*,
  SIAM J. Math. Anal. 29 (1998), 1–17.
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Theorem 11.2.1.
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Mathematics 2062,
  Springer 2013, Theorem 3.25.
-/

public section

open Filter Set
open scoped NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- A positive time step bounded by `1 / (2 (⌈|lam|⌉₊ + 1))` satisfies `0 < 1 + lam * τ`. -/
private lemma one_add_mul_pos (lam : ℝ) {τ : ℝ≥0}
    (hτ : τ ≤ (1 / (2 * (⌈|lam|⌉₊ + 1)) : ℝ≥0)) : 0 < 1 + lam * (τ : ℝ) := by
  have hle : (τ : ℝ) ≤ (2 * ((⌈|lam|⌉₊ : ℝ) + 1))⁻¹ := by
    have : (τ : ℝ) ≤ ((1 / (2 * (⌈|lam|⌉₊ + 1)) : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hτ
    simpa using this
  have habs : |lam| * (τ : ℝ) ≤ 1 / 2 := by
    calc |lam| * (τ : ℝ)
        ≤ ((⌈|lam|⌉₊ : ℝ) + 1) * (2 * ((⌈|lam|⌉₊ : ℝ) + 1))⁻¹ :=
          mul_le_mul ((Nat.le_ceil |lam|).trans (by linarith)) hle (NNReal.coe_nonneg τ)
            (by positivity)
      _ = 1 / 2 := by field_simp
  have hmul : -(|lam| * (τ : ℝ)) ≤ lam * (τ : ℝ) := by
    simpa [abs_mul, abs_of_nonneg (NNReal.coe_nonneg τ)] using neg_abs_le (lam * (τ : ℝ))
  linarith

/-- Small positive time steps satisfy `PenalizedConvex lam τ Φ` when `Φ` is `lam`-convex along
generalized geodesics based at every law. -/
private lemma eventually_penalizedConvex_of_generalizedGeodesicallyConvex
    {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ) :
    ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ Φ := by
  set τ₀ : ℝ≥0 := 1 / (2 * (⌈|lam|⌉₊ + 1))
  filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < τ₀)] with τ ⟨hτ_pos, hτ_lt⟩
  exact penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv hτ_pos
    (one_add_mul_pos lam hτ_lt.le).le

/-- **Convergence of the Jordan–Kinderlehrer–Otto scheme** (Ambrosio–Gigli–Savaré 2008, Theorems
4.0.4 and 11.2.1; Ambrosio–Gigli, *A user's guide to optimal transport*, Theorem 3.25). Let
`Φ : P₂(E) → (-∞, ∞]` be lower semicontinuous for `W₂` and `λ`-convex along generalized geodesics
with every base, and let `Φ μ₀ ≠ ⊤`. Then an `EVI_λ` solution `u` of `Φ` starts from `μ₀`, and for
all positive time steps `τ j → 0` and all sequences of JKO steps `J j` from `μ₀` with step `τ j`,
the piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` converge to `u` in `W₂`, uniformly on
every bounded time interval `[0, T]`. -/
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
  set τ₀ : ℝ≥0 := 1 / (2 * (⌈|lam|⌉₊ + 1))
  exact exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex
    (eventually_penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv) hΦ_lsc
    (by positivity : 0 < τ₀)
    ((hΦ_conv μ₀).moreauYosida_ne_bot hΦ_lsc hΦ_bot (one_add_mul_pos lam le_rfl) μ₀) hμ₀

/-- **Domain of Wasserstein `EVI_λ` flows.** For an energy `Φ : P₂(E) → (-∞, ∞]` that is lower
semicontinuous for `W₂` and `λ`-convex along generalized geodesics based at every law, the set of
initial laws from which an `EVI_λ` solution starts coincides with `closure {μ | Φ μ ≠ ⊤}` in
`P₂(E)`. -/
theorem WassersteinSpace.eviDomain_eq_closure {Φ : WassersteinSpace 2 E → EReal} {lam : ℝ}
    (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_bot : ∀ μ, Φ μ ≠ ⊥)
    (hΦ_conv : ∀ μ, GeneralizedGeodesicallyConvex lam Φ μ) :
    eviDomain lam Φ = closure {μ | Φ μ ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {μ : WassersteinSpace 2 E | Φ μ ≠ ⊤} with hemp | ⟨μ₁, _⟩
  · refine Subset.antisymm ?_ (by rw [hemp, closure_empty]; exact empty_subset _)
    simpa only [hemp, closure_empty] using eviDomain_subset_closure (lam := lam) (φ := Φ)
  set τ₀ : ℝ≥0 := 1 / (2 * (⌈|lam|⌉₊ + 1))
  exact eviDomain_eq_closure_of_penalizedConvex
    (eventually_penalizedConvex_of_generalizedGeodesicallyConvex hΦ_conv) hΦ_lsc
    (by positivity : 0 < τ₀)
    ((hΦ_conv μ₁).moreauYosida_ne_bot hΦ_lsc hΦ_bot (one_add_mul_pos lam le_rfl) μ₁)

end TauCeti
