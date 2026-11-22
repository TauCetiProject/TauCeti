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
# Wasserstein `EVI_λ` gradient flows and convergence of JKO schemes

Let `E` be a complete separable Hilbert space and let `φ : WassersteinSpace 2 E → EReal` be lower
semicontinuous and `λ`-convex along generalized geodesics (`lam`-convex) based at every law of
`P₂(E)`. In infinite dimensions, closed `W₂`-balls and energy sublevels need not be compact, so
compactness-based minimizing movement arguments do not apply directly. Instead, generalized geodesic
convexity yields coercivity (`TauCeti.GeneralizedGeodesicallyConvex.moreauYosida_ne_bot`), existence
and uniqueness of each Jordan–Kinderlehrer–Otto (JKO) step
(`TauCeti.GeneralizedGeodesicallyConvex.moreauYosidaResolvent_nonempty`,
`TauCeti.GeneralizedGeodesicallyConvex.existsUnique_mem_moreauYosidaResolvent`), and
`TauCeti.PenalizedConvex` (`TauCeti.penalizedConvex_of_generalizedGeodesicallyConvex`).

Applying the metric `EVI_λ` convergence theory to `WassersteinSpace 2 E`, this file proves that from
every initial law `μ₀` of finite energy (`φ μ₀ ≠ ⊤` and `φ μ₀ ≠ ⊥`) starts an `EVI_λ` gradient flow
`u` (unique on `[0, ∞)` by `TauCeti.IsEVISolution.eqOn`), and that piecewise constant JKO
interpolants converge uniformly to `u` on compact time intervals as the time step tends to `0`. When
`φ` never takes the value `⊥`, existence extends by contraction and stability to every
`μ₀ ∈ closure {μ | φ μ ≠ ⊤}`, characterizing the `EVI_λ` domain.

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent`: from every `μ₀` with
  `φ μ₀ ≠ ⊤` and `φ μ₀ ≠ ⊥` starts an `EVI_λ` gradient flow `u` with `u 0 = μ₀`, and all JKO
  schemes with positive step sizes `τ j → 0`, initial laws `J j 0 → μ₀` in `W₂`, and uniformly
  bounded initial energy converge uniformly to `u` on `[0, T]` (Ambrosio–Gigli–Savaré, Theorems
  4.0.4 and 11.2.1; Ambrosio–Gigli, Theorem 3.25).
* `TauCeti.exists_isEVISolution_of_mem_closure_of_generalizedGeodesicallyConvex`: when `φ` never
  takes `⊥`, an `EVI_λ` gradient flow starts from every `μ₀ ∈ closure {μ | φ μ ≠ ⊤}`.
* `TauCeti.eviDomain_eq_closure_of_generalizedGeodesicallyConvex`: when `φ` never takes `⊥`,
  `TauCeti.eviDomain lam φ = closure {μ | φ μ ≠ ⊤}`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapters 4 and 11 (Theorems 4.0.4 and 11.2.1).
* L. Ambrosio, N. Gigli, *A user's guide to optimal transport*, in *Modelling and Optimisation of
  Flows on Networks*, Lecture Notes in Math. 2062, Springer 2013, Theorem 3.25.
* R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck
  equation*, SIAM J. Math. Anal. 29 (1998), 1--17.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {lam : ℝ} {φ : WassersteinSpace 2 E → EReal}

private lemma exists_moreauYosida_ne_bot_and_penalizedConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    {μ₀ : WassersteinSpace 2 E} (hμ₀ : φ μ₀ ≠ ⊤) (hμ₀bot : φ μ₀ ≠ ⊥) :
    ∃ τ₀ : ℝ≥0, 0 < τ₀ ∧ moreauYosida φ τ₀ μ₀ ≠ ⊥ ∧
      ∀ τ : ℝ≥0, 0 < τ → τ < τ₀ → PenalizedConvex lam τ φ := by
  obtain ⟨τ₀, hτ₀, _, hm⟩ := exists_pos_abs_mul_le lam (by norm_num : (0 : ℝ) < 1 / 2) one_pos
  have hpos : ∀ {δ : ℝ≥0}, δ ≤ τ₀ → 0 < 1 + lam * (δ : ℝ) := fun {δ} hδ ↦
    one_add_mul_pos_of_abs_mul_le_half δ.property (hm hδ)
  exact ⟨τ₀, hτ₀,
    (hconv μ₀).moreauYosida_ne_bot (hφ.lowerSemicontinuousAt μ₀) hμ₀ hμ₀bot (hpos le_rfl) μ₀,
    fun τ hτ hττ₀ ↦ penalizedConvex_of_generalizedGeodesicallyConvex hconv hτ (hpos hττ₀.le).le⟩

/-- **Existence of Wasserstein `EVI_λ` flows and uniform convergence of JKO schemes**
(Ambrosio–Gigli–Savaré, Theorems 4.0.4 and 11.2.1; Ambrosio–Gigli, Theorem 3.25). Let
`φ : WassersteinSpace 2 E → EReal` be lower semicontinuous and `lam`-convex along generalized
geodesics based at every law of `P₂(E)`. Then for every `μ₀` of finite energy (`φ μ₀ ≠ ⊤` and
`φ μ₀ ≠ ⊥`), there starts from `μ₀` an `EVI_λ` flow `u` (`u 0 = μ₀`) such that for all positive
step sizes `τ j → 0` and all JKO sequences `J j` whose initial laws converge to `μ₀` in `W₂` with
uniformly bounded initial energy, the piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊`
converge uniformly to `u` on `[0, T]` for every `T : ℝ`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    {μ₀ : WassersteinSpace 2 E} (hμ₀ : φ μ₀ ≠ ⊤) (hμ₀bot : φ μ₀ ≠ ⊥) :
    ∃ u : ℝ → WassersteinSpace 2 E, u 0 = μ₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → WassersteinSpace 2 E), (∀ᶠ j in atTop, 0 < τ j) →
        Tendsto τ atTop (𝓝 0) → Tendsto (fun j ↦ J j 0) atTop (𝓝 μ₀) →
        (∃ S : ℝ, ∀ᶠ j in atTop, φ (J j 0) ≤ S) →
        (∀ᶠ j in atTop, ∀ k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn
          (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨τ₀, hτ₀, h₀, hpen⟩ :=
    exists_moreauYosida_ne_bot_and_penalizedConvex hφ hconv hμ₀ hμ₀bot
  exact exists_isEVISolution_tendstoUniformlyOn_of_penalizedConvex hφ hτ₀ hτ₀ hpen h₀ hμ₀

/-- **Characterization of the Wasserstein `EVI_λ` domain** (Ambrosio–Gigli–Savaré, Theorems 4.0.4
and 11.2.1). For an energy `φ` on `P₂(E)` that is lower semicontinuous, `lam`-convex along
generalized geodesics based at every law, and never equal to `⊥`,
`TauCeti.eviDomain lam φ = closure {μ | φ μ ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    (hbot : ∀ ν, φ ν ≠ ⊥) : eviDomain lam φ = closure {μ | φ μ ≠ ⊤} :=
  eviDomain_eq_closure_of_subset hφ fun _ hμ ↦
    let ⟨u, hu0, hu, _⟩ :=
      exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent hφ hconv hμ (hbot _)
    mem_eviDomain.2 ⟨u, hu, hu0⟩

/-- **Existence of Wasserstein `EVI_λ` flows on `closure {μ | φ μ ≠ ⊤}`**
(Ambrosio–Gigli–Savaré, Theorems 4.0.4 and 11.2.1). If `φ` is lower semicontinuous on `P₂(E)`,
`lam`-convex along generalized geodesics based at every law, and never equal to `⊥`, then an
`EVI_λ` gradient flow starts from every `μ₀ ∈ closure {μ | φ μ ≠ ⊤}`. -/
theorem exists_isEVISolution_of_mem_closure_of_generalizedGeodesicallyConvex
    (hφ : LowerSemicontinuous φ) (hconv : ∀ ν, GeneralizedGeodesicallyConvex lam φ ν)
    (hbot : ∀ ν, φ ν ≠ ⊥) {μ₀ : WassersteinSpace 2 E}
    (hμ₀ : μ₀ ∈ closure {μ | φ μ ≠ ⊤}) :
    ∃ u : ℝ → WassersteinSpace 2 E, IsEVISolution lam φ u ∧ u 0 = μ₀ :=
  mem_eviDomain.1
    (eviDomain_eq_closure_of_generalizedGeodesicallyConvex hφ hconv hbot ▸ hμ₀)

end TauCeti
