/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Subdifferential
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.OptimalTransport.Brenier
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# The strong Wasserstein subdifferential

Let `E` be a separable Hilbert space and `φ : P₂(E) → EReal` an energy on the quadratic
Wasserstein space. A vector field `ξ ∈ L²(μ; E)` is a *strong subgradient* of `φ` at a law `μ` of
finite energy if, as the displacement field `v` tends to `0` in `L²(μ; E)`,

`φ ((id + v)₊ μ) ≥ φ μ + ∫ ⟪ξ x, v x⟫ dμ + o(‖v‖_{L²(μ)})`.

The set of strong subgradients is the *strong Wasserstein subdifferential*
`∂ₛφ(μ) ⊆ L²(μ; E)` (`TauCeti.wassersteinStrongSubdifferential`). Writing `t = id + v`, this is the
condition `φ (t₊ μ) ≥ φ μ + ∫ ⟪ξ, t - id⟫ dμ + o(‖t - id‖_{L²(μ)})` as `t → id`, tested against
every map `t ∈ L²(μ; E)`, optimal or not. The Fréchet subdifferential
`TauCeti.wassersteinSubdifferential` tests instead against optimal couplings only, with the error
measured by `W₂(μ, t₊ μ) ≤ ‖t - id‖_{L²(μ)}`.

The pairing `∫ ⟪ξ x, v x⟫ dμ` is the inner product of `L²(μ; E)`, so `∂ₛφ(μ)` is a closed convex
subset of `L²(μ; E)`. Unlike the Fréchet subdifferential, it sees every direction of
perturbation: along `v = h • ζ` for a fixed `ζ ∈ L²(μ; E)`, a strong subgradient satisfies
`φ ((id + h • ζ)₊ μ) ≥ φ μ + h ⟪ξ, ζ⟫ - o(h)` for `h` of both signs. So if `φ` is differentiable
along this perturbation with derivative `D` at `h = 0`, then `⟪ξ, ζ⟫ = D`
(`TauCeti.inner_eq_of_mem_wassersteinStrongSubdifferential`), and an energy that is
differentiable along every perturbation has at most one strong subgradient
(`TauCeti.subsingleton_wassersteinStrongSubdifferential`). For a constant energy the strong
subdifferential is `{0}` at every law.

When every optimal coupling out of `μ` is induced by a map `T`, as Brenier's theorem guarantees
for a law `μ` absolutely continuous with respect to Lebesgue measure on a finite-dimensional
space, the optimal coupling of `μ` and `ν` is `(id, T)₊ μ` with `‖T - id‖_{L²(μ)} = W₂(μ, ν)`, and
every strong subgradient is a Fréchet subgradient
(`TauCeti.wassersteinStrongSubdifferential_subset_wassersteinSubdifferential` and its corollary
`wassersteinStrongSubdifferential_subset_wassersteinSubdifferential_of_absolutelyContinuous`).

For the potential energy `ν ↦ ∫ V dν` of a differentiable `m`-strongly convex potential `V` whose
gradient grows at most linearly, the gradient `∇V` is a strong subgradient at every law, by the
first-order condition `V (x + v x) ≥ V x + ⟪∇V x, v x⟫ + (m / 2) ‖v x‖²` integrated against `μ`;
differentiability of the potential energy along perturbations makes it the only one.

## Main definitions

* `TauCeti.wassersteinStrongSubdifferential φ μ`: the set of strong subgradients of `φ` at `μ`, a
  subset of `L²(μ; E)`.

## Main results

* `TauCeti.convex_wassersteinStrongSubdifferential` and
  `TauCeti.isClosed_wassersteinStrongSubdifferential`: the strong subdifferential is a closed
  convex subset of `L²(μ; E)`.
* `TauCeti.mem_wassersteinStrongSubdifferential_of_forall_le`: a global subgradient inequality with
  a quadratic error term gives a strong subgradient.
* `TauCeti.inner_eq_of_mem_wassersteinStrongSubdifferential`: a strong subgradient pairs with each
  direction of perturbation as the derivative of the energy along it.
* `TauCeti.subsingleton_wassersteinStrongSubdifferential`: an energy differentiable along every
  perturbation has at most one strong subgradient; for a constant energy the strong
  subdifferential is `{0}` (`TauCeti.wassersteinStrongSubdifferential_const`).
* `TauCeti.wassersteinStrongSubdifferential_subset_wassersteinSubdifferential` and
  `wassersteinStrongSubdifferential_subset_wassersteinSubdifferential_of_absolutelyContinuous`:
  where optimal couplings are induced by maps, in particular at absolutely continuous laws on a
  finite-dimensional space, strong subgradients are Fréchet subgradients.
* `StrongConvexOn.mem_wassersteinStrongSubdifferential_potentialEnergy` and
  `TauCeti.subsingleton_wassersteinStrongSubdifferential_potentialEnergy`: the gradient of a
  strongly convex potential is the unique strong subgradient of its potential energy.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §10.1 (Definition 10.1.1 for the Fréchet and
  strong subdifferentials at regular measures) and §10.4.1 for the potential energy.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

variable {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E}
  {ξ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)}

/-- The **strong Wasserstein subdifferential** `∂ₛφ(μ)` of an energy `φ` on `P₂(E)` at a law `μ`:
the set of fields `ξ ∈ L²(μ; E)` such that `φ μ` is finite and
`φ ((id + v)₊ μ) ≥ φ μ + ∫ ⟪ξ x, v x⟫ dμ + o(‖v‖)` as `v → 0` in `L²(μ; E)`. The little-o is
written out: for every `ε > 0`, eventually as `v → 0`, every law `ν` of `P₂(E)` equal to the law of
`x + v x` under `μ` satisfies `φ μ + ⟪ξ, v⟫ - ε ‖v‖ ≤ φ ν`, where `⟪ξ, v⟫ = ∫ ⟪ξ x, v x⟫ dμ` is
the inner product of `L²(μ; E)`. -/
def wassersteinStrongSubdifferential (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : Set (Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) :=
  {ξ | φ μ ≠ ⊥ ∧ φ μ ≠ ⊤ ∧ ∀ ε > 0,
    ∀ᶠ v : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E) in 𝓝 0, ∀ ν : WassersteinSpace 2 E,
      ((ν : ProbabilityMeasure E) : Measure E) =
        ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + v x) →
      φ μ + ((⟪ξ, v⟫ - ε * ‖v‖ : ℝ) : EReal) ≤ φ ν}

/-- The defining property of a strong Wasserstein subgradient. -/
theorem mem_wassersteinStrongSubdifferential_iff :
    ξ ∈ wassersteinStrongSubdifferential φ μ ↔ φ μ ≠ ⊥ ∧ φ μ ≠ ⊤ ∧ ∀ ε > 0,
      ∀ᶠ v : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E) in 𝓝 0, ∀ ν : WassersteinSpace 2 E,
        ((ν : ProbabilityMeasure E) : Measure E) =
          ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + v x) →
        φ μ + ((⟪ξ, v⟫ - ε * ‖v‖ : ℝ) : EReal) ≤ φ ν :=
  Iff.rfl

/-- An energy with a strong subgradient at `μ` is not `⊥` there. -/
theorem ne_bot_of_mem_wassersteinStrongSubdifferential
    (hξ : ξ ∈ wassersteinStrongSubdifferential φ μ) : φ μ ≠ ⊥ :=
  hξ.1

/-- An energy with a strong subgradient at `μ` is not `⊤` there. -/
theorem ne_top_of_mem_wassersteinStrongSubdifferential
    (hξ : ξ ∈ wassersteinStrongSubdifferential φ μ) : φ μ ≠ ⊤ :=
  hξ.2.1

/-- The strong Wasserstein subdifferential is convex. -/
theorem convex_wassersteinStrongSubdifferential (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : Convex ℝ (wassersteinStrongSubdifferential φ μ) := by
  intro ξ hξ ζ hζ a b ha hb hab
  refine ⟨hξ.1, hξ.2.1, fun ε hε ↦ ?_⟩
  filter_upwards [hξ.2.2 ε hε, hζ.2.2 ε hε] with v h₁ h₂ ν hν
  have h₁ := h₁ ν hν
  have h₂ := h₂ ν hν
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  -- The pairing of `a • ξ + b • ζ` is a convex combination of the two pairings, so it is
  -- dominated by the larger one.
  obtain rfl : b = 1 - a := by linarith
  rcases le_total ⟪ξ, v⟫ ⟪ζ, v⟫ with h | h
  · exact le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2
      (by nlinarith [mul_le_mul_of_nonneg_left h ha]))) h₂
  · exact le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2
      (by nlinarith [mul_le_mul_of_nonneg_left h hb]))) h₁

/-- The strong Wasserstein subdifferential is closed in `L²(μ; E)`. -/
theorem isClosed_wassersteinStrongSubdifferential (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : IsClosed (wassersteinStrongSubdifferential φ μ) := by
  refine isClosed_of_closure_subset fun ξ hξ ↦ ?_
  obtain ⟨ζ₀, hζ₀, -⟩ := Metric.mem_closure_iff.1 hξ 1 one_pos
  refine ⟨hζ₀.1, hζ₀.2.1, fun ε hε ↦ ?_⟩
  obtain ⟨ζ, hζ, hdist⟩ := Metric.mem_closure_iff.1 hξ (ε / 2) (half_pos hε)
  filter_upwards [hζ.2.2 (ε / 2) (half_pos hε)] with v hv ν hν
  refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) (hv ν hν)
  -- The pairings of `ξ` and `ζ` with `v` differ by at most `‖ξ - ζ‖ ‖v‖ ≤ (ε / 2) ‖v‖`.
  have h₁ := abs_le.1 (abs_real_inner_le_norm (ξ - ζ) v)
  rw [inner_sub_left] at h₁
  have h₂ : ‖ξ - ζ‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact hdist.le
  nlinarith [mul_le_mul_of_nonneg_right h₂ (norm_nonneg v)]

/-- **A global subgradient inequality gives a strong subgradient.** If `φ μ` is finite and, for
some `m : ℝ`, `φ ν ≥ φ μ + ⟪ξ, v⟫ + (m / 2) ‖v‖²` for every field `v ∈ L²(μ; E)` and the law `ν`
of `x + v x` under `μ`, then `ξ ∈ ∂ₛφ(μ)`. -/
theorem mem_wassersteinStrongSubdifferential_of_forall_le {m : ℝ} (hbot : φ μ ≠ ⊥)
    (htop : φ μ ≠ ⊤)
    (h : ∀ (v : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) (ν : WassersteinSpace 2 E),
      ((ν : ProbabilityMeasure E) : Measure E) =
        ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + v x) →
      φ μ + ((⟪ξ, v⟫ + m / 2 * ‖v‖ ^ 2 : ℝ) : EReal) ≤ φ ν) :
    ξ ∈ wassersteinStrongSubdifferential φ μ := by
  refine ⟨hbot, htop, fun ε hε ↦ ?_⟩
  filter_upwards [Metric.ball_mem_nhds 0 (show 0 < 2 * ε / (|m| + 1) by positivity)]
    with v hv ν hν
  refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) (h v ν hν)
  -- Near `0` the quadratic term is at least `-ε ‖v‖`.
  rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ (by positivity)] at hv
  have hd := norm_nonneg v
  have hm : |m| * ‖v‖ ≤ 2 * ε := by nlinarith
  nlinarith [neg_abs_le m, mul_le_mul_of_nonneg_right hm hd]

/-- The law of `μ` displaced by the class of `h • ζ` is the law of `x + h • ζ x`. -/
private theorem map_add_coeFn_smul (ζ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) (h : ℝ) :
    ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + (h • ζ) x) =
      ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ζ x) :=
  Measure.map_congr ((Lp.coeFn_smul h ζ).mono fun x hx ↦ by simp only [hx, Pi.smul_apply])

variable [BorelSpace E] [SecondCountableTopology E]

/-- Along the perturbation `x ↦ x + h • ζ x` of `μ`, a strong subgradient `ξ` bounds the energy
from below: for every `ε > 0` and `h` near `0`, `f h ≥ f 0 + h ⟪ξ, ζ⟫ - ε |h| ‖ζ‖`, where `f h`
is the energy of the perturbed law. -/
private theorem eventually_add_sub_le_of_mem_wassersteinStrongSubdifferential
    (hξ : ξ ∈ wassersteinStrongSubdifferential φ μ)
    (ζ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) {f : ℝ → ℝ}
    (hf : ∀ᶠ h in 𝓝 0, ∀ ν : WassersteinSpace 2 E, ((ν : ProbabilityMeasure E) : Measure E) =
      ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ζ x) → φ ν = f h)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : ℝ), f 0 + (h * ⟪ξ, ζ⟫ - ε * (|h| * ‖ζ‖)) ≤ f h := by
  -- At `h = 0` the perturbation is the identity, so `φ μ = f 0`.
  have h₀ : φ μ = f 0 := hf.self_of_nhds μ (by simp)
  have ht : Tendsto (fun h : ℝ ↦ h • ζ) (𝓝 0) (𝓝 ((0 : ℝ) • ζ)) := tendsto_id.smul_const ζ
  rw [zero_smul] at ht
  filter_upwards [hf, ht.eventually (hξ.2.2 ε hε)] with h hfh hP
  obtain ⟨ν, hν⟩ := exists_coe_eq_map_of_memLp (T := fun x ↦ x + h • ζ x)
    (μ.hasFiniteMoment.memLp_id.add ((Lp.memLp ζ).const_smul h))
  have hle := hP ν (hν.trans (map_add_coeFn_smul ζ h).symm)
  rw [hfh ν hν, h₀, ← EReal.coe_add, EReal.coe_le_coe_iff, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs] at hle
  exact hle

/-- **Strong subgradients and directional derivatives.** Let `ξ ∈ ∂ₛφ(μ)` and
`ζ ∈ L²(μ; E)`. Suppose that the energy is differentiable along the perturbation of `μ` by `ζ`:
for `h` near `0`, the law of `x + h • ζ x` under `μ` has energy `f h`, where `f` has derivative
`D` at `0`. Then `⟪ξ, ζ⟫ = D`, that is, `∫ ⟪ξ x, ζ x⟫ dμ = D`. -/
theorem inner_eq_of_mem_wassersteinStrongSubdifferential
    (hξ : ξ ∈ wassersteinStrongSubdifferential φ μ)
    (ζ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) {f : ℝ → ℝ} {D : ℝ}
    (hf : ∀ᶠ h in 𝓝 0, ∀ ν : WassersteinSpace 2 E, ((ν : ProbabilityMeasure E) : Measure E) =
      ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ζ x) → φ ν = f h)
    (hD : HasDerivAt f D 0) : ⟪ξ, ζ⟫ = D := by
  -- The one-sided difference quotients of `f` at `0` are within `ε ‖ζ‖` of `⟪ξ, ζ⟫`.
  have hA : ∀ ε > 0, |⟪ξ, ζ⟫ - D| ≤ ε * ‖ζ‖ := by
    intro ε hε
    have key := eventually_add_sub_le_of_mem_wassersteinStrongSubdifferential hξ ζ hf hε
    have h₁ : ⟪ξ, ζ⟫ - ε * ‖ζ‖ ≤ D := by
      refine ge_of_tendsto hD.tendsto_slope_zero_right ?_
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with h hh (hpos : 0 < h)
      rw [zero_add, smul_eq_mul, le_inv_mul_iff₀ hpos]
      rw [abs_of_pos hpos] at hh
      linarith
    have h₂ : D ≤ ⟪ξ, ζ⟫ + ε * ‖ζ‖ := by
      refine le_of_tendsto hD.tendsto_slope_zero_left ?_
      filter_upwards [nhdsWithin_le_nhds key, self_mem_nhdsWithin] with h hh (hneg : h < 0)
      rw [zero_add, smul_eq_mul, inv_mul_eq_div, div_le_iff_of_neg hneg]
      rw [abs_of_neg hneg] at hh
      linarith
    rw [abs_le]
    constructor <;> linarith
  refine eq_of_forall_dist_le fun η hη ↦ ?_
  rw [Real.dist_eq]
  refine (hA _ (div_pos hη (by positivity : (0 : ℝ) < ‖ζ‖ + 1))).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg ζ]

/-- **Uniqueness of strong subgradients.** If the energy `φ` is differentiable at `μ` along every
perturbation, that is, for each `ζ ∈ L²(μ; E)` the energy of the law of `x + h • ζ x` under `μ` is,
for `h` near `0`, a function of `h` differentiable at `0`, then `φ` has at most one strong
subgradient at `μ`. -/
theorem subsingleton_wassersteinStrongSubdifferential
    (hφ : ∀ ζ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E), ∃ f : ℝ → ℝ, ∃ D : ℝ,
      (∀ᶠ h in 𝓝 0, ∀ ν : WassersteinSpace 2 E, ((ν : ProbabilityMeasure E) : Measure E) =
        ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + h • ζ x) → φ ν = f h) ∧
      HasDerivAt f D 0) :
    (wassersteinStrongSubdifferential φ μ).Subsingleton := by
  intro ξ hξ ξ' hξ'
  refine ext_inner_left ℝ fun ζ ↦ ?_
  obtain ⟨f, D, hf, hD⟩ := hφ ζ
  rw [real_inner_comm ξ, real_inner_comm ξ',
    inner_eq_of_mem_wassersteinStrongSubdifferential hξ ζ hf hD,
    inner_eq_of_mem_wassersteinStrongSubdifferential hξ' ζ hf hD]

/-- The strong subdifferential of a constant energy is `{0}` at every law. -/
@[simp]
theorem wassersteinStrongSubdifferential_const (c : ℝ) (μ : WassersteinSpace 2 E) :
    wassersteinStrongSubdifferential (fun _ ↦ (c : EReal)) μ = {0} := by
  have h₀ : (0 : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) ∈
      wassersteinStrongSubdifferential (fun _ ↦ (c : EReal)) μ :=
    mem_wassersteinStrongSubdifferential_of_forall_le (m := 0) (EReal.coe_ne_bot c)
      (EReal.coe_ne_top c) fun v ν _ ↦ by simp
  refine eq_singleton_iff_unique_mem.2 ⟨h₀, fun ξ hξ ↦ ?_⟩
  exact subsingleton_wassersteinStrongSubdifferential
    (fun _ ↦ ⟨fun _ ↦ c, 0, .of_forall fun _ _ _ ↦ rfl, hasDerivAt_const 0 c⟩) hξ h₀

variable [CompleteSpace E]

/-- **Strong subgradients are Fréchet subgradients where optimal plans are induced by maps.**
Suppose that every optimal coupling for the quadratic cost of `μ` with a law `ν` of `P₂(E)` is the
graph plan `(id, T)₊ μ` of a map `T`. Then every strong subgradient of `φ` at `μ` is a Fréchet
subgradient. -/
theorem wassersteinStrongSubdifferential_subset_wassersteinSubdifferential
    (hmap : ∀ (ν : WassersteinSpace 2 E) (γ : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) γ
        ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
      ∃ T : E → E, AEMeasurable T ((μ : ProbabilityMeasure E) : Measure E) ∧
        γ = graphPlan T ((μ : ProbabilityMeasure E) : Measure E)) :
    wassersteinStrongSubdifferential φ μ ⊆ wassersteinSubdifferential φ μ := by
  intro ξ hξ
  refine mem_wassersteinSubdifferential_iff.2 ⟨hξ.1, hξ.2.1, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hξ.2.2 ε hε)
  filter_upwards [Metric.ball_mem_nhds μ hδ] with ν hν γ hγ
  obtain ⟨T, hT, rfl⟩ := hmap ν γ hγ
  have hlaw : ((μ : ProbabilityMeasure E) : Measure E).map T =
      ((ν : ProbabilityMeasure E) : Measure E) := by
    rw [← snd_graphPlan hT, hγ.toIsCoupling.snd_eq]
  have hv : MemLp (fun x ↦ T x - x) 2 ((μ : ProbabilityMeasure E) : Measure E) :=
    (memLp_of_hasFiniteMoment_map hT (hlaw ▸ ν.hasFiniteMoment)).sub μ.hasFiniteMoment.memLp_id
  -- The displacement `v = T - id` has norm `W₂(μ, ν)` and pushes `μ` to `ν`.
  have hnorm : ‖hv.toLp _‖ = dist μ ν := by
    refine (pow_left_inj₀ (norm_nonneg _) dist_nonneg two_ne_zero).1 ?_
    rw [hv.norm_toLp_sq, WassersteinSpace.dist_sq_eq_integral hγ,
      integral_graphPlan hT (by fun_prop)]
    simp only [norm_sub_rev]
  have hmapv : ((ν : ProbabilityMeasure E) : Measure E) =
      ((μ : ProbabilityMeasure E) : Measure E).map (fun x ↦ x + hv.toLp _ x) := by
    rw [← hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx, add_sub_cancel]
  have hpair : ⟪ξ, hv.toLp _⟫ =
      ∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂graphPlan T ((μ : ProbabilityMeasure E) : Measure E) := by
    rw [L2.inner_toLp, integral_graphPlan hT ((Lp.aestronglyMeasurable ξ).comp_measurePreserving
      hγ.toIsCoupling.measurePreserving_fst |>.inner (by fun_prop))]
  have := hball (y := hv.toLp _) (by rwa [dist_zero_right, hnorm, dist_comm]) ν hmapv
  rwa [hpair, hnorm] at this

/-- **Strong subgradients are Fréchet subgradients at absolutely continuous laws.** On a
finite-dimensional real inner product space, let `μ ∈ P₂(E)` be absolutely continuous with respect
to an additive Haar measure. Then every strong subgradient of an energy `φ` at `μ` is a Fréchet
subgradient: by Brenier's theorem every optimal coupling out of `μ` is induced by a map. -/
theorem wassersteinStrongSubdifferential_subset_wassersteinSubdifferential_of_absolutelyContinuous
    [FiniteDimensional ℝ E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
    (hμ : ((μ : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    wassersteinStrongSubdifferential φ μ ⊆ wassersteinSubdifferential φ μ :=
  wassersteinStrongSubdifferential_subset_wassersteinSubdifferential fun ν _ hγ ↦ by
    obtain ⟨u, -, -, -, -, hgraph⟩ :=
      (isOptimalCoupling_norm_sub_sq_div_two_of_edist_rpow_two hγ).exists_eq_graphPlan_gradient hμ
        (transportCost_norm_sub_sq_div_two_ne_top μ ν)
    exact ⟨_, (measurable_gradient _).aemeasurable, hgraph⟩

section PotentialEnergy

variable {V : E → ℝ} {m C : ℝ}

/-- **The gradient of a strongly convex potential is a strong subgradient of its potential
energy.** Let `V` be a differentiable `m`-strongly convex potential whose gradient grows at most
linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`. At every law `μ` of `P₂(E)`, every field `ξ ∈ L²(μ; E)` equal to
`∇V` almost everywhere is a strong subgradient of the potential energy `ν ↦ ∫ V dν`. -/
theorem _root_.StrongConvexOn.mem_wassersteinStrongSubdifferential_potentialEnergy
    (hV : StrongConvexOn univ m V) (hVd : Differentiable ℝ V)
    (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖))
    (hξ : ξ =ᵐ[((μ : ProbabilityMeasure E) : Measure E)] gradient V) :
    ξ ∈ wassersteinStrongSubdifferential
      (fun ν : WassersteinSpace 2 E ↦ potentialEnergy V ((ν : ProbabilityMeasure E) : Measure E))
      μ := by
  have hφ (ρ : WassersteinSpace 2 E) : potentialEnergy V ((ρ : ProbabilityMeasure E) : Measure E) =
      ((∫ x, V x ∂((ρ : ProbabilityMeasure E) : Measure E) : ℝ) : EReal) :=
    potentialEnergy_of_integrable
      (integrable_comp_of_norm_gradient_le hVd hV' ρ.hasFiniteMoment.memLp_id)
  refine mem_wassersteinStrongSubdifferential_of_forall_le (m := m) (by simp [hφ]) (by simp [hφ])
    fun v ν hν ↦ ?_
  have hT : AEMeasurable (fun x ↦ x + v x) ((μ : ProbabilityMeasure E) : Measure E) :=
    aemeasurable_id.add (Lp.aestronglyMeasurable v).aemeasurable
  -- The first-order condition along the graph plan of `x ↦ x + v x`, which couples `μ` and `ν`.
  have hγ := isCoupling_graphPlan ⟨hT, hν.symm⟩
  have h := hV.integral_add_add_le_of_isCoupling hVd hV' hξ hγ
  rw [integral_graphPlan hT ((Lp.aestronglyMeasurable ξ).comp_measurePreserving
      hγ.measurePreserving_fst |>.inner (by fun_prop)), integral_graphPlan hT (by fun_prop)] at h
  simp only [add_sub_cancel_left, sub_add_cancel_left, norm_neg] at h
  rw [hφ, hφ, ← EReal.coe_add, EReal.coe_le_coe_iff, L2.inner_def,
    ← Lp.integral_norm_sq_eq_norm_sq]
  exact h

/-- **The strong subgradient of a potential energy is unique.** Let `V` be a differentiable
potential whose gradient grows at most linearly, `‖∇V x‖ ≤ C (1 + ‖x‖)`. At every law `μ` of
`P₂(E)` the potential energy `ν ↦ ∫ V dν` has at most one strong subgradient: the potential energy
is differentiable along every perturbation of `μ`. -/
theorem subsingleton_wassersteinStrongSubdifferential_potentialEnergy
    (hVd : Differentiable ℝ V) (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖))
    (μ : WassersteinSpace 2 E) :
    (wassersteinStrongSubdifferential
      (fun ν : WassersteinSpace 2 E ↦ potentialEnergy V ((ν : ProbabilityMeasure E) : Measure E))
      μ).Subsingleton := by
  have hρ := μ.hasFiniteMoment.memLp_id
  refine subsingleton_wassersteinStrongSubdifferential fun ζ ↦
    ⟨fun h ↦ ∫ x, V (x + h • ζ x) ∂((μ : ProbabilityMeasure E) : Measure E), _,
      .of_forall fun h ν hν ↦ ?_, hasDerivAt_integral_comp_add_smul hVd hV' hρ (Lp.memLp ζ)⟩
  have hζ := (Lp.memLp ζ).const_smul h
  rw [hν, potentialEnergy_map (f := fun x ↦ x + h • ζ x) hVd.continuous.measurable
      (aemeasurable_id.add hζ.aestronglyMeasurable.aemeasurable),
    potentialEnergy_of_integrable (integrable_comp_of_norm_gradient_le
      (T := fun x ↦ x + h • ζ x) hVd hV' (hρ.add hζ))]

end PotentialEnergy

end TauCeti
