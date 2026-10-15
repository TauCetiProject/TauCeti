/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Convex.Strong
public import TauCeti.Analysis.GradientFlow.GeodesicConvex
public import TauCeti.Analysis.GradientFlow.Slope
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.EulerLagrange
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# The Wasserstein subdifferential

Let `E` be a separable Hilbert space and `φ : P₂(E) → EReal` an energy on the quadratic
Wasserstein space. A vector field `ξ ∈ L²(μ; E)` is a *(Fréchet) subgradient* of `φ` at a law `μ`
of finite energy if, as `ν → μ` in `P₂(E)`,

`φ ν ≥ φ μ + ∫ ⟪ξ x, y - x⟫ dγ(x, y) + o(W₂(μ, ν))`

for every optimal coupling `γ` of `μ` and `ν` for the quadratic cost. The set of subgradients is the
*Wasserstein subdifferential* `∂φ(μ) ⊆ L²(μ; E)` (`TauCeti.wassersteinSubdifferential`). It is the
object through which Ambrosio, Gigli and Savaré describe Wasserstein gradient flows: the velocity
field of a gradient flow of `φ` lies in `-∂φ(μ_t)`, and the element of minimal norm of `∂φ(μ)` plays
the role of the gradient. When `E` is finite-dimensional and `μ` is absolutely continuous with
respect to Lebesgue measure, the optimal coupling is unique and induced by a transport map `t_μ^ν`
(Brenier's theorem), and the pairing is `∫ ⟪ξ, t_μ^ν - id⟫ dμ`, as in the definition of
Ambrosio–Gigli–Savaré for regular measures. Quantifying over every optimal coupling makes the
definition meaningful for all laws of `P₂(E)`.

The little-o is written out: for every `ε > 0`, eventually as `ν → μ`, every optimal coupling `γ`
satisfies `φ μ + ∫ ⟪ξ x, y - x⟫ dγ - ε W₂(μ, ν) ≤ φ ν`. The subdifferential is empty at laws of
infinite energy.

The pairing `∫ ⟪ξ x, y - x⟫ dγ` is the `L²(γ)` inner product of `ξ ∘ Prod.fst` with the
displacement, whose `L²(γ)` norm is `W₂(μ, ν)` for an optimal `γ`. So it is linear in `ξ` and at
most `‖ξ‖ W₂(μ, ν)` in absolute value. These two facts make `∂φ(μ)` a closed convex subset of the
Hilbert space `L²(μ; E)`, so it has a unique element of minimal norm when it is nonempty, and they
bound the descending slope: `|∂φ|(μ) ≤ ‖ξ‖` for every subgradient `ξ`.

For an energy that is `m`-convex along geodesics, the defining inequality improves from a local
one with an error `o(W₂)` to a global one with the convexity term: at a law `μ` of finite energy,
`ξ ∈ ∂φ(μ)` exactly when `φ ν ≥ φ μ + ∫ ⟪ξ x, y - x⟫ dγ + (m / 2) W₂(μ, ν)²` for every law `ν`
and every optimal coupling `γ` of `μ` and `ν`. The proof applies the subgradient inequality at the
laws `μ_t` along the interpolation of `γ`, joined to `μ` by the optimal couplings
`(x, (1 - t) • x + t • y)₊ γ`, and lets `t → 0`.

The basic example is the potential energy `ν ↦ ∫ V dν` of a differentiable `m`-strongly convex
potential `V` whose gradient grows at most linearly: its gradient `∇V` is a subgradient at every
law of `P₂(E)`, by the first-order condition `V y ≥ V x + ⟪∇V x, y - x⟫ + (m / 2) ‖y - x‖²`
integrated against an optimal coupling.

## Main definitions

* `TauCeti.wassersteinSubdifferential φ μ`: the set of subgradients of `φ` at `μ`, a subset of
  `L²(μ; E)`.

## Main results

* `TauCeti.convex_wassersteinSubdifferential` and `TauCeti.isClosed_wassersteinSubdifferential`:
  the subdifferential is a closed convex subset of `L²(μ; E)`.
* `TauCeti.existsUnique_mem_wassersteinSubdifferential_forall_norm_le`: a nonempty subdifferential
  has a unique element of minimal norm.
* `TauCeti.descendingSlope_le_of_mem_wassersteinSubdifferential`: the descending slope of `φ` at
  `μ` is at most the norm of every subgradient.
* `TauCeti.mem_wassersteinSubdifferential_of_forall_le`: a global subgradient inequality with a
  quadratic error term gives a subgradient.
* `TauCeti.ConvexAlongGeodesics.mem_wassersteinSubdifferential_iff`: for an energy that is
  `m`-convex along geodesics, at a law of finite energy, the subgradients are exactly the fields
  satisfying the global subgradient inequality with the term `(m / 2) W₂(μ, ν)²`.
* `StrongConvexOn.mem_wassersteinSubdifferential_potentialEnergy` and
  `StrongConvexOn.nonempty_wassersteinSubdifferential_potentialEnergy`: the gradient of an
  `m`-strongly convex potential is a subgradient of its potential energy.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 10: §10.1 for the subdifferential at
  regular measures, its closedness, minimal selection and the slope bound, and §10.4 for the
  subdifferential of the potential energy.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {φ : WassersteinSpace 2 E → EReal} {μ : WassersteinSpace 2 E}
  {ξ : Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)}

/-- The **Wasserstein subdifferential** `∂φ(μ)` of an energy `φ` on `P₂(E)` at a law `μ`: the set
of fields `ξ ∈ L²(μ; E)` such that `φ μ` is finite and
`φ ν ≥ φ μ + ∫ ⟪ξ x, y - x⟫ dγ(x, y) + o(W₂(μ, ν))` as `ν → μ`, for every optimal coupling `γ` of
`μ` and `ν` for the quadratic cost. The little-o is written out: for every `ε > 0`, eventually as
`ν → μ`, `φ μ + ∫ ⟪ξ x, y - x⟫ dγ - ε W₂(μ, ν) ≤ φ ν` for every such `γ`. -/
def wassersteinSubdifferential (φ : WassersteinSpace 2 E → EReal) (μ : WassersteinSpace 2 E) :
    Set (Lp E 2 ((μ : ProbabilityMeasure E) : Measure E)) :=
  {ξ | φ μ ≠ ⊥ ∧ φ μ ≠ ⊤ ∧ ∀ ε > 0, ∀ᶠ ν : WassersteinSpace 2 E in 𝓝 μ, ∀ γ : Measure (E × E),
    IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) γ
      ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
    φ μ + ((∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ - ε * dist μ ν : ℝ) : EReal) ≤ φ ν}

/-- The defining property of a Wasserstein subgradient. -/
theorem mem_wassersteinSubdifferential_iff :
    ξ ∈ wassersteinSubdifferential φ μ ↔ φ μ ≠ ⊥ ∧ φ μ ≠ ⊤ ∧ ∀ ε > 0,
      ∀ᶠ ν : WassersteinSpace 2 E in 𝓝 μ, ∀ γ : Measure (E × E),
        IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) γ
          ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
      φ μ + ((∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ - ε * dist μ ν : ℝ) : EReal) ≤ φ ν :=
  Iff.rfl

/-- An energy with a subgradient at `μ` is not `⊥` there. -/
theorem ne_bot_of_mem_wassersteinSubdifferential (hξ : ξ ∈ wassersteinSubdifferential φ μ) :
    φ μ ≠ ⊥ :=
  hξ.1

/-- An energy with a subgradient at `μ` is not `⊤` there. -/
theorem ne_top_of_mem_wassersteinSubdifferential (hξ : ξ ∈ wassersteinSubdifferential φ μ) :
    φ μ ≠ ⊤ :=
  hξ.2.1

/-- The Wasserstein subdifferential is convex. -/
theorem convex_wassersteinSubdifferential (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : Convex ℝ (wassersteinSubdifferential φ μ) := by
  intro ξ hξ ζ hζ a b ha hb hab
  refine ⟨hξ.1, hξ.2.1, fun ε hε ↦ ?_⟩
  filter_upwards [hξ.2.2 ε hε, hζ.2.2 ε hε] with ν h₁ h₂ γ hγ
  have : IsProbabilityMeasure γ := hγ.isProbabilityMeasure
  rw [hγ.toIsCoupling.integral_inner_smul_add_smul (memLp_sub_of_hasFiniteMoment
    (hγ.toIsCoupling.fst_eq ▸ μ.hasFiniteMoment) (hγ.toIsCoupling.snd_eq ▸ ν.hasFiniteMoment))]
  -- The pairing of `a • ξ + b • ζ` is a convex combination of the two pairings, so it is
  -- dominated by the larger one.
  have h₁ := h₁ γ hγ
  have h₂ := h₂ γ hγ
  generalize ∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ = A at h₁ ⊢
  generalize ∫ z, ⟪ζ z.1, z.2 - z.1⟫ ∂γ = B at h₂ ⊢
  obtain rfl : b = 1 - a := by linarith
  rcases le_total A B with h | h
  · exact le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2
      (by nlinarith [mul_le_mul_of_nonneg_left h ha]))) h₂
  · exact le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2
      (by nlinarith [mul_le_mul_of_nonneg_left h hb]))) h₁

/-- The Wasserstein subdifferential is closed in `L²(μ; E)`. -/
theorem isClosed_wassersteinSubdifferential (φ : WassersteinSpace 2 E → EReal)
    (μ : WassersteinSpace 2 E) : IsClosed (wassersteinSubdifferential φ μ) := by
  refine isClosed_of_closure_subset fun ξ hξ ↦ ?_
  obtain ⟨ζ₀, hζ₀, -⟩ := Metric.mem_closure_iff.1 hξ 1 one_pos
  refine ⟨hζ₀.1, hζ₀.2.1, fun ε hε ↦ ?_⟩
  obtain ⟨ζ, hζ, hdist⟩ := Metric.mem_closure_iff.1 hξ (ε / 2) (half_pos hε)
  filter_upwards [hζ.2.2 (ε / 2) (half_pos hε)] with ν hν γ hγ
  refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) (hν γ hγ)
  -- The pairings of `ξ` and `ζ` differ by at most `‖ξ - ζ‖ W₂(μ, ν) ≤ (ε / 2) W₂(μ, ν)`.
  have : IsProbabilityMeasure γ := hγ.isProbabilityMeasure
  have h₁ := hγ.toIsCoupling.integral_inner_sub (memLp_sub_of_hasFiniteMoment
    (hγ.toIsCoupling.fst_eq ▸ μ.hasFiniteMoment) (hγ.toIsCoupling.snd_eq ▸ ν.hasFiniteMoment)) ξ ζ
  have h₂ := abs_le.1 (hγ.abs_integral_inner_le (ξ - ζ))
  have h₃ : ‖ξ - ζ‖ ≤ ε / 2 := by
    rw [← dist_eq_norm]
    exact hdist.le
  nlinarith [mul_le_mul_of_nonneg_right h₃ (dist_nonneg (x := μ) (y := ν))]

/-- **Minimal selection.** A nonempty Wasserstein subdifferential has a unique element of minimal
norm. -/
theorem existsUnique_mem_wassersteinSubdifferential_forall_norm_le
    (h : (wassersteinSubdifferential φ μ).Nonempty) :
    ∃! ξ, ξ ∈ wassersteinSubdifferential φ μ ∧ ∀ ζ ∈ wassersteinSubdifferential φ μ, ‖ξ‖ ≤ ‖ζ‖ := by
  obtain ⟨ξ, hξ, hmin⟩ := exists_norm_eq_iInf_of_complete_convex h
    (isClosed_wassersteinSubdifferential φ μ).isComplete (convex_wassersteinSubdifferential φ μ) 0
  have hle : ∀ ζ ∈ wassersteinSubdifferential φ μ, ‖ξ‖ ≤ ‖ζ‖ := fun ζ hζ ↦ by
    have := ciInf_le (f := fun w : wassersteinSubdifferential φ μ ↦ ‖0 - w.1‖)
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ ⟨ζ, hζ⟩
    simp only [zero_sub, norm_neg] at hmin this
    exact hmin ▸ this
  refine ⟨ξ, ⟨hξ, hle⟩, fun ξ' ⟨hξ', hle'⟩ ↦ ?_⟩
  -- Two minimizers have a midpoint in the subdifferential, so the parallelogram law forces them
  -- to coincide.
  have hm := hle _ (convex_wassersteinSubdifferential φ μ hξ' hξ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [← smul_add, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hm
  have h₁ := hle' ξ hξ
  have h₂ := hle ξ' hξ'
  have hpar := parallelogram_law_with_norm ℝ ξ' ξ
  rw [← sub_eq_zero, ← norm_eq_zero]
  nlinarith [norm_nonneg (ξ' - ξ), norm_nonneg (ξ' + ξ), norm_nonneg ξ]

/-- **The slope is at most the norm of a subgradient.** If `ξ ∈ ∂φ(μ)`, then the descending slope
of `φ` at `μ` is at most `‖ξ‖`. -/
theorem descendingSlope_le_of_mem_wassersteinSubdifferential
    (hξ : ξ ∈ wassersteinSubdifferential φ μ) : descendingSlope φ μ ≤ ‖ξ‖ₑ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ descendingSlope_le_of_eventually_le ?_
  filter_upwards [nhdsWithin_le_nhds (hξ.2.2 ε (NNReal.coe_pos.2 hε))] with ν hν
  obtain ⟨γ, hγ⟩ := exists_isOptimalCoupling_edist_rpow ((μ : ProbabilityMeasure E) : Measure E)
    ((ν : ProbabilityMeasure E) : Measure E) 2
  have h := hν γ hγ
  have hA := abs_le.1 (hγ.abs_integral_inner_le ξ)
  set A := ∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ μ = r := ⟨(φ μ).toReal, (EReal.coe_toReal hξ.2.1 hξ.1).symm⟩
  rw [hr, ← EReal.coe_add] at h
  -- The energy drops by at most `ε W₂(μ, ν) - A ≤ (‖ξ‖ + ε) W₂(μ, ν)`.
  have hdrop : φ μ - φ ν ≤ (((‖ξ‖ + ε) * dist μ ν : ℝ) : EReal) := by
    rw [hr]
    refine (EReal.sub_le_sub le_rfl h).trans ?_
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    nlinarith
  refine (EReal.toENNReal_le_toENNReal hdrop).trans_eq ?_
  rw [EReal.real_coe_toENNReal, ENNReal.ofReal_mul (by positivity), edist_dist,
    ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg, ofReal_norm, ENNReal.ofReal_coe_nnreal]

/-- **A global subgradient inequality gives a subgradient.** If `φ μ` is finite and, for some
`m : ℝ`, `φ ν ≥ φ μ + ∫ ⟪ξ x, y - x⟫ dγ + (m / 2) W₂(μ, ν)²` for every law `ν` and every optimal
coupling `γ` of `μ` and `ν`, then `ξ ∈ ∂φ(μ)`. -/
theorem mem_wassersteinSubdifferential_of_forall_le {m : ℝ} (hbot : φ μ ≠ ⊥) (htop : φ μ ≠ ⊤)
    (h : ∀ (ν : WassersteinSpace 2 E) (γ : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) γ
        ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
      φ μ + ((∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ + m / 2 * dist μ ν ^ 2 : ℝ) : EReal) ≤ φ ν) :
    ξ ∈ wassersteinSubdifferential φ μ := by
  refine ⟨hbot, htop, fun ε hε ↦ ?_⟩
  filter_upwards [Metric.ball_mem_nhds μ (show 0 < 2 * ε / (|m| + 1) by positivity)]
    with ν hν γ hγ
  refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) (h ν γ hγ)
  -- Near `μ` the quadratic term is at least `-ε W₂(μ, ν)`.
  rw [Metric.mem_ball, dist_comm, lt_div_iff₀ (by positivity)] at hν
  have hd := dist_nonneg (x := μ) (y := ν)
  have hm : |m| * dist μ ν ≤ 2 * ε := by nlinarith
  nlinarith [neg_abs_le m, mul_le_mul_of_nonneg_right hm hd]

/-- The real inequality behind the subgradient inequality along geodesics: if for every `ε > 0`
some `t ∈ (0, min 1 ε]` satisfies `r + t A - ε t d ≤ (1 - t) r + t s - (m / 2) t (1 - t) d²`, then
`r + A + (m / 2) d² ≤ s`. -/
private theorem add_add_le_of_forall_exists_le {r s A d m : ℝ} (hd : 0 ≤ d)
    (h : ∀ ε > 0, ∃ t ∈ Ioc (0 : ℝ) 1, t ≤ ε ∧
      r + (t * A - ε * (t * d)) ≤ (1 - t) * r + t * s - m / 2 * t * (1 - t) * d ^ 2) :
    r + (A + m / 2 * d ^ 2) ≤ s := by
  have hK : 0 < d + |m| * d ^ 2 + 1 := by positivity
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  obtain ⟨t, ht, htε, hts⟩ := h (η / (d + |m| * d ^ 2 + 1)) (by positivity)
  set ε := η / (d + |m| * d ^ 2 + 1)
  have hεK : ε * (d + |m| * d ^ 2 + 1) = η := div_mul_cancel₀ η hK.ne'
  -- After division by `t > 0`: `A - ε d ≤ s - r - (m / 2) (1 - t) d²`.
  have hdiv : A - ε * d ≤ s - r - m / 2 * (1 - t) * d ^ 2 := by
    have : t * (A - ε * d) ≤ t * (s - r - m / 2 * (1 - t) * d ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this ht.1
  have hmt : m / 2 * t * d ^ 2 ≤ |m| * ε * d ^ 2 := by
    have h₁ : m ≤ |m| := le_abs_self m
    have h₂ : 0 ≤ t * d ^ 2 := mul_nonneg ht.1.le (sq_nonneg d)
    have h₃ : t * d ^ 2 ≤ ε * d ^ 2 := mul_le_mul_of_nonneg_right htε (sq_nonneg d)
    nlinarith [abs_nonneg m]
  nlinarith [abs_nonneg m, sq_nonneg d]

/-- Let `c` be the interpolation of an optimal coupling `γ` of `μ` and `ν`, joined to `μ` by the
optimal couplings `(x, (1 - t) • x + t • y)₊ γ`. If `ξ ∈ ∂φ(μ)`, then for every `ε > 0` the
subgradient inequality with error `ε W₂` holds at some `c t` with `0 < t ≤ min 1 ε`. -/
private theorem exists_le_apply_of_mem_wassersteinSubdifferential {ν : WassersteinSpace 2 E}
    {γ : Measure (E × E)} {c : ℝ → WassersteinSpace 2 E}
    (hξ : ξ ∈ wassersteinSubdifferential φ μ) (hc : IsGeodesicSegment c μ ν)
    (hopt : ∀ t ∈ Icc (0 : ℝ) 1, IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ))
      (γ.map fun z ↦ (z.1, (1 - t) • z.1 + t • z.2))
      ((μ : ProbabilityMeasure E) : Measure E) ((c t : ProbabilityMeasure E) : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioc (0 : ℝ) 1, t ≤ ε ∧
      φ μ + ((t * ∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ - ε * (t * dist μ ν) : ℝ) : EReal) ≤ φ (c t) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hξ.2.2 ε hε)
  set d := dist μ ν
  set t := min (min 1 ε) (δ / (d + 1)) / 2
  have hd : 0 ≤ d := dist_nonneg
  have ht₀ : 0 < t := by positivity
  have ht₁ : t ≤ min (min 1 ε) (δ / (d + 1)) := half_le_self (by positivity)
  have htd : t * d < δ := by
    have h₁ : t ≤ δ / (d + 1) := ht₁.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h₁
    nlinarith
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht₀.le, ht₁.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  refine ⟨t, ⟨ht₀, ht.2⟩, ht₁.trans ((min_le_left _ _).trans (min_le_right _ _)), ?_⟩
  have hdist : dist μ (c t) = t * d := hc.dist_source_apply ht
  have := hball (by rwa [dist_comm, hdist]) _ (hopt t ht)
  rwa [(hopt t ht).toIsCoupling.integral_inner_map_smul_add_smul, hdist] at this

/-- **Subgradients of energies convex along geodesics.** If `φ` is `m`-convex along geodesics of
`P₂(E)` and `φ μ` is finite, then `ξ ∈ ∂φ(μ)` exactly when
`φ ν ≥ φ μ + ∫ ⟪ξ x, y - x⟫ dγ + (m / 2) W₂(μ, ν)²` for every law `ν` and every optimal coupling
`γ` of `μ` and `ν`. -/
theorem ConvexAlongGeodesics.mem_wassersteinSubdifferential_iff {m : ℝ}
    (hφ : ConvexAlongGeodesics m φ) (hbot : φ μ ≠ ⊥) (htop : φ μ ≠ ⊤) :
    ξ ∈ wassersteinSubdifferential φ μ ↔ ∀ (ν : WassersteinSpace 2 E) (γ : Measure (E × E)),
      IsOptimalCoupling (fun z : E × E ↦ edist z.1 z.2 ^ (2 : ℝ)) γ
        ((μ : ProbabilityMeasure E) : Measure E) ((ν : ProbabilityMeasure E) : Measure E) →
      φ μ + ((∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ + m / 2 * dist μ ν ^ 2 : ℝ) : EReal) ≤ φ ν := by
  refine ⟨fun hξ ν γ hγ ↦ ?_, mem_wassersteinSubdifferential_of_forall_le hbot htop⟩
  by_cases hν : φ ν = ⊤
  · rw [hν]
    exact le_top
  obtain ⟨c, hc, hopt⟩ := WassersteinSpace.exists_isGeodesicSegment_isOptimalCoupling hγ
  have hconv := hc.convexAlong_iff.1 (convexAlongGeodesics_def.1 hφ htop hν hc)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ μ = r := ⟨(φ μ).toReal, (EReal.coe_toReal htop hbot).symm⟩
  -- The convexity inequality along `μ_t` rules out `φ ν = ⊥`.
  obtain ⟨s, hs⟩ : ∃ s : ℝ, φ ν = s := by
    refine ⟨(φ ν).toReal, (EReal.coe_toReal hν fun hbot' ↦ ?_).symm⟩
    obtain ⟨t, ht, -, hlow⟩ := exists_le_apply_of_mem_wassersteinSubdifferential hξ hc hopt one_pos
    have hup := hconv t ⟨ht.1.le, ht.2⟩
    rw [hbot', EReal.coe_mul_bot_of_pos ht.1, EReal.add_bot, EReal.bot_sub] at hup
    rw [hr, ← EReal.coe_add] at hlow
    exact EReal.coe_ne_bot _ (le_bot_iff.1 (hlow.trans hup))
  -- Comparing the subgradient and convexity inequalities at `μ_t` and letting `ε → 0` gives the
  -- global inequality.
  rw [hr, hs, ← EReal.coe_add]
  refine EReal.coe_le_coe_iff.2 (add_add_le_of_forall_exists_le dist_nonneg fun ε hε ↦ ?_)
  obtain ⟨t, ht, htε, hlow⟩ := exists_le_apply_of_mem_wassersteinSubdifferential hξ hc hopt hε
  have hup := hconv t ⟨ht.1.le, ht.2⟩
  rw [hr, ← EReal.coe_add] at hlow
  rw [hr, hs, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub] at hup
  exact ⟨t, ht, htε, EReal.coe_le_coe_iff.1 (hlow.trans hup)⟩

section PotentialEnergy

variable {V : E → ℝ} {m C : ℝ}

/-- **The gradient of a strongly convex potential is a subgradient of its potential energy.** Let
`V` be a differentiable `m`-strongly convex potential whose gradient grows at most linearly,
`‖∇V x‖ ≤ C (1 + ‖x‖)`. At every law `μ` of `P₂(E)`, every field `ξ ∈ L²(μ; E)` equal to `∇V`
almost everywhere is a subgradient of the potential energy `ν ↦ ∫ V dν`. -/
theorem _root_.StrongConvexOn.mem_wassersteinSubdifferential_potentialEnergy
    (hV : StrongConvexOn univ m V) (hVd : Differentiable ℝ V)
    (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖))
    (hξ : ξ =ᵐ[((μ : ProbabilityMeasure E) : Measure E)] gradient V) :
    ξ ∈ wassersteinSubdifferential
      (fun ν : WassersteinSpace 2 E ↦ potentialEnergy V ((ν : ProbabilityMeasure E) : Measure E))
      μ := by
  have hint (ρ : WassersteinSpace 2 E) : Integrable V ((ρ : ProbabilityMeasure E) : Measure E) :=
    integrable_comp_of_norm_gradient_le hVd hV' ρ.hasFiniteMoment.memLp_id
  have hφ (ρ : WassersteinSpace 2 E) : potentialEnergy V ((ρ : ProbabilityMeasure E) : Measure E) =
      ((∫ x, V x ∂((ρ : ProbabilityMeasure E) : Measure E) : ℝ) : EReal) :=
    potentialEnergy_of_integrable (hint ρ)
  refine mem_wassersteinSubdifferential_of_forall_le (m := m) (by simp [hφ]) (by simp [hφ])
    fun ν γ hγ ↦ ?_
  simp only [hφ, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hγc := hγ.toIsCoupling
  have : IsProbabilityMeasure γ := hγ.isProbabilityMeasure
  have hγ₂ := integrable_norm_sub_sq_of_hasFiniteMoment (hγc.fst_eq ▸ μ.hasFiniteMoment)
    (hγc.snd_eq ▸ ν.hasFiniteMoment)
  have hgrad : MemLp (gradient V) 2 ((μ : ProbabilityMeasure E) : Measure E) :=
    (Lp.memLp ξ).ae_eq hξ
  -- Replace `ξ` by `∇V`, and every term by an integral against `γ`.
  have hpair : ∫ z, ⟪ξ z.1, z.2 - z.1⟫ ∂γ = ∫ z, ⟪gradient V z.1, z.2 - z.1⟫ ∂γ := by
    refine integral_congr_ae ?_
    filter_upwards [hγc.measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp hξ] with z hz
    simp only [Function.comp_apply] at hz
    rw [hz]
  have hinner : Integrable (fun z : E × E ↦ ⟪gradient V z.1, z.2 - z.1⟫) γ := by
    refine (hγc.integrable_inner_sub_comp_fst hγ₂ hgrad).neg.congr (.of_forall fun z ↦ ?_)
    rw [Pi.neg_apply, ← inner_neg_left, neg_sub, real_inner_comm]
  have h₁ : Integrable (fun z : E × E ↦ V z.1) γ := hγc.integrable_comp_fst (hint μ)
  have h₂ : Integrable (fun z : E × E ↦
      ⟪gradient V z.1, z.2 - z.1⟫ + m / 2 * ‖z.1 - z.2‖ ^ 2) γ :=
    hinner.add (hγ₂.const_mul _)
  have hsum : ∫ z, (V z.1 + (⟪gradient V z.1, z.2 - z.1⟫ + m / 2 * ‖z.1 - z.2‖ ^ 2)) ∂γ =
      ∫ z, V z.1 ∂γ + (∫ z, ⟪gradient V z.1, z.2 - z.1⟫ ∂γ +
        m / 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂γ) := by
    rw [integral_add h₁ h₂, integral_add hinner (hγ₂.const_mul _), integral_const_mul]
  rw [hpair, ← hγc.integral_comp_fst (hint μ).aestronglyMeasurable,
    ← hγc.integral_comp_snd (hint ν).aestronglyMeasurable,
    WassersteinSpace.dist_sq_eq_integral hγ, ← hsum]
  refine integral_mono (h₁.add h₂)
    (hγc.integrable_comp_snd (hint ν)) fun z ↦ ?_
  -- The first-order condition of strong convexity, at `z.1` towards `z.2`.
  have := hV.add_add_le_of_hasFDerivWithinAt (mem_univ z.1) (mem_univ z.2)
    (hVd z.1).hasFDerivAt.hasFDerivWithinAt
  rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply,
    norm_sub_rev] at this
  simpa only [Pi.add_apply, add_assoc] using this

/-- The potential energy of a differentiable `m`-strongly convex potential whose gradient grows at
most linearly has a nonempty Wasserstein subdifferential at every law of `P₂(E)`: it contains the
class of `∇V` in `L²(μ; E)`. -/
theorem _root_.StrongConvexOn.nonempty_wassersteinSubdifferential_potentialEnergy
    (hV : StrongConvexOn univ m V) (hVd : Differentiable ℝ V)
    (hV' : ∀ x, ‖gradient V x‖ ≤ C * (1 + ‖x‖)) (μ : WassersteinSpace 2 E) :
    (wassersteinSubdifferential
      (fun ν : WassersteinSpace 2 E ↦ potentialEnergy V ((ν : ProbabilityMeasure E) : Measure E))
      μ).Nonempty := by
  have hm : Measurable (gradient V) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ V)
  have hnorm : MemLp (fun x : E ↦ ‖x‖) 2 ((μ : ProbabilityMeasure E) : Measure E) :=
    μ.hasFiniteMoment.memLp_id.norm
  have hbound : MemLp (fun x : E ↦ C * (1 + ‖x‖)) 2 ((μ : ProbabilityMeasure E) : Measure E) :=
    ((memLp_const (1 : ℝ)).add hnorm).const_mul C
  have hgrad : MemLp (gradient V) 2 ((μ : ProbabilityMeasure E) : Measure E) := by
    refine hbound.of_le hm.aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (hV' x).trans (le_abs_self _)
  exact ⟨hgrad.toLp _, hV.mem_wassersteinSubdifferential_potentialEnergy hVd hV'
    hgrad.coeFn_toLp⟩

end PotentialEnergy

end TauCeti
