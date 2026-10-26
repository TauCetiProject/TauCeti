/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement
public import TauCeti.Topology.MetricSpace.CBBZero
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# The quantile isometry of the one-dimensional Wasserstein space

A probability law `μ` on `ℝ` is the law of its quantile function `Q_μ` under the uniform law on
`(0, 1)`, and for every exponent `1 ≤ p ≤ ∞` the `p`-Wasserstein distance of two real laws is the
`Lᵖ(0, 1)` distance of their quantile functions
(`TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub`). This file reads that formula as a statement
about the Wasserstein space `P_p(ℝ)`. A law has finite `p`-th moment exactly when its quantile
function lies in `Lᵖ(0, 1)`, so `μ ↦ Q_μ` is a map

`TauCeti.WassersteinSpace.quantileLp : P_p(ℝ) → Lᵖ(0, 1)`,

and it is an isometry. Its image is the cone of classes of nondecreasing functions: every
nondecreasing function of `Lᵖ(0, 1)` is, almost everywhere, the quantile function of the law into
which it pushes the uniform law. So `P_p(ℝ)` is isometric to the set of nondecreasing classes of
`Lᵖ(0, 1)`, with no density or moment assumption beyond the one defining `P_p(ℝ)`.

For `p = 2` the target `L²(0, 1)` is a Hilbert space, and the isometry makes `P₂(ℝ)` flat: it is
both a CAT(0) space and a space of nonnegative curvature in the sense of Alexandrov, so along every
geodesic segment `t ↦ μ_t` of `P₂(ℝ)` the squared distance from any law `σ` is exactly the Euclidean
expression
`W₂(σ, μ_t)² = (1 - t) W₂(σ, μ₀)² + t W₂(σ, μ₁)² - t (1 - t) W₂(μ₀, μ₁)²`
(`TauCeti.IsGeodesicSegment.dist_sq_eq`).

## Main definitions

* `TauCeti.WassersteinSpace.quantileLp` — the quantile function of a law of `P_p(ℝ)`, as an
  element of `Lᵖ(0, 1)`.

## Main statements

* `TauCeti.hasFiniteMoment_iff_memLp_quantile` — a real law has finite `p`-th moment exactly when
  its quantile function lies in `Lᵖ(0, 1)`.
* `TauCeti.WassersteinSpace.isometry_quantileLp` — the quantile map is an isometry from `P_p(ℝ)`
  into `Lᵖ(0, 1)`.
* `TauCeti.WassersteinSpace.range_quantileLp` — its image consists of the classes of the
  nondecreasing functions on `(0, 1)`.
* `TauCeti.WassersteinSpace.instIsCATZeroSpace` and `TauCeti.WassersteinSpace.instIsCBBZeroSpace`
  — `P₂(ℝ)` is CAT(0) and CBB(0).

## References

* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2, for the
  quantile description of one-dimensional transport.
* B. Kloeckner, *A geometric study of Wasserstein spaces: Euclidean spaces*, Ann. Sc. Norm.
  Super. Pisa Cl. Sci. (5) 9 (2010), 297--323, where `P₂(ℝ)` is identified with a convex subset of
  `L²(0, 1)`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {p : ℝ≥0∞}

/-- **Finite moments are integrable quantiles.** A real probability law has finite `p`-th moment
exactly when its quantile function lies in `Lᵖ(0, 1)`. At `p = ∞` both sides say that the law has
bounded support. -/
theorem hasFiniteMoment_iff_memLp_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasFiniteMoment p μ ↔ MemLp μ.quantile p (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hQ := Measure.measurable_quantile μ
  conv_lhs => rw [← Measure.map_quantile_volume_Ioo μ]
  rw [hasFiniteMoment_map_iff_memLp_edist hQ.aemeasurable 0]
  exact memLp_congr_enorm (hQ.edist measurable_const).aestronglyMeasurable hQ.aestronglyMeasurable
    (.of_forall fun t ↦ by simp [edist_eq_enorm_sub])

namespace WassersteinSpace

/-- The **quantile map** of the one-dimensional Wasserstein space: a law of `P_p(ℝ)`, sent to its
quantile function as an element of `Lᵖ(0, 1)`. It is an isometry for `1 ≤ p`
(`TauCeti.WassersteinSpace.isometry_quantileLp`). -/
def quantileLp (μ : WassersteinSpace p ℝ) : Lp ℝ p (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ((hasFiniteMoment_iff_memLp_quantile _).1 μ.hasFiniteMoment).toLp _

/-- The quantile map sends a law to the class of its quantile function. -/
theorem coeFn_quantileLp (μ : WassersteinSpace p ℝ) :
    quantileLp μ =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      ((μ : ProbabilityMeasure ℝ) : Measure ℝ).quantile :=
  MemLp.coeFn_toLp _

/-- The image of the quantile map is the set of classes of nondecreasing functions on `(0, 1)`:
a nondecreasing function of `Lᵖ(0, 1)` is almost everywhere the quantile function of the law into
which it pushes the uniform law. -/
theorem range_quantileLp :
    range (quantileLp : WassersteinSpace p ℝ → Lp ℝ p (volume.restrict (Ioo (0 : ℝ) 1))) =
      {f : Lp ℝ p (volume.restrict (Ioo (0 : ℝ) 1)) |
        ∃ g : ℝ → ℝ, MonotoneOn g (Ioo 0 1) ∧ f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g} := by
  ext f
  refine ⟨?_, fun ⟨g, hg, hfg⟩ ↦ ?_⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨_, Measure.monotoneOn_quantile _, coeFn_quantileLp μ⟩
  have hU : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  obtain ⟨ν, hν⟩ := exists_coe_eq_map_of_memLp (ν := ⟨_, hU⟩) ((Lp.memLp f).ae_eq hfg)
  refine ⟨ν, Lp.ext ?_⟩
  filter_upwards [coeFn_quantileLp ν, Measure.quantile_map_volume_Ioo_ae hg, hfg] with t hν' hg' hf
  rw [hν', hν, hf]
  exact hg'

variable [Fact (1 ≤ p)]

/-- The quantile map preserves the extended distance: the `p`-Wasserstein distance of two laws on
`ℝ` is the `Lᵖ(0, 1)` distance of their quantile functions. -/
@[simp]
theorem edist_quantileLp (μ ν : WassersteinSpace p ℝ) :
    edist (quantileLp μ) (quantileLp ν) = edist μ ν := by
  rw [Lp.edist_def, edist_def, wassersteinEDist_eq_eLpNorm_quantile_sub Fact.out]
  exact eLpNorm_congr_ae ((coeFn_quantileLp μ).sub (coeFn_quantileLp ν))

/-- **The quantile isometry.** For `1 ≤ p ≤ ∞`, sending a law to its quantile function is an
isometry from the Wasserstein space `P_p(ℝ)` into `Lᵖ(0, 1)`. -/
theorem isometry_quantileLp :
    Isometry (quantileLp : WassersteinSpace p ℝ → Lp ℝ p (volume.restrict (Ioo (0 : ℝ) 1))) :=
  edist_quantileLp

/-- The quantile map preserves the distance: the `p`-Wasserstein distance of two laws on `ℝ` is
the `Lᵖ(0, 1)` distance of their quantile functions. -/
@[simp]
theorem dist_quantileLp (μ ν : WassersteinSpace p ℝ) :
    dist (quantileLp μ) (quantileLp ν) = dist μ ν :=
  isometry_quantileLp.dist_eq μ ν

/-- **`P₂(ℝ)` is CAT(0).** The quadratic Wasserstein space of the line is a geodesic space that
embeds isometrically in the Hilbert space `L²(0, 1)`, so it satisfies the CN inequality. -/
instance instIsCATZeroSpace : IsCATZeroSpace (WassersteinSpace 2 ℝ) :=
  IsCATZeroSpace.of_isometry isometry_quantileLp

/-- **`P₂(ℝ)` is CBB(0).** The quadratic Wasserstein space of the line is a geodesic space that
embeds isometrically in the Hilbert space `L²(0, 1)`, so it satisfies the reverse CN inequality.
With `TauCeti.WassersteinSpace.instIsCATZeroSpace` this makes its geodesic triangles flat
(`TauCeti.IsGeodesicSegment.dist_sq_eq`). -/
instance instIsCBBZeroSpace : IsCBBZeroSpace (WassersteinSpace 2 ℝ) :=
  IsCBBZeroSpace.of_isometry isometry_quantileLp

end WassersteinSpace

end TauCeti
