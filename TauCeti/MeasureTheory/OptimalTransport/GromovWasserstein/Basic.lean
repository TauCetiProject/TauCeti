/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import TauCeti.MeasureTheory.OptimalTransport.Coupling
public import TauCeti.MeasureTheory.OptimalTransport.Gluing

/-!
# The Gromov–Wasserstein distance of measured kernels

A *measured kernel* is a triple `(X, μ, ω)`: a measurable space `X`, a measure `μ` on it, and a
kernel `ω : X × X → Z` with values in an extended metric space `Z`. A metric-measure space is the
special case `Z = ℝ` and `ω (x, x') = dist x x'`. Two measured kernels living on different spaces
cannot be compared pointwise; the Gromov–Wasserstein distance compares them through a coupling
`π` of `μ` and `ν`, measuring how badly `π` distorts the two kernels. For an exponent
`p : ℝ≥0∞` the **distortion** of `π` is the `L^p (π ⊗ π)` seminorm

`dis_p (π) = ‖(x, y), (x', y') ↦ edist (ωX (x, x')) (ωY (y, y'))‖_{L^p (π ⊗ π)}`,

and the **`p`-Gromov–Wasserstein distance** is its infimum over the couplings of `μ` and `ν`.
This file defines both, with no factor `1 / 2`, and proves that the Gromov–Wasserstein distance
is an extended pseudodistance on measured kernels: it vanishes from a kernel to itself, it is
symmetric, and for `1 ≤ p` it satisfies the triangle inequality.

As for `TauCeti.wassersteinEDist`, the objective is an `eLpNorm`, so the exponent `p = ∞` is a case
of the definition: there the distortion is the `π ⊗ π`-essential supremum of the kernel
discrepancy. For `0 < p < ∞` the `p`-th power of the distance is the infimum of the integrals
`∫∫ edist (ωX (x, x')) (ωY (y, y')) ^ p d(π ⊗ π)`.

The kernels are only assumed almost-everywhere strongly measurable, `AEStronglyMeasurable ωX
(μ.prod μ)`: this gives the kernel an essentially separable range, so no separability, completeness
or measurable structure is required of the target `Z`, and no topology is required of `X`. The
measures are raw `MeasureTheory.Measure`s, as for the Wasserstein distance; the theorems take the
finiteness instances they use.

## Main definitions

* `TauCeti.gromovWassersteinDistortion p ωX ωY π` — the `L^p (π ⊗ π)` seminorm of
  `edist (ωX (x, x')) (ωY (y, y'))`.
* `TauCeti.gromovWassersteinEDist p μ ωX ν ωY` — the infimum of the distortion over the couplings
  `π` of `μ` and `ν`.

## Main statements

* `TauCeti.gromovWassersteinEDist_le`, `TauCeti.le_gromovWassersteinEDist` and
  `TauCeti.gromovWassersteinEDist_lt_iff` — the universal property of the infimum;
* `TauCeti.gromovWassersteinDistortion_map_prodMk` — the distortion of the plan
  `(f, g)_# γ` induced by two measure-preserving parametrizations `f`, `g` of the marginals, read
  on `γ ⊗ γ`, with `TauCeti.gromovWassersteinEDist_le_eLpNorm` the resulting bound on the distance;
* `TauCeti.gromovWassersteinEDist_rpow` and `TauCeti.gromovWassersteinEDist_top` — the
  integral-of-a-power formula for `0 < p < ∞` and the essential-supremum formula for `p = ∞`;
* `TauCeti.gromovWassersteinDistortion_congr_ae` and `TauCeti.gromovWassersteinEDist_congr_ae` —
  invariance under almost-everywhere modification of the kernels;
* `TauCeti.gromovWassersteinEDist_comp_prodMap_eq_zero` — a measured kernel and its pullback along
  a measure-preserving map are at distance `0`;
* `TauCeti.gromovWassersteinEDist_self`, `TauCeti.gromovWassersteinEDist_comm` and
  `TauCeti.gromovWassersteinEDist_triangle` — the axioms of an extended pseudodistance, the
  triangle inequality for a standard Borel third carrier, from the general form
  `TauCeti.gromovWassersteinEDist_triangle_of_exists_glue` for any carriers along which the two
  couplings glue;
* `TauCeti.gromovWassersteinEDist_dirac_left` and `TauCeti.gromovWassersteinEDist_dirac_right` —
  the distance to a one-point measured kernel `({y}, δ_y, ω)` is the `L^p (μ ⊗ μ)` size
  `‖edist (ωX ·) (ω (y, y))‖_{L^p (μ ⊗ μ)}` of `ωX` about the point `ω (y, y)`.

## Implementation notes

The distance is an iterated `⨅` over plans and over proofs of `TauCeti.IsCoupling`, matching
`TauCeti.wassersteinEDist`: two measures with no coupling, for instance finite measures of
different total mass, are at distance `∞`.

The distance is not a metric on measured kernels, only an extended pseudometric: a kernel and its
pullback along a measure-preserving map are at distance `0`
(`TauCeti.gromovWassersteinEDist_comp_prodMap_eq_zero`), and so are two kernels agreeing almost
everywhere.

Some sources, among them Bauer, Mémoli, Needham and Nishino, put a factor `1 / 2` in front of the
infimum; the distance here is twice theirs.

## References

* F. Mémoli, *Gromov–Wasserstein distances and the metric approach to object matching*, Found.
  Comput. Math. 11 (2011), where the distance is defined on metric-measure spaces as an infimum
  of distortions over couplings and the triangle inequality is proved by gluing.
* K.-T. Sturm, *The space of spaces: curvature bounds and gradient flows on the space of metric
  measure spaces*, Mem. Amer. Math. Soc. 290 (2023).
* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*, J. Mach.
  Learn. Res. 26 (2025), for kernels with values in a general metric space `Z`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y W Ω Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MeasurableSpace Ω] {p : ℝ≥0∞} {a : ℝ≥0∞}

section EDist

variable [EDist Z] {μ : Measure X} {ν : Measure Y} {ωX : X × X → Z} {ωY : Y × Y → Z}
  {π : Measure (X × Y)}

/-- The **`p`-distortion** of a plan `π` on `X × Y` between the kernels `ωX` and `ωY`: the
`L^p (π ⊗ π)` seminorm of the kernel discrepancy
`((x, y), (x', y')) ↦ edist (ωX (x, x')) (ωY (y, y'))`. -/
def gromovWassersteinDistortion (p : ℝ≥0∞) (ωX : X × X → Z) (ωY : Y × Y → Z)
    (π : Measure (X × Y)) : ℝ≥0∞ :=
  eLpNorm (fun q : (X × Y) × (X × Y) ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) p
    (π.prod π)

theorem gromovWassersteinDistortion_def (p : ℝ≥0∞) (ωX : X × X → Z) (ωY : Y × Y → Z)
    (π : Measure (X × Y)) :
    gromovWassersteinDistortion p ωX ωY π =
      eLpNorm (fun q : (X × Y) × (X × Y) ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) p
        (π.prod π) :=
  (rfl)

/-- The **`p`-Gromov–Wasserstein distance** of the measured kernels `(X, μ, ωX)` and
`(Y, ν, ωY)`: the infimum, over the couplings `π` of `μ` and `ν`, of the distortion
`TauCeti.gromovWassersteinDistortion p ωX ωY π`.

It is `∞` when `μ` and `ν` have no coupling at all. No factor `1 / 2` is included. -/
def gromovWassersteinEDist (p : ℝ≥0∞) (μ : Measure X) (ωX : X × X → Z) (ν : Measure Y)
    (ωY : Y × Y → Z) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), gromovWassersteinDistortion p ωX ωY π

theorem gromovWassersteinEDist_def (p : ℝ≥0∞) (μ : Measure X) (ωX : X × X → Z) (ν : Measure Y)
    (ωY : Y × Y → Z) :
    gromovWassersteinEDist p μ ωX ν ωY =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), gromovWassersteinDistortion p ωX ωY π :=
  (rfl)

/-- Every coupling bounds the Gromov–Wasserstein distance from above by its distortion. -/
theorem gromovWassersteinEDist_le (hπ : IsCoupling π μ ν) (p : ℝ≥0∞) (ωX : X × X → Z)
    (ωY : Y × Y → Z) :
    gromovWassersteinEDist p μ ωX ν ωY ≤ gromovWassersteinDistortion p ωX ωY π :=
  iInf₂_le π hπ

/-- A bound valid on the distortion of every coupling bounds the Gromov–Wasserstein distance
from below. -/
theorem le_gromovWassersteinEDist
    (h : ∀ π, IsCoupling π μ ν → a ≤ gromovWassersteinDistortion p ωX ωY π) :
    a ≤ gromovWassersteinEDist p μ ωX ν ωY :=
  le_iInf₂ h

/-- The Gromov–Wasserstein distance is below a threshold exactly when the distortion of some
coupling is. -/
theorem gromovWassersteinEDist_lt_iff :
    gromovWassersteinEDist p μ ωX ν ωY < a ↔
      ∃ π, IsCoupling π μ ν ∧ gromovWassersteinDistortion p ωX ωY π < a := by
  simp only [gromovWassersteinEDist_def, iInf_lt_iff, exists_prop]

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace Z] {μ : Measure X} {ν : Measure Y} {ρ : Measure W}
  {ωX ωX' : X × X → Z} {ωY ωY' : Y × Y → Z} {ωW : W × W → Z} {π : Measure (X × Y)}

/-- Kernels reparametrized by two measure-preserving maps out of a common space `(Ω, γ)` give an
almost-everywhere strongly measurable discrepancy on `γ ⊗ γ`. -/
theorem aestronglyMeasurable_edist_comp {γ : Measure Ω} [SFinite γ] {f : Ω → X}
    {g : Ω → Y} (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    AEStronglyMeasurable (fun q : Ω × Ω ↦ edist (ωX (f q.1, f q.2)) (ωY (g q.1, g q.2)))
      (γ.prod γ) :=
  continuous_edist.comp_aestronglyMeasurable₂
    (hωX.comp_quasiMeasurePreserving (hf.prod hf).quasiMeasurePreserving)
    (hωY.comp_quasiMeasurePreserving (hg.prod hg).quasiMeasurePreserving)

/-- The kernel discrepancy integrated in the distortion of a coupling is almost-everywhere
strongly measurable for the square of the coupling. -/
theorem IsCoupling.aestronglyMeasurable_edist [SFinite π] (hπ : IsCoupling π μ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    AEStronglyMeasurable
      (fun q : (X × Y) × (X × Y) ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) (π.prod π) :=
  aestronglyMeasurable_edist_comp hπ.measurePreserving_fst hπ.measurePreserving_snd
    hωX hωY

/-- **Distortion of a parametrized plan.** If `f` and `g` push a measure `γ` on `Ω` forward to
`μ` and `ν`, the plan `(f, g)_# γ` couples them, and its distortion is the `L^p (γ ⊗ γ)` seminorm
of the discrepancy of the two pulled-back kernels. -/
theorem gromovWassersteinDistortion_map_prodMk {γ : Measure Ω} [SFinite γ] {f : Ω → X}
    {g : Ω → Y} (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (p : ℝ≥0∞) :
    gromovWassersteinDistortion p ωX ωY (γ.map fun w ↦ (f w, g w)) =
      eLpNorm (fun q : Ω × Ω ↦ edist (ωX (f q.1, f q.2)) (ωY (g q.1, g q.2))) p (γ.prod γ) := by
  have hfg : Measurable fun w ↦ (f w, g w) := hf.measurable.prodMk hg.measurable
  have hmeas :=
    (isCoupling_map_prodMk_of_measurePreserving hf hg).aestronglyMeasurable_edist hωX hωY
  rw [Measure.map_prod_map γ γ hfg hfg] at hmeas
  rw [gromovWassersteinDistortion_def, Measure.map_prod_map γ γ hfg hfg,
    eLpNorm_map_measure hmeas (hfg.prodMap hfg).aemeasurable]
  rfl

/-- **The common-parametrization bound.** If `f` and `g` push a measure `γ` on `Ω` forward to `μ`
and `ν`, the Gromov–Wasserstein distance of `(X, μ, ωX)` and `(Y, ν, ωY)` is at most the
`L^p (γ ⊗ γ)` seminorm of the discrepancy of the pulled-back kernels. -/
theorem gromovWassersteinEDist_le_eLpNorm {γ : Measure Ω} [SFinite γ] {f : Ω → X} {g : Ω → Y}
    (hf : MeasurePreserving f γ μ) (hg : MeasurePreserving g γ ν)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ ωX ν ωY ≤
      eLpNorm (fun q : Ω × Ω ↦ edist (ωX (f q.1, f q.2)) (ωY (g q.1, g q.2))) p (γ.prod γ) := by
  rw [← gromovWassersteinDistortion_map_prodMk hf hg hωX hωY]
  exact gromovWassersteinEDist_le (isCoupling_map_prodMk_of_measurePreserving hf hg) p ωX ωY

/-- For `0 < p < ∞`, the `p`-th power of the Gromov–Wasserstein distance is the infimum over
couplings `π` of `∫∫ edist (ωX (x, x')) (ωY (y, y')) ^ p d(π ⊗ π)`. -/
theorem gromovWassersteinEDist_rpow (hp0 : p ≠ 0) (hp : p ≠ ∞) [IsFiniteMeasure μ]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    gromovWassersteinEDist p μ ωX ν ωY ^ p.toReal =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        ∫⁻ q, edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)) ^ p.toReal ∂(π.prod π) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [gromovWassersteinEDist_def, ← ENNReal.orderIsoRpow_apply p.toReal hr,
    OrderIso.map_iInf]
  refine iInf_congr fun π ↦ ?_
  rw [OrderIso.map_iInf]
  refine iInf_congr fun hπ ↦ ?_
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  rw [ENNReal.orderIsoRpow_apply, gromovWassersteinDistortion_def,
    eLpNorm_rpow_eq_lintegral hp0 hp (hπ.aestronglyMeasurable_edist hωX hωY).aemeasurable]

/-- At exponent `∞`, the Gromov–Wasserstein distance is the infimum over couplings `π` of the
`π ⊗ π`-essential supremum of the kernel discrepancy. -/
theorem gromovWassersteinEDist_top [IsFiniteMeasure μ] (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hωY : AEStronglyMeasurable ωY (ν.prod ν)) :
    gromovWassersteinEDist ∞ μ ωX ν ωY =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
        eLpNormEssSup (fun q : (X × Y) × (X × Y) ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
          (π.prod π) := by
  rw [gromovWassersteinEDist_def]
  refine iInf_congr fun π ↦ iInf_congr fun hπ ↦ ?_
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  rw [gromovWassersteinDistortion_def,
    eLpNorm_exponent_top (hπ.aestronglyMeasurable_edist hωX hωY)]

/-- The distortion of a coupling does not see a modification of either kernel on a null set. -/
theorem gromovWassersteinDistortion_congr_ae [SFinite π] (hπ : IsCoupling π μ ν)
    (hX : ωX =ᵐ[μ.prod μ] ωX') (hY : ωY =ᵐ[ν.prod ν] ωY') (p : ℝ≥0∞) :
    gromovWassersteinDistortion p ωX ωY π = gromovWassersteinDistortion p ωX' ωY' π := by
  have hX' := (hπ.measurePreserving_fst.prod hπ.measurePreserving_fst).quasiMeasurePreserving
    |>.ae_eq_comp hX
  have hY' := (hπ.measurePreserving_snd.prod hπ.measurePreserving_snd).quasiMeasurePreserving
    |>.ae_eq_comp hY
  rw [gromovWassersteinDistortion_def, gromovWassersteinDistortion_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [hX', hY'] with q hqX hqY
  simp only [Function.comp_apply, Prod.map_def] at hqX hqY
  rw [hqX, hqY]

/-- The Gromov–Wasserstein distance does not see a modification of either kernel on a null set. -/
theorem gromovWassersteinEDist_congr_ae [IsFiniteMeasure μ] (hX : ωX =ᵐ[μ.prod μ] ωX')
    (hY : ωY =ᵐ[ν.prod ν] ωY') (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ ωX ν ωY = gromovWassersteinEDist p μ ωX' ν ωY' := by
  rw [gromovWassersteinEDist_def, gromovWassersteinEDist_def]
  refine iInf_congr fun π ↦ iInf_congr fun hπ ↦ ?_
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  exact gromovWassersteinDistortion_congr_ae hπ hX hY p

/-- A measured kernel `(Y, ν, ωY)` and its pullback `(X, μ, ωY ∘ (f × f))` along a
measure-preserving map `f` are at Gromov–Wasserstein distance `0`. In particular the
Gromov–Wasserstein distance is only an extended pseudodistance on measured kernels. -/
theorem gromovWassersteinEDist_comp_prodMap_eq_zero [SFinite μ] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (hωY : AEStronglyMeasurable ωY (ν.prod ν)) (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ (ωY ∘ Prod.map f f) ν ωY = 0 := by
  refine nonpos_iff_eq_zero.mp ((gromovWassersteinEDist_le_eLpNorm (MeasurePreserving.id μ) hf
    (hωY.comp_quasiMeasurePreserving (hf.prod hf).quasiMeasurePreserving) hωY p).trans_eq ?_)
  simp [Prod.map_def]

/-- A measured kernel is at Gromov–Wasserstein distance `0` from itself. -/
theorem gromovWassersteinEDist_self [SFinite μ] (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (p : ℝ≥0∞) : gromovWassersteinEDist p μ ωX μ ωX = 0 := by
  simpa using gromovWassersteinEDist_comp_prodMap_eq_zero (MeasurePreserving.id μ) hωX p

/-- Exchanging the two coordinates of a plan exchanges the roles of the two kernels and does not
change the distortion. -/
theorem gromovWassersteinDistortion_map_swap [SFinite π] (p : ℝ≥0∞) :
    gromovWassersteinDistortion p ωY ωX (π.map Prod.swap) =
      gromovWassersteinDistortion p ωX ωY π := by
  have he : MeasurableEmbedding (Prod.map (Prod.swap : X × Y → Y × X) Prod.swap) :=
    (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding.prodMap
      (MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding
  rw [gromovWassersteinDistortion_def, gromovWassersteinDistortion_def,
    Measure.map_prod_map π π measurable_swap measurable_swap, he.eLpNorm_map_measure]
  exact eLpNorm_congr_ae (.of_forall fun q ↦ edist_comm _ _)

/-- **Symmetry.** Exchanging the two measured kernels does not change their Gromov–Wasserstein
distance. -/
theorem gromovWassersteinEDist_comm (p : ℝ≥0∞) (μ : Measure X) [IsFiniteMeasure μ]
    (ωX : X × X → Z) (ν : Measure Y) (ωY : Y × Y → Z) :
    gromovWassersteinEDist p μ ωX ν ωY = gromovWassersteinEDist p ν ωY μ ωX := by
  refine le_antisymm (le_gromovWassersteinEDist fun σ hσ ↦ ?_)
    (le_gromovWassersteinEDist fun π hπ ↦ ?_)
  · have : IsFiniteMeasure σ := hσ.isFiniteMeasure_of_right
    exact (gromovWassersteinEDist_le hσ.swap p ωX ωY).trans_eq
      (gromovWassersteinDistortion_map_swap p)
  · have : IsFiniteMeasure π := hπ.isFiniteMeasure
    exact (gromovWassersteinEDist_le hπ.swap p ωY ωX).trans_eq
      (gromovWassersteinDistortion_map_swap p)

/-- **The triangle inequality**, for carriers along which couplings glue. If every coupling of
`μ` and `ν` and every coupling of `ν` and `ρ` are the two consecutive two-coordinate marginals of
a single measure on `X × Y × W`, then for `1 ≤ p` the Gromov–Wasserstein distance satisfies the
triangle inequality through `(Y, ν, ωY)`. -/
theorem gromovWassersteinEDist_triangle_of_exists_glue (hp : 1 ≤ p) [IsFiniteMeasure ν]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ))
    (hglue : ∀ π σ, IsCoupling π μ ν → IsCoupling σ ν ρ →
      ∃ γ : Measure (X × Y × W), γ.map (Prod.map id Prod.fst) = π ∧ γ.snd = σ) :
    gromovWassersteinEDist p μ ωX ρ ωW ≤
      gromovWassersteinEDist p μ ωX ν ωY + gromovWassersteinEDist p ν ωY ρ ωW := by
  refine ENNReal.le_iInf₂_add_iInf₂ fun π hπ σ hσ ↦ ?_
  have : IsFiniteMeasure π := hπ.isFiniteMeasure_of_right
  obtain ⟨γ, hγπ, hγσ⟩ := hglue π σ hπ hσ
  have he : Measurable (Prod.map (id : X → X) (Prod.fst : Y × W → Y)) :=
    measurable_id.prodMap measurable_fst
  have : IsFiniteMeasure γ := ⟨by
    rw [← preimage_univ (f := Prod.map (id : X → X) (Prod.fst : Y × W → Y)),
      ← Measure.map_apply he .univ, hγπ]
    exact measure_lt_top π univ⟩
  -- The three coordinates of the glued measure are measure-preserving parametrizations of the
  -- three marginals; every distortion in the statement is read on `γ ⊗ γ` through them.
  have hX : MeasurePreserving (fun w : X × Y × W ↦ w.1) γ μ := by
    refine ⟨measurable_fst, ?_⟩
    rw [← hπ.fst_eq, ← hγπ, Measure.fst, Measure.map_map measurable_fst he]
    rfl
  have hY : MeasurePreserving (fun w : X × Y × W ↦ w.2.1) γ ν := by
    refine ⟨measurable_fst.comp measurable_snd, ?_⟩
    rw [← hσ.fst_eq, ← hγσ, Measure.fst, Measure.snd, Measure.map_map measurable_fst
      measurable_snd]
    rfl
  have hW : MeasurePreserving (fun w : X × Y × W ↦ w.2.2) γ ρ := by
    refine ⟨measurable_snd.comp measurable_snd, ?_⟩
    rw [← hσ.snd_eq, ← hγσ, Measure.snd, Measure.snd, Measure.map_map measurable_snd
      measurable_snd]
    rfl
  have hπγ : π = γ.map fun w ↦ (w.1, w.2.1) := by
    rw [← hγπ, Prod.map_def]
    rfl
  have hσγ : σ = γ.map fun w ↦ (w.2.1, w.2.2) := by
    rw [← hγσ, Measure.snd]
  rw [hπγ, hσγ, gromovWassersteinDistortion_map_prodMk hX hY hωX hωY,
    gromovWassersteinDistortion_map_prodMk hY hW hωY hωW]
  calc gromovWassersteinEDist p μ ωX ρ ωW
      ≤ eLpNorm (fun q : (X × Y × W) × (X × Y × W) ↦
          edist (ωX (q.1.1, q.2.1)) (ωW (q.1.2.2, q.2.2.2))) p (γ.prod γ) :=
        gromovWassersteinEDist_le_eLpNorm hX hW hωX hωW p
    _ ≤ eLpNorm ((fun q : (X × Y × W) × (X × Y × W) ↦
            edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2.1, q.2.2.1))) +
          fun q ↦ edist (ωY (q.1.2.1, q.2.2.1)) (ωW (q.1.2.2, q.2.2.2))) p (γ.prod γ) :=
        eLpNorm_mono_enorm (aestronglyMeasurable_edist_comp hX hW hωX hωW) fun q ↦ by
          simpa only [Pi.add_apply, enorm_eq_self] using edist_triangle _ _ _
    _ ≤ _ := eLpNorm_add_le hp

/-- **The triangle inequality.** For `1 ≤ p` and a standard Borel third carrier, the
Gromov–Wasserstein distance satisfies the triangle inequality: the two couplings are glued along
the middle space by disintegrating the second one. -/
theorem gromovWassersteinEDist_triangle [StandardBorelSpace W] (hp : 1 ≤ p) [IsFiniteMeasure ν]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hωW : AEStronglyMeasurable ωW (ρ.prod ρ)) :
    gromovWassersteinEDist p μ ωX ρ ωW ≤
      gromovWassersteinEDist p μ ωX ν ωY + gromovWassersteinEDist p ν ωY ρ ωW :=
  gromovWassersteinEDist_triangle_of_exists_glue hp hωX hωY hωW fun π σ hπ hσ ↦
    have : IsFiniteMeasure σ := hσ.isFiniteMeasure
    Measure.exists_glue_of_standardBorel_right π σ (hπ.snd_eq.trans hσ.fst_eq.symm)

section Dirac

variable [MeasurableSingletonClass Y]

/-- **Distance to a one-point measured kernel.** A probability measure `μ` has exactly one
coupling with the Dirac measure `δ_y`, so the Gromov–Wasserstein distance from `({y}, δ_y, ωY)` to
`(X, μ, ωX)` is the `L^p (μ ⊗ μ)` size of `ωX` about the point `ωY (y, y)`. -/
theorem gromovWassersteinEDist_dirac_left (y : Y) (ωY : Y × Y → Z) [IsProbabilityMeasure μ]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (p : ℝ≥0∞) :
    gromovWassersteinEDist p (Measure.dirac y) ωY μ ωX =
      eLpNorm (fun q : X × X ↦ edist (ωY (y, y)) (ωX q)) p (μ.prod μ) := by
  have hy : MeasurePreserving (fun _ : X ↦ y) μ (Measure.dirac y) :=
    ⟨measurable_const, by rw [Measure.map_const, measure_univ, one_smul]⟩
  have hωY : AEStronglyMeasurable ωY ((Measure.dirac y).prod (Measure.dirac y)) := by
    rw [Measure.dirac_prod_dirac]
    exact aestronglyMeasurable_dirac
  have key : gromovWassersteinDistortion p ωY ωX (μ.map (Prod.mk y)) =
      eLpNorm (fun q : X × X ↦ edist (ωY (y, y)) (ωX q)) p (μ.prod μ) :=
    gromovWassersteinDistortion_map_prodMk hy (MeasurePreserving.id μ) hωY hωX p
  refine le_antisymm ((gromovWassersteinEDist_le (isCoupling_map_prodMk y μ) p ωY ωX).trans_eq
    key) (le_gromovWassersteinEDist fun π hπ ↦ ?_)
  rw [hπ.eq_map_prodMk, key]

/-- **Distance to a one-point measured kernel**, with the point on the right: the
Gromov–Wasserstein distance from `(X, μ, ωX)` to `({y}, δ_y, ωY)` is the `L^p (μ ⊗ μ)` size of
`ωX` about the point `ωY (y, y)`. -/
theorem gromovWassersteinEDist_dirac_right (y : Y) (ωY : Y × Y → Z) [IsProbabilityMeasure μ]
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (p : ℝ≥0∞) :
    gromovWassersteinEDist p μ ωX (Measure.dirac y) ωY =
      eLpNorm (fun q : X × X ↦ edist (ωX q) (ωY (y, y))) p (μ.prod μ) := by
  rw [gromovWassersteinEDist_comm, gromovWassersteinEDist_dirac_left y ωY hωX]
  exact eLpNorm_congr_ae (.of_forall fun q ↦ edist_comm _ _)

end Dirac

end PseudoEMetricSpace

end TauCeti
