/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.MetricMeasure.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Topology.EMetricSpace.MetricCoupling

/-!
# Sturm's transportation distance between metric-measure spaces

Two measures `μ` on an extended pseudometric space `X` and `ν` on another such space `Y` cannot be
compared by a Wasserstein distance until both spaces sit in a common space. Sturm's
*transportation distance* optimises over that common space as well: for an exponent `p : ℝ≥0∞`,

`D_p (μ, ν) = ⨅ f π, ‖f‖_{L^p (π)}`,

the infimum taken over the metric couplings `f` of `X` and `Y` (`TauCeti.IsMetricCoupling`), which
are the extended pseudometrics on `X ⊕ Y` restricting to the given distances, and over the
couplings `π` of `μ` and `ν`. For `p = 2` and probability measures of finite variance this is
Sturm's `L²`-transportation distance `𝔻` between metric-measure spaces. Informally, for a fixed
metric coupling the inner infimum is the `p`-Wasserstein distance between the copies of `μ` and `ν`
in `X ⊕ Y` with the glued pseudometric, since a coupling of the two copies only charges pairs with
one point in each space; so `D_p` measures how close `μ` and `ν` can be brought by placing `X` and
`Y` side by side.

This file defines `TauCeti.sturmEDist` and proves that it is an extended pseudodistance between
measures on varying spaces, invariant under measure-preserving isometries.

* It is symmetric, with no hypotheses (`TauCeti.sturmEDist_comm`).
* For `1 ≤ p` and a finite middle measure it satisfies the triangle inequality, when the third
  space is standard Borel (`TauCeti.sturmEDist_triangle`): the two metric couplings glue along the
  middle space (`TauCeti.IsMetricCoupling.comp`), and the two couplings glue along the middle
  measure.
* On a single space it is at most the Wasserstein distance
  (`TauCeti.sturmEDist_le_wassersteinEDist`), and in particular it vanishes on the diagonal
  (`TauCeti.sturmEDist_self`).
* A measure and its image under an isometry are at distance `0`
  (`TauCeti.sturmEDist_map_eq_zero`), and for `1 ≤ p`, replacing a finite measure by such an image
  does not change its distance to any measure on a standard Borel space
  (`TauCeti.sturmEDist_map_left`). Hence, for `1 ≤ p` and measures on standard Borel spaces, `D_p`
  only depends on the isomorphism classes of metric-measure spaces of finite mass
  (`TauCeti.MeasurePreservingIsometry.sturmEDist_left`), and such a space may be replaced by its
  support (`TauCeti.MetricMeasureSpace.sturmEDist_supportSpace`).
* Probability measures of finite `p`-th moment are at finite distance, for every exponent
  (`TauCeti.sturmEDist_ne_top`), by gluing the two spaces at a point. This is why Sturm restricts
  `𝔻` to normalized metric-measure spaces of finite variance.

## Main definitions

* `TauCeti.sturmEDist p μ ν`: the infimum of `eLpNorm (fun z ↦ f z.1 z.2) p π` over the metric
  couplings `f` and the couplings `π` of `μ` and `ν`.

## Implementation notes

The measures are raw `MeasureTheory.Measure`s, as for `TauCeti.wassersteinEDist`, and measures with
no coupling, such as finite measures of different total mass, are at distance `∞`. The metric
couplings take values in `[0, ∞]`; on ordinary pseudometric spaces this changes nothing, since a
metric coupling with a finite value is finite everywhere (`TauCeti.IsMetricCoupling.ne_top`) and
the identically infinite one contributes only the value `∞` against a nonzero measure.

The objective is measurable without any hypothesis on the couplings: the cross distances of a
metric coupling are jointly continuous (`TauCeti.IsMetricCoupling.continuous`), so they are
measurable as soon as the product carries its Borel sets, which is the
`MeasureTheory.OpensMeasurableSpace` hypothesis on products below. It holds for every pair of
second countable Borel spaces.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. I*, Acta Math. 196 (2006), 65--131, §3.1,
  where `𝔻` is defined by this infimum over couplings of the metrics and of the measures and shown
  to be a metric on isomorphism classes of normalized metric-measure spaces of finite variance.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X X' Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace X'] [PseudoEMetricSpace Y]
  [PseudoEMetricSpace Z] [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Z] {p q a : ℝ≥0∞} {μ : Measure X} {ν : Measure Y} {f : X → Y → ℝ≥0∞}
  {π : Measure (X × Y)}

/-- **Sturm's transportation distance** of `μ` and `ν`: the infimum, over the metric couplings `f`
of `X` and `Y` and the couplings `π` of `μ` and `ν`, of the `L^p (π)` seminorm of the cross
distance `fun z ↦ f z.1 z.2`. For `p = 2` and probability measures of finite variance this is
Sturm's distance `𝔻` between the metric-measure spaces `(X, μ)` and `(Y, ν)`.

It is `∞` when `μ` and `ν` have no coupling at all. -/
def sturmEDist (p : ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (f : X → Y → ℝ≥0∞) (_ : IsMetricCoupling f) (π : Measure (X × Y)) (_ : IsCoupling π μ ν),
    eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π

/-- Every metric coupling and every coupling of the measures bound the transportation distance
from above. -/
theorem sturmEDist_le (hf : IsMetricCoupling f) (hπ : IsCoupling π μ ν) (p : ℝ≥0∞) :
    sturmEDist p μ ν ≤ eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π :=
  (iInf₂_le f hf).trans (iInf₂_le π hπ)

/-- A bound valid for every metric coupling and every coupling of the measures bounds the
transportation distance from below. -/
theorem le_sturmEDist
    (h : ∀ f, IsMetricCoupling f → ∀ π, IsCoupling π μ ν →
      a ≤ eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π) :
    a ≤ sturmEDist p μ ν :=
  le_iInf₂ fun f hf ↦ le_iInf₂ (h f hf)

/-- The transportation distance is below a threshold exactly when some metric coupling and some
coupling of the measures are. -/
theorem sturmEDist_lt_iff :
    sturmEDist p μ ν < a ↔ ∃ f, IsMetricCoupling f ∧
      ∃ π, IsCoupling π μ ν ∧ eLpNorm (fun z : X × Y ↦ f z.1 z.2) p π < a := by
  simp only [sturmEDist, iInf_lt_iff, exists_prop]

/-- The transportation distance is monotone in the exponent when the first measure is a
probability measure. -/
theorem sturmEDist_mono_exponent (hpq : p ≤ q) (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) : sturmEDist p μ ν ≤ sturmEDist q μ ν :=
  iInf₂_mono fun _ _ ↦ iInf₂_mono fun π hπ ↦
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    eLpNorm_le_eLpNorm_of_exponent_le hpq

/-- One half of `TauCeti.sturmEDist_comm`: swapping a metric coupling and a coupling of the
measures preserves the objective. -/
private theorem sturmEDist_swap_le (p : ℝ≥0∞) (μ : Measure X) (ν : Measure Y) :
    sturmEDist p ν μ ≤ sturmEDist p μ ν :=
  le_sturmEDist fun _ hf _ hπ ↦ (sturmEDist_le hf.swap (isCoupling_map_swap_iff.2 hπ) p).trans_eq
    ((MeasurableEquiv.prodComm : X × Y ≃ᵐ Y × X).measurableEmbedding.eLpNorm_map_measure)

/-- **Symmetry.** Exchanging the two measures does not change their transportation distance. -/
theorem sturmEDist_comm (p : ℝ≥0∞) (μ : Measure X) (ν : Measure Y) :
    sturmEDist p μ ν = sturmEDist p ν μ :=
  le_antisymm (sturmEDist_swap_le p ν μ) (sturmEDist_swap_le p μ ν)

/-- On a single space, the transportation distance is at most the Wasserstein distance: the
distance of the space is a metric coupling of the space with itself. -/
theorem sturmEDist_le_wassersteinEDist (p : ℝ≥0∞) (μ ν : Measure X) :
    sturmEDist p μ ν ≤ wassersteinEDist p μ ν :=
  le_wassersteinEDist fun _ hπ ↦ sturmEDist_le isMetricCoupling_edist hπ p

/-- The transportation distance from a measure to itself vanishes. -/
@[simp]
theorem sturmEDist_self [MeasurableEq X] (p : ℝ≥0∞) (μ : Measure X) : sturmEDist p μ μ = 0 :=
  nonpos_iff_eq_zero.mp ((sturmEDist_le_wassersteinEDist p μ μ).trans_eq
    (wassersteinEDist_self p μ))

/-- **Isometric images are at distance zero.** A measure and its pushforward along an isometry are
at transportation distance `0`: the distance of `Y` pulled back along the isometry is a metric
coupling, and the graph plan of the isometry has zero cross distance. -/
theorem sturmEDist_map_eq_zero [OpensMeasurableSpace (X × Y)] {T : X → Y} (hT : Isometry T)
    (hTm : AEMeasurable T μ) (p : ℝ≥0∞) : sturmEDist p μ (μ.map T) = 0 := by
  have hf := IsMetricCoupling.of_isometry hT isometry_id
  refine nonpos_iff_eq_zero.mp ((sturmEDist_le hf (isCoupling_graphPlan_map hTm) p).trans_eq ?_)
  rw [graphPlan_def, eLpNorm_map_measure hf.continuous.aestronglyMeasurable
    (aemeasurable_prodMk_self hTm)]
  exact eLpNorm_eq_zero_of_ae_zero (.of_forall fun x ↦ by simp)

section Finite

variable [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/-- Gluing the two spaces at the points `x₀` and `y₀` and coupling the measures independently
bounds the transportation distance by the sum of the `p`-th moments about the two points. -/
theorem sturmEDist_le_eLpNorm_add_eLpNorm (hp : 1 ≤ p) (x₀ : X) (y₀ : Y) (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    sturmEDist p μ ν ≤ eLpNorm (fun x ↦ edist x₀ x) p μ + eLpNorm (fun y ↦ edist y₀ y) p ν := by
  have hπ := isCoupling_prod μ ν
  have hfst : eLpNorm (fun z : X × Y ↦ edist x₀ z.1) p (μ.prod ν) =
      eLpNorm (fun x ↦ edist x₀ x) p μ :=
    eLpNorm_comp_measurePreserving (continuous_const.edist continuous_id).aestronglyMeasurable
      hπ.measurePreserving_fst
  have hsnd : eLpNorm (fun z : X × Y ↦ edist y₀ z.2) p (μ.prod ν) =
      eLpNorm (fun y ↦ edist y₀ y) p ν :=
    eLpNorm_comp_measurePreserving (continuous_const.edist continuous_id).aestronglyMeasurable
      hπ.measurePreserving_snd
  rw [← hfst, ← hsnd]
  exact (sturmEDist_le (isMetricCoupling_edist_add_edist x₀ y₀) hπ p).trans
    (eLpNorm_add_le (f := fun z : X × Y ↦ edist x₀ z.1) (g := fun z ↦ edist y₀ z.2) hp)

/-- **Finiteness.** Probability measures of finite `p`-th moment are at finite transportation
distance, for every exponent `p`. -/
theorem sturmEDist_ne_top [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasFiniteMoment p μ) (hν : HasFiniteMoment p ν) : sturmEDist p μ ν ≠ ∞ := by
  obtain ⟨x₀, hx₀⟩ := hasFiniteMoment_def.1 hμ
  obtain ⟨y₀, hy₀⟩ := hasFiniteMoment_def.1 hν
  have hπ := isCoupling_prod μ ν
  refine (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top p)
    (ENNReal.add_lt_top.2 ⟨hx₀.eLpNorm_lt_top, hy₀.eLpNorm_lt_top⟩))).ne
  calc sturmEDist p μ ν
      ≤ ENNReal.LpAddConst p * (eLpNorm (fun z : X × Y ↦ edist x₀ z.1) p (μ.prod ν)
          + eLpNorm (fun z : X × Y ↦ edist y₀ z.2) p (μ.prod ν)) :=
        (sturmEDist_le (isMetricCoupling_edist_add_edist x₀ y₀) hπ p).trans
          (eLpNorm_add_le' (f := fun z : X × Y ↦ edist x₀ z.1) (g := fun z ↦ edist y₀ z.2) p)
    _ = ENNReal.LpAddConst p *
          (eLpNorm (fun x ↦ edist x₀ x) p μ + eLpNorm (fun y ↦ edist y₀ y) p ν) := by
        congr 2
        · exact eLpNorm_comp_measurePreserving
            (continuous_const.edist continuous_id).aestronglyMeasurable hπ.measurePreserving_fst
        · exact eLpNorm_comp_measurePreserving
            (continuous_const.edist continuous_id).aestronglyMeasurable hπ.measurePreserving_snd

end Finite

section Triangle

variable [OpensMeasurableSpace (X × Y)] [OpensMeasurableSpace (Y × Z)]
  [OpensMeasurableSpace (X × Z)] [StandardBorelSpace Z]

/-- **The triangle inequality.** This holds for `1 ≤ p` when the middle measure is finite and the
third space is standard Borel: the two metric couplings glue along the middle space and the two
couplings of measures glue along the middle measure. -/
theorem sturmEDist_triangle (hp : 1 ≤ p) (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure ν]
    (ρ : Measure Z) : sturmEDist p μ ρ ≤ sturmEDist p μ ν + sturmEDist p ν ρ := by
  refine ENNReal.le_iInf₂_add_iInf₂ fun f hf g hg ↦
    ENNReal.le_iInf₂_add_iInf₂ fun π hπ σ hσ ↦ ?_
  have : IsFiniteMeasure σ := hσ.isFiniteMeasure
  obtain ⟨γ, hγπ, hγσ⟩ := Measure.exists_glue_of_standardBorel_right π σ (by
    rw [hπ.snd_eq, hσ.fst_eq])
  have hcoup : IsCoupling (γ.map (Prod.map id Prod.snd)) μ ρ :=
    ⟨(Measure.fst_map_prodMap_id_snd hγπ).trans hπ.fst_eq,
      (Measure.snd_map_prodMap_id_snd hγσ).trans hσ.snd_eq⟩
  have hfg := hf.comp hg
  exact (sturmEDist_le hfg hcoup p).trans
    (MeasureTheory.eLpNorm_map_prodMap_id_snd_le hp hγπ hγσ hfg.continuous.measurable
      hf.continuous.measurable hg.continuous.measurable fun x y z ↦
        iInf_le (fun y ↦ f x y + g y z) y)

end Triangle

/-- **Invariance under isometries.** For `1 ≤ p`, replacing a finite measure by its pushforward
along an isometry does not change its transportation distance to any measure on a standard Borel
space. -/
theorem sturmEDist_map_left [OpensMeasurableSpace (X × X')] [OpensMeasurableSpace (X × Y)]
    [OpensMeasurableSpace (X' × Y)] [StandardBorelSpace Y] (hp : 1 ≤ p) {T : X → X'}
    (hT : Isometry T) (hTm : AEMeasurable T μ) [IsFiniteMeasure μ] (ν : Measure Y) :
    sturmEDist p (μ.map T) ν = sturmEDist p μ ν := by
  refine le_antisymm (le_sturmEDist fun f hf π hπ ↦ ?_) ?_
  · -- Glue `X'` to `Y` through the isometric copy of `X`, and push the coupling forward.
    have hg := (IsMetricCoupling.of_isometry isometry_id hT).comp hf
    have hfst := hπ.measurePreserving_fst
    have hTfst : AEMeasurable (fun z : X × Y ↦ T z.1) π :=
      hTm.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving
    have hTπ : AEMeasurable (fun z : X × Y ↦ (T z.1, z.2)) π :=
      hTfst.prodMk measurable_snd.aemeasurable
    have hcoup : IsCoupling (π.map fun z ↦ (T z.1, z.2)) (μ.map T) ν := by
      refine ⟨?_, (Measure.snd_map_prodMk₀ hTfst measurable_snd.aemeasurable).trans hπ.snd_eq⟩
      rw [Measure.fst_map_prodMk₀ hTfst measurable_snd.aemeasurable, ← hfst.map_eq,
        AEMeasurable.map_map_of_aemeasurable (by rw [hfst.map_eq]; exact hTm)
          measurable_fst.aemeasurable]
      -- `fun z ↦ T z.1` is `T ∘ Prod.fst` by unfolding `Function.comp`.
      rfl
    refine (sturmEDist_le hg hcoup p).trans ?_
    rw [eLpNorm_map_measure hg.continuous.aestronglyMeasurable hTπ]
    exact eLpNorm_mono_enorm (hg.continuous.aestronglyMeasurable.comp_aemeasurable hTπ) fun z ↦ by
      simpa only [Function.comp_apply, id_eq, edist_self, zero_add, enorm_eq_self] using
        iInf_le (fun x ↦ edist (T z.1) (T x) + f x z.2) z.1
  · calc sturmEDist p μ ν ≤ sturmEDist p μ (μ.map T) + sturmEDist p (μ.map T) ν :=
          sturmEDist_triangle hp μ (μ.map T) ν
      _ = sturmEDist p (μ.map T) ν := by rw [sturmEDist_map_eq_zero hT hTm, zero_add]

namespace MeasurePreservingIsometry

variable {X Y Z : Type*} [MetricSpace X] [MeasurableSpace X] [CompleteSpace X]
  [SecondCountableTopology X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [CompleteSpace Y]
  [SecondCountableTopology Y] [BorelSpace Y] [PseudoEMetricSpace Z] [MeasurableSpace Z]
  [SecondCountableTopology Z] [OpensMeasurableSpace Z] [StandardBorelSpace Z]
  {M : MetricMeasureSpace X} {N : MetricMeasureSpace Y}

/-- Metric-measure spaces related by a measure-preserving isometry are at transportation
distance `0`. -/
theorem sturmEDist_eq_zero (e : MeasurePreservingIsometry M N) (p : ℝ≥0∞) :
    sturmEDist p M.reference N.reference = 0 := by
  rw [← e.measurePreserving.map_eq]
  exact sturmEDist_map_eq_zero e.isometry e.measurePreserving.measurable.aemeasurable p

/-- **The transportation distance is an isomorphism invariant.** For `1 ≤ p`, metric-measure spaces
of finite mass related by a measure-preserving isometry are at the same transportation distance
from every measure on a standard Borel space. -/
theorem sturmEDist_left (e : MeasurePreservingIsometry M N) [IsFiniteMeasure N.reference]
    (hp : 1 ≤ p) (ρ : Measure Z) :
    sturmEDist p N.reference ρ = sturmEDist p M.reference ρ := by
  rw [← e.measurePreserving.map_eq] at ‹IsFiniteMeasure N.reference› ⊢
  have := Measure.isFiniteMeasure_of_map (μ := M.reference)
    e.measurePreserving.measurable.aemeasurable
  exact sturmEDist_map_left hp e.isometry e.measurePreserving.measurable.aemeasurable ρ

end MeasurePreservingIsometry

/-- For `1 ≤ p`, a metric-measure space of finite mass is at the same transportation distance as its
support from every measure on a standard Borel space. -/
theorem MetricMeasureSpace.sturmEDist_supportSpace {X Z : Type*} [MetricSpace X]
    [MeasurableSpace X] [CompleteSpace X] [SecondCountableTopology X] [BorelSpace X]
    [PseudoEMetricSpace Z] [MeasurableSpace Z] [SecondCountableTopology Z]
    [OpensMeasurableSpace Z] [StandardBorelSpace Z] (M : MetricMeasureSpace X)
    [IsFiniteMeasure M.reference] (hp : 1 ≤ p) (ρ : Measure Z) :
    sturmEDist p M.supportSpace.reference ρ = sturmEDist p M.reference ρ :=
  (M.supportInclusion.sturmEDist_left hp ρ).symm

end TauCeti
