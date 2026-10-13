/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Sequences
public import TauCeti.MeasureTheory.Measure.FrechetMean.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Topology.Instances.ENNReal

/-!
# Stability of Fréchet barycenters under Wasserstein convergence

Throughout, the exponent satisfies `1 ≤ p ≤ ∞`. The `p`-Fréchet radius
`R_p(μ, x) = ‖d(x, ·)‖_{Lᵖ(μ)}` of a law `μ` on an extended pseudometric space `X` depends
`1`-Lipschitz continuously on `μ` for the `p`-Wasserstein distance on laws on `X`:

`R_p(μ, x) ≤ R_p(ν, x) + W_p(μ, ν)` and `R_p(ν, x) ≤ R_p(μ, x) + W_p(μ, ν)`.

Indeed, along a coupling `π` of `μ` and `ν`, the triangle inequality `d(x, y) ≤ d(x, z) + d(z, y)`
and Minkowski's inequality in `Lᵖ(π)` bound one radius by the other plus the `Lᵖ(π)` seminorm of
the displacement. The same bound holds for the minimal radii `⨅ x, R_p(μ, x)`.

This gives the consistency of Fréchet barycenters. Let laws `μᵢ` converge to a probability law `μ`
in `W_p`, along any filter, and let `bᵢ` be a Fréchet barycenter of `μᵢ`. Then every cluster point
of the barycenters `bᵢ` is a Fréchet barycenter of `μ`, and the minimal radii of the `μᵢ` converge
to that of `μ`. If the `μᵢ` are probability laws as well, the barycenters stay eventually in every
ball about a point `x₀` of radius larger than `2 R_p(μ, x₀)`.

On a proper metric space the barycenters therefore have a subsequence converging to a Fréchet
barycenter of `μ`, and the whole family converges when `μ` has at most one barycenter, as in a
CAT(0) space at exponent `2`.

No topology on the space of laws enters: the hypothesis is only that `W_p(μᵢ, μ) → 0`. The carrier
`X` may itself be a space of laws, so these statements apply to population laws `P ∈ P(P_p(Y))`
on the Wasserstein space `P_p(Y)`, which is a Borel space for finite `p` over a Polish base; a
Fréchet barycenter of `P` is then a Wasserstein barycenter. That space is not proper, and
precompactness of Wasserstein barycenters needs an argument specific to it.

## Main statements

* `TauCeti.frechetRadius_le_add_wassersteinEDist` and
  `TauCeti.frechetRadius_le_add_wassersteinEDist'`: the Fréchet radius is `1`-Lipschitz in the law
  for the Wasserstein distance.
* `TauCeti.tendsto_frechetRadius_of_tendsto_wassersteinEDist` and
  `TauCeti.tendsto_iInf_frechetRadius_of_tendsto_wassersteinEDist`: Wasserstein convergence of
  the laws gives convergence of the radii and of the minimal radii.
* `TauCeti.isFrechetBarycenter_of_mapClusterPt`: every cluster point of Fréchet barycenters of
  converging laws is a Fréchet barycenter of the limit law.
* `TauCeti.eventually_edist_lt_of_isFrechetBarycenter`: such barycenters are eventually bounded.
* `TauCeti.exists_isFrechetBarycenter_tendsto_comp` and
  `TauCeti.tendsto_of_isFrechetBarycenter`: on a proper metric space, the barycenters converge
  along a subsequence, and converge outright when the limit barycenter is unique.

## References

* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Relat. Fields 168 (2017), 901--917.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace TauCeti

universe u v

variable {X : Type u} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p : ℝ≥0∞}

section Lipschitz

variable (hp : 1 ≤ p)
include hp

/-- Along a coupling `π` of `μ` and `ν`, the Fréchet radius of `μ` at `x` is at most that of `ν`
plus the `Lᵖ(π)` seminorm of the displacement. -/
theorem IsCoupling.frechetRadius_le_add {π : Measure (X × X)} {μ ν : Measure X}
    (hπ : IsCoupling π μ ν) (x : X) :
    frechetRadius p μ x ≤
      frechetRadius p ν x + eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
  have hx : Measurable fun y ↦ edist x y := (continuous_const.edist continuous_id).measurable
  rw [frechetRadius_def, frechetRadius_def, ← hπ.fst_eq, ← hπ.snd_eq, Measure.fst, Measure.snd,
    eLpNorm_map_measure hx.aestronglyMeasurable measurable_fst.aemeasurable,
    eLpNorm_map_measure hx.aestronglyMeasurable measurable_snd.aemeasurable]
  calc eLpNorm ((fun y ↦ edist x y) ∘ Prod.fst) p π
      ≤ eLpNorm ((fun y ↦ edist x y) ∘ Prod.snd + fun z : X × X ↦ edist z.1 z.2) p π :=
        eLpNorm_mono_enorm (hx.comp measurable_fst).aestronglyMeasurable fun z ↦ by
          simpa [edist_comm z.2 z.1] using edist_triangle x z.2 z.1
    _ ≤ _ := eLpNorm_add_le hp

/-- Along a coupling `π` of `μ` and `ν`, the Fréchet radius of `ν` at `x` is at most that of `μ`
plus the `Lᵖ(π)` seminorm of the displacement. -/
theorem IsCoupling.frechetRadius_le_add' {π : Measure (X × X)} {μ ν : Measure X}
    (hπ : IsCoupling π μ ν) (x : X) :
    frechetRadius p ν x ≤
      frechetRadius p μ x + eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π := by
  have hx : Measurable fun y ↦ edist x y := (continuous_const.edist continuous_id).measurable
  rw [frechetRadius_def, frechetRadius_def, ← hπ.fst_eq, ← hπ.snd_eq, Measure.fst, Measure.snd,
    eLpNorm_map_measure hx.aestronglyMeasurable measurable_fst.aemeasurable,
    eLpNorm_map_measure hx.aestronglyMeasurable measurable_snd.aemeasurable]
  calc eLpNorm ((fun y ↦ edist x y) ∘ Prod.snd) p π
      ≤ eLpNorm ((fun y ↦ edist x y) ∘ Prod.fst + fun z : X × X ↦ edist z.1 z.2) p π :=
        eLpNorm_mono_enorm (hx.comp measurable_snd).aestronglyMeasurable fun z ↦ by
          simpa using edist_triangle x z.1 z.2
    _ ≤ _ := eLpNorm_add_le hp

/-- **The Fréchet radius is `1`-Lipschitz in the law.** The Fréchet radius of `μ` at `x` is at
most that of `ν` plus the `p`-Wasserstein distance from `μ` to `ν`. -/
theorem frechetRadius_le_add_wassersteinEDist (μ ν : Measure X) (x : X) :
    frechetRadius p μ x ≤ frechetRadius p ν x + wassersteinEDist p μ ν := by
  rw [← tsub_le_iff_left]
  exact le_wassersteinEDist fun π hπ ↦ tsub_le_iff_left.2 (hπ.frechetRadius_le_add hp x)

/-- The mirror image of `TauCeti.frechetRadius_le_add_wassersteinEDist`: the Fréchet radius of `ν`
at `x` is at most that of `μ` plus the `p`-Wasserstein distance from `μ` to `ν`. -/
theorem frechetRadius_le_add_wassersteinEDist' (μ ν : Measure X) (x : X) :
    frechetRadius p ν x ≤ frechetRadius p μ x + wassersteinEDist p μ ν := by
  rw [← tsub_le_iff_left]
  exact le_wassersteinEDist fun π hπ ↦ tsub_le_iff_left.2 (hπ.frechetRadius_le_add' hp x)

/-- The minimal Fréchet radius of `μ` is at most that of `ν` plus the `p`-Wasserstein distance
from `μ` to `ν`. -/
theorem iInf_frechetRadius_le_add_wassersteinEDist (μ ν : Measure X) :
    ⨅ x, frechetRadius p μ x ≤ (⨅ x, frechetRadius p ν x) + wassersteinEDist p μ ν := by
  rw [ENNReal.iInf_add]
  exact iInf_mono fun x ↦ frechetRadius_le_add_wassersteinEDist hp μ ν x

/-- The mirror image of `TauCeti.iInf_frechetRadius_le_add_wassersteinEDist`. -/
theorem iInf_frechetRadius_le_add_wassersteinEDist' (μ ν : Measure X) :
    ⨅ x, frechetRadius p ν x ≤ (⨅ x, frechetRadius p μ x) + wassersteinEDist p μ ν := by
  rw [ENNReal.iInf_add]
  exact iInf_mono fun x ↦ frechetRadius_le_add_wassersteinEDist' hp μ ν x

variable {ι : Type v} {l : Filter ι} {μs : ι → Measure X} {μ : Measure X}

/-- If laws `μᵢ` converge to `μ` in `W_p`, their Fréchet radii at every point converge to that of
`μ`. -/
theorem tendsto_frechetRadius_of_tendsto_wassersteinEDist
    (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0)) (x : X) :
    Tendsto (fun i ↦ frechetRadius p (μs i) x) l (𝓝 (frechetRadius p μ x)) :=
  tendsto_of_le_add_of_le_add hμ
    (.of_forall fun i ↦ frechetRadius_le_add_wassersteinEDist hp (μs i) μ x)
    (.of_forall fun i ↦ frechetRadius_le_add_wassersteinEDist' hp (μs i) μ x)

/-- If laws `μᵢ` converge to `μ` in `W_p`, their minimal Fréchet radii converge to that of `μ`. -/
theorem tendsto_iInf_frechetRadius_of_tendsto_wassersteinEDist
    (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ⨅ x, frechetRadius p (μs i) x) l (𝓝 (⨅ x, frechetRadius p μ x)) :=
  tendsto_of_le_add_of_le_add hμ
    (.of_forall fun i ↦ iInf_frechetRadius_le_add_wassersteinEDist hp (μs i) μ)
    (.of_forall fun i ↦ iInf_frechetRadius_le_add_wassersteinEDist' hp (μs i) μ)

/-- **Consistency of Fréchet barycenters.** If laws `μᵢ` converge in `W_p` to a probability law
`μ` along a filter `l`, and `bᵢ` is eventually a Fréchet barycenter of `μᵢ`, then every cluster
point of the barycenters `bᵢ` along `l` is a Fréchet barycenter of `μ`. -/
theorem isFrechetBarycenter_of_mapClusterPt [IsProbabilityMeasure μ] {b : ι → X} {c : X}
    (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0))
    (hb : ∀ᶠ i in l, IsFrechetBarycenter p (μs i) (b i)) (hc : MapClusterPt c l b) :
    IsFrechetBarycenter p μ c := by
  -- Along the filter `l' ≤ l` on which `bᵢ → c`, compare `R_p(μ, c)` with the radii of the `μᵢ`.
  set l' := l ⊓ comap b (𝓝 c)
  have : l'.NeBot := neBot_inf_comap_iff_map.2 (by rw [inf_comm]; exact hc)
  have hbc : Tendsto (fun i ↦ edist c (b i)) l' (𝓝 0) := by
    have : Tendsto b l' (𝓝 c) := tendsto_comap.mono_left inf_le_right
    simpa [edist_comm c] using (tendsto_iff_edist_tendsto_0.1 this)
  have hμ' : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l' (𝓝 0) := hμ.mono_left inf_le_left
  have hb' : ∀ᶠ i in l', IsFrechetBarycenter p (μs i) (b i) := hb.filter_mono inf_le_left
  -- `R_p(μ, c) ≤ d(c, bᵢ) + R_p(μ, bᵢ) ≤ d(c, bᵢ) + R_p(μᵢ, bᵢ) + W_p(μᵢ, μ)`.
  have hcb (i : ι) : frechetRadius p μ c ≤
      edist c (b i) + (frechetRadius p (μs i) (b i) + wassersteinEDist p (μs i) μ) :=
    (frechetRadius_le_add hp μ (b i) c).trans
      (by gcongr; exact frechetRadius_le_add_wassersteinEDist' hp (μs i) μ (b i))
  refine isFrechetBarycenter_iff.2 ⟨?_, isFrechetMinimizer_iff.2 fun y ↦ ?_⟩
  · obtain ⟨i, hi, hiW, hic⟩ := (hb'.and ((hμ'.eventually (gt_mem_nhds zero_lt_one)).and
      (hbc.eventually (gt_mem_nhds zero_lt_one)))).exists
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hic.ne_top,
      ENNReal.add_ne_top.2 ⟨(isFrechetBarycenter_iff.1 hi).1, hiW.ne_top⟩⟩) (hcb i)
  · -- Minimality of `bᵢ` then gives `R_p(μ, c) ≤ d(c, bᵢ) + R_p(μ, y) + 2 W_p(μᵢ, μ)`.
    have hlim : Tendsto (fun i ↦ edist c (b i) +
        ((frechetRadius p μ y + wassersteinEDist p (μs i) μ) + wassersteinEDist p (μs i) μ))
        l' (𝓝 (frechetRadius p μ y)) := by
      simpa using hbc.add ((tendsto_const_nhds.add hμ').add hμ')
    refine ge_of_tendsto hlim (hb'.mono fun i hi ↦ (hcb i).trans ?_)
    gcongr
    exact (isFrechetMinimizer_iff.1 (isFrechetBarycenter_iff.1 hi).2 y).trans
      (frechetRadius_le_add_wassersteinEDist hp (μs i) μ y)

/-- **Boundedness of Fréchet barycenters.** If probability laws `μᵢ` converge in `W_p` to a
probability law `μ`, and `bᵢ` is eventually a Fréchet barycenter of `μᵢ`, then for every point
`x₀` the barycenters eventually lie within any distance `r > 2 R_p(μ, x₀)` of `x₀`. -/
theorem eventually_edist_lt_of_isFrechetBarycenter [∀ i, IsProbabilityMeasure (μs i)]
    {b : ι → X} (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0))
    (hb : ∀ᶠ i in l, IsFrechetBarycenter p (μs i) (b i)) {x₀ : X} {r : ℝ≥0∞}
    (hr : 2 * frechetRadius p μ x₀ < r) :
    ∀ᶠ i in l, edist (b i) x₀ < r := by
  -- `d(bᵢ, x₀) ≤ R_p(μᵢ, bᵢ) + R_p(μᵢ, x₀) ≤ 2 R_p(μᵢ, x₀)`, and `R_p(μᵢ, x₀) → R_p(μ, x₀)`.
  have hlim : Tendsto (fun i ↦ 2 * frechetRadius p (μs i) x₀) l
      (𝓝 (2 * frechetRadius p μ x₀)) :=
    ENNReal.Tendsto.const_mul (tendsto_frechetRadius_of_tendsto_wassersteinEDist hp hμ x₀)
      (Or.inr ENNReal.ofNat_ne_top)
  filter_upwards [hb, hlim.eventually (gt_mem_nhds hr)] with i hi hir
  calc edist (b i) x₀ ≤ frechetRadius p (μs i) (b i) + frechetRadius p (μs i) x₀ :=
        edist_le_frechetRadius_add hp (μs i) (b i) x₀
    _ ≤ frechetRadius p (μs i) x₀ + frechetRadius p (μs i) x₀ := by
      gcongr; exact isFrechetMinimizer_iff.1 (isFrechetBarycenter_iff.1 hi).2 x₀
    _ = 2 * frechetRadius p (μs i) x₀ := (two_mul _).symm
    _ < r := hir

end Lipschitz

section Proper

variable {Y : Type u} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [ProperSpace Y] {p : ℝ≥0∞} (hp : 1 ≤ p)
include hp

/-- On a proper metric space, if probability laws `μᵢ` converge in `W_p` to a probability law `μ`
and `bᵢ` is eventually a Fréchet barycenter of `μᵢ`, then the barycenters eventually lie in a
compact set. -/
private theorem exists_isCompact_eventually_mem {ι : Type v} {l : Filter ι} [l.NeBot]
    {μs : ι → Measure Y} [∀ i, IsProbabilityMeasure (μs i)] {μ : Measure Y} {b : ι → Y}
    (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0))
    (hb : ∀ᶠ i in l, IsFrechetBarycenter p (μs i) (b i)) :
    ∃ K, IsCompact K ∧ ∀ᶠ i in l, b i ∈ K := by
  -- Some barycenter `x₀ = bᵢ` has finite radius for `μ`, since `R_p(μ, bᵢ) ≤ R_p(μᵢ, bᵢ) + W_p`.
  obtain ⟨i, hi, hiW⟩ := (hb.and (hμ.eventually (gt_mem_nhds zero_lt_one))).exists
  have hx₀ : frechetRadius p μ (b i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(isFrechetBarycenter_iff.1 hi).1, hiW.ne_top⟩)
      (frechetRadius_le_add_wassersteinEDist' hp (μs i) μ (b i))
  set R := (frechetRadius p μ (b i)).toReal
  refine ⟨Metric.closedBall (b i) (2 * R + 1), isCompact_closedBall _ _, ?_⟩
  have hr : 2 * frechetRadius p μ (b i) < ENNReal.ofReal (2 * R + 1) := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hx₀, ENNReal.ofReal_one]
    exact ENNReal.lt_add_right (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hx₀) one_ne_zero
  filter_upwards [eventually_edist_lt_of_isFrechetBarycenter hp hμ hb hr] with j hj
  rw [Metric.mem_closedBall, dist_edist]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hj.le

/-- **Fréchet barycenters converge along a subsequence.** On a proper metric space, if probability
laws `μₙ` converge in `W_p` to a probability law `μ` and `bₙ` is a Fréchet barycenter of `μₙ` for
all large `n`, then some subsequence of the barycenters converges to a Fréchet barycenter of
`μ`. -/
theorem exists_isFrechetBarycenter_tendsto_comp {μs : ℕ → Measure Y}
    [∀ n, IsProbabilityMeasure (μs n)] {μ : Measure Y} [IsProbabilityMeasure μ] {b : ℕ → Y}
    (hμ : Tendsto (fun n ↦ wassersteinEDist p (μs n) μ) atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, IsFrechetBarycenter p (μs n) (b n)) :
    ∃ c, IsFrechetBarycenter p μ c ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (b ∘ φ) atTop (𝓝 c) := by
  obtain ⟨K, hK, hbK⟩ := exists_isCompact_eventually_mem hp hμ hb
  obtain ⟨c, -, φ, hφ, hbφ⟩ := tendsto_subseq_of_frequently_bounded hK.isBounded hbK.frequently
  exact ⟨c, isFrechetBarycenter_of_mapClusterPt hp hμ hb
    (hbφ.mapClusterPt.of_comp hφ.tendsto_atTop), φ, hφ, hbφ⟩

/-- **Fréchet barycenters converge to a unique limit barycenter.** On a proper metric space, if
probability laws `μᵢ` converge in `W_p` to a probability law `μ` whose only Fréchet barycenter is
`c`, and `bᵢ` is eventually a Fréchet barycenter of `μᵢ`, then `bᵢ → c`. -/
theorem tendsto_of_isFrechetBarycenter {ι : Type v} {l : Filter ι} {μs : ι → Measure Y}
    [∀ i, IsProbabilityMeasure (μs i)] {μ : Measure Y} [IsProbabilityMeasure μ] {b : ι → Y}
    {c : Y} (hμ : Tendsto (fun i ↦ wassersteinEDist p (μs i) μ) l (𝓝 0))
    (hb : ∀ᶠ i in l, IsFrechetBarycenter p (μs i) (b i))
    (hc : IsFrechetBarycenter p μ c) (hu : (frechetBarycenters p μ).Subsingleton) :
    Tendsto b l (𝓝 c) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  obtain ⟨K, hK, hbK⟩ := exists_isCompact_eventually_mem hp hμ hb
  exact hK.tendsto_nhds_of_unique_mapClusterPt hbK fun y _ hy ↦
    hu (mem_frechetBarycenters.2 (isFrechetBarycenter_of_mapClusterPt hp hμ hb hy))
      (mem_frechetBarycenters.2 hc)

end Proper

end TauCeti
