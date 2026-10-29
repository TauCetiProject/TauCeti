/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.DynamicPlan
public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Space

/-!
# Geodesics of the Gromov–Wasserstein space

Let `(X, μ, ωX)` and `(Y, ν, ωY)` be measured kernels with values in a metric space `Z`, and let
`π` be a plan on `X × Y`. Suppose that for `π ⊗ π`-almost every pair `q = ((x, y), (x', y'))` the
curve `t ↦ g q t` is a geodesic segment of `Z` from `ωX (x, x')` to `ωY (y, y')`. Then the
kernels `q ↦ g q t` on the carrier `(X × Y, π)` interpolate between the two measured kernels:

`GW_p (g · s, g · t) ≤ |s - t| * dis_p (π)`,

because along the diagonal plan of `π` the discrepancy at `q` is exactly `|s - t|` times the
discrepancy `edist (ωX (x, x')) (ωY (y, y'))` of the endpoints. At time `0` the interpolating kernel
is the pullback of `ωX` along the first projection, hence at distance `0` from `(X, μ, ωX)`, and
at time `1` it is at distance `0` from `(Y, ν, ωY)`.

When `π` is an optimal coupling, `dis_p (π) = GW_p (X, Y)`, so on the quotient
`GromovWassersteinSpace p Z` the classes of these kernels trace a constant-speed geodesic from the
class of `(X, μ, ωX)` to the class of `(Y, ν, ωY)`; the triangle inequality turns the displacement
bound into an equality. This needs a choice of geodesics in `Z` along which the interpolating
kernels are almost-everywhere strongly measurable. On a complete separable geodesic target,
`MeasureTheory.Measure.exists_measurable_ae_mem_geodesicPaths` chooses these geodesics relative
to the law of the pair of kernel values, without requiring a global Borel choice.
The companion module `Geodesic.Bicombing` treats supplied Borel or continuous bicombings.

The exponent `1 ≤ p ≤ ∞` is arbitrary, including `p = ∞`.

## Main results

* `TauCeti.gromovWassersteinEDist_le_of_ae_isGeodesicSegment`: the displacement bound between
  interpolating kernels.
* `TauCeti.gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_zero` and
  `TauCeti.gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_one`: the interpolation starts
  at the first measured kernel and ends at the second.
* `TauCeti.GromovWassersteinSpace.instIsGeodesicSpace`: over a complete separable geodesic target,
  `GromovWassersteinSpace p Z` is a geodesic space.

## References

* M. Bauer, F. Mémoli, T. Needham and M. Nishino, *The Z-Gromov–Wasserstein distance*,
  J. Mach. Learn. Res. 26 (2025), Theorem 45, geodesics by interpolation over an optimal coupling.
  The distance here uses the full distortion, without their factor of one half.
* K.-T. Sturm, *The space of spaces: curvature bounds and gradient flows on the space of metric
  measure spaces*, Mem. Amer. Math. Soc. 290 (2023), for the scalar case `Z = ℝ`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace TauCeti

section Interpolation

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoMetricSpace Z]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)} {ωX : X × X → Z} {ωY : Y × Y → Z}
  {g : (X × Y) × (X × Y) → ℝ → Z} {p : ℝ≥0∞}

/-- The discrepancy of the endpoint kernels is a.e. strongly measurable as soon as the
interpolating kernels at times `0` and `1` are, since it is their distance. -/
private theorem aestronglyMeasurable_dist_of_ae_isGeodesicSegment
    (hg : ∀ᵐ q ∂(π.prod π), IsGeodesicSegment (g q) (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
    (hgm : ∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun q ↦ g q t) (π.prod π)) :
    AEStronglyMeasurable (fun q ↦ dist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) (π.prod π) := by
  refine (continuous_dist.comp_aestronglyMeasurable₂ (hgm 0 (left_mem_Icc.2 zero_le_one))
    (hgm 1 (right_mem_Icc.2 zero_le_one))).congr ?_
  filter_upwards [hg] with q hq
  rw [hq.source, hq.target]

/-- **The displacement of interpolating kernels.** If `g q` is, for `π ⊗ π`-almost every `q`, a
geodesic segment from `ωX (q.1.1, q.2.1)` to `ωY (q.1.2, q.2.2)`, and the kernels `g · t` are a.e.
strongly measurable, then the kernels at times `s, t ∈ [0, 1]` on the carrier `(X × Y, π)` are at
Gromov–Wasserstein distance at most `|s - t|` times the distortion of `π`. -/
theorem gromovWassersteinEDist_le_of_ae_isGeodesicSegment [SFinite π]
    (hg : ∀ᵐ q ∂(π.prod π), IsGeodesicSegment (g q) (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
    (hgm : ∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun q ↦ g q t) (π.prod π)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (p : ℝ≥0∞) :
    gromovWassersteinEDist p π (fun q ↦ g q s) π (fun q ↦ g q t) ≤
      ENNReal.ofReal |s - t| * gromovWassersteinDistortion p ωX ωY π := by
  have hdist := aestronglyMeasurable_dist_of_ae_isGeodesicSegment hg hgm
  have hd : AEStronglyMeasurable (fun q ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
      (π.prod π) :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable hdist).congr
      (.of_forall fun _ ↦ (edist_dist _ _).symm)
  refine (gromovWassersteinEDist_le_eLpNorm (MeasurePreserving.id π) (MeasurePreserving.id π)
    (hgm s hs) (hgm t ht) p).trans_eq ?_
  -- Pass to the real distance, which the geodesic condition scales by the constant `|s - t|`.
  rw [gromovWassersteinDistortion_def,
    eLpNorm_congr_enorm_ae hd hdist (.of_forall fun q ↦ by simp [edist_dist,
      Real.enorm_of_nonneg dist_nonneg]),
    ← Real.enorm_of_nonneg (abs_nonneg (s - t)), ← eLpNorm_const_smul]
  refine eLpNorm_congr_enorm_ae
    (continuous_edist.comp_aestronglyMeasurable₂ (hgm s hs) (hgm t ht))
    (hdist.const_smul _) ?_
  filter_upwards [hg] with q hq
  simp only [id_eq, Pi.smul_apply, smul_eq_mul, enorm_eq_self, edist_dist, hq.dist_eq s hs t ht,
    Real.enorm_of_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)]

/-- **The interpolation starts at the first kernel.** If `π` couples `μ` and `ν` and `g q` is,
for `π ⊗ π`-almost every `q`, a geodesic segment starting at `ωX (q.1.1, q.2.1)`, then the kernel
`g · 0` on `(X × Y, π)` is at Gromov–Wasserstein distance `0` from `(X, μ, ωX)`. -/
theorem gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_zero [IsFiniteMeasure μ]
    (hπ : IsCoupling π μ ν) (hωX : AEStronglyMeasurable ωX (μ.prod μ))
    (hg : ∀ᵐ q ∂(π.prod π), IsGeodesicSegment (g q) (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
    (p : ℝ≥0∞) :
    gromovWassersteinEDist p π (fun q ↦ g q 0) μ ωX = 0 := by
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  have h0 : (fun q ↦ g q 0) =ᵐ[π.prod π] ωX ∘ Prod.map Prod.fst Prod.fst := by
    filter_upwards [hg] with q hq using hq.source
  rw [gromovWassersteinEDist_congr_ae h0 .rfl]
  exact gromovWassersteinEDist_comp_prodMap_eq_zero hπ.measurePreserving_fst hωX p

/-- **The interpolation ends at the second kernel.** If `π` couples `μ` and `ν` and `g q` is,
for `π ⊗ π`-almost every `q`, a geodesic segment ending at `ωY (q.1.2, q.2.2)`, then the kernel
`g · 1` on `(X × Y, π)` is at Gromov–Wasserstein distance `0` from `(Y, ν, ωY)`. -/
theorem gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_one [IsFiniteMeasure ν]
    (hπ : IsCoupling π μ ν) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (hg : ∀ᵐ q ∂(π.prod π), IsGeodesicSegment (g q) (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
    (p : ℝ≥0∞) :
    gromovWassersteinEDist p π (fun q ↦ g q 1) ν ωY = 0 := by
  have : IsFiniteMeasure π := hπ.isFiniteMeasure_of_right
  have h1 : (fun q ↦ g q 1) =ᵐ[π.prod π] ωY ∘ Prod.map Prod.snd Prod.snd := by
    filter_upwards [hg] with q hq using hq.target
  rw [gromovWassersteinEDist_congr_ae h1 .rfl]
  exact gromovWassersteinEDist_comp_prodMap_eq_zero hπ.measurePreserving_snd hωY p

/-- An interpolating kernel has finite `p`-size whenever the first kernel has finite `p`-size
about `z` and the plan has finite distortion: each value lies within the endpoint discrepancy of
the value of the first kernel. -/
private theorem memLp_edist_of_ae_isGeodesicSegment [SFinite π] (hp : 1 ≤ p)
    (hπ : IsCoupling π μ ν)
    (hg : ∀ᵐ q ∂(π.prod π), IsGeodesicSegment (g q) (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)))
    (hgm : ∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun q ↦ g q t) (π.prod π)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {z : Z} (hz : MemLp (fun q ↦ edist (ωX q) z) p (μ.prod μ))
    (hdis : gromovWassersteinDistortion p ωX ωY π ≠ ∞) :
    MemLp (fun q ↦ edist (g q t) z) p (π.prod π) := by
  have hgt := continuous_edist.comp_aestronglyMeasurable₂ (hgm t ht)
    (aestronglyMeasurable_const (b := z))
  have hle : eLpNorm (fun q ↦ edist (g q t) z) p (π.prod π) ≤
      eLpNorm ((fun q ↦ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2))) +
        fun q ↦ edist (ωX (q.1.1, q.2.1)) z) p (π.prod π) := by
    refine eLpNorm_mono_enorm_ae hgt ?_
    filter_upwards [hg] with q hq
    simp only [Pi.add_apply, enorm_eq_self]
    have hdt : dist (g q t) (g q 0) = t * dist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)) := by
      rw [dist_comm, hq.source, hq.dist_source_apply ht]
    calc edist (g q t) z ≤ edist (g q t) (g q 0) + edist (g q 0) z := edist_triangle _ _ _
      _ ≤ edist (ωX (q.1.1, q.2.1)) (ωY (q.1.2, q.2.2)) + edist (ωX (q.1.1, q.2.1)) z := by
        gcongr
        · rw [edist_dist, edist_dist, hdt]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left dist_nonneg ht.2)
        · rw [hq.source]
  have hX : eLpNorm (fun q ↦ edist (ωX (q.1.1, q.2.1)) z) p (π.prod π) ≠ ∞ :=
    (eLpNorm_comp_measurePreserving hz.aestronglyMeasurable
      (hπ.measurePreserving_fst.prod hπ.measurePreserving_fst)).trans_ne hz.eLpNorm_ne_top
  rw [gromovWassersteinDistortion_def] at hdis
  exact (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hdis, hX⟩)
    (hle.trans (eLpNorm_add_le hp))).lt_top

end Interpolation

namespace GromovWassersteinSpace

universe u v

variable {p : ℝ≥0∞} {Z : Type v} [MetricSpace Z] [Fact (1 ≤ p)]

/-- The GW space is geodesic as soon as every coupling of two presentations carries an
a.e. strongly measurable family of geodesic segments joining the paired kernel values: the classes
of the interpolating kernels over an optimal coupling form a geodesic segment. -/
theorem isGeodesicSpace_of_ae_isGeodesicSegment
    (h : ∀ (K L : GromovWassersteinPresentation.{u} p Z) (π : Measure (K.Carrier × L.Carrier)),
      IsCoupling π K.measure L.measure →
      ∃ g : (K.Carrier × L.Carrier) × (K.Carrier × L.Carrier) → ℝ → Z,
        (∀ᵐ q ∂(π.prod π),
          IsGeodesicSegment (g q) (K.kernel (q.1.1, q.2.1)) (L.kernel (q.1.2, q.2.2))) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun q ↦ g q t) (π.prod π)) :
    IsGeodesicSpace (GromovWassersteinSpace.{u} p Z) where
  exists_isGeodesicSegment x y := by
    obtain ⟨K, rfl⟩ := mk_surjective x
    obtain ⟨L, rfl⟩ := mk_surjective y
    obtain ⟨π, hπ, hπopt⟩ := exists_isCoupling_gromovWassersteinDistortion_eq_of_standardBorelSpace
      K.measure L.measure K.aestronglyMeasurable_kernel L.aestronglyMeasurable_kernel p
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    obtain ⟨g, hg, hgm⟩ := h K L π hπ
    have hdis : gromovWassersteinDistortion p K.kernel L.kernel π ≠ ∞ :=
      hπopt ▸ GromovWassersteinPresentation.gromovWassersteinEDist_ne_top Fact.out K L
    -- The interpolating presentations on the carrier `(K.Carrier × L.Carrier, π)`.
    let M : Icc (0 : ℝ) 1 → GromovWassersteinPresentation.{u} p Z := fun t ↦
      { Carrier := K.Carrier × L.Carrier
        measure := π
        kernel := fun q ↦ g q t
        aestronglyMeasurable_kernel := hgm t t.2
        finite_moment := K.finite_moment.imp fun _ hz ↦
          memLp_edist_of_ae_isGeodesicSegment Fact.out hπ hg hgm t.2 hz hdis }
    refine ⟨fun t ↦ mk (M (projIcc 0 1 zero_le_one t)), isGeodesicSegment_of_dist_le ?_ ?_ ?_⟩
    · rw [projIcc_left, ← edist_eq_zero, edist_mk]
      exact gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_zero hπ
        K.aestronglyMeasurable_kernel hg p
    · rw [projIcc_right, ← edist_eq_zero, edist_mk]
      exact gromovWassersteinEDist_eq_zero_of_ae_isGeodesicSegment_one hπ
        L.aestronglyMeasurable_kernel hg p
    · intro s hs t ht hst
      have hle := gromovWassersteinEDist_le_of_ae_isGeodesicSegment hg hgm hs ht p
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)] at hle
      rw [projIcc_of_mem _ hs, projIcc_of_mem _ ht, dist_mk, dist_mk, ← hπopt,
        ← ENNReal.toReal_ofReal (sub_nonneg.2 hst), ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdis) hle

/-- **The Gromov–Wasserstein space over a Polish geodesic target is geodesic.** Over a complete
separable geodesic metric space `Z`, any two weak-isomorphism classes of measured kernels are
joined by a geodesic segment of `GromovWassersteinSpace p Z`, for every `1 ≤ p ≤ ∞`. It is traced
by interpolating the two kernels along geodesics of `Z` chosen measurably relative to an optimal
coupling. -/
instance instIsGeodesicSpace [CompleteSpace Z] [SecondCountableTopology Z] [IsGeodesicSpace Z] :
    IsGeodesicSpace (GromovWassersteinSpace.{u} p Z) := by
  borelize Z
  refine isGeodesicSpace_of_ae_isGeodesicSegment fun K L π hπ ↦ ?_
  have : IsFiniteMeasure π := hπ.isFiniteMeasure
  -- The pair of kernel values, whose law the geodesics are chosen relative to.
  let κ : (K.Carrier × L.Carrier) × (K.Carrier × L.Carrier) → Z × Z :=
    fun q ↦ (K.kernel (q.1.1, q.2.1), L.kernel (q.1.2, q.2.2))
  have hκ : AEMeasurable κ (π.prod π) :=
    (hπ.aestronglyMeasurable_kernel_prodMk K.aestronglyMeasurable_kernel
      L.aestronglyMeasurable_kernel).aemeasurable
  obtain ⟨G, hG, hGae⟩ := ((π.prod π).map κ).exists_measurable_ae_mem_geodesicPaths
    (.of_forall fun z ↦ IsGeodesicSpace.exists_mem_geodesicPaths z.1 z.2)
  refine ⟨fun q ↦ IccExtend zero_le_one (G (κ q)), ?_, fun t _ ↦ ?_⟩
  · filter_upwards [ae_of_ae_map hκ hGae] with q ⟨hmem, h0, h1⟩
    have hseg := mem_geodesicPaths_iff_isGeodesicSegment.1 hmem
    rwa [h0, h1] at hseg
  · exact ((ContinuousMap.measurable_eval _).comp_aemeasurable
      (hG.comp_aemeasurable hκ)).aestronglyMeasurable

end GromovWassersteinSpace

end TauCeti
