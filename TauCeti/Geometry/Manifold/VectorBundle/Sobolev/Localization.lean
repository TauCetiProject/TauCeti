/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
import TauCeti.MeasureTheory.Function.Lp.Dual

/-!
# Functionals on `Lᵖ` sections localized to one chart

Let `A` be a finite bundle atlas of a smooth vector bundle `V → M` with finite-dimensional model
fibre `F`, over a manifold modelled on a finite-dimensional inner product space `E`, and let
`1 < p < ∞` with conjugate exponent `q`. A continuous functional `Λ` on the chart data of `Lᵖ`
sections is, over an open `Q` with closure in the image of chart `i`, integration of the chart-`i`
components against an `L^q` field: `Λ w = ∑_c ∫_Q H_c wᵢ_c` for every `Lᵖ` section `w` vanishing
off the points read in chart `i` inside `Q`
(`TauCeti.SobolevSection.exists_memLp_forall_apply_eq_sum_setIntegral`).

The block of every chart `j` of `Λ` is represented by `L^q` coefficients (the duality
`MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq`). A section vanishing off the points of
`Q` has chart-`j` data vanishing off the localized image `A.localizedImage i j Q`
(`TauCeti.SobolevSection.value_eq_zero_ae_of_mem_aeZeroOff`), where they are the transfer of its
chart-`i` data (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). So `Λ` restricted to such
sections is a continuous functional of the chart-`i` data over `Q`, again represented by `L^q`
coefficients.

## Main results

* `TauCeti.SobolevSection.value_eq_zero_ae_of_mem_aeZeroOff`: the chart data of a section vanishing
  off the points of `Q` vanish almost everywhere off the localized images.
* `TauCeti.SobolevSection.exists_memLp_forall_apply_eq_sum_setIntegral`: the local representation
  of a functional on `Lᵖ` sections.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.2.3 (the cokernel step).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal ContDiff

namespace TauCeti

open FiniteBundleAtlas

namespace SobolevSection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V) {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- The chart data of a section vanishing off the points read in chart `i` inside `Q` vanish almost
everywhere, in every chart `j`, off the localized image. -/
theorem value_eq_zero_ae_of_mem_aeZeroOff {i : Fin A.n} {Q : Opens E}
    (hQi : (Q : Set E) ⊆ A.image i) {w : SobolevSection A μ p 0}
    (hw : w ∈ aeZeroOff A μ p 0 ((A.chart i).symm '' Q))
    (j : Fin A.n) (c : Fin (finrank ℝ F)) :
    ∀ᵐ y ∂μ.restrict (A.sectionChartData.image j : Set E),
      y ∉ A.localizedImage i j Q →
        Wkp.value 0 ((w : A.sectionChartData.SobolevData μ p 0) j c) y = 0 := by
  filter_upwards [mem_aeZeroOff.1 hw j, A.sectionChartData.chartValueL_apply_ae μ p 0 j w,
    ae_restrict_mem (A.sectionChartData.image j).isOpen.measurableSet] with y hy hsum hyj hyP
  have hyj' : y ∈ A.image j := by rwa [sectionChartData_image] at hyj
  have h0 := hy (symm_notMem_image_of_notMem_localizedImage subset_rfl hQi hyj' hyP)
  rw [hsum] at h0
  simpa [Finsupp.single_apply] using congrArg (fun v ↦ (finBasis ℝ F).repr v c) h0

omit [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- A continuous functional on the chart data of sections is the sum over the charts of its
restrictions to the chart blocks. -/
private theorem apply_eq_sum_single
    (Λ' : A.sectionChartData.SobolevData μ p 0 →L[ℝ] ℝ)
    (v : A.sectionChartData.SobolevData μ p 0) :
    Λ' v = ∑ j, Λ' (Pi.single j (v j)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  exact map_sum Λ' _ _

variable {q : ℝ≥0∞} [hq₁ : Fact (1 ≤ q)] [hpq : p.HolderConjugate q]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- **Chartwise representation.** For `1 < p < ∞`, the restriction of a continuous functional on
the chart data of sections to the block of chart `j` is integration against an `L^q` field of
coefficients, one for each component. -/
private theorem exists_memLp_apply_single_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ' : A.sectionChartData.SobolevData μ p 0 →L[ℝ] ℝ)
    (j : Fin A.sectionChartData.n) :
    ∃ H : E → EuclideanSpace ℝ (Fin (finrank ℝ F)),
      MemLp H q (μ.restrict (A.sectionChartData.image j)) ∧
      ∀ g : Fin (finrank ℝ F) →
          Lp ℝ p (μ.restrict (A.sectionChartData.image j : Set E)),
        Λ' (Pi.single j g) = ∑ c, ∫ x in A.sectionChartData.image j, H x c * g c x ∂μ := by
  -- The block of chart `j` is `Fin _ → Wkp μ (image j) p 0`, which is `Fin _ → Lᵖ` by definition
  -- (`Wkp.value_zero` is `rfl`), so the duality for `Lᵖ` tuples applies to it directly.
  obtain ⟨H, hH, -, hΛ⟩ := MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq (p := q) (q := p)
    hp hp_top (EuclideanSpace.basisFun (Fin (finrank ℝ F)) ℝ)
    (Λ'.comp (ContinuousLinearMap.single ℝ
      (fun j ↦ Fin (finrank ℝ F) →
        Wkp μ (A.sectionChartData.image j) p 0) j))
  exact ⟨H, hH, fun g ↦ by simpa [EuclideanSpace.inner_single_right] using hΛ g⟩

include hq₁ hpq in
/-- **Localizing a functional to one chart.** Let `Q` be open with closure in the image of chart
`i`, and `1 < p < ∞`. For a continuous functional `Λ'` on the chart data of sections, there is a
continuous functional `ℓ` on chart-`i` data over `Q` with `Λ' w = ℓ (w_i|_Q)` for every `Lᵖ`
section `w` whose chart-`j` data vanish off the localized image, for every chart `j`. -/
private theorem exists_localization [T2Space M] (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ' : A.sectionChartData.SobolevData μ p 0 →L[ℝ] ℝ)
    (i : Fin A.sectionChartData.n) {Q : Opens E}
    (hQi : closure (Q : Set E) ⊆ A.image i)
    (hQ : Q ≤ A.sectionChartData.image i) :
    ∃ ℓ : (Fin (finrank ℝ F) → Wkp μ Q p 0) →L[ℝ] ℝ,
      ∀ w ∈ A.sectionChartData.sobolevSections μ p 0,
        (∀ (j : Fin A.sectionChartData.n) c,
          ∀ᵐ y ∂μ.restrict (A.sectionChartData.image j : Set E),
          y ∉ A.localizedImage i j Q → Wkp.value 0 (w j c) y = 0) →
        Λ' w = ℓ fun c ↦ Wkp.restrictL hQ 0 (w i c) := by
  choose H hH hΛ using exists_memLp_apply_single_eq (q := q) A hp hp_top Λ'
  -- The localized images and the transfer of chart-`i` data to them.
  set P : Fin A.sectionChartData.n → Opens E := fun j ↦ A.localizedImage i j Q
  have hPj (j : Fin A.n) :
      P j ≤ A.sectionChartData.image j := by
    rw [sectionChartData_image]
    exact A.localizedImage_le_image i j Q
  have hPc (j : Fin A.sectionChartData.n) :=
    A.isCompact_closure_localizedImage i j Q
  have hPD (j : Fin A.sectionChartData.n) :=
    A.closure_localizedImage_subset_transferDomain (j := j) hQi
  have hPQ (j : Fin A.sectionChartData.n) := A.mapsTo_localizedImage i j Q
  -- The coefficients of chart `j`, restricted to its localized image.
  set G : (j : Fin A.sectionChartData.n) → Fin (finrank ℝ F) →
      Lp ℝ q (μ.restrict (P j : Set E)) :=
    fun j c ↦ (((hH j).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) c)).mono_measure
      (Measure.restrict_mono (hPj j) le_rfl)).toLp _
  refine ⟨∑ j, ∑ c, (MeasureTheory.Lp.toDual ℝ _ q p (G j c)).comp ((Wkp.valueL 0).comp
    ((ContinuousLinearMap.proj c).comp (A.transferL μ p 0 i j (hPc j) (hPD j)
      (hPQ j)))), fun w hw hvan ↦ ?_⟩
  rw [apply_eq_sum_single A Λ' w]
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hΛ j]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  -- The chart-`j` data on the localized image are the transfer of the chart-`i` data over `Q`.
  -- `restrictL_eq_transferL` is stated for the chart images `A.image`, which are the domains
  -- `A.sectionChartData.image` of the chart data by definition (`sectionChartData_image`).
  have htr : Wkp.restrictL (hPj j) 0 (w j c) =
      A.transferL μ p 0 i j (hPc j) (hPD j) (hPQ j) (fun l ↦ Wkp.restrictL hQ 0 (w i l)) c :=
    A.restrictL_eq_transferL μ p 0 hw (A.localizedImage_subset_overlap i j Q) (hPc j) (hPD j) hQ
      (hPQ j) c
  rw [← htr, Wkp.valueL_apply, MeasureTheory.Lp.toDual_apply]
  -- Pass from the chart image to the localized image, where the data are the restricted data.
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (A.sectionChartData.image j).isOpen.measurableSet.nullMeasurableSet (hPj j) ?_]
  · refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (((hH j).continuousLinearMap_comp
        (EuclideanSpace.proj (𝕜 := ℝ) c)).mono_measure (Measure.restrict_mono (hPj j) le_rfl)),
      Wkp.value_restrictL_ae (hPj j) 0 (w j c)] with y hy₁ hy₂
    simp only [G]
    rw [hy₁, hy₂, Wkp.value_zero, PiLp.proj_apply]
  · have h := (ae_restrict_iff' (A.sectionChartData.image j).isOpen.measurableSet).1
      (hvan j c)
    filter_upwards [h] with y hy hyd
    rw [← Wkp.value_zero (w j c), hy hyd.1 hyd.2, mul_zero]

include hq₁ hpq in
/-- **Local representation of functionals on `Lᵖ` sections.** Let `1 < p < ∞`, `q` the conjugate
exponent, `Λ` a continuous functional on the chart data of `Lᵖ` sections, and `Q` open with closure
in the image of chart `i`. There is an `L^q` field `H` of coefficients on `Q`, one for each
component, with `Λ w = ∑_c ∫_Q H_c wᵢ_c` for every `Lᵖ` section `w` vanishing almost everywhere
off the points read in chart `i` inside `Q`. -/
theorem exists_memLp_forall_apply_eq_sum_setIntegral [T2Space M] (hp : 1 < p) (hp_top : p ≠ ⊤)
    (Λ : A.sectionChartData.SobolevData μ p 0 →L[ℝ] ℝ) (i : Fin A.n) {Q : Opens E}
    (hQi : closure (Q : Set E) ⊆ A.image i) :
    ∃ H : E → EuclideanSpace ℝ (Fin (finrank ℝ F)), MemLp H q (μ.restrict Q) ∧
      ∀ w : SobolevSection A μ p 0, w ∈ aeZeroOff A μ p 0 ((A.chart i).symm '' Q) →
        Λ w = ∑ c, ∫ z in Q, H z c *
          Wkp.value 0 ((w : A.sectionChartData.SobolevData μ p 0) i c) z ∂μ := by
  have hQ : Q ≤ A.sectionChartData.image i := by
    rw [sectionChartData_image]
    exact fun y hy ↦ hQi (subset_closure hy)
  obtain ⟨ℓ, hℓ⟩ := exists_localization (q := q) A hp hp_top Λ i hQi hQ
  -- `ℓ` acts on `Fin _ → Wkp μ Q p 0`, which is `Fin _ → Lᵖ(Q)` by definition (`Wkp.value_zero`
  -- is `rfl`), so it is read as a functional on `Lᵖ` tuples.
  obtain ⟨H, hH, -, hHℓ⟩ := MeasureTheory.Lp.exists_memLp_forall_dual_pi_apply_eq (p := q) (q := p)
    (μ := μ.restrict (Q : Set E)) hp hp_top (EuclideanSpace.basisFun (Fin (finrank ℝ F)) ℝ)
    (ℓ : StrongDual ℝ (Fin (finrank ℝ F) → Lp ℝ p (μ.restrict (Q : Set E))))
  refine ⟨H, hH, fun w hw ↦ ?_⟩
  rw [hℓ _ w.prop (value_eq_zero_ae_of_mem_aeZeroOff A (fun y hy ↦ hQi (subset_closure hy)) hw),
    hHℓ]
  simp only [EuclideanSpace.inner_basisFun_real]
  refine Finset.sum_congr rfl fun c _ ↦ integral_congr_ae ?_
  -- On `Q`, the restricted data are the chart-`i` data.
  filter_upwards [Wkp.value_restrictL_ae hQ 0 ((w : A.sectionChartData.SobolevData μ p 0) i c)]
    with z hz
  rw [← Wkp.value_zero (Wkp.restrictL hQ 0 _), hz]

end SobolevSection

end TauCeti
