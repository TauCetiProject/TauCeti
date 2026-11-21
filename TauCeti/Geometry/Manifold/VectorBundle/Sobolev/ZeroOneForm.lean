/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart

/-!
# Sobolev `(0,1)`-forms over a complex curve

Let `M` be a complex curve without boundary, a complex manifold modelled on `ℂ`, and let `V → M`
be a complex vector bundle with finite-dimensional model fibre `F`, regarded as a real vector
bundle. A `V`-valued one-form `η : T_x M → V x` is a `(0,1)`-form when it is complex antilinear,
`η (i v) = -(i • η v)` (`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm` for the almost
complex structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ M`). This file
constructs the target space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` of real Cauchy–Riemann operators on a
compact boundaryless curve as a closed subspace of the Sobolev space
`TauCeti.SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k` of `V`-valued one-forms, built on the charts
of a finite bundle atlas `A` of `V`.

The subspace theory is first developed for general chart data
`C : TauCeti.SectionChartData E (G →L[ℝ] F) S` whose model fibre is a space of continuous real
linear maps between complex normed spaces (`TauCeti.SectionChartData.antilinearSobolevSections`),
so that the same construction serves Riemann surfaces with boundary. An element belongs to the
subspace when its chart data are complex antilinear almost everywhere in every chart; it is the
intersection of the kernels of continuous linear maps, hence closed and complete whenever the
ambient Sobolev space is complete. When a section-level map lifts the model-fibre projection
`ContinuousLinearMap.complexAntilinearPartL` on every chart image, applying this constant linear
map chartwise gives a continuous projection (`TauCeti.SectionChartData.antilinearPartSobolevL`), so
the subspace is complemented, and the projection commutes with lowering the order, lowering the
exponent, and chartwise multiplication by smooth real functions.

For a complex manifold, `TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart` shows that a
one-form is a `(0,1)`-form at a point exactly when its chart reading `η : ℂ →L[ℝ] F` is complex
antilinear (`TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_coord_tangentHom`), and that its
`(0,1)`-part is read as `ContinuousLinearMap.complexAntilinearPartL` of its reading
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart`). Instantiating the chart-data
construction gives `TauCeti.zeroOneSobolevSections A μ p k`, its continuous projection
`TauCeti.zeroOnePartSobolevL`, the scale inclusions `TauCeti.zeroOneLowerOrderL` and
`TauCeti.zeroOneOfExponentLEL`, and multiplication by smooth real functions
`TauCeti.zeroOneContMDiffSMulL`.

## Main definitions

* `TauCeti.SectionChartData.antilinearSobolevSections`: the subspace of Sobolev sections of chart
  data with fibre `G →L[ℝ] F` whose chart readings are complex antilinear almost everywhere.
* `TauCeti.SectionChartData.antilinearPartSobolevL`,
  `TauCeti.SectionChartData.antilinearLowerOrderL`,
  `TauCeti.SectionChartData.antilinearOfExponentLEL`: the projection and scale inclusions on
  `antilinearSobolevSections`.
* `TauCeti.zeroOneSobolevSections A μ p k`: the `(0,1)`-forms in `W^{k,p}` of `V`-valued
  one-forms.
* `TauCeti.zeroOnePartSobolevL`: the continuous `(0,1)`-projection onto it.
* `TauCeti.zeroOneLowerOrderL`, `TauCeti.zeroOneOfExponentLEL`,
  `TauCeti.zeroOneContMDiffSMulL`: the order and exponent inclusions and multiplication by smooth
  real functions on `zeroOneSobolevSections`.

## Main results

* `TauCeti.SectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul`,
  `TauCeti.SectionChartData.restrict_antilinearPartSobolevL_of_chartValueL_ae_smul`: chartwise real
  scalar multiplication operators preserve `antilinearSobolevSections` and their restrictions
  commute with `antilinearPartSobolevL`.
* `TauCeti.mem_zeroOneSobolevSections_iff`,
  `TauCeti.mem_zeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.mem_zeroOneSobolevSections_of_isZeroOneForm`: characterizations of membership.
* `TauCeti.isClosed_zeroOneSobolevSections`, `TauCeti.zeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_zeroOneSobolevSections`: closedness, completeness, and
  complementedness.
* `TauCeti.zeroOnePartSobolevL_coe`, `TauCeti.chartValueL_zeroOnePartSobolevL_ae`,
  `TauCeti.zeroOnePartSobolevL_eq_zero_iff`, `TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`:
  properties of the `(0,1)`-projection.
* `TauCeti.zeroOneLowerOrderL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneOfExponentLEL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneContMDiffSMulL_zeroOnePartSobolevL`: the `(0,1)`-projection commutes with the
  scale inclusions and with multiplication by smooth real functions.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_apply
  complexAntilinearPartL_apply_I_smul complexAntilinearPartL_eq_self_iff
  complexAntilinearPartL_eq_zero_iff)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

universe u

namespace TauCeti

/-! ### Complex-antilinear Sobolev sections of general chart data -/

namespace SectionChartData

section Antilinear

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [FiniteDimensional ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E (G →L[ℝ] F) S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The subspace of `C.sobolevSections μ p k` consisting of elements whose chart data in every
chart are complex antilinear almost everywhere
(`SectionChartData.mem_antilinearSobolevSections_iff`). -/
def antilinearSobolevSections : Submodule ℝ (C.sobolevSections μ p k) :=
  ⨅ i : Fin C.n, LinearMap.ker
    (((complexAntilinearPartL - ContinuousLinearMap.id ℝ (G →L[ℝ] F)).compLpL p _).comp
      ((C.chartValueL μ p k i).comp (C.sobolevSections μ p k).subtypeL)).toLinearMap

instance antilinearSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (C.antilinearSobolevSections μ p k) :=
  (C.antilinearSobolevSections μ p k).normedAddCommGroup

instance antilinearSobolevSections.instNormedSpace :
    NormedSpace ℝ (C.antilinearSobolevSections μ p k) :=
  (C.antilinearSobolevSections μ p k).normedSpace

instance antilinearSobolevSections.instIsTopologicalAddGroup :
    IsTopologicalAddGroup (C.antilinearSobolevSections μ p k) :=
  Submodule.isTopologicalAddGroup (C.antilinearSobolevSections μ p k)

variable {C μ p k}

/-- An element of `C.sobolevSections μ p k` belongs to `C.antilinearSobolevSections μ p k` iff its
chart data in every chart are complex antilinear almost everywhere. -/
theorem mem_antilinearSobolevSections_iff {w : C.sobolevSections μ p k} :
    w ∈ C.antilinearSobolevSections μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), ∀ v : G,
        C.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • C.chartValueL μ p k i w y v) := by
  simp only [antilinearSobolevSections, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Lp.eq_zero_iff_ae_eq_zero]
  refine forall_congr' fun i ↦ ?_
  have hc := ContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ.restrict (C.image i))
    (complexAntilinearPartL - ContinuousLinearMap.id ℝ (G →L[ℝ] F)) (C.chartValueL μ p k i w)
  have key : (fun y ↦ (complexAntilinearPartL - ContinuousLinearMap.id ℝ _ :
      (G →L[ℝ] F) →L[ℝ] G →L[ℝ] F) (C.chartValueL μ p k i w y)) =ᵐ[μ.restrict (C.image i)] 0 ↔
      ∀ᵐ y ∂μ.restrict (C.image i), ∀ v : G,
        C.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • C.chartValueL μ p k i w y v) :=
    Filter.eventually_congr (Filter.Eventually.of_forall fun _ ↦
      sub_eq_zero.trans complexAntilinearPartL_eq_self_iff)
  exact ⟨fun h ↦ key.1 (hc.symm.trans h), fun h ↦ hc.trans (key.2 h)⟩

/-- `C.antilinearSobolevSections μ p k` is a closed subspace of `C.sobolevSections μ p k`. -/
theorem isClosed_antilinearSobolevSections :
    IsClosed (C.antilinearSobolevSections μ p k : Set (C.sobolevSections μ p k)) := by
  rw [antilinearSobolevSections, Submodule.coe_iInf]
  exact isClosed_iInter fun _ ↦ ContinuousLinearMap.isClosed_ker _

/-- When the ambient Sobolev section space is complete, its complex-antilinear subspace is a Banach
space. -/
instance antilinearSobolevSections.instCompleteSpace [CompleteSpace (C.sobolevSections μ p k)] :
    CompleteSpace (C.antilinearSobolevSections μ p k) :=
  C.isClosed_antilinearSobolevSections.completeSpace_coe

/-! #### The complex-antilinear projection on chart data -/

section Projection

variable (C μ p k)
  (proj : S → S)
  (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))

private theorem constMapL_mem_antilinearSobolevSections (w : C.sobolevSections μ p k) :
    C.constMapL μ p k complexAntilinearPartL proj hproj w ∈
      C.antilinearSobolevSections μ p k :=
  mem_antilinearSobolevSections_iff.2 fun i ↦
    (C.chartValueL_constMapL_ae μ p k hproj w i).mono fun y hy v ↦ by
      rw [hy]
      exact complexAntilinearPartL_apply_I_smul _ v

private theorem constMapL_eq_self_of_mem_antilinearSobolevSections {w : C.sobolevSections μ p k}
    (hw : w ∈ C.antilinearSobolevSections μ p k) :
    C.constMapL μ p k complexAntilinearPartL proj hproj w = w :=
  C.eq_of_chartValueL_ae_eq fun i ↦ by
    filter_upwards [C.chartValueL_constMapL_ae μ p k hproj w i,
      mem_antilinearSobolevSections_iff.1 hw i] with y h₁ h₂
    rw [h₁, complexAntilinearPartL_eq_self_iff.2 h₂]

/-- **The complex-antilinear projection on chart data.** When `proj : S → S` acts on chart readings
by `ContinuousLinearMap.complexAntilinearPartL`, applying `complexAntilinearPartL` chartwise gives a
continuous projection of `C.sobolevSections μ p k` onto `C.antilinearSobolevSections μ p k`. -/
def antilinearPartSobolevL :
    C.sobolevSections μ p k →L[ℝ] C.antilinearSobolevSections μ p k :=
  (C.constMapL μ p k complexAntilinearPartL proj hproj).codRestrict _
    (C.constMapL_mem_antilinearSobolevSections μ p k proj hproj)

variable {C μ p k}

/-- The components of `C.antilinearPartSobolevL μ p k proj hproj w` are those of `w` transformed by
the matrix of `ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem coe_coe_antilinearPartSobolevL (w : C.sobolevSections μ p k) :
    ((C.antilinearPartSobolevL μ p k proj hproj w : C.sobolevSections μ p k) :
        C.SobolevData μ p k) =
      C.constMapData μ p k complexAntilinearPartL w :=
  C.coe_constMapL (μ := μ) (p := p) (k := k) hproj w

/-- The chart data of `C.antilinearPartSobolevL μ p k proj hproj w` are the complex antilinear parts
of the chart data of `w`. -/
theorem chartValueL_antilinearPartSobolevL_ae (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p k i (C.antilinearPartSobolevL μ p k proj hproj w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ complexAntilinearPartL (C.chartValueL μ p k i w y) :=
  C.chartValueL_constMapL_ae μ p k hproj w i

/-- The complex-antilinear projection of `w` vanishes iff the chart data of `w` are complex linear
almost everywhere on the image of every chart. -/
theorem antilinearPartSobolevL_eq_zero_iff {w : C.sobolevSections μ p k} :
    C.antilinearPartSobolevL μ p k proj hproj w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), ∀ v : G,
        C.chartValueL μ p k i w y (Complex.I • v) = Complex.I • C.chartValueL μ p k i w y v := by
  have h0 (i : Fin C.n) : C.chartValueL μ p k i
      ((0 : C.sobolevSections μ p k) : C.SobolevData μ p k) =ᵐ[μ.restrict (C.image i)] 0 := by
    rw [ZeroMemClass.coe_zero, map_zero]
    exact Lp.coeFn_zero _ _ _
  rw [← ZeroMemClass.coe_eq_zero, antilinearPartSobolevL, ContinuousLinearMap.coe_codRestrict_apply]
  refine ⟨fun h i ↦ ?_, fun h ↦ C.eq_of_chartValueL_ae_eq fun i ↦ ?_⟩
  · filter_upwards [C.chartValueL_constMapL_ae μ p k hproj w i, h ▸ h0 i] with y h₁ h₂
    rw [← complexAntilinearPartL_eq_zero_iff, ← h₁, h₂, Pi.zero_apply]
  · filter_upwards [C.chartValueL_constMapL_ae μ p k hproj w i, h i, h0 i] with y h₁ h₂ h₃
    rw [h₁, complexAntilinearPartL_eq_zero_iff.2 h₂, h₃, Pi.zero_apply]

/-- If the chart data of `w` in chart `i` equal the reading of a section `s`, the chart data of its
complex-antilinear projection equal the reading of `proj s`. -/
theorem chartValueL_antilinearPartSobolevL_ae_coord {w : C.sobolevSections μ p k} {s : S}
    {i : Fin C.n} (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    C.chartValueL μ p k i (C.antilinearPartSobolevL μ p k proj hproj w) =ᵐ[μ.restrict (C.image i)]
      C.coord i (proj s) :=
  C.chartValueL_constMapL_ae_coord hproj hw

/-- The complex-antilinear projection fixes elements of `C.antilinearSobolevSections μ p k`. -/
@[simp]
theorem antilinearPartSobolevL_coe (w : C.antilinearSobolevSections μ p k) :
    C.antilinearPartSobolevL μ p k proj hproj w = w :=
  Subtype.ext (C.constMapL_eq_self_of_mem_antilinearSobolevSections μ p k proj hproj w.property)

/-- An element of `C.sobolevSections μ p k` is fixed by the complex-antilinear projection iff it
belongs to `C.antilinearSobolevSections μ p k`. -/
theorem coe_antilinearPartSobolevL_eq_self_iff {w : C.sobolevSections μ p k} :
    (C.antilinearPartSobolevL μ p k proj hproj w : C.sobolevSections μ p k) = w ↔
      w ∈ C.antilinearSobolevSections μ p k :=
  ⟨fun h ↦ h ▸ (C.antilinearPartSobolevL μ p k proj hproj w).property,
    C.constMapL_eq_self_of_mem_antilinearSobolevSections μ p k proj hproj⟩

/-- The complex-antilinear projection is surjective. -/
theorem antilinearPartSobolevL_surjective :
    Function.Surjective (C.antilinearPartSobolevL μ p k proj hproj) :=
  fun w ↦ ⟨w, C.antilinearPartSobolevL_coe proj hproj w⟩

end Projection

/-! #### Lowering the order -/

/-- Forgetting the highest derivative preserves `C.antilinearSobolevSections`. -/
theorem lowerOrderL_mem_antilinearSobolevSections {w : C.sobolevSections μ p (k + 1)}
    (hw : w ∈ C.antilinearSobolevSections μ p (k + 1)) :
    C.lowerOrderL μ p k w ∈ C.antilinearSobolevSections μ p k :=
  mem_antilinearSobolevSections_iff.2 fun i ↦ by
    simpa only [C.chartValueL_coe_lowerOrderL] using mem_antilinearSobolevSections_iff.1 hw i

variable (C μ p k) in
/-- The continuous inclusion of `C.antilinearSobolevSections μ p (k + 1)` into
`C.antilinearSobolevSections μ p k`. -/
def antilinearLowerOrderL :
    C.antilinearSobolevSections μ p (k + 1) →L[ℝ] C.antilinearSobolevSections μ p k :=
  (C.lowerOrderL μ p k).restrict fun _ ↦ C.lowerOrderL_mem_antilinearSobolevSections

@[simp]
theorem coe_antilinearLowerOrderL (w : C.antilinearSobolevSections μ p (k + 1)) :
    (C.antilinearLowerOrderL μ p k w : C.sobolevSections μ p k) = C.lowerOrderL μ p k w :=
  ContinuousLinearMap.coe_restrict_apply _ w

/-- The complex-antilinear projection commutes with forgetting the highest derivative. -/
theorem antilinearLowerOrderL_antilinearPartSobolevL (proj : S → S)
    (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))
    (w : C.sobolevSections μ p (k + 1)) :
    C.antilinearLowerOrderL μ p k (C.antilinearPartSobolevL μ p (k + 1) proj hproj w) =
      C.antilinearPartSobolevL μ p k proj hproj (C.lowerOrderL μ p k w) :=
  Subtype.ext (C.lowerOrderL_constMapL μ p k hproj w)

end Antilinear

/-! #### Lowering the integrability exponent -/

section Exponent

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [FiniteDimensional ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E (G →L[ℝ] F) S)
  (μ : Measure E) [μ.IsAddHaarMeasure] [∀ i, IsFiniteMeasure (μ.restrict (C.image i : Set E))]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (k : ℕ)

variable {C μ k} in
/-- Lowering the integrability exponent preserves `C.antilinearSobolevSections`. -/
theorem ofExponentLEL_mem_antilinearSobolevSections {w : C.sobolevSections μ q k}
    (hpq : p ≤ q) (hw : w ∈ C.antilinearSobolevSections μ q k) :
    C.ofExponentLEL μ k hpq w ∈ C.antilinearSobolevSections μ p k :=
  mem_antilinearSobolevSections_iff.2 fun i ↦ by
    simpa only [chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL] using
      mem_antilinearSobolevSections_iff.1 hw i

/-- For `p ≤ q`, the continuous inclusion of `C.antilinearSobolevSections μ q k` into
`C.antilinearSobolevSections μ p k`. -/
def antilinearOfExponentLEL (hpq : p ≤ q) :
    C.antilinearSobolevSections μ q k →L[ℝ] C.antilinearSobolevSections μ p k :=
  (C.ofExponentLEL μ k hpq).restrict fun _ ↦ C.ofExponentLEL_mem_antilinearSobolevSections hpq

variable {C μ k}

@[simp]
theorem coe_antilinearOfExponentLEL (hpq : p ≤ q) (w : C.antilinearSobolevSections μ q k) :
    (C.antilinearOfExponentLEL μ k hpq w : C.sobolevSections μ p k) =
      C.ofExponentLEL μ k hpq w :=
  ContinuousLinearMap.coe_restrict_apply _ w

/-- Lowering the exponent on `C.antilinearSobolevSections` is injective. -/
theorem antilinearOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (C.antilinearOfExponentLEL μ k hpq) := fun _ _ h ↦
  Subtype.ext <| C.ofExponentLEL_injective hpq <|
    (C.coe_antilinearOfExponentLEL hpq _).symm.trans <|
      (congrArg Subtype.val h).trans (C.coe_antilinearOfExponentLEL hpq _)

omit [Fact (1 ≤ q)] in
@[simp]
theorem antilinearOfExponentLEL_self (w : C.antilinearSobolevSections μ p k) :
    C.antilinearOfExponentLEL μ k le_rfl w = w :=
  Subtype.ext <| (C.coe_antilinearOfExponentLEL le_rfl w).trans (C.ofExponentLEL_self w.val)

@[simp]
theorem antilinearOfExponentLEL_antilinearOfExponentLEL {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (w : C.antilinearSobolevSections μ r k) :
    C.antilinearOfExponentLEL μ k hpq (C.antilinearOfExponentLEL μ k hqr w) =
      C.antilinearOfExponentLEL μ k (hpq.trans hqr) w :=
  Subtype.ext <| by simp [C.ofExponentLEL_ofExponentLEL]

/-- Lowering the exponent commutes with forgetting the highest derivative on
`C.antilinearSobolevSections`. -/
theorem antilinearLowerOrderL_antilinearOfExponentLEL (hpq : p ≤ q)
    (w : C.antilinearSobolevSections μ q (k + 1)) :
    C.antilinearLowerOrderL μ p k (C.antilinearOfExponentLEL μ (k + 1) hpq w) =
      C.antilinearOfExponentLEL μ k hpq (C.antilinearLowerOrderL μ q k w) :=
  Subtype.ext <| by simp [C.lowerOrderL_ofExponentLEL]

/-- Lowering the exponent commutes with the complex-antilinear projection. -/
theorem antilinearOfExponentLEL_antilinearPartSobolevL (proj : S → S)
    (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))
    (hpq : p ≤ q) (w : C.sobolevSections μ q k) :
    C.antilinearOfExponentLEL μ k hpq (C.antilinearPartSobolevL μ q k proj hproj w) =
      C.antilinearPartSobolevL μ p k proj hproj (C.ofExponentLEL μ k hpq w) :=
  Subtype.ext <| C.eq_of_chartValueL_ae_eq fun i ↦ by
    rw [coe_antilinearOfExponentLEL, chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    refine (C.chartValueL_antilinearPartSobolevL_ae proj hproj w i).trans ?_
    symm
    simpa only [chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL] using
      C.chartValueL_antilinearPartSobolevL_ae proj hproj (C.ofExponentLEL μ k hpq w) i

end Exponent

/-! #### Chartwise multiplication by real functions -/

section SMul

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [FiniteDimensional ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  {C : SectionChartData E (G →L[ℝ] F) S}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- Any operator on `C.sobolevSections μ p k` that acts chartwise almost everywhere by real scalar
multiplication preserves `C.antilinearSobolevSections μ p k`. -/
theorem mem_antilinearSobolevSections_of_chartValueL_ae_smul
    {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    {w : C.sobolevSections μ p k} (hw : w ∈ C.antilinearSobolevSections μ p k) :
    T w ∈ C.antilinearSobolevSections μ p k := by
  rw [mem_antilinearSobolevSections_iff] at hw ⊢
  intro i
  filter_upwards [hT w i, hw i] with y hy hwy v
  rw [hy, smul_apply, smul_apply, hwy v, smul_neg, smul_comm (ψ i y) Complex.I]

/-- Restricting a chartwise real-scalar-multiplication operator to `C.antilinearSobolevSections`
commutes with the complex-antilinear projection. -/
theorem restrict_antilinearPartSobolevL_of_chartValueL_ae_smul
    {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (proj : S → S)
    (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    T.restrict (fun _ ↦ C.mem_antilinearSobolevSections_of_chartValueL_ae_smul hT)
        (C.antilinearPartSobolevL μ p k proj hproj w) =
      C.antilinearPartSobolevL μ p k proj hproj (T w) :=
  Subtype.ext <| C.eq_of_chartValueL_ae_eq fun i ↦ by
    rw [ContinuousLinearMap.coe_restrict_apply]
    filter_upwards [hT (C.antilinearPartSobolevL μ p k proj hproj w) i,
      C.chartValueL_antilinearPartSobolevL_ae proj hproj w i,
      C.chartValueL_antilinearPartSobolevL_ae proj hproj (T w) i,
      hT w i] with y h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, map_smul]

end SMul

end SectionChartData

/-! ### The Sobolev space of `(0,1)`-forms over a boundaryless complex curve -/

section ZeroOne

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

omit [FiniteDimensional ℝ F] in
variable {A} in
private theorem mem_image_of_mem_image_tangentHom {i : Fin A.n} {y : ℂ}
    (hy : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i) : y ∈ A.image i :=
  A.mem_image.2 ((A.tangentHom 𝓘(ℝ, ℂ)).mem_image.1 hy)

omit [FiniteDimensional ℝ F] in
private theorem sectionChartData_coord_zeroOnePart [∀ x, ContinuousSMul ℂ (V x)]
    (i : Fin (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) {y : ℂ}
    (hy : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i
        (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i θ y) := by
  rw [(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_of_mem _ hy,
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_of_mem _ hy]
  exact A.coord_tangentHom_zeroOnePart i θ y

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The `(0,1)`-forms in the Sobolev space `W^{k,p}` of `V`-valued one-forms on a complex curve,
the space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)`: the elements whose chart data are complex antilinear almost
everywhere on the image of every chart (`TauCeti.mem_zeroOneSobolevSections_iff`). -/
def zeroOneSobolevSections : Submodule ℝ (SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearSobolevSections μ p k

instance zeroOneSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (zeroOneSobolevSections A μ p k) :=
  (zeroOneSobolevSections A μ p k).normedAddCommGroup

instance zeroOneSobolevSections.instNormedSpace :
    NormedSpace ℝ (zeroOneSobolevSections A μ p k) :=
  (zeroOneSobolevSections A μ p k).normedSpace

instance zeroOneSobolevSections.instIsTopologicalAddGroup :
    IsTopologicalAddGroup (zeroOneSobolevSections A μ p k) :=
  Submodule.isTopologicalAddGroup (zeroOneSobolevSections A μ p k)

variable {A μ p k}

/-- An element of `W^{k,p}` of `V`-valued one-forms is a `(0,1)`-form exactly when its chart data
are complex antilinear almost everywhere on the image of every chart. -/
theorem mem_zeroOneSobolevSections_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i), ∀ v : ℂ,
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y v) :=
  SectionChartData.mem_antilinearSobolevSections_iff

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
one-form `θ` is a `(0,1)`-form exactly when `θ` is a `(0,1)`-form almost everywhere in every
chart. -/
theorem mem_zeroOneSobolevSections_iff_isZeroOneForm
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i),
        (ofComplexManifold ℂ M).IsZeroOneForm (θ ((A.chart i).symm y)) := by
  rw [mem_zeroOneSobolevSections_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i,
    ae_restrict_mem ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i).isOpen.measurableSet]
    with y h hy
  rw [h, A.isZeroOneForm_iff_coord_tangentHom i θ (mem_image_of_mem_image_tangentHom hy)]

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
`(0,1)`-form is a `(0,1)`-form. -/
theorem mem_zeroOneSobolevSections_of_isZeroOneForm
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ)
    (hθ : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (θ x)) :
    w ∈ zeroOneSobolevSections A μ p k :=
  (mem_zeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦ .of_forall fun _ ↦ hθ _

/-- The `(0,1)`-forms form a closed subspace of `SobolevSection`. -/
theorem isClosed_zeroOneSobolevSections :
    IsClosed
      (zeroOneSobolevSections A μ p k : Set (SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)) :=
  SectionChartData.isClosed_antilinearSobolevSections

/-- **Completeness.** The Sobolev `(0,1)`-forms form a Banach space. -/
instance zeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (zeroOneSobolevSections A μ p k) :=
  SectionChartData.antilinearSobolevSections.instCompleteSpace

/-! ### The `(0,1)`-projection -/

variable (A μ p k) in
/-- **The `(0,1)`-projection.** The continuous projection of `W^{k,p}` of `V`-valued one-forms onto
the `(0,1)`-forms, applying `η ↦ ½ (η + i • η ∘ i)` to the chart data. It lifts the pointwise
`(0,1)`-projection `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`) and fixes the `(0,1)`-forms
(`TauCeti.zeroOnePartSobolevL_coe`). -/
def zeroOnePartSobolevL :
    SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearPartSobolevL μ p k
    (fun θ x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x))
    (fun i θ _ hy ↦ sectionChartData_coord_zeroOnePart A i θ hy)

/-- The components of the `(0,1)`-projection of `w` are those of `w` transformed by the matrix of
the complex antilinear part `ContinuousLinearMap.complexAntilinearPartL` of the model fibre. -/
@[simp]
theorem coe_coe_zeroOnePartSobolevL (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
    ((zeroOnePartSobolevL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.constMapData μ p k complexAntilinearPartL w :=
  SectionChartData.coe_coe_antilinearPartSobolevL _ _ w

/-- The chart data of the `(0,1)`-projection of `w` are the `(0,1)`-projections
`η ↦ ½ (η + i • η ∘ i)` of the chart data of `w`. -/
theorem chartValueL_zeroOnePartSobolevL_ae (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)
    (i : Fin A.n) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)] fun y ↦
        complexAntilinearPartL ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y) :=
  SectionChartData.chartValueL_antilinearPartSobolevL_ae _ _ w i

/-- The `(0,1)`-projection of `w` vanishes exactly when the chart data of `w` are complex linear
almost everywhere on the image of every chart. -/
theorem zeroOnePartSobolevL_eq_zero_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    zeroOnePartSobolevL A μ p k w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i), ∀ v : ℂ,
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          Complex.I • (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y v :=
  SectionChartData.antilinearPartSobolevL_eq_zero_iff _ _

variable [∀ x, ContinuousSMul ℂ (V x)] in
/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` are the readings of
a one-form `θ`, the chart data of its `(0,1)`-projection in chart `i` are the readings of the
`(0,1)`-part of `θ`. -/
theorem chartValueL_zeroOnePartSobolevL_ae_coord
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {i : Fin A.n}
    (hw : (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x) := by
  have hcoord := (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_ae_eq μ i
  exact (SectionChartData.chartValueL_antilinearPartSobolevL_ae_coord _ _
    (hw.trans (hcoord θ).symm)).trans (hcoord _)

/-- The `(0,1)`-projection fixes the `(0,1)`-forms. -/
@[simp]
theorem zeroOnePartSobolevL_coe (w : zeroOneSobolevSections A μ p k) :
    zeroOnePartSobolevL A μ p k w = w :=
  SectionChartData.antilinearPartSobolevL_coe _ _ w

/-- An element of `W^{k,p}` of `V`-valued one-forms is fixed by the `(0,1)`-projection exactly when
it is a `(0,1)`-form. -/
theorem coe_zeroOnePartSobolevL_eq_self_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    (zeroOnePartSobolevL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) = w ↔
      w ∈ zeroOneSobolevSections A μ p k :=
  SectionChartData.coe_antilinearPartSobolevL_eq_self_iff _ _

/-- The `(0,1)`-projection is onto the `(0,1)`-forms. -/
theorem zeroOnePartSobolevL_surjective : Function.Surjective (zeroOnePartSobolevL A μ p k) :=
  SectionChartData.antilinearPartSobolevL_surjective _ _

/-- **Complemented.** The `(0,1)`-forms are a complemented subspace of `W^{k,p}` of `V`-valued
one-forms, with the `(0,1)`-projection as a continuous projection onto it. -/
theorem closedComplemented_zeroOneSobolevSections :
    (zeroOneSobolevSections A μ p k).ClosedComplemented :=
  ⟨zeroOnePartSobolevL A μ p k, zeroOnePartSobolevL_coe⟩

/-! ### Lowering the order -/

/-- Forgetting the highest derivative of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem lowerOrderL_mem_zeroOneSobolevSections
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + 1)}
    (hw : w ∈ zeroOneSobolevSections A μ p (k + 1)) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrderL μ p k w ∈
      zeroOneSobolevSections A μ p k :=
  SectionChartData.lowerOrderL_mem_antilinearSobolevSections hw

variable (A μ p k) in
/-- The continuous inclusion of the `(0,1)`-forms of order `k + 1` into those of order `k`. -/
def zeroOneLowerOrderL :
    zeroOneSobolevSections A μ p (k + 1) →L[ℝ] zeroOneSobolevSections A μ p k :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearLowerOrderL μ p k

/-- The inclusion of `(0,1)`-forms forgets the highest derivative. -/
@[simp]
theorem coe_zeroOneLowerOrderL (w : zeroOneSobolevSections A μ p (k + 1)) :
    (zeroOneLowerOrderL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrderL μ p k w :=
  SectionChartData.coe_antilinearLowerOrderL w

/-- The `(0,1)`-projection commutes with forgetting the highest derivative. -/
theorem zeroOneLowerOrderL_zeroOnePartSobolevL
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOnePartSobolevL A μ p (k + 1) w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrderL μ p k w) :=
  SectionChartData.antilinearLowerOrderL_antilinearPartSobolevL _ _ w

/-! ### Lowering the integrability exponent -/

section Exponent

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (A μ k) in
/-- For `p ≤ q`, the continuous inclusion of the `(0,1)`-forms of exponent `q` into those of
exponent `p`. -/
def zeroOneOfExponentLEL (hpq : p ≤ q) :
    zeroOneSobolevSections A μ q k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearOfExponentLEL μ k hpq

@[simp]
theorem coe_zeroOneOfExponentLEL (hpq : p ≤ q) (w : zeroOneSobolevSections A μ q k) :
    (zeroOneOfExponentLEL A μ k hpq w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w :=
  SectionChartData.coe_antilinearOfExponentLEL hpq w

/-- Lowering the integrability exponent on `(0,1)`-forms is injective. -/
theorem zeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (zeroOneOfExponentLEL A μ k hpq) :=
  SectionChartData.antilinearOfExponentLEL_injective hpq

omit [Fact (1 ≤ q)] in
@[simp]
theorem zeroOneOfExponentLEL_self (w : zeroOneSobolevSections A μ p k) :
    zeroOneOfExponentLEL A μ k le_rfl w = w :=
  SectionChartData.antilinearOfExponentLEL_self w

@[simp]
theorem zeroOneOfExponentLEL_zeroOneOfExponentLEL {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (w : zeroOneSobolevSections A μ r k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOneOfExponentLEL A μ k hqr w) =
      zeroOneOfExponentLEL A μ k (hpq.trans hqr) w :=
  SectionChartData.antilinearOfExponentLEL_antilinearOfExponentLEL hpq hqr w

/-- Lowering the exponent commutes with forgetting the highest derivative on `(0,1)`-forms. -/
theorem zeroOneLowerOrderL_zeroOneOfExponentLEL (hpq : p ≤ q)
    (w : zeroOneSobolevSections A μ q (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOneOfExponentLEL A μ (k + 1) hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOneLowerOrderL A μ q k w) :=
  SectionChartData.antilinearLowerOrderL_antilinearOfExponentLEL hpq w

/-- Lowering the exponent commutes with the `(0,1)`-projection. -/
theorem zeroOneOfExponentLEL_zeroOnePartSobolevL (hpq : p ≤ q)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOnePartSobolevL A μ q k w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w) :=
  SectionChartData.antilinearOfExponentLEL_antilinearPartSobolevL _ _ hpq w

end Exponent

/-! ### Multiplication by smooth real functions -/

section SMul

variable {φ ψ : M → ℝ}

variable (A μ p k) in
/-- Multiplication by a smooth real function `φ : M → ℝ` on the Sobolev `(0,1)`-forms
`zeroOneSobolevSections A μ p k`. -/
def zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ) :
    zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ).restrict fun _ ↦
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul
      (SobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p k) :
    (zeroOneContMDiffSMulL A μ p k hφ w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ w :=
  ContinuousLinearMap.coe_restrict_apply _ w

@[simp]
theorem zeroOneContMDiffSMulL_const (c : ℝ) :
    zeroOneContMDiffSMulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w; exact Subtype.ext (DFunLike.congr_fun (SobolevSection.contMDiffSMulL_const c) w.val)

theorem zeroOneContMDiffSMulL_add (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.add hψ) =
      zeroOneContMDiffSMulL A μ p k hφ + zeroOneContMDiffSMulL A μ p k hψ := by
  ext1 w; exact Subtype.ext (DFunLike.congr_fun (SobolevSection.contMDiffSMulL_add hφ hψ) w.val)

theorem zeroOneContMDiffSMulL_mul (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.mul hψ) =
      (zeroOneContMDiffSMulL A μ p k hφ).comp (zeroOneContMDiffSMulL A μ p k hψ) := by
  ext1 w; exact Subtype.ext (DFunLike.congr_fun (SobolevSection.contMDiffSMulL_mul hφ hψ) w.val)

/-- Smooth real multiplication commutes with forgetting the highest derivative on `(0,1)`-forms. -/
theorem zeroOneLowerOrderL_zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOneContMDiffSMulL A μ p (k + 1) hφ w) =
      zeroOneContMDiffSMulL A μ p k hφ (zeroOneLowerOrderL A μ p k w) :=
  Subtype.ext (SobolevSection.lowerOrderL_contMDiffSMulL hφ w.val)

/-- Smooth real multiplication commutes with the `(0,1)`-projection. -/
theorem zeroOneContMDiffSMulL_zeroOnePartSobolevL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
    zeroOneContMDiffSMulL A μ p k hφ (zeroOnePartSobolevL A μ p k w) =
      zeroOnePartSobolevL A μ p k
        (SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ w) :=
  SectionChartData.restrict_antilinearPartSobolevL_of_chartValueL_ae_smul
    (SobolevSection.chartValueL_contMDiffSMulL_ae hφ) _ _ w

end SMul

end ZeroOne

end TauCeti
