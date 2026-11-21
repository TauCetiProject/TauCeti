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

Let `M` be a boundaryless complex curve (modelled on `ℂ`) and `V → M` a complex vector bundle
with finite-dimensional fibre `F`, regarded as a real bundle. A `V`-valued one-form
`η : T_x M → V x` is a `(0,1)`-form when `η (i v) = -(i • η v)`
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm` for `ofComplexManifold ℂ M`). We construct
`W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` as a closed complemented Banach subspace of
`TauCeti.SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k` for a finite bundle atlas `A` of `V`.

First, for general chart data `C : TauCeti.SectionChartData E (G →L[ℝ] F) S` whose model fibre is
`G →L[ℝ] F`, `TauCeti.SectionChartData.antilinearSobolevSections` cuts out the sections whose
chart data are complex antilinear almost everywhere in every chart; a section-level map lifting
`ContinuousLinearMap.complexAntilinearPartL` gives the continuous projection
`TauCeti.SectionChartData.antilinearPartSobolevL`, which commutes with
`antilinearLowerOrdersL`, `antilinearOfExponentLEL`, and chartwise smooth real multiplication.
Using `TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart`, instantiating on
`(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData` yields `TauCeti.zeroOneSobolevSections A μ p k`,
`TauCeti.zeroOnePartSobolevL`, `TauCeti.zeroOneLowerOrdersL`, `TauCeti.zeroOneOfExponentLEL`, and
`TauCeti.zeroOneContMDiffSMulL`.

## Main definitions

* `TauCeti.SectionChartData.antilinearSobolevSections`,
  `TauCeti.SectionChartData.antilinearPartSobolevL`,
  `TauCeti.SectionChartData.antilinearLowerOrdersL`,
  `TauCeti.SectionChartData.antilinearOfExponentLEL`: chart-data subspace, projection, and scale
  inclusions.
* `TauCeti.zeroOneSobolevSections`, `TauCeti.zeroOnePartSobolevL`, `TauCeti.zeroOneLowerOrdersL`,
  `TauCeti.zeroOneOfExponentLEL`, `TauCeti.zeroOneContMDiffSMulL`: native `(0,1)`-forms,
  `(0,1)`-projection, order/exponent inclusions, and multiplication by smooth real functions.

## Main results

* `TauCeti.mem_zeroOneSobolevSections_iff`, `TauCeti.mem_zeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.isClosed_zeroOneSobolevSections`, `TauCeti.zeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_zeroOneSobolevSections`: membership, closedness, completeness, and
  complementedness.
* `TauCeti.zeroOnePartSobolevL_coe`, `TauCeti.zeroOnePartSobolevL_eq_zero_iff`,
  `TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`: properties of the `(0,1)`-projection.
* `TauCeti.zeroOneLowerOrdersL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneOfExponentLEL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneContMDiffSMulL_zeroOnePartSobolevL`: commutation with scale inclusions and smooth
  real multiplication.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix C.1–C.2.
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

/-- Forgetting derivatives preserves `C.antilinearSobolevSections`. -/
theorem lowerOrdersL_mem_antilinearSobolevSections (d : ℕ) {w : C.sobolevSections μ p (k + d)}
    (hw : w ∈ C.antilinearSobolevSections μ p (k + d)) :
    C.lowerOrdersL μ p k d w ∈ C.antilinearSobolevSections μ p k :=
  mem_antilinearSobolevSections_iff.2 fun i ↦ by
    simpa only [C.chartValueL_lowerOrdersL] using mem_antilinearSobolevSections_iff.1 hw i

variable (C μ p k) in
/-- The continuous inclusion of `C.antilinearSobolevSections μ p (k + d)` into
`C.antilinearSobolevSections μ p k`. -/
def antilinearLowerOrdersL (d : ℕ) :
    C.antilinearSobolevSections μ p (k + d) →L[ℝ] C.antilinearSobolevSections μ p k :=
  (C.lowerOrdersL μ p k d).restrict fun _ ↦ C.lowerOrdersL_mem_antilinearSobolevSections d

@[simp]
theorem coe_antilinearLowerOrdersL (d : ℕ) (w : C.antilinearSobolevSections μ p (k + d)) :
    (C.antilinearLowerOrdersL μ p k d w : C.sobolevSections μ p k) =
      C.lowerOrdersL μ p k d w :=
  ContinuousLinearMap.coe_restrict_apply _ w

/-- The complex-antilinear projection commutes with forgetting derivatives. -/
theorem antilinearLowerOrdersL_antilinearPartSobolevL (d : ℕ) (proj : S → S)
    (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))
    (w : C.sobolevSections μ p (k + d)) :
    C.antilinearLowerOrdersL μ p k d (C.antilinearPartSobolevL μ p (k + d) proj hproj w) =
      C.antilinearPartSobolevL μ p k proj hproj (C.lowerOrdersL μ p k d w) :=
  Subtype.ext (C.lowerOrdersL_constMapL μ p k d hproj w)

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

/-- Lowering the exponent commutes with forgetting derivatives on
`C.antilinearSobolevSections`. -/
theorem antilinearLowerOrdersL_antilinearOfExponentLEL (d : ℕ) (hpq : p ≤ q)
    (w : C.antilinearSobolevSections μ q (k + d)) :
    C.antilinearLowerOrdersL μ p k d (C.antilinearOfExponentLEL μ (k + d) hpq w) =
      C.antilinearOfExponentLEL μ k hpq (C.antilinearLowerOrdersL μ q k d w) :=
  Subtype.ext <| by simp [C.lowerOrdersL_ofExponentLEL]

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
private theorem sectionChartData_coord_zeroOnePart
    (i : Fin (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) {y : ℂ}
    (hy : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i
        (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i θ y) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
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

/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` are the readings of
a one-form `θ`, the chart data of its `(0,1)`-projection in chart `i` are the readings of the
`(0,1)`-part of `θ`. -/
theorem chartValueL_zeroOnePartSobolevL_ae_coord
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {i : Fin A.n}
    (hw : (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
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

/-- Forgetting derivatives preserves the native `(0,1)` condition. -/
theorem lowerOrdersL_mem_zeroOneSobolevSections (d : ℕ)
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + d)}
    (hw : w ∈ zeroOneSobolevSections A μ p (k + d)) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w ∈
      zeroOneSobolevSections A μ p k :=
  SectionChartData.lowerOrdersL_mem_antilinearSobolevSections d hw

variable (A μ p k) in
/-- The continuous inclusion of native `(0,1)`-forms from order `k + d` to order `k`. -/
def zeroOneLowerOrdersL (d : ℕ) :
    zeroOneSobolevSections A μ p (k + d) →L[ℝ] zeroOneSobolevSections A μ p k :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearLowerOrdersL μ p k d

/-- As a function, the native order inclusion is the restriction of the canonical order map. -/
theorem coeFn_zeroOneLowerOrdersL_eq_codRestrict (d : ℕ) :
    ⇑(zeroOneLowerOrdersL A μ p k d) =
      Set.codRestrict
        (⇑((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d) ∘
          ⇑(zeroOneSobolevSections A μ p (k + d)).subtypeL)
        (zeroOneSobolevSections A μ p k)
        (fun w ↦ lowerOrdersL_mem_zeroOneSobolevSections d w.property) :=
  funext fun w ↦ Subtype.ext (SectionChartData.coe_antilinearLowerOrdersL d w)

/-- The inclusion acts by the canonical order inclusion on the underlying one-form. -/
@[simp]
theorem coe_zeroOneLowerOrdersL (d : ℕ) (w : zeroOneSobolevSections A μ p (k + d)) :
    (zeroOneLowerOrdersL A μ p k d w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w :=
  SectionChartData.coe_antilinearLowerOrdersL d w

/-- Forgetting zero derivatives is the identity. -/
@[simp]
theorem zeroOneLowerOrdersL_zero (w : zeroOneSobolevSections A μ p k) :
    zeroOneLowerOrdersL A μ p k 0 w = w :=
  Subtype.ext <| by simp only [coe_zeroOneLowerOrdersL, SectionChartData.lowerOrdersL_zero]

omit k in
/-- Coercion to one-forms commutes with equality transport of the Sobolev order. -/
@[simp]
theorem coe_zeroOneSobolevSections_eqRec {a b : ℕ} (h : a = b)
    (w : zeroOneSobolevSections A μ p a) :
    ((h ▸ w : zeroOneSobolevSections A μ p b) : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p b) =
      h ▸ (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p a) := by
  subst b; rfl

/-- Native order inclusions compose, with the source order reassociated by `Nat.add_assoc`. -/
@[simp]
theorem zeroOneLowerOrdersL_zeroOneLowerOrdersL (d e : ℕ)
    (w : zeroOneSobolevSections A μ p ((k + d) + e)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneLowerOrdersL A μ p (k + d) e w) =
      zeroOneLowerOrdersL A μ p k (d + e) ((Nat.add_assoc k d e) ▸ w) := by
  apply Subtype.ext
  simpa only [coe_zeroOneLowerOrdersL, coe_zeroOneSobolevSections_eqRec] using
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL_lowerOrdersL μ p k d e w

/-- Forgetting `d + 1` derivatives first forgets the highest derivative. -/
theorem zeroOneLowerOrdersL_succ (d : ℕ) :
    zeroOneLowerOrdersL A μ p k (d + 1) =
      (zeroOneLowerOrdersL A μ p k d).comp (zeroOneLowerOrdersL A μ p (k + d) 1) :=
  ContinuousLinearMap.ext fun w ↦ (zeroOneLowerOrdersL_zeroOneLowerOrdersL d 1 w).symm

/-- The native order inclusion is injective. -/
theorem zeroOneLowerOrdersL_injective (d : ℕ) :
    Function.Injective (zeroOneLowerOrdersL A μ p k d) := fun _ _ hw ↦
  Subtype.ext <| (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL_injective μ p k d <| by
    rw [← coe_zeroOneLowerOrdersL, hw, coe_zeroOneLowerOrdersL]

/-- The native `(0,1)` projection commutes with forgetting derivatives. -/
theorem zeroOneLowerOrdersL_zeroOnePartSobolevL (d : ℕ)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOnePartSobolevL A μ p (k + d) w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearPartSobolevL d _ _ w

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

/-- Lowering the exponent commutes with forgetting derivatives on `(0,1)`-forms. -/
theorem zeroOneLowerOrdersL_zeroOneOfExponentLEL (d : ℕ) (hpq : p ≤ q)
    (w : zeroOneSobolevSections A μ q (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneOfExponentLEL A μ (k + d) hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOneLowerOrdersL A μ q k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearOfExponentLEL d hpq w

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

/-- Smooth real multiplication commutes with forgetting derivatives on `(0,1)`-forms. -/
theorem zeroOneLowerOrdersL_zeroOneContMDiffSMulL (d : ℕ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneContMDiffSMulL A μ p (k + d) hφ w) =
      zeroOneContMDiffSMulL A μ p k hφ (zeroOneLowerOrdersL A μ p k d w) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [zeroOneLowerOrdersL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    refine (congrArg (zeroOneLowerOrdersL A μ p k d) (Subtype.ext ?_)).trans (ih _)
    simp only [coe_zeroOneLowerOrdersL, coe_zeroOneContMDiffSMulL,
      SectionChartData.lowerOrdersL_one]
    exact SobolevSection.lowerOrderL_contMDiffSMulL hφ w.val

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
