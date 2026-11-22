/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent

/-!
# Complex-antilinear Sobolev sections of chart data

For general chart data `C : TauCeti.SectionChartData E (G →L[ℝ] F) S` whose model fibre consists
of real-linear maps between complex normed spaces `G` and `F`, this file constructs the closed
subspace `TauCeti.SectionChartData.antilinearSobolevSections` of Sobolev sections whose chart data
are complex antilinear almost everywhere in every chart.

When a section-level map `proj : S → S` acts on chart readings by
`ContinuousLinearMap.complexAntilinearPartL`, applying `complexAntilinearPartL` chartwise yields
the continuous projection `TauCeti.SectionChartData.antilinearPartSobolevL` onto this subspace.
The subspace and projection are compatible with forgetting derivatives
(`TauCeti.SectionChartData.antilinearLowerOrdersL`), lowering the integrability exponent
(`TauCeti.SectionChartData.antilinearOfExponentLEL`), and chartwise real scalar multiplication
(`TauCeti.SectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul`,
`TauCeti.SectionChartData.restrict_antilinearPartSobolevL_of_chartValueL_ae_smul`).

Instantiating this chart-data layer on the tangent-hom atlas yields both the boundaryless and
bordered Sobolev `(0,1)`-form spaces.

## Main definitions

* `TauCeti.SectionChartData.antilinearSobolevSections`: the subspace of complex-antilinear Sobolev
  sections of `C`.
* `TauCeti.SectionChartData.antilinearPartSobolevL`: the continuous projection onto
  `antilinearSobolevSections`.
* `TauCeti.SectionChartData.antilinearLowerOrdersL`: the continuous order inclusion on
  `antilinearSobolevSections`.
* `TauCeti.SectionChartData.antilinearOfExponentLEL`: the continuous exponent inclusion on
  `antilinearSobolevSections`.

## Main results

* `TauCeti.SectionChartData.mem_antilinearSobolevSections_iff`,
  `TauCeti.SectionChartData.isClosed_antilinearSobolevSections`,
  `TauCeti.SectionChartData.antilinearSobolevSections.instCompleteSpace`: membership, closedness,
  and completeness.
* `TauCeti.SectionChartData.antilinearPartSobolevL_coe`,
  `TauCeti.SectionChartData.antilinearPartSobolevL_eq_zero_iff`: properties of the projection.
* `TauCeti.SectionChartData.antilinearLowerOrdersL_injective`,
  `TauCeti.SectionChartData.antilinearOfExponentLEL_injective`: injectivity of the order and
  exponent inclusions.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., §2.4,
  Appendix C.1–C.2.
-/

public section

noncomputable section

open MeasureTheory Module Set
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_I_smul
  complexAntilinearPartL_eq_self_iff complexAntilinearPartL_eq_zero_iff)
open scoped ENNReal

universe u

namespace TauCeti

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

/-- As a section in `C.sobolevSections μ p k`, `C.antilinearPartSobolevL μ p k proj hproj w` is
`C.constMapL μ p k complexAntilinearPartL proj hproj w`. -/
theorem coe_antilinearPartSobolevL (w : C.sobolevSections μ p k) :
    (C.antilinearPartSobolevL μ p k proj hproj w : C.sobolevSections μ p k) =
      C.constMapL μ p k complexAntilinearPartL proj hproj w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ w

/-- The components of `C.antilinearPartSobolevL μ p k proj hproj w` are those of `w` transformed by
the matrix of `ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem coe_coe_antilinearPartSobolevL (w : C.sobolevSections μ p k) :
    ((C.antilinearPartSobolevL μ p k proj hproj w : C.sobolevSections μ p k) :
        C.SobolevData μ p k) =
      C.constMapData μ p k complexAntilinearPartL w := by
  rw [coe_antilinearPartSobolevL]
  exact C.coe_constMapL (μ := μ) (p := p) (k := k) hproj w

/-- The chart data of `C.antilinearPartSobolevL μ p k proj hproj w` are the complex antilinear parts
of the chart data of `w`. -/
theorem chartValueL_antilinearPartSobolevL_ae (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p k i (C.antilinearPartSobolevL μ p k proj hproj w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ complexAntilinearPartL (C.chartValueL μ p k i w y) := by
  rw [coe_antilinearPartSobolevL]
  exact C.chartValueL_constMapL_ae μ p k hproj w i

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
  rw [← ZeroMemClass.coe_eq_zero, coe_antilinearPartSobolevL]
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
      C.coord i (proj s) := by
  rw [coe_antilinearPartSobolevL]
  exact C.chartValueL_constMapL_ae_coord hproj hw

/-- The complex-antilinear projection fixes elements of `C.antilinearSobolevSections μ p k`. -/
@[simp]
theorem antilinearPartSobolevL_coe (w : C.antilinearSobolevSections μ p k) :
    C.antilinearPartSobolevL μ p k proj hproj w = w :=
  Subtype.ext <| (C.coe_antilinearPartSobolevL proj hproj w).trans
    (C.constMapL_eq_self_of_mem_antilinearSobolevSections μ p k proj hproj w.property)

/-- An element of `C.sobolevSections μ p k` is fixed by the complex-antilinear projection iff it
belongs to `C.antilinearSobolevSections μ p k`. -/
@[simp]
theorem coe_antilinearPartSobolevL_eq_self_iff {w : C.sobolevSections μ p k} :
    (C.antilinearPartSobolevL μ p k proj hproj w : C.sobolevSections μ p k) = w ↔
      w ∈ C.antilinearSobolevSections μ p k := by
  rw [coe_antilinearPartSobolevL]
  exact ⟨fun h ↦ h ▸ (C.antilinearPartSobolevL μ p k proj hproj w).property,
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

/-- Forgetting zero derivatives is the identity on `C.antilinearSobolevSections`. -/
@[simp]
theorem antilinearLowerOrdersL_zero (w : C.antilinearSobolevSections μ p k) :
    C.antilinearLowerOrdersL μ p k 0 w = w :=
  Subtype.ext <| by simp only [coe_antilinearLowerOrdersL, C.lowerOrdersL_zero]

omit k in
/-- Coercion to `C.sobolevSections` commutes with equality transport of the Sobolev order. -/
@[simp]
theorem coe_antilinearSobolevSections_eqRec {a b : ℕ} (h : a = b)
    (w : C.antilinearSobolevSections μ p a) :
    ((h ▸ w : C.antilinearSobolevSections μ p b) : C.sobolevSections μ p b) =
      h ▸ (w : C.sobolevSections μ p a) := by
  subst b; rfl

/-- Order inclusions on `C.antilinearSobolevSections` compose, with the source order reassociated
by `Nat.add_assoc`. -/
@[simp]
theorem antilinearLowerOrdersL_antilinearLowerOrdersL (d e : ℕ)
    (w : C.antilinearSobolevSections μ p ((k + d) + e)) :
    C.antilinearLowerOrdersL μ p k d (C.antilinearLowerOrdersL μ p (k + d) e w) =
      C.antilinearLowerOrdersL μ p k (d + e) ((Nat.add_assoc k d e) ▸ w) := by
  apply Subtype.ext
  simpa only [coe_antilinearLowerOrdersL, coe_antilinearSobolevSections_eqRec] using
    C.lowerOrdersL_lowerOrdersL μ p k d e w

/-- Forgetting `d + 1` derivatives on `C.antilinearSobolevSections` first forgets the highest
derivative. -/
theorem antilinearLowerOrdersL_succ (d : ℕ) :
    C.antilinearLowerOrdersL μ p k (d + 1) =
      (C.antilinearLowerOrdersL μ p k d).comp (C.antilinearLowerOrdersL μ p (k + d) 1) :=
  ContinuousLinearMap.ext fun w ↦ (C.antilinearLowerOrdersL_antilinearLowerOrdersL d 1 w).symm

/-- Lowering the order on `C.antilinearSobolevSections` is injective. -/
theorem antilinearLowerOrdersL_injective (d : ℕ) :
    Function.Injective (C.antilinearLowerOrdersL μ p k d) := fun _ _ hw ↦
  Subtype.ext <| C.lowerOrdersL_injective μ p k d <| by
    rw [← coe_antilinearLowerOrdersL, hw, coe_antilinearLowerOrdersL]

/-- The complex-antilinear projection commutes with forgetting derivatives. -/
theorem antilinearLowerOrdersL_antilinearPartSobolevL (d : ℕ) (proj : S → S)
    (hproj : ∀ i s, ∀ y ∈ C.image i, C.coord i (proj s) y = complexAntilinearPartL (C.coord i s y))
    (w : C.sobolevSections μ p (k + d)) :
    C.antilinearLowerOrdersL μ p k d (C.antilinearPartSobolevL μ p (k + d) proj hproj w) =
      C.antilinearPartSobolevL μ p k proj hproj (C.lowerOrdersL μ p k d w) := by
  apply Subtype.ext
  rw [coe_antilinearLowerOrdersL, coe_antilinearPartSobolevL, coe_antilinearPartSobolevL]
  exact C.lowerOrdersL_constMapL μ p k d hproj w

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

end TauCeti
