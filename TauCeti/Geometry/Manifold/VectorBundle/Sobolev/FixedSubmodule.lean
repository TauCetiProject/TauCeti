/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent

/-!
# Subspaces of Sobolev sections cut out by constant fibre operators

Let `C : TauCeti.SectionChartData E F S` be chart data reading sections in `S` as `F`-valued
functions on finitely many open subsets `C.image i` of a finite-dimensional real inner product space
`E`, and let `P : F →L[ℝ] F` be a continuous linear endomorphism of the model fibre. This file
studies the subspace `C.fixedSubmodule μ p k P` of the Sobolev space `C.sobolevSections μ p k`
consisting of the elements whose chart data are fixed by `P` almost everywhere on every chart image.

Such subspaces arise whenever a geometric subbundle is read in every preferred chart as the fixed
subspace of a single linear operator on the model fibre: for instance the `(0,1)`-forms with values
in a complex vector bundle over a Riemann surface without or with boundary are cut out on chart
readings by `ContinuousLinearMap.complexAntilinearPartL`.

Because `C.fixedSubmodule μ p k P` is the intersection over the finitely many charts of the kernels
of continuous linear maps into `Lᵖ`, it is closed
(`TauCeti.SectionChartData.isClosed_fixedSubmodule`) and complete whenever `C.sobolevSections μ p k`
is complete. Lowering the Sobolev order (`TauCeti.SectionChartData.fixedLowerOrderL`), lowering the
integrability exponent on charts of finite measure (`TauCeti.SectionChartData.fixedOfExponentLEL`),
and applying any continuous linear endomorphism that acts chartwise as multiplication by real-valued
functions (`TauCeti.SectionChartData.fixedSMulEndL`) all preserve the subspace.

When `P` is idempotent (`IsIdempotentElem P`) and lifts a map `Ψ : S → S` on sections, applying the
constant matrix of `P` componentwise via `TauCeti.SectionChartData.constMapL` gives a continuous
linear retraction `C.projFixedL μ p k hP hΨ` onto `C.fixedSubmodule μ p k P`
(`TauCeti.SectionChartData.projFixedL_coe`), showing that the subspace is continuously complemented.
The retraction commutes with order inclusions, exponent inclusions and chartwise scalar multiplier
operators.

## Main definitions

* `TauCeti.SectionChartData.fixedSubmodule`: the submodule of `C.sobolevSections μ p k` where chart
  data are fixed by `P : F →L[ℝ] F` almost everywhere on every chart image.
* `TauCeti.SectionChartData.projFixedL`: the continuous linear retraction onto `fixedSubmodule` when
  `P` is idempotent and lifts `Ψ : S → S`.
* `TauCeti.SectionChartData.fixedLowerOrderL`, `TauCeti.SectionChartData.fixedOfExponentLEL`,
  `TauCeti.SectionChartData.fixedSMulEndL`: order lowering, exponent lowering and chartwise scalar
  multiplier endomorphisms restricted to `fixedSubmodule`.

## Main results

* `TauCeti.SectionChartData.mem_fixedSubmodule_iff`,
  `TauCeti.SectionChartData.mem_fixedSubmodule_iff_coord`: characterizations of membership by chart
  data and by section readings.
* `TauCeti.SectionChartData.isClosed_fixedSubmodule`,
  `TauCeti.SectionChartData.fixedSubmodule.instCompleteSpace`: closedness and completeness.
* `TauCeti.SectionChartData.projFixedL_coe`,
  `TauCeti.SectionChartData.coe_projFixedL_eq_self_iff`: `projFixedL` is a retraction onto
  `fixedSubmodule`.
* `TauCeti.SectionChartData.fixedLowerOrderL_projFixedL`,
  `TauCeti.SectionChartData.fixedOfExponentLEL_projFixedL`,
  `TauCeti.SectionChartData.fixedSMulEndL_projFixedL`: `projFixedL` commutes with lowering the
  order, lowering the exponent and chartwise scalar multipliers.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

universe u

namespace TauCeti

namespace SectionChartData

section FixedSubmodule

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The submodule of `C.sobolevSections μ p k` consisting of the elements whose chart data are fixed
by `P : F →L[ℝ] F` almost everywhere on the image of every chart. -/
def fixedSubmodule (P : F →L[ℝ] F) : Submodule ℝ (C.sobolevSections μ p k) :=
  ⨅ i : Fin C.n, LinearMap.ker
    (((P - ContinuousLinearMap.id ℝ F).compLpL p _).comp
      ((C.chartValueL μ p k i).comp (C.sobolevSections μ p k).subtypeL)).toLinearMap

variable {C μ p k}

/-- An element of `C.sobolevSections μ p k` belongs to `C.fixedSubmodule μ p k P` if and only if its
chart data in every chart `i` are fixed by `P` almost everywhere on `C.image i`. -/
theorem mem_fixedSubmodule_iff {P : F →L[ℝ] F} {w : C.sobolevSections μ p k} :
    w ∈ C.fixedSubmodule μ p k P ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i),
        P (C.chartValueL μ p k i w y) = C.chartValueL μ p k i w y := by
  simp only [fixedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i ↦ ?_
  have hc := ContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ.restrict (C.image i))
    (P - ContinuousLinearMap.id ℝ F) (C.chartValueL μ p k i w)
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.eq_zero_iff_ae_eq_zero]
  have key : (fun y ↦ (P - ContinuousLinearMap.id ℝ F) (C.chartValueL μ p k i w y))
        =ᵐ[μ.restrict (C.image i)] 0 ↔
      ∀ᵐ y ∂μ.restrict (C.image i),
        P (C.chartValueL μ p k i w y) = C.chartValueL μ p k i w y :=
    Filter.eventually_congr (Filter.Eventually.of_forall fun _ ↦ sub_eq_zero)
  exact ⟨fun h ↦ key.1 (hc.symm.trans h), fun h ↦ hc.trans (key.2 h)⟩

/-- An element whose chart data equal the readings of a section `s` almost everywhere belongs to
`C.fixedSubmodule μ p k P` if and only if the readings of `s` are fixed by `P` almost everywhere in
every chart. -/
theorem mem_fixedSubmodule_iff_coord {P : F →L[ℝ] F} {w : C.sobolevSections μ p k} {s : S}
    (hw : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    w ∈ C.fixedSubmodule μ p k P ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), P (C.coord i s y) = C.coord i s y := by
  rw [mem_fixedSubmodule_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i] with y hy
  rw [hy]

/-- An element whose chart data equal the readings of a section fixed by `P` on every chart image
belongs to `C.fixedSubmodule μ p k P`. -/
theorem mem_fixedSubmodule_of_coord {P : F →L[ℝ] F} {w : C.sobolevSections μ p k} {s : S}
    (hw : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s)
    (hs : ∀ i, ∀ y ∈ C.image i, P (C.coord i s y) = C.coord i s y) :
    w ∈ C.fixedSubmodule μ p k P :=
  (mem_fixedSubmodule_iff_coord hw).2 fun i ↦
    (ae_restrict_mem (C.image i).isOpen.measurableSet).mono (hs i)

variable (C μ p k) in
/-- `C.fixedSubmodule μ p k P` is closed in `C.sobolevSections μ p k`. -/
theorem isClosed_fixedSubmodule (P : F →L[ℝ] F) :
    IsClosed (C.fixedSubmodule μ p k P : Set (C.sobolevSections μ p k)) := by
  rw [fixedSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun _ ↦ ContinuousLinearMap.isClosed_ker _

variable (C μ p k) in
/-- Normed additive group structure on `C.fixedSubmodule μ p k P`, registered directly on the head
symbol so continuous linear operator spaces on `C.fixedSubmodule μ p k P` do not time out searching
across nested `Submodule` coercions. -/
noncomputable instance fixedSubmodule.instNormedAddCommGroup (P : F →L[ℝ] F) :
    NormedAddCommGroup (C.fixedSubmodule μ p k P) :=
  Submodule.normedAddCommGroup _

variable (C μ p k) in
/-- Real normed space structure on `C.fixedSubmodule μ p k P`. -/
noncomputable instance fixedSubmodule.instNormedSpace (P : F →L[ℝ] F) :
    NormedSpace ℝ (C.fixedSubmodule μ p k P) :=
  Submodule.normedSpace _

variable (C μ p k) in
/-- When `C.sobolevSections μ p k` is complete, so is `C.fixedSubmodule μ p k P`. -/
instance fixedSubmodule.instCompleteSpace [CompleteSpace (C.sobolevSections μ p k)]
    (P : F →L[ℝ] F) : CompleteSpace (C.fixedSubmodule μ p k P) :=
  (C.isClosed_fixedSubmodule μ p k P).completeSpace_coe

/-! ### Constant fibre maps and idempotent projections -/

section Projection

variable {P : F →L[ℝ] F} {Ψ : S → S}

/-- When `P` lifts `Ψ : S → S`, an element of `C.sobolevSections μ p k` is fixed by
`C.constMapL μ p k P Ψ hΨ` if and only if it belongs to `C.fixedSubmodule μ p k P`. -/
theorem constMapL_eq_self_iff
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    {w : C.sobolevSections μ p k} :
    C.constMapL μ p k P Ψ hΨ w = w ↔ w ∈ C.fixedSubmodule μ p k P := by
  rw [mem_fixedSubmodule_iff]
  refine ⟨fun h i ↦ ?_, fun h ↦ eq_of_chartValueL_ae_eq fun i ↦ ?_⟩
  · filter_upwards [C.chartValueL_constMapL_ae μ p k hΨ w i] with y hy
    simpa [h] using hy.symm
  · exact (C.chartValueL_constMapL_ae μ p k hΨ w i).trans (h i)

variable (C μ p k) in
/-- When `P` lifts `Ψ : S → S`, `C.fixedSubmodule μ p k P` is the fixed submodule of the
endomorphism `C.constMapL μ p k P Ψ hΨ`. -/
theorem fixedSubmodule_eq_fixedSubmodule_constMapL
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y)) :
    C.fixedSubmodule μ p k P = (C.constMapL μ p k P Ψ hΨ).toLinearMap.fixedSubmodule :=
  Submodule.ext fun _ ↦ (constMapL_eq_self_iff hΨ).symm

/-- `C.constMapL μ p k P Ψ hΨ w` vanishes if and only if the chart data of `w` lie in `ker P` almost
everywhere on every chart image. -/
theorem constMapL_eq_zero_iff
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    {w : C.sobolevSections μ p k} :
    C.constMapL μ p k P Ψ hΨ w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), P (C.chartValueL μ p k i w y) = 0 := by
  have h0 (i : Fin C.n) : C.chartValueL μ p k i
      ((0 : C.sobolevSections μ p k) : C.SobolevData μ p k) =ᵐ[μ.restrict (C.image i)] 0 := by
    rw [ZeroMemClass.coe_zero, map_zero]
    exact Lp.coeFn_zero _ _ _
  refine ⟨fun h i ↦ ?_, fun h ↦ eq_of_chartValueL_ae_eq fun i ↦ ?_⟩
  · filter_upwards [C.chartValueL_constMapL_ae μ p k hΨ w i, h ▸ h0 i] with y h₁ h₂
    rw [← h₁, h₂, Pi.zero_apply]
  · filter_upwards [C.chartValueL_constMapL_ae μ p k hΨ w i, h i, h0 i] with y h₁ h₂ h₃
    rw [h₁, h₂, h₃, Pi.zero_apply]

/-- If `P` is idempotent and lifts `Ψ`, then `C.constMapL μ p k P Ψ hΨ` lands in
`C.fixedSubmodule μ p k P`. -/
theorem constMapL_mem_fixedSubmodule (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    C.constMapL μ p k P Ψ hΨ w ∈ C.fixedSubmodule μ p k P :=
  mem_fixedSubmodule_iff.2 fun i ↦ (C.chartValueL_constMapL_ae μ p k hΨ w i).mono fun y hy ↦ by
    rw [hy]
    exact DFunLike.congr_fun hP.eq _

variable (C)

variable (μ p k) in
/-- **Idempotent fibre projection.** When `P : F →L[ℝ] F` is idempotent and lifts `Ψ : S → S`,
`C.constMapL μ p k P Ψ hΨ` restricts to a continuous linear retraction onto
`C.fixedSubmodule μ p k P`. -/
def projFixedL (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y)) :
    C.sobolevSections μ p k →L[ℝ] C.fixedSubmodule μ p k P :=
  (C.constMapL μ p k P Ψ hΨ).codRestrict _ (constMapL_mem_fixedSubmodule hP hΨ)

/-- Coercing `C.projFixedL μ p k hP hΨ w` to `C.sobolevSections μ p k` recovers
`C.constMapL μ p k P Ψ hΨ w`. -/
@[simp]
theorem coe_projFixedL (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    (C.projFixedL μ p k hP hΨ w : C.sobolevSections μ p k) = C.constMapL μ p k P Ψ hΨ w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- The `SobolevData` components of `C.projFixedL μ p k hP hΨ w` equal
`C.constMapData μ p k P w`. -/
theorem coe_coe_projFixedL (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    ((C.projFixedL μ p k hP hΨ w : C.sobolevSections μ p k) : C.SobolevData μ p k) =
      C.constMapData μ p k P w :=
  C.coe_constMapL (μ := μ) (p := p) (k := k) hΨ w

/-- The chart data of `C.projFixedL μ p k hP hΨ w` are those of `w` composed with `P`, almost
everywhere on `C.image i`. -/
theorem chartValueL_projFixedL_ae (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p k i (C.projFixedL μ p k hP hΨ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ P (C.chartValueL μ p k i w y) :=
  C.chartValueL_constMapL_ae μ p k hΨ w i

/-- If the chart data of `w` in chart `i` equal the reading of `s`, then the chart data of
`C.projFixedL μ p k hP hΨ w` equal the reading of `Ψ s`. -/
theorem chartValueL_projFixedL_ae_coord (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    {w : C.sobolevSections μ p k} {i : Fin C.n} {s : S}
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    C.chartValueL μ p k i (C.projFixedL μ p k hP hΨ w) =ᵐ[μ.restrict (C.image i)]
      C.coord i (Ψ s) :=
  C.chartValueL_constMapL_ae_coord hΨ hw

variable (μ p k) in
/-- `C.projFixedL μ p k hP hΨ w` vanishes if and only if the chart data of `w` lie in `ker P`
almost everywhere on every chart image. -/
theorem projFixedL_eq_zero_iff (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    {w : C.sobolevSections μ p k} :
    C.projFixedL μ p k hP hΨ w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (C.image i), P (C.chartValueL μ p k i w y) = 0 := by
  rw [← ZeroMemClass.coe_eq_zero, C.coe_projFixedL]
  exact constMapL_eq_zero_iff hΨ

/-- `C.projFixedL μ p k hP hΨ` fixes every element of `C.fixedSubmodule μ p k P`. -/
@[simp]
theorem projFixedL_coe (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.fixedSubmodule μ p k P) :
    C.projFixedL μ p k hP hΨ w = w :=
  Subtype.ext ((constMapL_eq_self_iff hΨ).2 w.2)

variable (μ p k) in
/-- An element of `C.sobolevSections μ p k` is fixed by `C.projFixedL μ p k hP hΨ` if and only if it
belongs to `C.fixedSubmodule μ p k P`. -/
theorem coe_projFixedL_eq_self_iff (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    {w : C.sobolevSections μ p k} :
    (C.projFixedL μ p k hP hΨ w : C.sobolevSections μ p k) = w ↔
      w ∈ C.fixedSubmodule μ p k P :=
  constMapL_eq_self_iff hΨ

variable (μ p k) in
/-- `C.projFixedL μ p k hP hΨ` is surjective. -/
theorem projFixedL_surjective (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y)) :
    Function.Surjective (C.projFixedL μ p k hP hΨ) :=
  fun w ↦ ⟨w, C.projFixedL_coe hP hΨ w⟩

end Projection

/-! ### Lowering the Sobolev order -/

/-- Lowering the Sobolev order preserves `C.fixedSubmodule`. -/
theorem lowerOrderL_mem_fixedSubmodule {P : F →L[ℝ] F}
    {w : C.sobolevSections μ p (k + 1)} (hw : w ∈ C.fixedSubmodule μ p (k + 1) P) :
    C.lowerOrderL μ p k w ∈ C.fixedSubmodule μ p k P := by
  rw [mem_fixedSubmodule_iff] at hw ⊢
  intro i
  rw [C.chartValueL_coe_lowerOrderL]
  exact hw i

variable (C μ p k) in
/-- The continuous inclusion of `C.fixedSubmodule μ p (k + 1) P` into `C.fixedSubmodule μ p k P`. -/
def fixedLowerOrderL (P : F →L[ℝ] F) :
    C.fixedSubmodule μ p (k + 1) P →L[ℝ] C.fixedSubmodule μ p k P :=
  ((C.lowerOrderL μ p k).comp (C.fixedSubmodule μ p (k + 1) P).subtypeL).codRestrict _
    fun w ↦ lowerOrderL_mem_fixedSubmodule w.2

@[simp]
theorem coe_fixedLowerOrderL (P : F →L[ℝ] F) (w : C.fixedSubmodule μ p (k + 1) P) :
    (C.fixedLowerOrderL μ p k P w : C.sobolevSections μ p k) = C.lowerOrderL μ p k w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

variable (C) in
/-- `C.projFixedL` commutes with lowering the Sobolev order. -/
theorem fixedLowerOrderL_projFixedL {P : F →L[ℝ] F} {Ψ : S → S} (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (w : C.sobolevSections μ p (k + 1)) :
    C.fixedLowerOrderL μ p k P (C.projFixedL μ p (k + 1) hP hΨ w) =
      C.projFixedL μ p k hP hΨ (C.lowerOrderL μ p k w) :=
  Subtype.ext (C.lowerOrderL_constMapL μ p k hΨ w)

end FixedSubmodule

/-! ### Lowering the integrability exponent -/

section Exponent

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  [∀ i, IsFiniteMeasure (μ.restrict (C.image i : Set E))]
  {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] (k : ℕ)

variable {C μ k} in
/-- Lowering the integrability exponent commutes with a constant fibre map. -/
theorem ofExponentLEL_constMapL {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (hpq : p ≤ q) (w : C.sobolevSections μ q k) :
    C.ofExponentLEL μ k hpq (C.constMapL μ q k L Ψ hΨ w) =
      C.constMapL μ p k L Ψ hΨ (C.ofExponentLEL μ k hpq w) :=
  eq_of_chartValueL_ae_eq fun i ↦ by
    rw [C.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    filter_upwards [C.chartValueL_constMapL_ae μ q k hΨ w i,
      C.chartValueL_constMapL_ae μ p k hΨ (C.ofExponentLEL μ k hpq w) i] with y h₁ h₂
    rw [h₁, h₂, C.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]

variable {C μ k} in
/-- Lowering the integrability exponent preserves `C.fixedSubmodule`. -/
theorem ofExponentLEL_mem_fixedSubmodule {P : F →L[ℝ] F} (hpq : p ≤ q)
    {w : C.sobolevSections μ q k} (hw : w ∈ C.fixedSubmodule μ q k P) :
    C.ofExponentLEL μ k hpq w ∈ C.fixedSubmodule μ p k P := by
  rw [mem_fixedSubmodule_iff] at hw ⊢
  intro i
  rw [C.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
  exact hw i

/-- For `p ≤ q`, the continuous inclusion of `C.fixedSubmodule μ q k P` into
`C.fixedSubmodule μ p k P`. -/
def fixedOfExponentLEL (P : F →L[ℝ] F) (hpq : p ≤ q) :
    C.fixedSubmodule μ q k P →L[ℝ] C.fixedSubmodule μ p k P :=
  ((C.ofExponentLEL μ k hpq).comp (C.fixedSubmodule μ q k P).subtypeL).codRestrict _
    fun w ↦ ofExponentLEL_mem_fixedSubmodule hpq w.2

variable {C μ k}

@[simp]
theorem coe_fixedOfExponentLEL (P : F →L[ℝ] F) (hpq : p ≤ q) (w : C.fixedSubmodule μ q k P) :
    (C.fixedOfExponentLEL μ k P hpq w : C.sobolevSections μ p k) = C.ofExponentLEL μ k hpq w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- Lowering the exponent on `C.fixedSubmodule` is injective. -/
theorem fixedOfExponentLEL_injective (P : F →L[ℝ] F) (hpq : p ≤ q) :
    Function.Injective (C.fixedOfExponentLEL μ k P hpq) :=
  fun _ _ h ↦ Subtype.ext (C.ofExponentLEL_injective hpq (congrArg Subtype.val h))

@[simp]
theorem fixedOfExponentLEL_self (P : F →L[ℝ] F) (w : C.fixedSubmodule μ p k P) :
    C.fixedOfExponentLEL μ k P le_rfl w = w :=
  Subtype.ext (C.ofExponentLEL_self (w : C.sobolevSections μ p k))

@[simp]
theorem fixedOfExponentLEL_fixedOfExponentLEL (P : F →L[ℝ] F) (hpq : p ≤ q) (hqr : q ≤ r)
    (w : C.fixedSubmodule μ r k P) :
    C.fixedOfExponentLEL μ k P hpq (C.fixedOfExponentLEL μ k P hqr w) =
      C.fixedOfExponentLEL μ k P (hpq.trans hqr) w :=
  Subtype.ext (C.ofExponentLEL_ofExponentLEL hpq hqr (w : C.sobolevSections μ r k))

/-- Lowering the exponent on `C.fixedSubmodule` commutes with lowering the order. -/
theorem fixedLowerOrderL_fixedOfExponentLEL (P : F →L[ℝ] F) (hpq : p ≤ q)
    (w : C.fixedSubmodule μ q (k + 1) P) :
    C.fixedLowerOrderL μ p k P (C.fixedOfExponentLEL μ (k + 1) P hpq w) =
      C.fixedOfExponentLEL μ k P hpq (C.fixedLowerOrderL μ q k P w) :=
  Subtype.ext (C.lowerOrderL_ofExponentLEL hpq (w : C.sobolevSections μ q (k + 1)))

variable (C) in
/-- `C.projFixedL` commutes with lowering the integrability exponent. -/
theorem fixedOfExponentLEL_projFixedL {P : F →L[ℝ] F} {Ψ : S → S} (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (hpq : p ≤ q) (w : C.sobolevSections μ q k) :
    C.fixedOfExponentLEL μ k P hpq (C.projFixedL μ q k hP hΨ w) =
      C.projFixedL μ p k hP hΨ (C.ofExponentLEL μ k hpq w) :=
  Subtype.ext (ofExponentLEL_constMapL hΨ hpq w)

end Exponent

/-! ### Chartwise scalar multiplier endomorphisms -/

section SMulEnd

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

variable {C μ p k} in
/-- Any continuous linear endomorphism `T` of `C.sobolevSections μ p k` that acts on chart data as
multiplication by real-valued functions `ψ i` commutes with every real-linear constant fibre map. -/
theorem smulEnd_constMapL {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k}
    {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    T (C.constMapL μ p k L Ψ hΨ w) = C.constMapL μ p k L Ψ hΨ (T w) :=
  eq_of_chartValueL_ae_eq fun i ↦ by
    filter_upwards [hT (C.constMapL μ p k L Ψ hΨ w) i,
      C.chartValueL_constMapL_ae μ p k hΨ w i,
      C.chartValueL_constMapL_ae μ p k hΨ (T w) i,
      hT w i] with y h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, map_smul]

variable {C μ p k} in
/-- Any continuous linear endomorphism `T` of `C.sobolevSections μ p k` that acts on chart data as
multiplication by real-valued functions preserves `C.fixedSubmodule μ p k P`. -/
theorem smulEnd_mem_fixedSubmodule {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k}
    {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    {P : F →L[ℝ] F} {w : C.sobolevSections μ p k} (hw : w ∈ C.fixedSubmodule μ p k P) :
    T w ∈ C.fixedSubmodule μ p k P := by
  rw [mem_fixedSubmodule_iff] at hw ⊢
  intro i
  filter_upwards [hT w i, hw i] with y h₁ h₂
  rw [h₁, map_smul, h₂]

/-- Restricts a continuous linear endomorphism `T` of `C.sobolevSections μ p k` that acts on chart
data as multiplication by real-valued functions `ψ i` to `C.fixedSubmodule μ p k P`. -/
def fixedSMulEndL (P : F →L[ℝ] F) (T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k)
    {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y) :
    C.fixedSubmodule μ p k P →L[ℝ] C.fixedSubmodule μ p k P :=
  (T.comp (C.fixedSubmodule μ p k P).subtypeL).codRestrict _
    fun w ↦ smulEnd_mem_fixedSubmodule hT w.2

variable {C μ p k}

@[simp]
theorem coe_fixedSMulEndL (P : F →L[ℝ] F)
    (T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k) {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.fixedSubmodule μ p k P) :
    (C.fixedSMulEndL μ p k P T hT w : C.sobolevSections μ p k) = T w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

variable (C) in
/-- `C.projFixedL` commutes with any continuous linear endomorphism acting chartwise as
multiplication by real-valued functions. -/
theorem fixedSMulEndL_projFixedL {P : F →L[ℝ] F} {Ψ : S → S} (hP : IsIdempotentElem P)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = P (C.coord i s y))
    (T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k) {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.sobolevSections μ p k) :
    C.fixedSMulEndL μ p k P T hT (C.projFixedL μ p k hP hΨ w) =
      C.projFixedL μ p k hP hΨ (T w) :=
  Subtype.ext (smulEnd_constMapL hT hΨ w)

/-- If `T` equals `c • id` on `C.sobolevSections μ p k`, then its restriction `C.fixedSMulEndL`
equals `c • id` on `C.fixedSubmodule μ p k P`. -/
theorem fixedSMulEndL_eq_smul_id (P : F →L[ℝ] F)
    (T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k) {ψ : Fin C.n → E → ℝ}
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    {c : ℝ} (hc : T = c • ContinuousLinearMap.id ℝ _) :
    C.fixedSMulEndL μ p k P T hT = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  refine Subtype.ext ?_
  simp only [coe_fixedSMulEndL, hc, smul_apply, ContinuousLinearMap.id_apply, Submodule.coe_smul]

/-- Restriction via `C.fixedSMulEndL` preserves sums of chartwise scalar multiplier operators. -/
theorem fixedSMulEndL_eq_add (P : F →L[ℝ] F)
    {T₁₂ T₁ T₂ : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k}
    {ψ₁₂ ψ₁ ψ₂ : Fin C.n → E → ℝ}
    (hT₁₂ : ∀ w i, C.chartValueL μ p k i (T₁₂ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₁₂ i y • C.chartValueL μ p k i w y)
    (hT₁ : ∀ w i, C.chartValueL μ p k i (T₁ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₁ i y • C.chartValueL μ p k i w y)
    (hT₂ : ∀ w i, C.chartValueL μ p k i (T₂ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₂ i y • C.chartValueL μ p k i w y)
    (hadd : T₁₂ = T₁ + T₂) :
    C.fixedSMulEndL μ p k P T₁₂ hT₁₂ =
      C.fixedSMulEndL μ p k P T₁ hT₁ + C.fixedSMulEndL μ p k P T₂ hT₂ := by
  ext1 w
  refine Subtype.ext ?_
  simp only [coe_fixedSMulEndL, hadd, add_apply, Submodule.coe_add]

/-- Restriction via `C.fixedSMulEndL` preserves compositions of chartwise scalar multiplier
operators. -/
theorem fixedSMulEndL_eq_comp (P : F →L[ℝ] F)
    {T₁₂ T₁ T₂ : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k}
    {ψ₁₂ ψ₁ ψ₂ : Fin C.n → E → ℝ}
    (hT₁₂ : ∀ w i, C.chartValueL μ p k i (T₁₂ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₁₂ i y • C.chartValueL μ p k i w y)
    (hT₁ : ∀ w i, C.chartValueL μ p k i (T₁ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₁ i y • C.chartValueL μ p k i w y)
    (hT₂ : ∀ w i, C.chartValueL μ p k i (T₂ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ₂ i y • C.chartValueL μ p k i w y)
    (hcomp : T₁₂ = T₁.comp T₂) :
    C.fixedSMulEndL μ p k P T₁₂ hT₁₂ =
      (C.fixedSMulEndL μ p k P T₁ hT₁).comp (C.fixedSMulEndL μ p k P T₂ hT₂) := by
  ext1 w
  refine Subtype.ext ?_
  simp only [coe_fixedSMulEndL, hcomp, ContinuousLinearMap.comp_apply]

/-- Lowering the Sobolev order commutes with chartwise scalar multiplier operators sharing the same
multipliers `ψ`. -/
theorem lowerOrderL_smulEnd
    {T' : C.sobolevSections μ p (k + 1) →L[ℝ] C.sobolevSections μ p (k + 1)}
    {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hT' : ∀ w i, C.chartValueL μ p (k + 1) i (T' w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p (k + 1) i w y)
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.sobolevSections μ p (k + 1)) :
    C.lowerOrderL μ p k (T' w) = T (C.lowerOrderL μ p k w) :=
  eq_of_chartValueL_ae_eq fun i ↦ by
    rw [C.chartValueL_coe_lowerOrderL]
    filter_upwards [hT' w i, hT (C.lowerOrderL μ p k w) i] with y h₁ h₂
    rw [h₁, h₂, C.chartValueL_coe_lowerOrderL]

/-- `C.fixedLowerOrderL` commutes with `C.fixedSMulEndL` for chartwise scalar multiplier operators
sharing the same multipliers `ψ`. -/
theorem fixedLowerOrderL_fixedSMulEndL (P : F →L[ℝ] F)
    {T' : C.sobolevSections μ p (k + 1) →L[ℝ] C.sobolevSections μ p (k + 1)}
    {T : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hT' : ∀ w i, C.chartValueL μ p (k + 1) i (T' w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p (k + 1) i w y)
    (hT : ∀ w i, C.chartValueL μ p k i (T w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.fixedSubmodule μ p (k + 1) P) :
    C.fixedLowerOrderL μ p k P (C.fixedSMulEndL μ p (k + 1) P T' hT' w) =
      C.fixedSMulEndL μ p k P T hT (C.fixedLowerOrderL μ p k P w) :=
  Subtype.ext (lowerOrderL_smulEnd hT' hT (w : C.sobolevSections μ p (k + 1)))

section ExponentSMul

variable [∀ i, IsFiniteMeasure (μ.restrict (C.image i : Set E))] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Lowering the integrability exponent commutes with chartwise scalar multiplier operators sharing
the same multipliers `ψ`. -/
theorem ofExponentLEL_smulEnd (hpq : p ≤ q)
    {Tq : C.sobolevSections μ q k →L[ℝ] C.sobolevSections μ q k}
    {Tp : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hTq : ∀ w i, C.chartValueL μ q k i (Tq w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ q k i w y)
    (hTp : ∀ w i, C.chartValueL μ p k i (Tp w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.sobolevSections μ q k) :
    C.ofExponentLEL μ k hpq (Tq w) = Tp (C.ofExponentLEL μ k hpq w) :=
  eq_of_chartValueL_ae_eq fun i ↦ by
    rw [C.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
    filter_upwards [hTq w i, hTp (C.ofExponentLEL μ k hpq w) i] with y h₁ h₂
    rw [h₁, h₂, C.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]

/-- `C.fixedOfExponentLEL` commutes with `C.fixedSMulEndL` for chartwise scalar multiplier
operators sharing the same multipliers `ψ`. -/
theorem fixedOfExponentLEL_fixedSMulEndL (P : F →L[ℝ] F) (hpq : p ≤ q)
    {Tq : C.sobolevSections μ q k →L[ℝ] C.sobolevSections μ q k}
    {Tp : C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k} {ψ : Fin C.n → E → ℝ}
    (hTq : ∀ w i, C.chartValueL μ q k i (Tq w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ q k i w y)
    (hTp : ∀ w i, C.chartValueL μ p k i (Tp w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ i y • C.chartValueL μ p k i w y)
    (w : C.fixedSubmodule μ q k P) :
    C.fixedOfExponentLEL μ k P hpq (C.fixedSMulEndL μ q k P Tq hTq w) =
      C.fixedSMulEndL μ p k P Tp hTp (C.fixedOfExponentLEL μ k P hpq w) :=
  Subtype.ext (ofExponentLEL_smulEnd hpq hTq hTp (w : C.sobolevSections μ q k))

end ExponentSMul

end SMulEnd

end SectionChartData

end TauCeti
