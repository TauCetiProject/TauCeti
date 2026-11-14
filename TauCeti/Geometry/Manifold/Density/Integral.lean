/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.CompactSupport
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Order.Disjointed

/-!
# Integration of densities on manifolds

A rough density `μ` of degree `m` is read in a preferred chart through a model basis `b`: its
coefficient `μ.inChartAt b α y` is the value of `μ` at `(extChartAt I α).symm y` on the image of
`b` under the derivative of the inverse chart, extended by zero outside the chart target. On a
chart overlap two coefficients differ by the absolute determinant of the transition derivative,
and two bases change the coefficient by their absolute change-of-basis determinant. The absolute
Jacobian change-of-variables formula therefore makes the chartwise integrals independent of
chart, basis and cover, with no orientation.

`TauCeti.integralDensity μ` is the integral of a compactly supported integrable rough density:
the sum of its chart integrals over the disjointed pieces of a finite open chart cover of its
support. `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals` computes it with any such
cover and any model basis. On an oriented manifold the integral of a top form is the integral of
its density (`TauCeti.integralTopForm_eq_integralDensity`).

As for top forms, the manifold needs no Hausdorff assumption or measurable structure, and may
have boundary or corners: only the model carries its Borel measurable structure.

## Main definitions

* `TauCeti.RoughDensity.inChartAt`: the coefficient of a rough density in a preferred chart.
* `TauCeti.IntegrableDensity`: compact support and integrable coefficients in every chart.
* `TauCeti.integralDensity`: the integral of a rough density.

## Main results

* `TauCeti.RoughDensity.inChartAt_changeChart`: the absolute determinant law on chart overlaps.
* `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals`: independence of chart, basis and
  cover.
* `TauCeti.integralTopForm_eq_integralDensity`: `∫_o φ = ∫ φ.toDensity o`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

namespace RoughDensity

/-- The coefficient of a rough density in the preferred chart at `α` and a model basis `b`: the
value of the density on the image of `b` under the derivative of the inverse chart, extended by
zero outside the chart target. -/
def inChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) : ℝ := by
  classical
  exact if y ∈ (extChartAt I α).target then
    μ ((extChartAt I α).symm y)
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i))
  else 0

/-- In the chart target, the chart coefficient is the value of the density on the transported
model basis. -/
theorem inChartAt_of_mem_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    μ.inChartAt b α y = μ ((extChartAt I α).symm y)
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i)) := by
  unfold inChartAt
  exact ite_eq_left hy

/-- Outside the chart target, the chart coefficient is zero. -/
theorem inChartAt_of_notMem_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    {y : E} (hy : y ∉ (extChartAt I α).target) : μ.inChartAt b α y = 0 := by
  unfold inChartAt
  exact ite_eq_right hy

@[simp]
theorem inChartAt_zero (b : Basis (Fin m) ℝ E) (α : M) :
    (0 : RoughDensity I M m).inChartAt b α = 0 := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [inChartAt_of_mem_target _ b α hy]
    rfl
  · rw [inChartAt_of_notMem_target _ b α hy]
    rfl

@[simp]
theorem inChartAt_add (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (μ + ν).inChartAt b α = μ.inChartAt b α + ν.inChartAt b α := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Pi.add_apply, inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy,
      inChartAt_of_mem_target _ b α hy]
    rfl
  · rw [Pi.add_apply, inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy,
      inChartAt_of_notMem_target _ b α hy, add_zero]

@[simp]
theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (c • μ).inChartAt b α = c • μ.inChartAt b α := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Pi.smul_apply, inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy]
    rfl
  · rw [Pi.smul_apply, inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy,
      smul_zero]

variable [FiniteDimensional ℝ E]

/-- The constant top form given by the determinant of a model basis. Its chart coefficients
are the determinants of the derivatives of the inverse charts. -/
private def detForm (b : Basis (Fin m) ℝ E) : RoughForm I M ℝ m :=
  fun _ ↦ AlternatingMap.toContinuousAlternatingMap b.det

private theorem detForm_apply (b : Basis (Fin m) ℝ E) (x : M) (v : Fin m → TangentSpace I x) :
    (detForm b : RoughForm I M ℝ m) x v = b.det v := by
  change AlternatingMap.toContinuousAlternatingMap b.det v = b.det v
  rw [AlternatingMap.coe_toContinuousAlternatingMap]

/-- In the chart target, the coefficient of a density is its value on the model basis, at the
chart preimage, times the absolute determinant of the derivative of the inverse chart. -/
private theorem inChartAt_eq_abs_det_mul (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    μ.inChartAt b α y =
      |(detForm b : RoughForm I M ℝ m).inChartAt α y b| * μ ((extChartAt I α).symm y) b := by
  rw [inChartAt_of_mem_target μ b α hy, RoughForm.inChartAt_apply, detForm_apply]
  exact (μ _).apply_eq_abs_det_mul b _

/-- The coefficient of the determinant form in its own chart at the chart point is one. -/
private theorem detForm_inChartAt_self [IsManifold I 1 M] (b : Basis (Fin m) ℝ E) (x : M) :
    (detForm b : RoughForm I M ℝ m).inChartAt x (extChartAt I x x) b = 1 := by
  rw [RoughForm.inChartAt_chart_apply _ x (mem_extChartAt_source x)]
  simp only [tangentCoordChange_self (mem_extChartAt_source x)]
  exact (detForm_apply b x _).trans b.det_self

/-- In its own chart at the chart point, the coefficient of a density is its value on the
model basis. -/
theorem inChartAt_self [IsManifold I 1 M] (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (x : M) : μ.inChartAt b x (extChartAt I x x) = μ x b := by
  rw [inChartAt_eq_abs_det_mul μ b x ((extChartAt I x).map_source (mem_extChartAt_source x)),
    detForm_inChartAt_self, abs_one, one_mul, (extChartAt I x).left_inv (mem_extChartAt_source x)]

/-- On an overlap of two preferred charts, the chart coefficients of a density differ by the
absolute determinant of the within-range transition derivative. This includes boundary and
corner points. -/
theorem inChartAt_changeChart [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) {α β x : M} (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source) :
    μ.inChartAt b α (extChartAt I α x) =
      |(fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I)
        (extChartAt I α x)).toLinearMap.det| * μ.inChartAt b β (extChartAt I β x) := by
  have hc := (detForm b : RoughForm I M ℝ m).inChartAt_apply_basis_eq_det_mul b
    ((extChartAt I α).map_source hα) (x := β) (by rwa [(extChartAt I α).left_inv hα])
  rw [(extChartAt I α).left_inv hα] at hc
  rw [inChartAt_eq_abs_det_mul μ b α ((extChartAt I α).map_source hα),
    inChartAt_eq_abs_det_mul μ b β ((extChartAt I β).map_source hβ), hc, abs_mul,
    (extChartAt I α).left_inv hα, (extChartAt I β).left_inv hβ, mul_assoc]

omit [FiniteDimensional ℝ E] in
/-- Changing the model basis multiplies the chart coefficient of a density by the absolute
change-of-basis determinant. -/
theorem inChartAt_basis_change (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E) (α : M)
    (y : E) : μ.inChartAt b' α y = |b.det b'| * μ.inChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · let L : E →L[ℝ] E := mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y
    have h' : μ ((extChartAt I α).symm y) (fun i ↦ L (b' i)) =
        |b.det (fun i ↦ L (b' i))| * μ ((extChartAt I α).symm y) b :=
      (μ _).apply_eq_abs_det_mul b _
    have h : μ ((extChartAt I α).symm y) (fun i ↦ L (b i)) =
        |b.det (fun i ↦ L (b i))| * μ ((extChartAt I α).symm y) b :=
      (μ _).apply_eq_abs_det_mul b _
    have hd' : b.det (fun i ↦ L (b' i)) = LinearMap.det L.toLinearMap * b.det b' :=
      b.det_comp L.toLinearMap b'
    have hd : b.det (fun i ↦ L (b i)) = LinearMap.det L.toLinearMap := by
      rw [show (fun i ↦ L (b i)) = L.toLinearMap ∘ b from rfl, b.det_comp, b.det_self, mul_one]
    rw [inChartAt_of_mem_target μ b' α hy, inChartAt_of_mem_target μ b α hy]
    change (μ ((extChartAt I α).symm y)) (fun i ↦ L (b' i)) =
      |b.det b'| * (μ ((extChartAt I α).symm y)) (fun i ↦ L (b i))
    rw [h', h, hd', hd, abs_mul]
    ring
  · rw [inChartAt_of_notMem_target μ b' α hy, inChartAt_of_notMem_target μ b α hy, mul_zero]

variable [MeasurableSpace E] [BorelSpace E]

/-- Chart integrals of a density, and their integrability, agree on an actual chart overlap,
by the absolute Jacobian change-of-variables formula. No orientation or sign data enter. -/
theorem integral_inChartAt_changeChart [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s)) (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ y in (extChartAt I α) '' s, μ.inChartAt b α y ∂ν) =
        (∫ y in (extChartAt I β) '' s, μ.inChartAt b β y ∂ν) ∧
      (IntegrableOn (μ.inChartAt b α) ((extChartAt I α) '' s) ν ↔
        IntegrableOn (μ.inChartAt b β) ((extChartAt I β) '' s) ν) := by
  let A := (extChartAt I α) '' s
  let e := (extChartAt I α).symm ≫ extChartAt I β
  let D := fun y ↦ fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I) y
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  have hcoef : ∀ y ∈ A, |(D y).toLinearMap.det| • μ.inChartAt b β (e y) = μ.inChartAt b α y := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x :=
      congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, smul_eq_mul, inChartAt_changeChart μ b (hsub hx).1 (hsub hx).2]
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul ν hs hderiv hinj]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul ν hs hderiv hinj]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

omit [FiniteDimensional ℝ E] in
/-- Chart integrals of a density over a set do not depend on the model basis, each basis
carrying its normalized Haar measure. -/
theorem setIntegral_inChartAt_basis_eq (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) (s : Set E) :
    (∫ y in s, μ.inChartAt b' α y ∂b'.addHaar) = ∫ y in s, μ.inChartAt b α y ∂b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [b.addHaar_eq_smul_of_basis b', Measure.restrict_smul, integral_smul_measure]
  simp_rw [inChartAt_basis_change μ b b']
  rw [integral_const_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hd), one_mul]

omit [FiniteDimensional ℝ E] in
/-- Integrability of the chart coefficients of a density does not depend on the model basis. -/
theorem integrable_inChartAt_basis_iff (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) :
    Integrable (μ.inChartAt b' α) b'.addHaar ↔ Integrable (μ.inChartAt b α) b.addHaar := by
  have hd : b.det b' ≠ 0 := (b.isUnit_det b').ne_zero
  rw [b.addHaar_eq_smul_of_basis b', integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero hd))) ENNReal.ofReal_ne_top]
  have heq : μ.inChartAt b' α = fun y ↦ |b.det b'| * μ.inChartAt b α y :=
    funext (inChartAt_basis_change μ b b' α)
  rw [heq]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hd)) _

end RoughDensity

/-- A rough density is integrable when it has compact support and its coefficients are
integrable in every preferred chart and every model basis. The model uses its Borel measurable
structure. In degrees other than the dimension of the model there is no model basis, and no
density is integrable. -/
def IntegrableDensity (μ : RoughDensity I M m) : Prop := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact IsCompact (_root_.tsupport (α := Density E m) μ) ∧ Nonempty (Basis (Fin m) ℝ E) ∧
    ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.inChartAt b α) b.addHaar

section WithMeasure

variable [MeasurableSpace E] [BorelSpace E]

/-- The coordinate characterization of integrability, with any Borel measurable structure on
the model. -/
theorem integrableDensity_iff (μ : RoughDensity I M m) :
    IntegrableDensity μ ↔ IsCompact (_root_.tsupport (α := Density E m) μ) ∧
      Nonempty (Basis (Fin m) ℝ E) ∧
      ∀ (b : Basis (Fin m) ℝ E) (α : M), Integrable (μ.inChartAt b α) b.addHaar := by
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  rfl

/-- One model basis suffices to check integrability of a compactly supported density. -/
theorem integrableDensity_of_basis {μ : RoughDensity I M m}
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) (b : Basis (Fin m) ℝ E)
    (hi : ∀ α : M, Integrable (μ.inChartAt b α) b.addHaar) : IntegrableDensity μ :=
  (integrableDensity_iff μ).mpr ⟨hc, ⟨b⟩, fun b' α ↦
    (μ.integrable_inChartAt_basis_iff b b' α).mpr (hi α)⟩

end WithMeasure

/-- Integrable densities have compact topological support. -/
theorem IntegrableDensity.isCompact {μ : RoughDensity I M m} (hi : IntegrableDensity μ) :
    IsCompact (_root_.tsupport (α := Density E m) μ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  exact ((integrableDensity_iff μ).mp hi).1

/-- The sum of two integrable densities is integrable. -/
theorem IntegrableDensity.add {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ)
    (hν : IntegrableDensity ν) : IntegrableDensity (μ + ν) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ hν ⊢
  refine ⟨(hμ.1.union hν.1).of_isClosed_subset (isClosed_tsupport _) ?_, hμ.2.1, ?_⟩
  · exact tsupport_add (α := Density E m) (show M → Density E m from μ) ν
  · intro b α
    rw [RoughDensity.inChartAt_add]
    exact (hμ.2.2 b α).add (hν.2.2 b α)

/-- A constant multiple of an integrable density is integrable. -/
theorem IntegrableDensity.smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) (c : ℝ) :
    IntegrableDensity (c • μ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ ⊢
  refine ⟨hμ.1.of_isClosed_subset (isClosed_tsupport _) ?_, hμ.2.1, ?_⟩
  · exact tsupport_smul_subset_right (fun _ : M ↦ c) (show M → Density E m from μ)
  · intro b α
    rw [RoughDensity.inChartAt_smul]
    exact (hμ.2.2 b α).smul c

/-- The disjointed pieces of an open chart cover are chart measurable. -/
private theorem isChartMeasurable_disjointed [MeasurableSpace E] [OpensMeasurableSpace E] {n : ℕ}
    {u : Fin n → Set M} (hu : ∀ i, IsOpen (u i)) (i : Fin n) :
    IsChartMeasurable I (disjointed u i) := by
  rw [disjointed_apply]
  have ho : IsOpen ((Finset.Iio i).sup u) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isOpen_biUnion fun j _ ↦ hu j
  exact (hu i).isChartMeasurable.diff ho.isChartMeasurable

/-- The sum of the chart integrals of a density over the disjointed pieces of a finite chart
cover. -/
private def coverSum [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E)
    {n : ℕ} (α : Fin n → M) (u : Fin n → Set M) : ℝ :=
  ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar

variable [FiniteDimensional ℝ E]

section Cover

variable [IsManifold I 1 M] [MeasurableSpace E] [BorelSpace E]

/-- A chart integral of an integrable density over a chart-measurable set splits along the
disjointed pieces of any finite open chart cover of the support. -/
private theorem setIntegral_inChartAt_refine (μ : RoughDensity I M m) (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) (α : M) {n : ℕ} (v : Fin n → Set M)
    (hv : ∀ j, IsOpen (v j)) (hc : _root_.tsupport (α := Density E m) μ ⊆ ⋃ j, v j)
    {u : Set M} (hu : IsChartMeasurable I u) (hus : u ⊆ (extChartAt I α).source) :
    (∫ y in (extChartAt I α) '' u, μ.inChartAt b α y ∂b.addHaar) =
      ∑ j, ∫ y in (extChartAt I α) '' (u ∩ disjointed v j), μ.inChartAt b α y ∂b.addHaar := by
  let e := extChartAt I α
  let f := μ.inChartAt b α
  let w : Fin n → Set E := fun j ↦ e '' (u ∩ disjointed v j)
  have hw (j : Fin n) : MeasurableSet (w j) :=
    (hu.inter (isChartMeasurable_disjointed hv j)).image_extChartAt α
      (inter_subset_left.trans hus)
  have hws : (⋃ j, w j) ⊆ e '' u := iUnion_subset fun _ ↦ image_mono inter_subset_left
  have hdisj : Pairwise (fun i j ↦ Disjoint (w i) (w j)) := by
    intro i j hij
    exact ((disjoint_disjointed v hij).mono inter_subset_right inter_subset_right).image e.injOn
      (inter_subset_left.trans hus) (inter_subset_left.trans hus)
  have hf : Integrable f b.addHaar := ((integrableDensity_iff μ).mp hi).2.2 b α
  have hz : ∀ y ∈ e '' u \ ⋃ j, w j, f y = 0 := by
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    have hx0 : x ∉ _root_.tsupport (α := Density E m) μ := by
      intro ht
      have hx' : x ∈ ⋃ j, disjointed v j := by rw [iUnion_disjointed]; exact hc ht
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx'
      exact hn (mem_iUnion.mpr ⟨j, mem_image_of_mem e ⟨hx, hj⟩⟩)
    have hμ : μ x = 0 := image_eq_zero_of_notMem_tsupport (α := Density E m) hx0
    have hcoef := RoughDensity.inChartAt_changeChart μ b (hus hx) (mem_extChartAt_source x)
    rw [RoughDensity.inChartAt_self, hμ] at hcoef
    exact hcoef.trans (mul_zero _)
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hu.image_extChartAt α hus) hws hz).trans
    (integral_iUnion_fintype hw hdisj (fun _ ↦ hf.integrableOn))

/-- Two finite open chart covers of the support give the same sum of chart integrals. -/
private theorem coverSum_eq (μ : RoughDensity I M m)
    (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E) {n n' : ℕ}
    (α : Fin n → M) (u : Fin n → Set M) (hu : ∀ i, IsOpen (u i))
    (hus : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i)
    (β : Fin n' → M) (v : Fin n' → Set M) (hv : ∀ j, IsOpen (v j))
    (hvs : ∀ j, v j ⊆ (extChartAt I (β j)).source)
    (hd : _root_.tsupport (α := Density E m) μ ⊆ ⋃ j, v j) :
    coverSum μ b α u = coverSum μ b β v := by
  unfold coverSum
  simp_rw [setIntegral_inChartAt_refine μ hi b _ v hv hd (isChartMeasurable_disjointed hu _)
      ((disjointed_subset u _).trans (hus _)),
    setIntegral_inChartAt_refine μ hi b _ u hu hc (isChartMeasurable_disjointed hv _)
      ((disjointed_subset v _).trans (hvs _))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have h := (μ.integral_inChartAt_changeChart b (α i) (β j) (s := disjointed u i ∩ disjointed v j)
    (fun x hx ↦ ⟨(disjointed_subset u i).trans (hus i) hx.1,
      (disjointed_subset v j).trans (hvs j) hx.2⟩)
    (((isChartMeasurable_disjointed hu i).inter
      (isChartMeasurable_disjointed hv j)).image_extChartAt
        (α i) (inter_subset_left.trans ((disjointed_subset u i).trans (hus i)))) b.addHaar).1
  simpa only [inter_comm] using h

end Cover

/-- The integral of a rough density. It is zero unless the density is integrable, in particular
unless its degree is the dimension of the model. The sum of chart integrals over the disjointed
pieces of a chosen finite open chart cover of the support defines it; by
`integralDensity_eq_sum_disjointed_chart_integrals` it does not depend on that cover or on the
model basis. -/
def integralDensity (μ : RoughDensity I M m) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  exact if hi : IntegrableDensity μ then
    let h := exists_finite_precompact_chart_cover (I := I) hi.isCompact
    coverSum μ (Classical.choice ((integrableDensity_iff μ).mp hi).2.1)
      h.choose_spec.choose h.choose_spec.choose_spec.choose
  else 0

/-- A nonintegrable density has zero integral. -/
theorem integralDensity_eq_zero_of_not_integrable {μ : RoughDensity I M m}
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by
  rw [integralDensity, dite_eq_right hi]

/-- The integral of an integrable density is the sum of its chart integrals over the disjointed
pieces of any finite open chart cover of its support, in any model basis. -/
theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {n : ℕ} (α : Fin n → M) (u : Fin n → Set M)
    (hu : ∀ i, IsOpen (u i)) (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i) :
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  let : LocallyCompactSpace H := I.locallyCompactSpace
  rw [integralDensity, dite_eq_left hi]
  dsimp only
  let h := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  have hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  unfold coverSum
  simp_rw [μ.setIntegral_inChartAt_basis_eq b]
  exact coverSum_eq μ hi b _ _ (fun i ↦ (hp.1 i).1) (fun i ↦ (hp.1 i).2.1) hp.2 α u hu hs hc

/-- An integrable density supported in a preferred chart has that chart's integral. -/
theorem integralDensity_eq_integral_inChartAt [IsManifold I 1 M] [MeasurableSpace E]
    [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E)
    (α : M) (hs : _root_.tsupport (α := Density E m) μ ⊆ (extChartAt I α).source) :
    integralDensity μ = ∫ y, μ.inChartAt b α y ∂b.addHaar := by
  rw [integralDensity_eq_sum_disjointed_chart_integrals hi b (fun _ : Fin 1 ↦ α)
    (fun _ ↦ (extChartAt I α).source) (fun _ ↦ isOpen_extChartAt_source α) (fun _ ↦ Subset.rfl)
    (hs.trans (subset_iUnion_of_subset 0 Subset.rfl))]
  rw [Fin.sum_univ_one, disjointed_of_isMin _ (fun j _ ↦ le_of_eq (Subsingleton.elim _ _)),
    (extChartAt I α).image_source_eq_target]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  exact μ.inChartAt_of_notMem_target b α hy

/-- The zero density has zero integral. -/
@[simp]
theorem integralDensity_zero : integralDensity (0 : RoughDensity I M m) = 0 := by
  classical
  by_cases hi : IntegrableDensity (0 : RoughDensity I M m)
  · let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    rw [integralDensity, dite_eq_left hi]
    simp [coverSum]
  · exact integralDensity_eq_zero_of_not_integrable hi

/-- The integral of densities is additive on integrable densities. -/
theorem integralDensity_add [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ + ν) = integralDensity μ + integralDensity ν := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨b⟩ := ((integrableDensity_iff μ).mp hμ).2.1
  obtain ⟨n, α, u, _, hp, hc⟩ :=
    exists_finite_precompact_chart_cover (I := I) (hμ.isCompact.union hν.isCompact)
  have hsum : _root_.tsupport (α := Density E m) (μ + ν) ⊆
      _root_.tsupport (α := Density E m) μ ∪ _root_.tsupport (α := Density E m) ν :=
    tsupport_add (α := Density E m) (show M → Density E m from μ) ν
  rw [integralDensity_eq_sum_disjointed_chart_integrals (hμ.add hν) b α u (fun i ↦ (hp i).1)
      (fun i ↦ (hp i).2.1) (hsum.trans hc),
    integralDensity_eq_sum_disjointed_chart_integrals hμ b α u (fun i ↦ (hp i).1)
      (fun i ↦ (hp i).2.1) (subset_union_left.trans hc),
    integralDensity_eq_sum_disjointed_chart_integrals hν b α u (fun i ↦ (hp i).1)
      (fun i ↦ (hp i).2.1) (subset_union_right.trans hc), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RoughDensity.inChartAt_add]
  exact integral_add (((integrableDensity_iff μ).mp hμ).2.2 b (α i)).integrableOn
    (((integrableDensity_iff ν).mp hν).2.2 b (α i)).integrableOn

/-- Constant scalar multiplication commutes with the integral of integrable densities. -/
theorem integralDensity_smul [IsManifold I 1 M] {μ : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (c : ℝ) : integralDensity (c • μ) = c * integralDensity μ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  obtain ⟨b⟩ := ((integrableDensity_iff μ).mp hμ).2.1
  obtain ⟨n, α, u, _, hp, hc⟩ := exists_finite_precompact_chart_cover (I := I) hμ.isCompact
  have hsub : _root_.tsupport (α := Density E m) (c • μ) ⊆ _root_.tsupport (α := Density E m) μ :=
    tsupport_smul_subset_right (fun _ : M ↦ c) (show M → Density E m from μ)
  rw [integralDensity_eq_sum_disjointed_chart_integrals (hμ.smul c) b α u (fun i ↦ (hp i).1)
      (fun i ↦ (hp i).2.1) (hsub.trans hc),
    integralDensity_eq_sum_disjointed_chart_integrals hμ b α u (fun i ↦ (hp i).1)
      (fun i ↦ (hp i).2.1) hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RoughDensity.inChartAt_smul]
  exact integral_const_mul c _

section TopForm

variable [IsManifold I 1 M]

/-- In a preferred chart, the coefficient of the density of a top form is its signed coefficient
against an orientation lift, weighted by the relative sign of the model basis. -/
theorem RoughForm.toDensity_inChartAt (l : Manifold.OrientationLift I M (Fin m))
    (φ : RoughForm I M ℝ m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (φ.toDensity (Manifold.Orientation.mk l)).inChartAt b α y =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [← (extChartAt I α).right_inv hy]
    set x := (extChartAt I α).symm y
    have hx : x ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
    have hα : x ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
    have hxx : x ∈ (chartAt H x).source := mem_chart_source H x
    let D := fderivWithin ℝ (extChartAt I x ∘ (extChartAt I α).symm) (range I)
      (extChartAt I α x)
    have hD : 0 < (l.signAt α x : ℝ) * (l.signAt x x : ℝ) * D.toLinearMap.det := by
      rw [l.signAt_of_mem hα, l.signAt_of_mem hxx]
      exact l.compatible α x x hα hxx
    have hsq : (l.signAt x x : ℝ) * l.signAt x x = 1 := by
      exact_mod_cast Int.isUnit_mul_self (l.signAt x x).isUnit
    have habs : |D.toLinearMap.det| = (l.signAt α x : ℝ) * (l.signAt x x : ℝ) *
        D.toLinearMap.det := by
      rw [← abs_of_pos hD, abs_mul, abs_mul, abs_unit_intCast, abs_unit_intCast, one_mul, one_mul]
    -- The value of the density at `x` on the model basis.
    have hval : (φ.toDensity (Manifold.Orientation.mk l)) x b =
        (Orientation.signBasis l.modelOrientation b : ℝ) * l.signAt x x * φ x b := by
      have hs := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (l.signBasis_orientationAt b x)
      simp only [Units.val_mul, Int.cast_mul] at hs
      rw [← hs]
      exact (φ.toDensity_apply_basis _ x b).trans
        (by rw [Manifold.Orientation.orientationAt_mk]; rfl)
    -- The form coefficient changes to the chart at `x` with the signed determinant.
    have hcoef := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
      (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
    rw [(extChartAt I α).left_inv hx,
      RoughForm.inChartAt_chart_apply φ x (mem_extChartAt_source x)] at hcoef
    simp only [tangentCoordChange_self (mem_extChartAt_source x)] at hcoef
    rw [RoughDensity.inChartAt_changeChart _ b hx (mem_extChartAt_source x),
      RoughDensity.inChartAt_self, hval, RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
      hcoef, habs]
    linear_combination
      ((Orientation.signBasis l.modelOrientation b : ℝ) * l.signAt α x * D.toLinearMap.det *
        φ x b) * hsq
  · rw [RoughDensity.inChartAt_of_notMem_target _ b α hy, RoughForm.signedInChartAt_apply,
      dite_eq_right hy, mul_zero]

/-- The density of a top form has the topological support of the form. -/
theorem RoughForm.tsupport_toDensity (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) :
    _root_.tsupport (α := Density E m) (φ.toDensity o) =
      _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ := by
  have h : ∀ x, φ.toDensity o x = 0 ↔ φ x = 0 := fun x ↦ by
    classical
    let c : Basis (Fin m) ℝ (TangentSpace I x) :=
      finBasisOfFinrankEq ℝ _ (o.fact_finrank_tangentSpace x).out
    have hc : φ.toDensity o x c = 0 ↔ φ x c = 0 := by
      rw [φ.toDensity_apply o x c]
      split_ifs <;> simp only [neg_eq_zero]
    rw [← Density.apply_basis_eq_zero_iff _ c, hc]
    refine ⟨fun h ↦ ContinuousAlternatingMap.ext fun v ↦ ?_, fun h ↦ by rw [h]; rfl⟩
    rw [ContinuousAlternatingMap.apply_eq_det_mul (b := c), h, mul_zero]
    rfl
  simp only [_root_.tsupport, Function.support]
  congr 1
  ext x
  exact not_congr (h x)

/-- On an oriented manifold, a top form is integrable exactly when its density is. -/
theorem integrableDensity_toDensity_iff (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) : IntegrableDensity (φ.toDensity o) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  rw [integrableDensity_iff, integrableTopForm_iff, RoughForm.tsupport_toDensity]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun b ↦ forall_congr' fun α ↦ ?_))
  have heq : (φ.toDensity (Manifold.Orientation.mk l)).inChartAt b α = fun y ↦
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y :=
    funext (RoughForm.toDensity_inChartAt l φ b α)
  have hu : IsUnit ((Orientation.signBasis l.modelOrientation b : ℤ) : ℝ) :=
    isUnit_iff_ne_zero.mpr (abs_pos.mp (by rw [abs_unit_intCast]; exact one_pos))
  rw [heq, integrable_const_mul_iff hu]
  apply φ.integrable_signedInChartAt_iff_unsigned b α (fun x ↦ l.signAt α x) ?_ b.addHaar
  apply continuousOn_iff_continuous_domRestrict.mp
  simpa only [extChartAt_source] using l.continuousOn_signAt α

/-- On an oriented manifold, the integral of a top form is the integral of its density. -/
theorem integralTopForm_eq_integralDensity (o : Manifold.Orientation I M (Fin m))
    (φ : RoughForm I M ℝ m) : integralTopForm o φ = integralDensity (φ.toDensity o) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : LocallyCompactSpace H := I.locallyCompactSpace
  by_cases hi : IntegrableTopForm φ
  · have hd := (integrableDensity_toDensity_iff o φ).mpr hi
    obtain ⟨l, rfl⟩ := o.exists_lift
    let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
    obtain ⟨n, α, u, _, hp, hc⟩ := exists_finite_precompact_chart_cover (I := I) hi.isCompact
    rw [integralTopForm_eq_sum_disjointed_chart_integrals l φ hi b α u (fun i ↦ (hp i).1)
        (fun i ↦ (hp i).2.1) hc,
      integralDensity_eq_sum_disjointed_chart_integrals hd b α u (fun i ↦ (hp i).1)
        (fun i ↦ (hp i).2.1) (by rwa [RoughForm.tsupport_toDensity]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦
      (RoughForm.toDensity_inChartAt l φ b (α i) y).symm)
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
      integralDensity_eq_zero_of_not_integrable (mt (integrableDensity_toDensity_iff o φ).mp hi)]

end TopForm

end TauCeti
