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
import TauCeti.Geometry.Manifold.ExtChartAt.Integral
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Topology.Algebra.Module.FiniteDimension
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
support. `TauCeti.integralDensity_eq_sum_disjointed_chart_integrals` computes it with any
finite chart-measurable chart cover of the points where the density is nonzero, and any model
basis. On an oriented manifold the integral of a top form is the integral of its density
(`TauCeti.integralTopForm_eq_integralDensity`).

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
  · rw [inChartAt_of_mem_target _ b α hy, Pi.zero_apply, Density.zero_apply, Pi.zero_apply]
  · rw [inChartAt_of_notMem_target _ b α hy, Pi.zero_apply]

@[simp]
theorem inChartAt_add (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (μ + ν).inChartAt b α = μ.inChartAt b α + ν.inChartAt b α := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Pi.add_apply, inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy,
      inChartAt_of_mem_target _ b α hy, Pi.add_apply, Density.add_apply]
  · rw [Pi.add_apply, inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy,
      inChartAt_of_notMem_target _ b α hy, add_zero]

@[simp]
theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (c • μ).inChartAt b α = c • μ.inChartAt b α := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Pi.smul_apply, inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy,
      Pi.smul_apply, Density.smul_apply]
  · rw [Pi.smul_apply, inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy,
      smul_zero]

/-- The chart coefficients of the negative of a density are the negatives of its coefficients. -/
@[simp]
theorem inChartAt_neg (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (-μ).inChartAt b α = -μ.inChartAt b α := by
  funext y
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Pi.neg_apply, inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy,
      Pi.neg_apply, Density.neg_apply]
  · rw [Pi.neg_apply, inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy,
      neg_zero]

/-- The chart coefficients of a difference of densities are the differences of their
coefficients. -/
@[simp]
theorem inChartAt_sub (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (μ - ν).inChartAt b α = μ.inChartAt b α - ν.inChartAt b α := by
  rw [sub_eq_add_neg, inChartAt_add, inChartAt_neg, ← sub_eq_add_neg]

/-- Multiplying a density by a function multiplies its chart coefficient by the value of the
function at the chart preimage. -/
theorem inChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    inChartAt (I := I) (fun x ↦ f x • μ x) b α y =
      f ((extChartAt I α).symm y) * μ.inChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [inChartAt_of_mem_target _ b α hy, inChartAt_of_mem_target _ b α hy, Density.smul_apply,
      smul_eq_mul]
  · rw [inChartAt_of_notMem_target _ b α hy, inChartAt_of_notMem_target _ b α hy, mul_zero]

/-- The constant top form given by the determinant of a model basis. Its chart coefficients
are the determinants of the derivatives of the inverse charts. -/
private def detForm (b : Basis (Fin m) ℝ E) : RoughForm I M ℝ m :=
  have := Module.Finite.of_basis b
  fun _ ↦ AlternatingMap.toContinuousAlternatingMap b.det

private theorem detForm_apply (b : Basis (Fin m) ℝ E) (x : M) (v : Fin m → TangentSpace I x) :
    (detForm b : RoughForm I M ℝ m) x v = b.det v := by
  have := Module.Finite.of_basis b
  simp only [detForm]
  exact congrFun (AlternatingMap.coe_toContinuousAlternatingMap b.det) v

/-- In the chart target, the coefficient of a density is its value on the model basis, at the
chart preimage, times the absolute determinant of the derivative of the inverse chart. -/
private theorem inChartAt_eq_abs_det_mul (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    μ.inChartAt b α y =
      |(detForm b : RoughForm I M ℝ m).inChartAt α y b| * μ ((extChartAt I α).symm y) b := by
  rw [inChartAt_of_mem_target μ b α hy, RoughForm.inChartAt_apply, detForm_apply]
  exact (μ _).apply_eq_abs_det_mul b _

/-- In its own chart at the chart point, the coefficient of a density is its value on the
model basis. -/
theorem inChartAt_self [IsManifold I 1 M] (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (x : M) : μ.inChartAt b x (extChartAt I x x) = μ x b := by
  rw [inChartAt_of_mem_target μ b x (mem_extChartAt_target x), mfderivWithin_range_extChartAt_symm,
    extChartAt_to_inv]
  -- The derivative of the inverse chart at the chart point is the identity, applied pointwise.
  rfl

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

/-- Changing the model basis multiplies the chart coefficient of a density by the absolute
change-of-basis determinant. -/
theorem inChartAt_basis_change (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E) (α : M)
    (y : E) : μ.inChartAt b' α y = |b.det b'| * μ.inChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · -- Both tangent spaces of the inverse chart derivative are the model space, so the
    -- density transformation law applies to it as an endomorphism of `E`.
    let L : E →L[ℝ] E := mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y
    let ν := μ ((extChartAt I α).symm y)
    have hL (v : Fin m → E) : ν (fun i ↦ L (v i)) = |LinearMap.det (L : E →ₗ[ℝ] E)| * ν v :=
      ν.comp_apply _ v
    rw [inChartAt_of_mem_target μ b' α hy, inChartAt_of_mem_target μ b α hy]
    calc ν (fun i ↦ L (b' i))
        = |LinearMap.det (L : E →ₗ[ℝ] E)| * ν b' := hL b'
      _ = |b.det b'| * (|LinearMap.det (L : E →ₗ[ℝ] E)| * ν b) := by
        rw [mul_left_comm]
        exact congrArg _ (ν.apply_eq_abs_det_mul b b')
      _ = |b.det b'| * ν (fun i ↦ L (b i)) := by rw [hL b]
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
  have := Module.Finite.of_basis b
  exact TauCeti.setIntegral_image_extChartAt_changeChart α β hsub hs
    (fun x hx ↦ (inChartAt_changeChart μ b (hsub hx).1 (hsub hx).2).symm) ν

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

section OpenCover

variable [IsManifold I 1 M]

/-- Integrability on an open chart cover of the support introduces integrability of a compactly
supported density. One model basis suffices. -/
theorem RoughDensity.integrableDensity_of_open_cover {J : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ)) (b : Basis (Fin m) ℝ E)
    (β : J → M) (u : J → Set M) (hu : ∀ i, IsOpen (u i))
    (hsource : ∀ i, u i ⊆ (chartAt H (β i)).source)
    (hcover : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i, u i)
    (hlocal : ∀ i, IntegrableOn (μ.inChartAt b (β i)) ((extChartAt I (β i)) '' u i) b.addHaar) :
    IntegrableDensity μ := by
  classical
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover u hu hcover
  have hcover' : _root_.tsupport (α := Density E m) μ ⊆ ⋃ i : t, u i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  refine integrableDensity_of_basis hc b fun α ↦ ?_
  let s : t → Set M := fun i ↦ (extChartAt I α).source ∩ u i
  let A : t → Set E := fun i ↦ (extChartAt I α) '' s i
  have hpiece (i : t) : IntegrableOn (μ.inChartAt b α) (A i) b.addHaar := by
    have hsub : s i ⊆ (extChartAt I α).source ∩ (extChartAt I (β i)).source := fun x hx ↦
      ⟨hx.1, by simpa only [extChartAt_source] using hsource i hx.2⟩
    apply (μ.integral_inChartAt_changeChart b α (β i) hsub
      ((hu i).measurableSet_image_extChartAt_source_inter α) b.addHaar).2.mpr
    exact (hlocal i).mono_set (image_mono inter_subset_right)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (integrableOn_finite_iUnion.mpr hpiece)
  intro y hy
  have hn := Function.mem_support.mp hy
  by_cases hyt : y ∈ (extChartAt I α).target
  · have hne : μ ((extChartAt I α).symm y) ≠ 0 := fun hz ↦ hn (by
      rw [RoughDensity.inChartAt_of_mem_target μ b α hyt, hz, Density.zero_apply])
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover' (subset_tsupport (α := Density E m) μ hne))
    exact mem_iUnion.mpr ⟨i, ⟨(extChartAt I α).symm y,
      ⟨(extChartAt I α).map_target hyt, hi⟩, (extChartAt I α).right_inv hyt⟩⟩
  · exact absurd (RoughDensity.inChartAt_of_notMem_target μ b α hyt) hn

/-- A compactly supported density whose support lies in a preferred chart is integrable exactly
when its coefficient in that chart, in one model basis, is integrable. -/
theorem RoughDensity.integrableDensity_iff_of_tsupport_subset_chart {μ : RoughDensity I M m}
    (b : Basis (Fin m) ℝ E) (α : M) (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (chartAt H α).source) :
    IntegrableDensity μ ↔ Integrable (μ.inChartAt b α) b.addHaar := by
  refine ⟨fun h ↦ ((integrableDensity_iff μ).mp h).2.2 b α, fun hi ↦ ?_⟩
  exact μ.integrableDensity_of_open_cover hc b (fun _ : Unit ↦ α) (fun _ ↦ (chartAt H α).source)
    (fun _ ↦ (chartAt H α).open_source) (fun _ ↦ Subset.rfl)
    (fun x hx ↦ mem_iUnion.mpr ⟨(), hs hx⟩) fun _ ↦ hi.integrableOn

end OpenCover

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
  refine ⟨(hμ.1.union hν.1).of_isClosed_subset (isClosed_tsupport _)
    (RoughDensity.tsupport_add_subset μ ν), hμ.2.1, fun b α ↦ ?_⟩
  rw [RoughDensity.inChartAt_add]
  exact (hμ.2.2 b α).add (hν.2.2 b α)

/-- A constant multiple of an integrable density is integrable. -/
theorem IntegrableDensity.smul {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) (c : ℝ) :
    IntegrableDensity (c • μ) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff] at hμ ⊢
  refine ⟨hμ.1.of_isClosed_subset (isClosed_tsupport _) (RoughDensity.tsupport_smul_subset c μ),
    hμ.2.1, fun b α ↦ ?_⟩
  rw [RoughDensity.inChartAt_smul]
  exact (hμ.2.2 b α).smul c

/-- Multiplication by a nonzero scalar preserves density integrability. -/
theorem integrableDensity_smul_iff {c : ℝ} (hc : c ≠ 0) (μ : RoughDensity I M m) :
    IntegrableDensity (c • μ) ↔ IntegrableDensity μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul c⟩
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h.smul c⁻¹

/-- In top degree, witnessed by a model basis `b` of the degree's size, the zero density is
integrable. -/
theorem IntegrableDensity.zero (b : Basis (Fin m) ℝ E) :
    IntegrableDensity (0 : RoughDensity I M m) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  rw [integrableDensity_iff]
  refine ⟨?_, ⟨b⟩, fun b α ↦ ?_⟩
  · exact isCompact_empty.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_zero (X := M) (α := Density E m)).le
  · rw [RoughDensity.inChartAt_zero]
    exact integrable_zero E ℝ b.addHaar

/-- Negation preserves density integrability. -/
theorem IntegrableDensity.neg {μ : RoughDensity I M m} (hμ : IntegrableDensity μ) :
    IntegrableDensity (-μ) := by
  simpa only [neg_one_smul] using hμ.smul (-1)

/-- The difference of two integrable densities is integrable. -/
theorem IntegrableDensity.sub {μ ν : RoughDensity I M m} (hμ : IntegrableDensity μ)
    (hν : IntegrableDensity ν) : IntegrableDensity (μ - ν) := by
  simpa only [sub_eq_add_neg] using hμ.add hν.neg

/-- In top degree, witnessed by a model basis `b` of the degree's size, finite sums of integrable
densities are integrable. The basis is needed for the empty sum. -/
theorem IntegrableDensity.sum {ι : Type*} (b : Basis (Fin m) ℝ E)
    (μ : ι → RoughDensity I M m) (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    IntegrableDensity (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IntegrableDensity.zero (I := I) (M := M) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hμ i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj))

/-- The sum of the chart integrals of a density over the disjointed pieces of a finite chart
cover. -/
private def coverSum [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E)
    {n : ℕ} (α : Fin n → M) (u : Fin n → Set M) : ℝ :=
  ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar

variable [FiniteDimensional ℝ E]

/-- `coverSum` for the chosen finite open chart cover of a compact set `K`. -/
private def chosenCoverSum [MeasurableSpace E] [BorelSpace E] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (K : Set M) (hK : IsCompact K) : ℝ :=
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  let h := exists_finite_precompact_chart_cover (I := I) hK
  coverSum μ b h.choose_spec.choose h.choose_spec.choose_spec.choose

private theorem chosenCoverSum_congr [MeasurableSpace E] [BorelSpace E]
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) {K K' : Set M} (hK : IsCompact K)
    (hK' : IsCompact K') (h : K = K') : chosenCoverSum μ b K hK = chosenCoverSum μ b K' hK' := by
  subst h
  rfl

private theorem chosenCoverSum_smul [MeasurableSpace E] [BorelSpace E] (c : ℝ)
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (K : Set M) (hK : IsCompact K) :
    chosenCoverSum (c • μ) b K hK = c * chosenCoverSum μ b K hK := by
  simp only [chosenCoverSum, coverSum, RoughDensity.inChartAt_smul, Pi.smul_apply, smul_eq_mul,
    integral_const_mul, Finset.mul_sum]

/-- The integral of a rough density. It is zero unless the density is integrable, in particular
unless its degree is the dimension of the model. The sum of chart integrals over the disjointed
pieces of a chosen finite open chart cover of the support defines it; by
`integralDensity_eq_sum_disjointed_chart_integrals` it does not depend on that cover or on the
model basis. -/
def integralDensity (μ : RoughDensity I M m) : ℝ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact if hi : IntegrableDensity μ then
    chosenCoverSum μ (Classical.choice ((integrableDensity_iff μ).mp hi).2.1)
      (_root_.tsupport (α := Density E m) μ) hi.isCompact
  else 0

/-- A nonintegrable density has zero integral. -/
theorem integralDensity_eq_zero_of_not_integrable {μ : RoughDensity I M m}
    (hi : ¬IntegrableDensity μ) : integralDensity μ = 0 := by
  rw [integralDensity, dite_eq_right hi]

/-- The integral of an integrable density is the sum of its chart integrals over the disjointed
pieces of any finite chart-measurable chart cover of the points where it is nonzero, in any model
basis. -/
theorem integralDensity_eq_sum_disjointed_chart_integrals [IsManifold I 1 M]
    [MeasurableSpace E] [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ)
    (b : Basis (Fin m) ℝ E) {n : ℕ} (α : Fin n → M) (u : Fin n → Set M)
    (hu : ∀ i, IsChartMeasurable I (u i)) (hs : ∀ i, u i ⊆ (extChartAt I (α i)).source)
    (hc : {x | μ x ≠ 0} ⊆ ⋃ i, u i) :
    integralDensity μ =
      ∑ i, ∫ y in (extChartAt I (α i)) '' disjointed u i, μ.inChartAt b (α i) y ∂b.addHaar := by
  classical
  have hm : ‹MeasurableSpace E› = borel E := BorelSpace.measurable_eq
  cases hm
  let : MeasurableSpace E := borel E
  let : LocallyCompactSpace H := I.locallyCompactSpace
  rw [integralDensity, dite_eq_left hi]
  unfold chosenCoverSum coverSum
  let h := exists_finite_precompact_chart_cover (I := I) hi.isCompact
  have hp := h.choose_spec.choose_spec.choose_spec.choose_spec
  simp_rw [μ.setIntegral_inChartAt_basis_eq b]
  have hint (β : M) (t : Set E) : IntegrableOn (μ.inChartAt b β) t b.addHaar :=
    (((integrableDensity_iff μ).mp hi).2.2 b β).integrableOn
  -- The coefficient of a density vanishes at the coordinates of the points where it vanishes.
  have hz (β : M) (x : M) (hx : x ∈ (extChartAt I β).source) (hx0 : x ∉ {x | μ x ≠ 0}) :
      μ.inChartAt b β (extChartAt I β x) = 0 := by
    have hμ : μ ((extChartAt I β).symm (extChartAt I β x)) = 0 := by
      rw [(extChartAt I β).left_inv hx]
      exact of_not_not hx0
    rw [RoughDensity.inChartAt_of_mem_target μ b β ((extChartAt I β).map_source hx), hμ,
      Density.zero_apply]
  exact sum_setIntegral_image_extChartAt_disjointed_eq hz
    (fun β γ _ hsub hm ↦ (μ.integral_inChartAt_changeChart b β γ hsub
      (hm.image_extChartAt β (hsub.trans inter_subset_left)) b.addHaar).1)
    _ _ (fun i ↦ (hp.1 i).1.isChartMeasurable) (fun i ↦ (hp.1 i).2.1)
    (fun x hx ↦ hp.2 (subset_closure hx)) (fun _ ↦ hint _ _)
    α u hu hs hc (fun _ ↦ hint _ _)

/-- An integrable density that vanishes outside a preferred chart has that chart's integral. -/
theorem integralDensity_eq_integral_inChartAt [IsManifold I 1 M] [MeasurableSpace E]
    [BorelSpace E] {μ : RoughDensity I M m} (hi : IntegrableDensity μ) (b : Basis (Fin m) ℝ E)
    (α : M) (hs : {x | μ x ≠ 0} ⊆ (extChartAt I α).source) :
    integralDensity μ = ∫ y, μ.inChartAt b α y ∂b.addHaar := by
  rw [integralDensity_eq_sum_disjointed_chart_integrals hi b (fun _ : Fin 1 ↦ α)
    (fun _ ↦ (extChartAt I α).source) (fun _ ↦ (isOpen_extChartAt_source α).isChartMeasurable)
    (fun _ ↦ Subset.rfl) (hs.trans (subset_iUnion_of_subset 0 Subset.rfl))]
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
    simp [chosenCoverSum, coverSum]
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
  have hu (i : Fin n) : IsChartMeasurable I (u i) := (hp i).1.isChartMeasurable
  rw [integralDensity_eq_sum_disjointed_chart_integrals (hμ.add hν) b α u hu (fun i ↦ (hp i).2.1)
      fun x hx ↦ hc (RoughDensity.tsupport_add_subset μ ν (subset_closure hx)),
    integralDensity_eq_sum_disjointed_chart_integrals hμ b α u hu (fun i ↦ (hp i).2.1)
      fun x hx ↦ hc (Or.inl (subset_closure hx)),
    integralDensity_eq_sum_disjointed_chart_integrals hν b α u hu (fun i ↦ (hp i).2.1)
      fun x hx ↦ hc (Or.inr (subset_closure hx)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [RoughDensity.inChartAt_add]
  exact integral_add (((integrableDensity_iff μ).mp hμ).2.2 b (α i)).integrableOn
    (((integrableDensity_iff ν).mp hν).2.2 b (α i)).integrableOn

/-- Integration of densities commutes with finite sums of integrable densities. -/
theorem integralDensity_sum [IsManifold I 1 M] {ι : Type*} (μ : ι → RoughDensity I M m)
    (s : Finset ι) (hμ : ∀ i ∈ s, IntegrableDensity (μ i)) :
    integralDensity (∑ i ∈ s, μ i) = ∑ i ∈ s, integralDensity (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hμi := hμ i (Finset.mem_insert_self i s)
    let : MeasurableSpace E := borel E
    let : BorelSpace E := ⟨rfl⟩
    obtain ⟨b⟩ := ((integrableDensity_iff (μ i)).mp hμi).2.1
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      integralDensity_add hμi (IntegrableDensity.sum b μ s fun j hj ↦
        hμ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hμ j (Finset.mem_insert_of_mem hj)]

/-- Constant scalar multiplication commutes with the integral of densities, including
nonintegrable ones. -/
theorem integralDensity_smul (c : ℝ) (μ : RoughDensity I M m) :
    integralDensity (c • μ) = c * integralDensity μ := by
  by_cases hc0 : c = 0
  · rw [hc0, zero_smul, zero_mul, integralDensity_zero]
  by_cases hμ : IntegrableDensity μ
  swap
  · rw [integralDensity_eq_zero_of_not_integrable hμ, integralDensity_eq_zero_of_not_integrable
      (mt (integrableDensity_smul_iff hc0 μ).mp hμ), mul_zero]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  rw [integralDensity, dite_eq_left (hμ.smul c), integralDensity, dite_eq_left hμ,
    chosenCoverSum_congr _ _ _ hμ.isCompact (RoughDensity.tsupport_smul hc0 μ),
    chosenCoverSum_smul]

/-- The integral of the negative of a density is the negative of its integral. -/
@[simp]
theorem integralDensity_neg (μ : RoughDensity I M m) :
    integralDensity (-μ) = -integralDensity μ := by
  simpa only [neg_one_smul, neg_one_mul] using integralDensity_smul (-1) μ

/-- The integral of densities is subtractive on integrable densities. -/
theorem integralDensity_sub [IsManifold I 1 M] {μ ν : RoughDensity I M m}
    (hμ : IntegrableDensity μ) (hν : IntegrableDensity ν) :
    integralDensity (μ - ν) = integralDensity μ - integralDensity ν := by
  rw [sub_eq_add_neg, integralDensity_add hμ hν.neg, integralDensity_neg, ← sub_eq_add_neg]

section TopForm

variable [IsManifold I 1 M]

/-- In a preferred chart, the coefficient of the density of a top form is its signed coefficient
against an orientation lift, weighted by the relative sign of the model basis. -/
theorem RoughDensity.inChartAt_toDensity (l : Manifold.OrientationLift I M (Fin m))
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
    -- The orientation lift relates the chart signs at `x` through the transition determinant.
    have hdet : (l.signAt α x : ℝ) * D.toLinearMap.det =
        |D.toLinearMap.det| * (l.signAt x x : ℝ) := by
      simpa only [l.signAt_of_mem hα, l.signAt_of_mem hxx] using l.sign_mul_det α x x hα hxx
    -- The value of the density at `x` on the model basis.
    have hval : (φ.toDensity (Manifold.Orientation.mk l)) x b =
        (Orientation.signBasis l.modelOrientation b : ℝ) * l.signAt x x * φ x b := by
      have hs := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (l.signBasis_orientationAt b x)
      simp only [Units.val_mul, Int.cast_mul] at hs
      rw [← hs, ← Manifold.Orientation.orientationAt_mk]
      exact φ.toDensity_apply_basis _ x b
    -- The form coefficient changes to the chart at `x` with the signed determinant.
    have hcoef := φ.inChartAt_apply_basis_eq_det_mul b ((extChartAt I α).map_source hx)
      (x := x) (by rw [(extChartAt I α).left_inv hx]; exact mem_extChartAt_source x)
    rw [(extChartAt I α).left_inv hx, RoughForm.inChartAt_extChartAt_self] at hcoef
    rw [RoughDensity.inChartAt_changeChart _ b hx (mem_extChartAt_source x),
      RoughDensity.inChartAt_self, hval, RoughForm.signedInChartAt_apply_of_mem_source _ _ _ _ hx,
      hcoef]
    linear_combination (-((Orientation.signBasis l.modelOrientation b : ℝ) * φ x b)) * hdet
  · rw [RoughDensity.inChartAt_of_notMem_target _ b α hy, RoughForm.signedInChartAt_apply,
      dite_eq_right hy, mul_zero]

/-- On an oriented manifold, a top form is integrable exactly when its density is. -/
@[simp]
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
    funext (RoughDensity.inChartAt_toDensity l φ b α)
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
      integralDensity_eq_sum_disjointed_chart_integrals hd b α u
        (fun i ↦ (hp i).1.isChartMeasurable) (fun i ↦ (hp i).2.1)
        (fun x hx ↦ hc (by rw [← RoughForm.tsupport_toDensity]; exact subset_closure hx)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦
      (RoughDensity.inChartAt_toDensity l φ b (α i) y).symm)
  · rw [integralTopForm_eq_zero_of_not_integrable o φ hi,
      integralDensity_eq_zero_of_not_integrable (mt (integrableDensity_toDensity_iff o φ).mp hi)]

end TopForm

end TauCeti
