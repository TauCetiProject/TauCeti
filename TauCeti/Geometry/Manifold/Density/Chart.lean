/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Chart
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Chart coefficients of rough densities

A rough density `μ` of degree `m` is read in a preferred chart through a model basis `b`: its
coefficient `μ.inChartAt b α y` is the value of `μ` at `(extChartAt I α).symm y` on the image of
`b` under the derivative of the inverse chart, extended by zero outside the chart target. On a
chart overlap two coefficients differ by the absolute determinant of the transition derivative
(`TauCeti.RoughDensity.inChartAt_changeChart`), and two bases change the coefficient by their
absolute change-of-basis determinant (`TauCeti.RoughDensity.inChartAt_basis_change`).

These pointwise identities, together with support, algebraic operations, and pointwise
nonnegativity (`TauCeti.RoughDensity.inChartAt_nonneg`), are independent of integration and
measure theory.

## Main definitions

* `TauCeti.RoughDensity.inChartAt`: the coefficient of a rough density in a preferred chart.

## Main results

* `TauCeti.RoughDensity.inChartAt_changeChart`: the absolute determinant law on chart overlaps.
* `TauCeti.RoughDensity.inChartAt_basis_change`: the absolute change-of-basis determinant law.
* `TauCeti.RoughDensity.inChartAt_nonneg`: nonnegativity of chart coefficients for nonnegative
  densities.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Set Module
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

/-- If `μ ((extChartAt I α).symm y) = 0`, then `μ.inChartAt b α y = 0`. -/
theorem inChartAt_eq_zero_of_apply_eq_zero {μ : RoughDensity I M m} (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (h : μ ((extChartAt I α).symm y) = 0) : μ.inChartAt b α y = 0 := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.inChartAt_of_mem_target b α hy, h, Density.zero_apply]
  · exact μ.inChartAt_of_notMem_target b α hy

/-- If `x ∈ (extChartAt I α).source` lies outside `tsupport μ`, then
`μ.inChartAt b α (extChartAt I α x) = 0`. -/
theorem inChartAt_eq_zero_of_notMem_tsupport (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {x : M} (hx : x ∈ (extChartAt I α).source)
    (hn : x ∉ _root_.tsupport (α := Density E m) μ) :
    μ.inChartAt b α (extChartAt I α x) = 0 :=
  inChartAt_eq_zero_of_apply_eq_zero b α <| by
    rw [(extChartAt I α).left_inv hx]
    exact _root_.image_eq_zero_of_notMem_tsupport (α := Density E m) hn

/-- Chart coefficients vanish outside the coordinate target. -/
theorem support_inChartAt_subset_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) : Function.support (μ.inChartAt b α) ⊆ (extChartAt I α).target := by
  intro y hy
  by_contra hyt
  exact hy (μ.inChartAt_of_notMem_target b α hyt)

/-- `Function.support (μ.inChartAt b α)` lies in the coordinate image of
`(extChartAt I α).source ∩ tsupport μ`. -/
theorem support_inChartAt_subset (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    Function.support (μ.inChartAt b α) ⊆
      (extChartAt I α) '' ((extChartAt I α).source ∩ _root_.tsupport (α := Density E m) μ) := by
  intro y hy
  have hyt := μ.support_inChartAt_subset_target b α hy
  refine ⟨(extChartAt I α).symm y, ⟨(extChartAt I α).map_target hyt, ?_⟩,
    (extChartAt I α).right_inv hyt⟩
  exact _root_.subset_tsupport (α := Density E m) μ fun h0 ↦
    Function.mem_support.mp hy (inChartAt_eq_zero_of_apply_eq_zero b α h0)

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

@[simp]
theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (c • μ).inChartAt b α = c • μ.inChartAt b α :=
  funext (inChartAt_fun_smul (fun _ ↦ c) μ b α)

/-- The chart coefficients of the negative of a density are the negatives of its coefficients. -/
@[simp]
theorem inChartAt_neg (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (-μ).inChartAt b α = -μ.inChartAt b α := by
  rw [← neg_one_smul ℝ μ, inChartAt_smul, neg_one_smul]

/-- The chart coefficients of a difference of densities are the differences of their
coefficients. -/
@[simp]
theorem inChartAt_sub (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    (μ - ν).inChartAt b α = μ.inChartAt b α - ν.inChartAt b α := by
  rw [sub_eq_add_neg, inChartAt_add, inChartAt_neg, ← sub_eq_add_neg]

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

/-- On the model space, the coefficient of a density in any chart is its value on the model
basis. -/
@[simp]
theorem inChartAt_modelSpace (μ : RoughDensity 𝓘(ℝ, E) E m)
    (b : Basis (Fin m) ℝ E) (α : E) : μ.inChartAt b α = fun y ↦ μ y b := by
  funext y
  -- All charts of the model space are the identity chart, so this is `inChartAt_self` at `y`.
  exact μ.inChartAt_self b y

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

/-- If `μ` is nonnegative on every tangent basis, then its chart coefficient `μ.inChartAt b α`
is nonnegative everywhere. -/
theorem inChartAt_nonneg {μ : RoughDensity I M m}
    (hμ : ∀ x (c : Basis (Fin m) ℝ (TangentSpace I x)), 0 ≤ μ x c)
    (b : Basis (Fin m) ℝ E) (α : M) (y : E) : 0 ≤ μ.inChartAt b α y := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.inChartAt_of_mem_target b α hy]
    -- `TangentSpace I ((extChartAt I α).symm y)` is definitionally `E`, so `b` gives a tangent
    -- basis via `tangentSpaceCastModel` to evaluate `apply_eq_abs_det_mul`.
    let c : Basis (Fin m) ℝ (TangentSpace I ((extChartAt I α).symm y)) :=
      b.map (tangentSpaceCastModel I ((extChartAt I α).symm y)).symm.toLinearEquiv
    rw [(μ ((extChartAt I α).symm y)).apply_eq_abs_det_mul c
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i))]
    exact mul_nonneg (abs_nonneg _) (hμ _ c)
  · rw [μ.inChartAt_of_notMem_target b α hy]

end RoughDensity

end TauCeti
