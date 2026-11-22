/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.LinearAlgebra.Density.Pullback
public import TauCeti.MeasureTheory.Integral.Bochner.Density
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic
public import TauCeti.Geometry.Manifold.Orientation.Lift
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Symm
import TauCeti.Geometry.Manifold.ExtChartAt.Cover

/-!
# Coordinate expressions and chart coefficients of rough densities

Defines `TauCeti.RoughDensity.inChartAt` and `TauCeti.RoughDensity.coeffInChartAt`, proves overlap
Jacobian laws (`inChartAt_eq_compLinearMap`, `coeffInChartAt_changeChart`), bundle continuity
(`continuousOn_inChartAt_of_continuousOn_section`), and `RoughForm.coeffInChartAt_toDensity`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Bundle Set Filter MeasureTheory Module
open scoped Manifold Topology

namespace TauCeti

namespace RoughDensity

section InChartAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Coordinate expression of `μ` in the preferred extended chart at `α` (unspecified outside
`(extChartAt I α).target`). -/
def inChartAt (μ : RoughDensity I M m) (α : M) (z : E) : Density E m :=
  (μ ((extChartAt I α).symm z)).compLinearMap
    ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, E) z).symm.toLinearMap)
    ⟨(tangentSpaceCastModel I ((extChartAt I α).symm z)).symm.toLinearEquiv⟩

/-- Evaluation of `inChartAt` on a tuple of model vectors. -/
theorem inChartAt_apply (μ : RoughDensity I M m) (α : M) (z : E) (v : Fin m → E) :
    μ.inChartAt α z v = μ ((extChartAt I α).symm z)
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z (v i)) := by
  rw [inChartAt, Density.compLinearMap_apply]; rfl

/-- The zero rough density has zero coordinate expression in every chart. -/
@[simp] theorem inChartAt_zero (α : M) : (0 : RoughDensity I M m).inChartAt α = 0 := by
  funext z; ext v; simp only [inChartAt_apply, Pi.zero_apply, Density.zero_apply]

/-- Coordinate expressions distribute over addition. -/
@[simp] theorem inChartAt_add (μ ν : RoughDensity I M m) (α : M) :
    (μ + ν).inChartAt α = μ.inChartAt α + ν.inChartAt α := by
  funext z; ext v; simp only [Pi.add_apply, Density.add_apply, inChartAt_apply]

/-- Coordinate expressions commute with constant scalar multiplication. -/
@[simp] theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (α : M) :
    (c • μ).inChartAt α = c • μ.inChartAt α := by
  funext z; ext v; simp only [Pi.smul_apply, Density.smul_apply, inChartAt_apply]

/-- Coordinate expressions commute with negation. -/
@[simp] theorem inChartAt_neg (μ : RoughDensity I M m) (α : M) :
    (-μ).inChartAt α = -μ.inChartAt α := by rw [← neg_one_smul ℝ μ, inChartAt_smul, neg_one_smul]

/-- Coordinate expressions distribute over subtraction. -/
@[simp] theorem inChartAt_sub (μ ν : RoughDensity I M m) (α : M) :
    (μ - ν).inChartAt α = μ.inChartAt α - ν.inChartAt α := by
  rw [sub_eq_add_neg, inChartAt_add, inChartAt_neg, sub_eq_add_neg]

/-- Scalar localization multiplies `inChartAt` by the pulled-back scalar function. -/
theorem inChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M m) (α : M) (z : E) :
    inChartAt (I := I) (fun x ↦ f x • μ x) α z = f ((extChartAt I α).symm z) • μ.inChartAt α z := by
  ext v; simp only [inChartAt_apply, Density.smul_apply]

/-- Evaluating `inChartAt` at `extChartAt I α x` transports vectors via `tangentCoordChange`. -/
theorem inChartAt_chart_apply [IsManifold I 1 M] (μ : RoughDensity I M m) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin m → E) :
    μ.inChartAt α (extChartAt I α x) v = μ x (fun i ↦ tangentCoordChange I α x x (v i)) := by
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [inChartAt_apply, ← TangentBundle.symmL_trivializationAt hx',
    TangentBundle.symmL_trivializationAt_eq_core hx', (extChartAt I α).left_inv hx]; rfl

/-- Evaluating `μ.inChartAt x` at `extChartAt I x x` recovers `μ x`, without atlas smoothness. -/
theorem inChartAt_extChartAt_self (μ : RoughDensity I M m) (x : M) :
    μ.inChartAt x (extChartAt I x x) = μ x := by
  have hmf := (hasMFDerivWithinAt_extChartAt_symm_self (I := I) x).mfderivWithin
    (I.uniqueDiffOn.uniqueDiffWithinAt
      (extChartAt_target_subset_range x (mem_extChartAt_target x))).uniqueMDiffWithinAt
  -- `TangentSpace I x` is definitionally `E`, so `id ∘ v` agrees with `v`.
  ext v; rw [inChartAt_apply, (extChartAt I x).left_inv (mem_extChartAt_source x), hmf]; rfl

private theorem inChartAt_chart_eq_compLinearEquiv [IsManifold I 1 M] (μ : RoughDensity I M m)
    {α x : M} (hx : x ∈ (extChartAt I α).source) :
    μ.inChartAt α (extChartAt I α x) = Density.compLinearEquiv
      ((trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x
        (by rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)])).symm
      (μ x) := by
  ext v; rw [inChartAt_apply, Density.compLinearEquiv_apply]
  simp_rw [mfderivWithin_extChartAt_symm_apply_eq_trivializationAt_symm α
    ((extChartAt I α).map_source hx)]
  rw [(extChartAt I α).left_inv hx]
  exact congrArg (μ x) (funext fun _ ↦ (Trivialization.linearEquivAt_symm_apply ..).symm)

/-- Two rough densities agree at `x ∈ (extChartAt I α).source` iff their coordinate expressions
agree at `extChartAt I α x`. -/
theorem inChartAt_chart_eq_iff [IsManifold I 1 M] {μ ν : RoughDensity I M m} {α x : M}
    (hx : x ∈ (extChartAt I α).source) :
    μ.inChartAt α (extChartAt I α x) = ν.inChartAt α (extChartAt I α x) ↔ μ x = ν x := by
  rw [μ.inChartAt_chart_eq_compLinearEquiv hx, ν.inChartAt_chart_eq_compLinearEquiv hx]
  exact (Density.compLinearEquiv _).injective.eq_iff

/-- Evaluating `μ.inChartAt α` at `extChartAt I α x` on a model basis `b` equals evaluating `μ x`
on some basis of `TangentSpace I x`. -/
theorem exists_basis_inChartAt_chart_apply_eq [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    ∃ b' : Basis (Fin m) ℝ (TangentSpace I x), μ.inChartAt α (extChartAt I α x) b = μ x b' :=
  ⟨b.map ((trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x
    (by rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)])).symm, by
    rw [μ.inChartAt_chart_eq_compLinearEquiv hx, Density.compLinearEquiv_apply]
    exact congrArg (μ x) (funext fun _ ↦ (Basis.map_apply ..).symm)⟩

/-- Evaluating `μ.inChartAt α` at a target point `y` on a model basis `b` equals evaluating
`μ ((extChartAt I α).symm y)` on some basis of the tangent space there. -/
theorem exists_basis_inChartAt_apply_eq [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    ∃ b' : Basis (Fin m) ℝ (TangentSpace I ((extChartAt I α).symm y)),
      μ.inChartAt α y b = μ ((extChartAt I α).symm y) b' := by
  simpa only [(extChartAt I α).right_inv hy] using
    μ.exists_basis_inChartAt_chart_apply_eq b α ((extChartAt I α).map_target hy)

/-- On a preferred-chart overlap, `inChartAt` pulls back by the coordinate-change derivative. -/
theorem inChartAt_eq_compLinearMap [IsManifold I 1 M] (μ : RoughDensity I M m) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    μ.inChartAt x₀ z =
      (μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z))).compLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap
        ⟨LinearEquiv.refl ℝ E⟩ := by
  have hcomp := mfderivWithin_extChartAt_symm_eq_comp_fderivWithin hz hx
  ext v
  rw [inChartAt_apply, Density.compLinearMap_apply, inChartAt_apply, (extChartAt I x).left_inv hx]
  exact congrArg _ (funext fun i ↦ congrArg (· (v i)) hcomp)

/-- Between overlapping preferred charts, `inChartAt` transforms by the absolute Jacobian
determinant within `range I`, including boundary and corner points. -/
theorem inChartAt_apply_eq_abs_det_mul [IsManifold I 1 M] (μ : RoughDensity I M m)
    {x₀ x : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) (v : Fin m → E) :
    μ.inChartAt x₀ z v =
      |(fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z).toLinearMap.det| *
        μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z)) v := by
  rw [μ.inChartAt_eq_compLinearMap hz hx, Density.compLinearMap_apply, Density.comp_apply]

end InChartAt

section CoeffInChartAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Scalar chart coefficient of `μ` in a model basis `b`, zero outside `(extChartAt I α).target`. -/
def coeffInChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) : E → ℝ :=
  (extChartAt I α).target.indicator fun y ↦ μ.inChartAt α y b

/-- `coeffInChartAt` agrees with evaluating the zero-extended coordinate density on `b`. -/
theorem coeffInChartAt_eq_indicator_apply (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (y : E) : μ.coeffInChartAt b α y = ((extChartAt I α).target.indicator (μ.inChartAt α) y) b := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [coeffInChartAt, indicator_of_mem hy, indicator_of_mem hy]
  · rw [coeffInChartAt, indicator_of_notMem hy, indicator_of_notMem hy, Density.zero_apply]

open scoped Classical in
/-- Pointwise formula for `coeffInChartAt`, zero outside `(extChartAt I α).target`. -/
theorem coeffInChartAt_apply (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    μ.coeffInChartAt b α y = if y ∈ (extChartAt I α).target then μ.inChartAt α y b else 0 :=
  Set.indicator_apply ..

/-- Inside the chart target, `coeffInChartAt` evaluates `inChartAt` on `b`. -/
theorem coeffInChartAt_apply_of_mem_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    μ.coeffInChartAt b α y = μ.inChartAt α y b := indicator_of_mem hy _

/-- Outside the chart target, `coeffInChartAt` vanishes. -/
theorem coeffInChartAt_apply_of_notMem_target (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {y : E} (hy : y ∉ (extChartAt I α).target) :
    μ.coeffInChartAt b α y = 0 := indicator_of_notMem hy _

/-- At the chart image of a source point, `coeffInChartAt` evaluates `inChartAt` on `b`. -/
theorem coeffInChartAt_apply_of_mem_source (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    μ.coeffInChartAt b α (extChartAt I α x) = μ.inChartAt α (extChartAt I α x) b :=
  μ.coeffInChartAt_apply_of_mem_target b α ((extChartAt I α).map_source hx)

/-- Evaluating `μ.coeffInChartAt b x` at `extChartAt I x x` recovers `μ x b`. -/
theorem coeffInChartAt_extChartAt_self (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (x : M) : μ.coeffInChartAt b x (extChartAt I x x) = μ x b := by
  rw [μ.coeffInChartAt_apply_of_mem_target b x (mem_extChartAt_target x),
    inChartAt_extChartAt_self]
  rfl

/-- If `μ ((extChartAt I α).symm y) = 0`, then `μ.coeffInChartAt b α y = 0`. -/
theorem coeffInChartAt_eq_zero_of_apply_eq_zero {μ : RoughDensity I M m} (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (h : μ ((extChartAt I α).symm y) = 0) : μ.coeffInChartAt b α y = 0 := by
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [μ.coeffInChartAt_apply_of_mem_target b α hy, inChartAt_apply, h, Density.zero_apply]
  · exact μ.coeffInChartAt_apply_of_notMem_target b α hy

/-- The zero rough density has zero chart coefficient everywhere. -/
@[simp] theorem coeffInChartAt_zero (b : Basis (Fin m) ℝ E) (α : M) :
    (0 : RoughDensity I M m).coeffInChartAt b α = 0 := by funext y; simp [coeffInChartAt]

/-- `coeffInChartAt` is additive in the rough density. -/
@[simp] theorem coeffInChartAt_add (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (y : E) : (μ + ν).coeffInChartAt b α y = μ.coeffInChartAt b α y + ν.coeffInChartAt b α y := by
  classical simp only [coeffInChartAt_apply]; split_ifs <;> simp

/-- Pointwise scalar multiplication multiplies `coeffInChartAt` by the pulled-back scalar. -/
theorem coeffInChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    coeffInChartAt (I := I) (fun x ↦ f x • μ x) b α y =
      f ((extChartAt I α).symm y) * μ.coeffInChartAt b α y := by
  classical simp only [coeffInChartAt_apply]; split_ifs <;> simp [inChartAt_fun_smul]

/-- `coeffInChartAt` commutes with constant scalar multiplication. -/
@[simp] theorem coeffInChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) : (c • μ).coeffInChartAt b α y = c * μ.coeffInChartAt b α y :=
  coeffInChartAt_fun_smul (fun _ ↦ c) μ b α y

/-- `coeffInChartAt` commutes with negation. -/
@[simp] theorem coeffInChartAt_neg (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (y : E) : (-μ).coeffInChartAt b α y = -μ.coeffInChartAt b α y := by
  rw [← neg_one_smul ℝ μ, coeffInChartAt_smul, neg_one_mul]

/-- `coeffInChartAt` respects subtraction. -/
@[simp] theorem coeffInChartAt_sub (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (y : E) : (μ - ν).coeffInChartAt b α y = μ.coeffInChartAt b α y - ν.coeffInChartAt b α y := by
  rw [sub_eq_add_neg, coeffInChartAt_add, coeffInChartAt_neg, sub_eq_add_neg]

/-- Indicator localization restricts `coeffInChartAt` to the corresponding coordinate piece. -/
theorem coeffInChartAt_indicator (s : Set M) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    coeffInChartAt (I := I) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x • μ x) b α y =
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s).indicator
        (μ.coeffInChartAt b α) y := by
  rw [coeffInChartAt_fun_smul]
  by_cases hy : y ∈ (extChartAt I α).target
  · by_cases hs : (extChartAt I α).symm y ∈ s
    · rw [indicator_of_mem hs, one_mul, indicator_of_mem (mem_inter hy (mem_preimage.mpr hs))]
    · rw [indicator_of_notMem hs, zero_mul,
        indicator_of_notMem (mt mem_of_mem_inter_right (mt mem_preimage.mp hs))]
  · rw [μ.coeffInChartAt_apply_of_notMem_target b α hy, mul_zero,
      indicator_of_notMem (mt mem_of_mem_inter_left hy)]

/-- Equal densities on `s ⊆ (extChartAt I α).source` have equal `coeffInChartAt` on `e '' s`. -/
theorem eqOn_coeffInChartAt_image {μ ν : RoughDensity I M m} {s : Set M} (h : ∀ x ∈ s, μ x = ν x)
    (b : Basis (Fin m) ℝ E) (α : M) (hs : s ⊆ (extChartAt I α).source) :
    EqOn (μ.coeffInChartAt b α) (ν.coeffInChartAt b α) ((extChartAt I α) '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [coeffInChartAt_apply_of_mem_source _ _ _ (hs hx),
    coeffInChartAt_apply_of_mem_source _ _ _ (hs hx), inChartAt_apply, inChartAt_apply,
    (extChartAt I α).left_inv (hs hx), h x hx]

/-- Chart coefficients vanish outside the coordinate target. -/
theorem support_coeffInChartAt_subset_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) : Function.support (μ.coeffInChartAt b α) ⊆ (extChartAt I α).target :=
  support_indicator_subset

/-- `support (μ.coeffInChartAt b α)` lies in the coordinate image of `source ∩ tsupport μ`. -/
theorem support_coeffInChartAt_subset (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    Function.support (μ.coeffInChartAt b α) ⊆
      (extChartAt I α) '' ((extChartAt I α).source ∩ _root_.tsupport (α := Density E m) μ) :=
  fun _ hy ↦ let ht := μ.support_coeffInChartAt_subset_target b α hy
  ⟨_, ⟨(extChartAt I α).map_target ht, _root_.subset_tsupport (α := Density E m) μ fun h0 ↦
    Function.mem_support.mp hy (coeffInChartAt_eq_zero_of_apply_eq_zero b α h0)⟩,
    (extChartAt I α).right_inv ht⟩

/-- Continuity of `μ.inChartAt α` on the target implies continuity of `μ.coeffInChartAt b α`. -/
theorem continuousOn_coeffInChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (hμ : ContinuousOn (μ.inChartAt α) (extChartAt I α).target) :
    ContinuousOn (μ.coeffInChartAt b α) (extChartAt I α).target :=
  ((Density.continuous_eval b).comp_continuousOn hμ).congr fun _ ↦
    μ.coeffInChartAt_apply_of_mem_target b α

/-- A density supported compactly in one chart with continuous coordinate expression there has
integrable chart coefficient against any measure finite on compact sets. -/
theorem integrable_coeffInChartAt [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (hμ : ContinuousOn (μ.inChartAt α) (extChartAt I α).target)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (extChartAt I α).source)
    (ν : Measure E) [IsFiniteMeasureOnCompacts ν] : Integrable (μ.coeffInChartAt b α) ν :=
  (integrableOn_iff_integrable_of_support_subset
    ((μ.support_coeffInChartAt_subset b α).trans (image_mono inter_subset_right))).mp <|
    ((μ.continuousOn_coeffInChartAt b α hμ).mono
      ((image_mono hs).trans (extChartAt I α).image_source_eq_target.subset)).integrableOn_compact
      (hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs))

variable [MeasurableSpace E] [BorelSpace E]

/-- Integrability of `coeffInChartAt` against `b.addHaar` is independent of `b`. -/
theorem integrable_coeffInChartAt_basis_iff (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) : Integrable (μ.coeffInChartAt b' α) b'.addHaar ↔
      Integrable (μ.coeffInChartAt b α) b.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integrable_density_apply_iff b' ((extChartAt I α).target.indicator (μ.inChartAt α))

/-- Set integrability of `coeffInChartAt` against `b.addHaar` is independent of `b`. -/
theorem integrableOn_coeffInChartAt_basis_iff (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) (s : Set E) : IntegrableOn (μ.coeffInChartAt b' α) s b'.addHaar ↔
      IntegrableOn (μ.coeffInChartAt b α) s b.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integrableOn_density_apply_iff b' ((extChartAt I α).target.indicator (μ.inChartAt α)) s

/-- The normalized Haar integral of `coeffInChartAt` is independent of `b`. -/
theorem integral_coeffInChartAt_basis_eq (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) : (∫ y, μ.coeffInChartAt b α y ∂b.addHaar) =
      ∫ y, μ.coeffInChartAt b' α y ∂b'.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integral_density_apply_eq b' ((extChartAt I α).target.indicator (μ.inChartAt α))

/-- The normalized Haar set integral of `coeffInChartAt` is independent of `b`. -/
theorem setIntegral_coeffInChartAt_basis_eq (μ : RoughDensity I M m) (b b' : Basis (Fin m) ℝ E)
    (α : M) (s : Set E) : (∫ y in s, μ.coeffInChartAt b α y ∂b.addHaar) =
      ∫ y in s, μ.coeffInChartAt b' α y ∂b'.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.setIntegral_density_apply_eq b' ((extChartAt I α).target.indicator (μ.inChartAt α)) s

/-- On a measurable overlap piece, both the Haar set integral and integrability of `coeffInChartAt`
are invariant under change of chart, with no orientation compatibility. -/
theorem coeffInChartAt_changeChart [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s)) (ν : Measure E) [ν.IsAddHaarMeasure] :
    ((∫ y in (extChartAt I α) '' s, μ.coeffInChartAt b α y ∂ν) =
        ∫ y in (extChartAt I β) '' s, μ.coeffInChartAt b β y ∂ν) ∧
      (IntegrableOn (μ.coeffInChartAt b α) ((extChartAt I α) '' s) ν ↔
        IntegrableOn (μ.coeffInChartAt b β) ((extChartAt I β) '' s) ν) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  refine TauCeti.extChartAt_coordChange_setIntegral_and_integrableOn α β hsub hs
    (μ.coeffInChartAt b α) (μ.coeffInChartAt b β) (fun x hx ↦ ?_) ν
  have ⟨hα, hβ⟩ := hsub hx
  have hl := (extChartAt I α).left_inv hα
  have hc := μ.inChartAt_apply_eq_abs_det_mul ((extChartAt I α).map_source hα) (hl.symm ▸ hβ) b
  rw [hl] at hc
  rw [μ.coeffInChartAt_apply_of_mem_source b α hα, μ.coeffInChartAt_apply_of_mem_source b β hβ,
    hc, smul_eq_mul]

/-- A rough density supported in two preferred charts has equal chart-coefficient integrals. -/
theorem integral_coeffInChartAt_eq_of_tsupport_subset [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α β : M)
    (hsub : _root_.tsupport (α := Density E m) μ ⊆
      (extChartAt I α).source ∩ (extChartAt I β).source)
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ y, μ.coeffInChartAt b α y ∂ν) = ∫ y, μ.coeffInChartAt b β y ∂ν := by
  have := b.finiteDimensional_of_finite
  have hfull (γ : M) :
      (∫ y in (extChartAt I γ) '' ((extChartAt I α).source ∩ (extChartAt I β).source),
        μ.coeffInChartAt b γ y ∂ν) = ∫ y, μ.coeffInChartAt b γ y ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦ by_contra fun hn ↦
      hy (image_mono (inter_subset_right.trans hsub)
        (μ.support_coeffInChartAt_subset b γ (Function.mem_support.mpr hn)))
  exact (hfull α).symm.trans ((μ.coeffInChartAt_changeChart b α β Subset.rfl
    ((isOpen_extChartAt_source (I := I) β).measurableSet_image_extChartAt_source_inter (I := I) α)
    ν).1.trans (hfull β))

end CoeffInChartAt

section BundleContinuity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- On a chart target, `μ.inChartAt α z (finBasis ℝ E)` is the fiber coordinate of `μ` in the
preferred trivialization of `TauCeti.DensityBundle`. -/
theorem inChartAt_finBasis_eq_trivializationAt (μ : (x : M) → DensityBundle I M x) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    inChartAt (I := I) μ α z (finBasis ℝ E) = (trivializationAt ℝ (DensityBundle I M) α
      ⟨(extChartAt I α).symm z, μ ((extChartAt I α).symm z)⟩).2 := by
  rw [Density.trivializationAt_eq, Trivialization.density_apply, inChartAt_apply]
  exact congrArg _ (funext fun i ↦
    mfderivWithin_extChartAt_symm_apply_eq_trivializationAt_symm α hz (finBasis ℝ E i))

/-- A section of `TauCeti.DensityBundle` continuous on a chart source has continuous coordinate
expression on that chart's target, including at boundary and corner points. -/
theorem continuousOn_inChartAt_of_continuousOn_section {μ : (x : M) → DensityBundle I M x} {α : M}
    (hμ : ContinuousOn (fun x ↦ TotalSpace.mk' ℝ x (μ x)) (extChartAt I α).source) :
    ContinuousOn (inChartAt (I := I) μ α) (extChartAt I α).target := by
  let e := trivializationAt ℝ (DensityBundle I M) α
  have hmap : MapsTo (fun x ↦ TotalSpace.mk' ℝ x (μ x)) (extChartAt I α).source e.source := by
    intro x hx; rw [e.mem_source]; dsimp only [TotalSpace.mk', e]
    rw [Density.trivializationAt_eq, Trivialization.density_baseSet,
      TangentBundle.trivializationAt_baseSet]; simpa only [extChartAt_source] using hx
  refine ((finBasis ℝ E).continuous_density.comp_continuousOn
    ((((e.continuousOn.comp hμ hmap).snd).comp (continuousOn_extChartAt_symm α)
      (extChartAt I α).mapsTo_symm).congr fun _ hz ↦
        inChartAt_finBasis_eq_trivializationAt μ α hz)).congr fun z _ ↦ ?_
  simpa only [Function.comp_apply, Basis.densityEquiv_apply, Basis.densityEquiv_symm_apply] using
    ((finBasis ℝ E).densityEquiv.symm_apply_apply (inChartAt (I := I) μ α z)).symm

end BundleContinuity

end RoughDensity

namespace RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

/-- On a chart target, the coordinate expression of `φ.toDensity (Orientation.mk l)` on `b` equals
that of `φ` weighted by the model-basis sign and the source chart sign of `l`. -/
theorem inChartAt_toDensity_apply_basis (φ : RoughForm I M ℝ m)
    (l : Manifold.OrientationLift I M (Fin m)) (b : Basis (Fin m) ℝ E) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (φ.toDensity (Manifold.Orientation.mk l)).inChartAt α y b =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        (l.signAt α ((extChartAt I α).symm y) : ℝ) * φ.inChartAt α y b := by
  set x := (extChartAt I α).symm y
  have hx : x ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  let e : TangentSpace I x ≃ₗ[ℝ] E := (trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x
    (by rwa [TangentBundle.trivializationAt_baseSet])
  let b' : Basis (Fin m) ℝ (TangentSpace I x) := b.map e.symm
  have hb' : (b' : Fin m → TangentSpace I x) =
      fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i) :=
    funext fun i ↦ (mfderivWithin_extChartAt_symm_apply_eq_trivializationAt_symm α hy (b i)).symm
  have hsign : (Orientation.signBasis (l.orientationAt x) b' : ℝ) =
      (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α x : ℝ) := by
    have h₂ := l.mapOrientation_orientationAt hx; have hb'e : b'.map e = b := by ext; simp [b']
    rw [Trivialization.mapOrientation_apply] at h₂
    rw [← Orientation.signBasis_map (l.orientationAt x) b' e, hb'e, h₂,
      l.chartOrientation_eq_ite, l.signAt_of_mem hx]
    rcases Int.units_eq_one_or (l.sign α ⟨x, hx⟩) with hs | hs <;>
      simp [hs, Orientation.signBasis_neg]
  rw [RoughDensity.inChartAt_apply, RoughForm.inChartAt_apply, ← hb',
    φ.toDensity_apply_basis, Manifold.Orientation.orientationAt_mk, hsign]

/-- At every point of `E`, `coeffInChartAt` of `φ.toDensity (Orientation.mk l)` equals
`φ.signedInChartAt` weighted by the model-basis sign. -/
theorem coeffInChartAt_toDensity (φ : RoughForm I M ℝ m) (l : Manifold.OrientationLift I M (Fin m))
    (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (φ.toDensity (Manifold.Orientation.mk l)).coeffInChartAt b α y =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y := by
  classical by_cases hy : y ∈ (extChartAt I α).target
  · rw [RoughDensity.coeffInChartAt_apply_of_mem_target _ b α hy,
      φ.inChartAt_toDensity_apply_basis l b α hy, RoughForm.signedInChartAt_apply,
      dite_eq_left hy, mul_assoc]
  · rw [RoughDensity.coeffInChartAt_apply_of_notMem_target _ b α hy,
      RoughForm.signedInChartAt_apply, dite_eq_right hy, mul_zero]

end RoughForm

end TauCeti
