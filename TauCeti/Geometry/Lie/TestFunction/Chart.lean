/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.ExtendByZero
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Test functions in a chart

This file compares the test functions `LieTestFunction I G` on a manifold with Mathlib's
Euclidean test functions `TestFunction`, through a chart.

Composition with a diffeomorphism `Φ : M ≃ₘ⟮I, J⟯ N` identifies the test functions on `N` with
those on `M`. An open subset `Ω` of a normed space `E` is a manifold modelled on `𝓘(ℝ, E)`, and
extension by zero identifies its test functions with Mathlib's `𝓓(Ω, ℂ)`. For a manifold `G`
modelled on a boundaryless `I`, the extended chart at `x` is a diffeomorphism from the chart
domain `chartSource H x` onto the open set `chartTarget I x` of `E`; composing the two
identifications gives the chart comparison `chartEquiv I x` between test functions on the chart
domain and Mathlib's test functions on its image. With `LieTestFunction.restrict` and
`LieTestFunction.extendByZero` this compares a test function on `G` supported in a chart domain
with a Euclidean test function.

## Main definitions

* `TauCeti.LieTestFunction.compDiffeomorph Φ`: the linear equivalence `a ↦ a ∘ Φ`.
* `TauCeti.LieTestFunction.equivTestFunction Ω`: test functions on the open subset `Ω` of `E`,
  as a manifold, are Mathlib's `𝓓(Ω, ℂ)`.
* `TauCeti.LieTestFunction.chartSource H x`, `chartTarget I x`: the chart domain at `x` and its
  image under the extended chart, as open sets.
* `TauCeti.LieTestFunction.chartDiffeomorph I x`: the extended chart at `x` as a diffeomorphism
  between them.
* `TauCeti.LieTestFunction.chartEquiv I x`: test functions on the chart domain at `x` are
  Mathlib's test functions on its image, by composition with the inverse chart.
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold Distributions

namespace TauCeti

namespace LieTestFunction

section Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- Composition of test functions with a diffeomorphism `Φ : M → N`, `a ↦ a ∘ Φ`. -/
def compDiffeomorph (Φ : M ≃ₘ⟮I, J⟯ N) : LieTestFunction J N ≃ₗ[ℂ] LieTestFunction I M where
  toFun a := ⟨a ∘ Φ, a.contMDiff.comp Φ.contMDiff,
    a.hasCompactSupport.comp_homeomorph Φ.toHomeomorph⟩
  invFun a := ⟨a ∘ Φ.symm, a.contMDiff.comp Φ.symm.contMDiff,
    a.hasCompactSupport.comp_homeomorph Φ.symm.toHomeomorph⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := ext fun x ↦ congr_arg a (Φ.apply_symm_apply x)
  right_inv a := ext fun x ↦ congr_arg a (Φ.symm_apply_apply x)

@[simp]
theorem compDiffeomorph_apply (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction J N) (x : M) :
    compDiffeomorph Φ a x = a (Φ x) :=
  (rfl)

@[simp]
theorem compDiffeomorph_symm_apply (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction I M) (y : N) :
    (compDiffeomorph Φ).symm a y = a (Φ.symm y) :=
  (rfl)

end Diffeomorph

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Opens E)

/-- A Euclidean test function, as a test function on the normed space `E` as a manifold. -/
private def ofTestFunction (φ : 𝓓(Ω, ℂ)) : LieTestFunction 𝓘(ℝ, E) E :=
  ⟨φ, φ.contDiff.contMDiff, φ.hasCompactSupport⟩

/-- Test functions on an open subset `Ω` of a normed space `E`, with its manifold structure
modelled on `𝓘(ℝ, E)`, are Mathlib's test functions `𝓓(Ω, ℂ)`: a test function on `Ω` is sent to
its extension by zero to `E`. -/
def equivTestFunction : LieTestFunction 𝓘(ℝ, E) Ω ≃ₗ[ℂ] 𝓓(Ω, ℂ) where
  toFun a := ⟨extendByZero Ω a, contMDiff_iff_contDiff.1 (extendByZero Ω a).contMDiff,
    (extendByZero Ω a).hasCompactSupport, tsupport_extendByZero_subset Ω a⟩
  invFun φ := restrict (ofTestFunction Ω φ) φ.tsupport_subset
  map_add' a b := TestFunction.ext fun y ↦ congr($(map_add (extendByZero Ω) a b) y)
  map_smul' c a := TestFunction.ext fun y ↦ congr($(map_smul (extendByZero Ω) c a) y)
  left_inv a := restrict_extendByZero a
  right_inv φ := TestFunction.ext fun y ↦
    congr($(extendByZero_restrict (ofTestFunction Ω φ) φ.tsupport_subset) y)

@[simp]
theorem equivTestFunction_apply_coe (a : LieTestFunction 𝓘(ℝ, E) Ω) (y : Ω) :
    equivTestFunction Ω a y = a y :=
  extendByZero_apply_coe Ω a y

theorem equivTestFunction_apply_of_notMem (a : LieTestFunction 𝓘(ℝ, E) Ω) {y : E}
    (hy : y ∉ Ω) : equivTestFunction Ω a y = 0 :=
  extendByZero_apply_of_notMem Ω a hy

@[simp]
theorem equivTestFunction_symm_apply (φ : 𝓓(Ω, ℂ)) (y : Ω) :
    (equivTestFunction Ω).symm φ y = φ y :=
  (restrict_apply _ _ y).trans rfl

end Euclidean

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

variable (H) in
/-- The domain of the preferred chart at `x`, as an open set. -/
def chartSource (x : G) : Opens G :=
  ⟨(chartAt H x).source, (chartAt H x).open_source⟩

@[simp]
theorem coe_chartSource (x : G) : (chartSource H x : Set G) = (chartAt H x).source :=
  (rfl)

@[simp]
theorem mem_chartSource {x g : G} : g ∈ chartSource H x ↔ g ∈ (chartAt H x).source :=
  Iff.rfl

/-- The image of the preferred chart at `x` under the model `I`, an open set of `E` for a
boundaryless model. -/
def chartTarget [I.Boundaryless] (x : G) : Opens E :=
  ⟨(extChartAt I x).target, isOpen_extChartAt_target x⟩

@[simp]
theorem coe_chartTarget [I.Boundaryless] (x : G) :
    (chartTarget I x : Set E) = (extChartAt I x).target :=
  (rfl)

variable {I} in
@[simp]
theorem mem_chartTarget [I.Boundaryless] {x : G} {y : E} :
    y ∈ chartTarget I x ↔ y ∈ (extChartAt I x).target :=
  Iff.rfl

variable [I.Boundaryless] [IsManifold I ∞ G]

/-- The extended chart at `x` maps the chart domain smoothly to its image. -/
private theorem contMDiff_extChartAt_restrict (x : G) :
    ContMDiff I 𝓘(ℝ, E) ∞ (fun u : chartSource H x ↦
      (⟨extChartAt I x u, (extChartAt I x).map_source
        (by simpa using mem_chartSource.1 u.property)⟩ :
        chartTarget I x)) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiffOn_extChartAt (x := x)).comp_contMDiff contMDiff_subtypeVal
    fun u ↦ mem_chartSource.1 u.property

/-- The inverse of the extended chart at `x` maps the image of the chart smoothly to the chart
domain. -/
private theorem contMDiff_extChartAt_symm_restrict (x : G) :
    ContMDiff 𝓘(ℝ, E) I ∞ (fun y : chartTarget I x ↦
      (⟨(extChartAt I x).symm y, by
        rw [mem_chartSource, ← extChartAt_source I]
        exact (extChartAt I x).map_target (mem_chartTarget.1 y.property)⟩ :
        chartSource H x)) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiffOn_extChartAt_symm x).comp_contMDiff contMDiff_subtypeVal
    fun y ↦ mem_chartTarget.1 y.property

/-- The extended chart at `x`, as a diffeomorphism from the chart domain onto its image in `E`. -/
def chartDiffeomorph (x : G) : chartSource H x ≃ₘ⟮I, 𝓘(ℝ, E)⟯ chartTarget I x where
  toFun u := ⟨extChartAt I x u, (extChartAt I x).map_source
    (by simpa using mem_chartSource.1 u.property)⟩
  invFun y := ⟨(extChartAt I x).symm y, by
    rw [mem_chartSource, ← extChartAt_source I]
    exact (extChartAt I x).map_target (mem_chartTarget.1 y.property)⟩
  left_inv u := Subtype.ext ((extChartAt I x).left_inv
    (by simpa using mem_chartSource.1 u.property))
  right_inv y := Subtype.ext ((extChartAt I x).right_inv
    (mem_chartTarget.1 y.property))
  contMDiff_toFun := contMDiff_extChartAt_restrict I x
  contMDiff_invFun := contMDiff_extChartAt_symm_restrict I x

@[simp]
theorem coe_chartDiffeomorph_apply (x : G) (u : chartSource H x) :
    (chartDiffeomorph I x u : E) = extChartAt I x u :=
  (rfl)

@[simp]
theorem coe_chartDiffeomorph_symm_apply (x : G) (y : chartTarget I x) :
    ((chartDiffeomorph I x).symm y : G) = (extChartAt I x).symm y :=
  (rfl)

/-- The chart comparison at `x`: a test function on the chart domain at `x`, composed with the
inverse of the extended chart and extended by zero, is a Euclidean test function on the image of
the chart. A test function `a` on `G` with `tsupport a ⊆ (chartAt H x).source` is compared through
`chartEquiv I x (restrict a h)`, and a Euclidean test function `φ` gives the test function
`extendByZero _ ((chartEquiv I x).symm φ)` on `G`. -/
def chartEquiv (x : G) :
    LieTestFunction I (chartSource H x) ≃ₗ[ℂ] 𝓓(chartTarget I x, ℂ) :=
  (compDiffeomorph (chartDiffeomorph I x)).symm.trans (equivTestFunction _)

theorem chartEquiv_apply_of_mem (x : G) (a : LieTestFunction I (chartSource H x)) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartEquiv I x a y = a ((chartDiffeomorph I x).symm ⟨y, mem_chartTarget.2 hy⟩) :=
  equivTestFunction_apply_coe (chartTarget I x) _ ⟨y, mem_chartTarget.2 hy⟩

theorem chartEquiv_apply_of_notMem (x : G) (a : LieTestFunction I (chartSource H x)) {y : E}
    (hy : y ∉ (extChartAt I x).target) : chartEquiv I x a y = 0 :=
  equivTestFunction_apply_of_notMem (chartTarget I x) _ hy

@[simp]
theorem chartEquiv_symm_apply (x : G) (φ : 𝓓(chartTarget I x, ℂ)) (u : chartSource H x) :
    (chartEquiv I x).symm φ u = φ (extChartAt I x u) :=
  equivTestFunction_symm_apply _ φ (chartDiffeomorph I x u)

/-- A test function on `G` supported in the chart domain at `x`, read in the chart, at a point of
the chart image. -/
theorem chartEquiv_restrict_apply_of_mem (x : G) (a : LieTestFunction I G)
    (h : tsupport a ⊆ chartSource H x) {y : E} (hy : y ∈ (extChartAt I x).target) :
    chartEquiv I x (restrict a h) y = a ((extChartAt I x).symm y) :=
  (chartEquiv_apply_of_mem I x _ hy).trans (restrict_apply _ _ _)

/-- The test function on `G` given by a Euclidean test function in the chart at `x`, at a point
of the chart domain. -/
theorem extendByZero_chartEquiv_symm_apply_of_mem [T2Space G] (x : G)
    (φ : 𝓓(chartTarget I x, ℂ)) {g : G} (hg : g ∈ (chartAt H x).source) :
    extendByZero _ ((chartEquiv I x).symm φ) g = φ (extChartAt I x g) :=
  (extendByZero_apply_coe (chartSource H x) _ ⟨g, mem_chartSource.2 hg⟩).trans
    (chartEquiv_symm_apply I x φ _)

end Chart

end LieTestFunction

end TauCeti
