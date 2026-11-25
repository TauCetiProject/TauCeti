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
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas

/-!
# Test functions in a chart

This file compares the test functions `LieTestFunction I G` on a manifold with Mathlib's
Euclidean test functions `TestFunction`, through a chart.

Composition with a diffeomorphism `Φ : M ≃ₘ⟮I, J⟯ N` identifies the test functions on `N` with
those on `M`. An open subset `Ω` of a normed space `E` is a manifold modelled on `𝓘(ℝ, E)`, and
extension by zero identifies its test functions with Mathlib's `𝓓(Ω, ℂ)`. For a manifold `G`
modelled on a boundaryless `I`, the extended chart at `x` is a diffeomorphism from the chart
domain `chartSourceOpens H x` onto the open set `extChartTargetOpens I x` of `E`
(`TauCeti.extChartAtDiffeomorph`); composing the two
identifications gives the chart comparison `chartEquiv I x` between test functions on the chart
domain and Mathlib's test functions on its image. With `LieTestFunction.restrict` and
`LieTestFunction.extendByZero` this compares a test function on `G` supported in a chart domain
with a Euclidean test function.

## Main definitions

* `TauCeti.LieTestFunction.compDiffeomorph Φ`: the linear equivalence `a ↦ a ∘ Φ`.
* `TauCeti.LieTestFunction.equivTestFunction Ω`: test functions on the open subset `Ω` of `E`,
  as a manifold, are Mathlib's `𝓓(Ω, ℂ)`.
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

@[simp]
theorem support_compDiffeomorph (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction J N) :
    support (compDiffeomorph Φ a) = Φ ⁻¹' support a :=
  support_comp_eq_preimage a Φ

@[simp]
theorem tsupport_compDiffeomorph (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction J N) :
    tsupport (compDiffeomorph Φ a) = Φ ⁻¹' tsupport a :=
  tsupport_comp_eq_preimage a Φ.toHomeomorph

@[simp]
theorem support_compDiffeomorph_symm (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction I M) :
    support ((compDiffeomorph Φ).symm a) = Φ.symm ⁻¹' support a :=
  support_comp_eq_preimage a Φ.symm

@[simp]
theorem tsupport_compDiffeomorph_symm (Φ : M ≃ₘ⟮I, J⟯ N) (a : LieTestFunction I M) :
    tsupport ((compDiffeomorph Φ).symm a) = Φ.symm ⁻¹' tsupport a :=
  tsupport_comp_eq_preimage a Φ.symm.toHomeomorph

end Diffeomorph

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Opens E)

/-- A Euclidean test function, as a test function on the normed space `E` as a manifold. -/
private def ofTestFunction (φ : 𝓓(Ω, ℂ)) : LieTestFunction 𝓘(ℝ, E) E :=
  ⟨φ, φ.contDiff.contMDiff, φ.hasCompactSupport⟩

@[simp]
private theorem ofTestFunction_apply (φ : 𝓓(Ω, ℂ)) (y : E) : ofTestFunction Ω φ y = φ y :=
  (rfl)

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

/-- As a function on `E`, the test function `equivTestFunction Ω a` is the extension by zero of
`a`. -/
theorem coe_equivTestFunction (a : LieTestFunction 𝓘(ℝ, E) Ω) :
    ⇑(equivTestFunction Ω a) = ⇑(extendByZero Ω a) :=
  (rfl)

theorem equivTestFunction_apply_of_notMem (a : LieTestFunction 𝓘(ℝ, E) Ω) {y : E}
    (hy : y ∉ Ω) : equivTestFunction Ω a y = 0 :=
  extendByZero_apply_of_notMem Ω a hy

@[simp]
theorem equivTestFunction_symm_apply (φ : 𝓓(Ω, ℂ)) (y : Ω) :
    (equivTestFunction Ω).symm φ y = φ y :=
  (restrict_apply _ _ y).trans (ofTestFunction_apply Ω φ y)

end Euclidean

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

variable [I.Boundaryless] [IsManifold I ∞ G]

/-- The chart comparison at `x`: a test function on the chart domain at `x`, composed with the
inverse of the extended chart and extended by zero, is a Euclidean test function on the image of
the chart. A test function `a` on `G` with `tsupport a ⊆ (chartAt H x).source` is compared through
`chartEquiv I x (restrict a h)`, and a Euclidean test function `φ` gives the test function
`extendByZero _ ((chartEquiv I x).symm φ)` on `G`. -/
def chartEquiv (x : G) :
    LieTestFunction I (chartSourceOpens H x) ≃ₗ[ℂ] 𝓓(extChartTargetOpens I x, ℂ) :=
  (compDiffeomorph (extChartAtDiffeomorph (I := I) ∞ x)).symm.trans (equivTestFunction _)

@[simp]
theorem tsupport_chartEquiv (x : G) (a : LieTestFunction I (chartSourceOpens H x)) :
    tsupport (chartEquiv I x a) = extChartAt I x '' ((↑) '' tsupport a) := by
  rw [chartEquiv, LinearEquiv.trans_apply, coe_equivTestFunction, tsupport_extendByZero,
    tsupport_compDiffeomorph_symm, ← Diffeomorph.image_eq_preimage_symm, image_image,
    image_image]
  simp

theorem chartEquiv_apply_of_mem (x : G) (a : LieTestFunction I (chartSourceOpens H x)) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartEquiv I x a y =
      a ((extChartAtDiffeomorph (I := I) ∞ x).symm ⟨y, mem_extChartTargetOpens.2 hy⟩) :=
  equivTestFunction_apply_coe (extChartTargetOpens I x) _ ⟨y, mem_extChartTargetOpens.2 hy⟩

theorem chartEquiv_apply_of_notMem (x : G) (a : LieTestFunction I (chartSourceOpens H x)) {y : E}
    (hy : y ∉ (extChartAt I x).target) : chartEquiv I x a y = 0 :=
  equivTestFunction_apply_of_notMem (extChartTargetOpens I x) _ (mt mem_extChartTargetOpens.1 hy)

@[simp]
theorem chartEquiv_symm_apply (x : G) (φ : 𝓓(extChartTargetOpens I x, ℂ))
    (u : chartSourceOpens H x) :
    (chartEquiv I x).symm φ u = φ (extChartAt I x u) := by
  rw [← coe_extChartAtDiffeomorph_apply (n := ∞)]
  exact equivTestFunction_symm_apply _ φ (extChartAtDiffeomorph (I := I) ∞ x u)

/-- A test function on `G` supported in the chart domain at `x`, read in the chart, at a point of
the chart image. -/
theorem chartEquiv_restrict_apply_of_mem (x : G) (a : LieTestFunction I G)
    (h : tsupport a ⊆ chartSourceOpens H x) {y : E} (hy : y ∈ (extChartAt I x).target) :
    chartEquiv I x (restrict a h) y = a ((extChartAt I x).symm y) :=
  (chartEquiv_apply_of_mem I x _ hy).trans <| (restrict_apply _ _ _).trans <| by
    rw [coe_extChartAtDiffeomorph_symm_apply]

/-- The test function on `G` given by a Euclidean test function in the chart at `x`, at a point
of the chart domain. -/
theorem extendByZero_chartEquiv_symm_apply_of_mem [T2Space G] (x : G)
    (φ : 𝓓(extChartTargetOpens I x, ℂ)) {g : G} (hg : g ∈ (chartAt H x).source) :
    extendByZero _ ((chartEquiv I x).symm φ) g = φ (extChartAt I x g) :=
  (extendByZero_apply_coe (chartSourceOpens H x) _ ⟨g, mem_chartSourceOpens.2 hg⟩).trans
    (chartEquiv_symm_apply I x φ _)

end Chart

end LieTestFunction

end TauCeti
