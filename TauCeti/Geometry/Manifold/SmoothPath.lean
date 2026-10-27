/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Connected.Clopen

/-!
# Smooth paths in a manifold

This file joins points of a manifold by globally `C^n` curves `γ : ℝ → M` parametrized by
`[0, 1]`, for every finite or infinite `n : ℕ∞`.

Two curves with a common endpoint are concatenated by `TauCeti.Manifold.smoothTrans`. Each curve
is reparametrized by Mathlib's `Real.smoothTransition`, so that the concatenation is stationary on
a neighbourhood of the joining time and therefore as regular as the two curves
(`ContMDiff.smoothTrans`). Near a point `x`, every point is joined to `x` by a `C^n` curve with
values in a prescribed neighbourhood of `x`: in the extended chart at `x` this is a reparametrized
segment, which stays in the model range because `range I` is convex
(`TauCeti.Manifold.eventually_exists_contMDiff_path`). Consequently any two points of a
preconnected manifold are joined by a `C^n` curve (`TauCeti.Manifold.exists_contMDiff_path`).

Such curves are what line integrals of differential forms are evaluated on: the concatenation is
used to compare line integrals along different curves with the same endpoints.

## Main declarations

* `TauCeti.Manifold.smoothTrans γ₁ γ₂`: the concatenation of `γ₁` and `γ₂`, stationary near the
  joining time `1 / 2`.
* `ContMDiff.smoothTrans`: the concatenation of `C^n` curves with a common
  endpoint is `C^n`.
* `TauCeti.Manifold.eventually_exists_contMDiff_path`: points close to `x` are joined to `x` by
  `C^n` curves inside any given neighbourhood of `x`.
* `TauCeti.Manifold.exists_contMDiff_path`: a preconnected `C^n` manifold is `C^n` path connected.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} {n : ℕ∞}

/-! ### Concatenation -/

/-- The concatenation of two curves `γ₁ γ₂ : ℝ → M`: on `[0, 1 / 2]` it runs along `γ₁` from
`γ₁ 0` to `γ₁ 1`, and on `[1 / 2, 1]` along `γ₂` from `γ₂ 0` to `γ₂ 1`. Both curves are
reparametrized by `Real.smoothTransition`, so that the concatenation is stationary on
`[1 / 3, 2 / 3]`. When `γ₁ 1 = γ₂ 0` it is as regular as the two curves
(`ContMDiff.smoothTrans`). -/
def smoothTrans (γ₁ γ₂ : ℝ → M) : ℝ → M :=
  (Iic (1 / 2 : ℝ)).piecewise (fun t ↦ γ₁ (Real.smoothTransition (6 * t - 1)))
    fun t ↦ γ₂ (Real.smoothTransition (6 * t - 4))

variable {γ₁ γ₂ : ℝ → M}

/-- The concatenation starts at the starting point of the first curve. -/
@[simp]
theorem smoothTrans_zero : smoothTrans γ₁ γ₂ 0 = γ₁ 0 := by
  rw [smoothTrans, piecewise_eq_of_mem _ _ _ (by norm_num : (0 : ℝ) ∈ Iic (1 / 2)),
    Real.smoothTransition.zero_of_nonpos (by norm_num)]

/-- The concatenation ends at the endpoint of the second curve. -/
@[simp]
theorem smoothTrans_one : smoothTrans γ₁ γ₂ 1 = γ₂ 1 := by
  rw [smoothTrans, piecewise_eq_of_notMem _ _ _ (by norm_num : (1 : ℝ) ∉ Iic (1 / 2)),
    Real.smoothTransition.one_of_one_le (by norm_num)]

/-- Before time `2 / 3`, the concatenation of two curves with a common endpoint is the
reparametrized first curve. -/
theorem smoothTrans_eqOn_left (h : γ₁ 1 = γ₂ 0) :
    EqOn (smoothTrans γ₁ γ₂) (fun t ↦ γ₁ (Real.smoothTransition (6 * t - 1))) (Iio (2 / 3)) := by
  intro t ht
  by_cases ht' : t ≤ 1 / 2
  · exact piecewise_eq_of_mem _ _ _ ht'
  rw [smoothTrans, piecewise_eq_of_notMem _ _ _ ht',
    Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.mp ht])]
  beta_reduce
  rw [Real.smoothTransition.one_of_one_le (by linarith), h]

/-- After time `1 / 3`, the concatenation of two curves with a common endpoint is the
reparametrized second curve. -/
theorem smoothTrans_eqOn_right (h : γ₁ 1 = γ₂ 0) :
    EqOn (smoothTrans γ₁ γ₂) (fun t ↦ γ₂ (Real.smoothTransition (6 * t - 4))) (Ioi (1 / 3)) := by
  intro t ht
  by_cases ht' : t ≤ 1 / 2
  · rw [smoothTrans, piecewise_eq_of_mem _ _ _ ht',
      Real.smoothTransition.one_of_one_le (by linarith [mem_Ioi.mp ht])]
    beta_reduce
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), h]
  · exact piecewise_eq_of_notMem _ _ _ ht'

variable [TopologicalSpace M] [ChartedSpace H M]

/-- A `C^n` curve reparametrized by an affine change of parameter followed by
`Real.smoothTransition` is `C^n`. -/
private theorem contMDiff_comp_smoothTransition {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (c : ℝ) : ContMDiff 𝓘(ℝ, ℝ) I n fun t ↦ γ (Real.smoothTransition (6 * t - c)) := by
  refine hγ.comp (contMDiff_iff_contDiff.mpr ?_)
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The concatenation of two `C^n` curves with a common endpoint is `C^n`. -/
theorem _root_.ContMDiff.smoothTrans (h₁ : ContMDiff 𝓘(ℝ, ℝ) I n γ₁)
    (h₂ : ContMDiff 𝓘(ℝ, ℝ) I n γ₂) (h : γ₁ 1 = γ₂ 0) :
    ContMDiff 𝓘(ℝ, ℝ) I n (TauCeti.Manifold.smoothTrans γ₁ γ₂) := by
  refine (contMDiff_comp_smoothTransition h₁ 1).piecewise_Iic
    (contMDiff_comp_smoothTransition h₂ 4) ?_
  -- near the joining time both pieces equal the common endpoint
  have hmem : Ioo (1 / 3 : ℝ) (2 / 3) ∈ 𝓝 (1 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hmem] with t ht
  exact ((smoothTrans_eqOn_left h ht.2).symm.trans (smoothTrans_eqOn_right h ht.1) :)

/-! ### Existence of smooth paths -/

/-- Every point `y` close enough to `x` is joined to `x` by a `C^n` curve with values in a given
neighbourhood `U` of `x`. The curve is a reparametrized segment in the extended chart at `x`; the
manifold may have boundary or corners. -/
theorem eventually_exists_contMDiff_path [IsManifold I n M] {x : M} {U : Set M} (hU : U ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t, γ t ∈ U := by
  set e := extChartAt I x
  -- a ball about the chart point, intersected with the model range, lies in the chart target and
  -- maps into `U`
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, Metric.ball (e x) ε ∩ range I ⊆ e.target ∩ e.symm ⁻¹' U := by
    rw [← Metric.mem_nhdsWithin_iff]
    refine inter_mem (extChartAt_target_mem_nhdsWithin x) ?_
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) x] at hU
    exact hU
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds (e x) hε)] with y hys hyb
  have hconv : Convex ℝ (Metric.ball (e x) ε ∩ range I) := (convex_ball _ _).inter I.convex_range
  have hx : e x ∈ Metric.ball (e x) ε ∩ range I := ⟨Metric.mem_ball_self hε, mem_range_self _⟩
  have hy : e y ∈ Metric.ball (e x) ε ∩ range I := ⟨hyb, mem_range_self _⟩
  -- the reparametrized segment from `e x` to `e y`
  set c : ℝ → E := fun t ↦ e x + Real.smoothTransition t • (e y - e x)
  have hc (t : ℝ) : c t ∈ Metric.ball (e x) ε ∩ range I :=
    hconv.add_smul_sub_mem hx hy ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hcd : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n c :=
    contMDiff_iff_contDiff.mpr (contDiff_const.add (Real.smoothTransition.contDiff.smul
      contDiff_const))
  refine ⟨e.symm ∘ c, (contMDiffOn_extChartAt_symm x).comp_contMDiff hcd fun t ↦ (hsub (hc t)).1,
    ?_, ?_, fun t ↦ (hsub (hc t)).2⟩
  · simp only [Function.comp_apply, c, Real.smoothTransition.zero, zero_smul, add_zero]
    exact e.left_inv (mem_extChartAt_source x)
  · simp only [Function.comp_apply, c, Real.smoothTransition.one, one_smul, add_sub_cancel]
    exact e.left_inv hys

/-- **Smooth path connectedness.** Any two points of a preconnected `C^n` manifold are joined by a
`C^n` curve parametrized by `[0, 1]`. The manifold may have boundary or corners. -/
theorem exists_contMDiff_path [IsManifold I n M] [PreconnectedSpace M] (x y : M) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ γ 0 = x ∧ γ 1 = y := by
  refine PreconnectedSpace.induction₂' (fun x y ↦ ∃ γ : ℝ → M,
    ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ γ 0 = x ∧ γ 1 = y) (fun x ↦ ?_) ⟨fun x y z ↦ ?_⟩ x y
  · filter_upwards [eventually_exists_contMDiff_path (n := n) (I := I) univ_mem]
      with y hy
    obtain ⟨γ, hγ, hγ0, hγ1, -⟩ := hy
    -- the reversed curve joins `y` to `x`
    refine ⟨⟨γ, hγ, hγ0, hγ1⟩, fun t ↦ γ (1 - t), ?_, by simpa using hγ1, by simpa using hγ0⟩
    exact hγ.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
  · rintro ⟨γ₁, h₁, h₁0, h₁1⟩ ⟨γ₂, h₂, h₂0, h₂1⟩
    exact ⟨smoothTrans γ₁ γ₂, h₁.smoothTrans h₂ (h₁1.trans h₂0.symm), by simp [h₁0],
      by simp [h₂1]⟩

end TauCeti.Manifold
