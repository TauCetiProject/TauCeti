/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth curves joining points of a manifold

A connected `C^n` manifold is `C^n`-path connected: any two of its points are joined by a `C^n`
curve `γ : ℝ → M` which is constant on `(-∞, 0]` and on `[1, ∞)`
(`TauCeti.exists_contMDiff_curve`). This holds over every model with corners, so manifolds with
boundary or corners are included. Points close to `x` are joined to `x` by such curves staying in
any prescribed neighbourhood of `x` (`TauCeti.eventually_exists_contMDiff_curve`): in the chart
at `x`, follow the segment to the chart point of `y`, reparametrized by `Real.smoothTransition`.
Mathlib's `range I` is convex, so the segment stays in the model range.

Curves which are constant near their endpoints can be concatenated smoothly
(`TauCeti.curveConcat`, `ContMDiff.curveConcat`). The concatenation runs through `γ₁` on
`[0, 1/3]` and through `γ₂` on `[2/3, 1]`, and rests at the junction point in between, so that it
is locally a reparametrization of one of the two curves.

These curves are the test curves of line integrals: a closed `1`-form whose integral along every
smooth loop vanishes is exact, with primitive the integral along smooth curves from a base point.

## Main declarations

* `TauCeti.curveConcat`: the concatenation of two curves `ℝ → X`.
* `ContMDiff.curveConcat`: the concatenation of two `C^n` curves constant near the
  junction point is `C^n`.
* `TauCeti.eventually_exists_contMDiff_curve`: nearby points are joined by short `C^n` curves.
* `TauCeti.exists_contMDiff_curve`: a preconnected `C^n` manifold is `C^n`-path connected.
-/

public section

noncomputable section

open Set Filter Metric
open scoped Manifold Topology

namespace TauCeti

/-! ### Concatenation of curves -/

section Concat

variable {X : Type*}

/-- The concatenation of two curves `γ₁ γ₂ : ℝ → X`: it is `γ₁ (3 * t)` for `t ≤ 1/2` and
`γ₂ (3 * t - 2)` for `t > 1/2`. On `[0, 1]` it runs through `γ₁` on `[0, 1]` and then through `γ₂`
on `[0, 1]`. When `γ₁` is constant on `[1, ∞)` and `γ₂` on `(-∞, 0]` with the same value, it rests
at that point on `[1/3, 2/3]`, so near every parameter it agrees with a reparametrization of `γ₁`
or of `γ₂` (`TauCeti.eqOn_curveConcat_left`, `TauCeti.eqOn_curveConcat_right`). -/
def curveConcat (γ₁ γ₂ : ℝ → X) (t : ℝ) : X :=
  if t ≤ 1 / 2 then γ₁ (3 * t) else γ₂ (3 * t - 2)

variable {γ₁ γ₂ : ℝ → X} {t : ℝ}

theorem curveConcat_of_le (ht : t ≤ 1 / 2) : curveConcat γ₁ γ₂ t = γ₁ (3 * t) := by
  simp only [curveConcat, ht, ↓reduceIte]

theorem curveConcat_of_lt (ht : 1 / 2 < t) : curveConcat γ₁ γ₂ t = γ₂ (3 * t - 2) := by
  simp only [curveConcat, ht.not_ge, ↓reduceIte]

variable {y : X}

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation agrees with `γ₁` at triple speed before time `2/3`. -/
theorem eqOn_curveConcat_left (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    EqOn (curveConcat γ₁ γ₂) (fun t ↦ γ₁ (3 * t)) (Iio (2 / 3)) := by
  intro t ht
  rcases le_or_gt t (1 / 2) with h | h
  · exact curveConcat_of_le h
  · rw [curveConcat_of_lt h]
    exact (h₂ _ (by linarith [mem_Iio.mp ht])).trans (h₁ _ (by linarith)).symm

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation agrees with `γ₂` at triple speed, shifted, after time `1/3`. -/
theorem eqOn_curveConcat_right (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    EqOn (curveConcat γ₁ γ₂) (fun t ↦ γ₂ (3 * t - 2)) (Ioi (1 / 3)) := by
  intro t ht
  rcases le_or_gt t (1 / 2) with h | h
  · rw [curveConcat_of_le h]
    exact (h₁ _ (by linarith [mem_Ioi.mp ht])).trans (h₂ _ (by linarith)).symm
  · exact curveConcat_of_lt h

/-- If `γ₁` rests at `y` from time `1` on and `γ₂` rests at `y` up to time `0`, then the
concatenation rests at `y` between times `1/3` and `2/3`. -/
theorem curveConcat_eq_of_mem_Icc (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y)
    (ht : t ∈ Icc (1 / 3) (2 / 3)) : curveConcat γ₁ γ₂ t = y := by
  rcases le_or_gt t (1 / 2) with h | h
  · rw [curveConcat_of_le h, h₁ _ (by linarith [ht.1])]
  · rw [curveConcat_of_lt h, h₂ _ (by linarith [ht.2])]

end Concat

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The concatenation of two `C^n` curves, the first resting at `y` from time `1` on and the
second resting at `y` up to time `0`, is `C^n`. -/
theorem _root_.ContMDiff.curveConcat {n : WithTop ℕ∞} {γ₁ γ₂ : ℝ → M} {y : M}
    (hγ₁ : ContMDiff 𝓘(ℝ, ℝ) I n γ₁) (hγ₂ : ContMDiff 𝓘(ℝ, ℝ) I n γ₂)
    (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    ContMDiff 𝓘(ℝ, ℝ) I n (TauCeti.curveConcat γ₁ γ₂) := by
  intro t
  rcases lt_or_ge t (2 / 3) with ht | ht
  · have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 3 * s :=
      (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 3 * s).contMDiff
    exact ((hγ₁.comp hs) t).congr_of_eventuallyEq
      ((eqOn_curveConcat_left h₁ h₂).eventuallyEq_of_mem (Iio_mem_nhds ht))
  · have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 3 * s - 2 :=
      (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 3 * s - 2).contMDiff
    exact ((hγ₂.comp hs) t).congr_of_eventuallyEq
      ((eqOn_curveConcat_right h₁ h₂).eventuallyEq_of_mem (Ioi_mem_nhds (by linarith)))

/-! ### Smooth path connectivity -/

variable {n : ℕ∞}

/-- Points close to `x` are joined to `x` by `C^n` curves staying in a prescribed neighbourhood
`U` of `x`, which are constant on `(-∞, 0]` and on `[1, ∞)`. -/
theorem eventually_exists_contMDiff_curve [IsManifold I n M] {x : M} {U : Set M} (hU : U ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧
      (∀ t, 1 ≤ t → γ t = y) ∧ ∀ t, γ t ∈ U := by
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, ball (extChartAt I x x) ε ∩ range I ⊆
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U := by
    rw [← Metric.mem_nhdsWithin_iff]
    refine inter_mem (extChartAt_target_mem_nhdsWithin x) ?_
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) x] at hU
    exact hU
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds (ball_mem_nhds _ hε)]
    with y hys hyb
  -- In the chart at `x`, follow the segment from the chart point of `x` to that of `y`.
  set c : ℝ → E := fun t ↦ extChartAt I x x +
    Real.smoothTransition t • (extChartAt I x y - extChartAt I x x) with hc_def
  have hmem (t : ℝ) : c t ∈ ball (extChartAt I x x) ε ∩ range I :=
    ((convex_ball _ _).inter I.convex_range).add_smul_sub_mem
      ⟨mem_ball_self hε, extChartAt_target_subset_range x (mem_extChartAt_target x)⟩
      ⟨hyb, extChartAt_target_subset_range x ((extChartAt I x).map_source hys)⟩
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) n c :=
    (contDiff_const.add (Real.smoothTransition.contDiff.smul contDiff_const)).contMDiff
  refine ⟨(extChartAt I x).symm ∘ c,
    (contMDiffOn_extChartAt_symm x).comp_contMDiff hc fun t ↦ (hsub (hmem t)).1,
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ (hsub (hmem t)).2⟩
  · simp [hc_def, Real.smoothTransition.zero_of_nonpos ht]
  · have hys' : y ∈ (chartAt H x).source := by rwa [← extChartAt_source (I := I)]
    simp [hc_def, Real.smoothTransition.one_of_one_le ht, (chartAt H x).left_inv hys']

/-- **Smooth path connectivity.** In a preconnected `C^n` manifold, any two points are joined by a
`C^n` curve `γ : ℝ → M` which is constant on `(-∞, 0]` and on `[1, ∞)`. -/
theorem exists_contMDiff_curve [IsManifold I n M] [PreconnectedSpace M] (x y : M) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧ ∀ t, 1 ≤ t → γ t = y := by
  refine PreconnectedSpace.induction₂'
    (fun x y ↦ ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ (∀ t ≤ 0, γ t = x) ∧
      ∀ t, 1 ≤ t → γ t = y) (fun x ↦ ?_) ⟨fun x y z ⟨γ₁, hγ₁, h₁, h₁'⟩ ⟨γ₂, hγ₂, h₂, h₂'⟩ ↦ ?_⟩ x y
  · filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := n) (x := x) univ_mem]
      with y hy
    obtain ⟨γ, hγ, h₀, h₁, -⟩ := hy
    have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n fun s : ℝ ↦ 1 - s :=
      (by fun_prop : ContDiff ℝ n fun s : ℝ ↦ 1 - s).contMDiff
    exact ⟨⟨γ, hγ, h₀, h₁⟩, γ ∘ fun s ↦ 1 - s, hγ.comp hs,
      fun t ht ↦ h₁ _ (by linarith), fun t ht ↦ h₀ _ (by linarith)⟩
  · refine ⟨curveConcat γ₁ γ₂, ContMDiff.curveConcat hγ₁ hγ₂ h₁' h₂, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · rw [curveConcat_of_le (by linarith), h₁ _ (by linarith)]
    · rw [curveConcat_of_lt (by linarith), h₂' _ (by linarith)]

end TauCeti
