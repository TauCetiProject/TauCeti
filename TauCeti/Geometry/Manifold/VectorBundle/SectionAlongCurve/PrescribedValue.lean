/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Sections along a curve with a prescribed interior value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth
manifold, and let `γ` be a curve which is `C^n` on a parameter set `s`. For `a < c < b`, every
vector `v` of the fibre of `V` at `γ c` is the value at `c` of a section along `γ` which is `C^n`
on `s` and vanishes at `a` and `b`: extend `v` to a global `C^n` section with
`FiberBundle.exists_contMDiff_section_eq`, restrict it to `γ`, and multiply by a smooth bump
function around `c` supported in `(a, b)`. The model fibre need not be finite-dimensional.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- For `a < c < b`, every vector of `V` at `γ c` is the value at `c` of a section along `γ`
which vanishes at `a` and `b` and is `C^n` on a given parameter set on which `γ` is `C^n`. -/
theorem exists_contMDiffOn_sectionAlong_eq_zero_endpoints {n : ℕ∞}
    [ContMDiffVectorBundle n F V I] {γ : ℝ → M} {s : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ s) {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (v : V (γ c)) :
    ∃ W : ∀ t, V (γ t),
      ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F)) n (fun t ↦ TotalSpace.mk' F (γ t) (W t)) s ∧
        W a = 0 ∧ W b = 0 ∧ W c = v := by
  obtain ⟨X, hX, hXc⟩ := FiberBundle.exists_contMDiff_section_eq I F n v
  let δ := min (c - a) (b - c) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let φ : ContDiffBump c := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hφa : φ a = 0 := φ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hac)]
    dsimp only [φ, δ]
    linarith [min_le_left (c - a) (b - c)])
  have hφb : φ b = 0 := φ.zero_of_le_dist (by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hcb)]
    dsimp only [φ, δ]
    linarith [min_le_right (c - a) (b - c)])
  refine ⟨fun t ↦ φ t • X (γ t),
    (φ.contDiff (n := n)).contMDiff.contMDiffOn.smul_totalSpace (hX.comp_contMDiffOn hγ), ?_, ?_,
    ?_⟩
  · simp only [hφa, zero_smul]
  · simp only [hφb, zero_smul]
  · simp only [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_smul, hXc]

end TauCeti.Manifold
