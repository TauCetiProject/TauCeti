/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Length.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Smooth dependence of the length of regular curves

For a family jointly `C^(n+1)` along `{w₀} × [a, b]` whose central curve has nonzero
velocity, its real-valued length is `C^n` at `w₀` when the metric is `C^n`.
This includes smooth dependence on any normed-space parameter and supplies the length
regularity used in smooth upper distance barriers in comparison geometry.
No completeness assumption is needed.
-/

public noncomputable section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {C : P → ℝ → M} {w₀ : P}

/-- If `C` is jointly `C^(n+1)` along `{w₀} × [a, b]` and `C w₀` has nonzero velocity there,
then `w ↦ (pathELength I (C w) a b).toReal` is `C^n` at `w₀` for a `C^n` metric.
The order `n = ∞` gives smoothness at `w₀`. -/
theorem contDiffAt_toReal_pathELength_of_curveVelocity_ne_zero {n : ℕ∞}
    [IsManifold I 1 M] [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] {a b : ℝ}
    (hC : ∀ t ∈ Icc a b,
      ContMDiffAt 𝓘(ℝ, P × ℝ) I (n + 1) (fun z : P × ℝ ↦ C z.1 z.2) (w₀, t))
    (hv : ∀ t ∈ Icc a b, curveVelocity I (C w₀) t ≠ 0) :
    ContDiffAt ℝ n (fun w ↦ (Manifold.pathELength I (C w) a b).toReal) w₀ := by
  by_cases hab : a ≤ b
  swap
  · simpa only [pathELength_eq_zero_of_le (le_of_not_ge hab), ENNReal.toReal_zero] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : P ↦ (0 : ℝ)) w₀)
  rw [← contDiffWithinAt_univ]
  refine contDiffWithinAt_iff_forall_nat_le.2 fun k hk ↦ ?_
  have hk' : (k : ℕ∞ω) ≤ (n : ℕ∞ω) := by exact_mod_cast hk
  have hkn : (k : ℕ∞ω) + 1 ≤ (n : ℕ∞ω) + 1 := by gcongr
  have : IsManifold I ((k : ℕ∞ω) + 1) M := IsManifold.of_le hkn
  have : IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := n) (by exact_mod_cast hk)
  obtain ⟨W, hWo, hW, hspeed, heq⟩ :=
    exists_isOpen_contDiffOn_norm_curveVelocity (m := k) (n := (k : ℕ∞ω) + 1)
      le_rfl (by simp) hab (fun t ht ↦ (hC t ht).of_le hkn) hv
  obtain ⟨U, V, hUo, _, hwU, hV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hWo hW
  have hint : ContDiffOn ℝ k (fun w ↦ ∫ t in a..b, ‖curveVelocity I (C w) t‖) U :=
    ContDiffOn.parametric_intervalIntegral hUo
      (hspeed.mono ((prod_mono_right hV).trans hUV))
  exact ((hint.contDiffAt (hUo.mem_nhds (hwU rfl))).congr_of_eventuallyEq heq).contDiffWithinAt

end TauCeti.Manifold
