/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Test functions on `ℂ` restricted to the real axis

Let `Ω ⊆ ℂ` be open, `V` a real inner product space and `Λ ⊆ V` a real subspace. Boundary
conditions along the real axis are tested weakly against the test functions `φ ∈ 𝓓(Ω, V)` whose
values on `ℝ` lie in `Λ`, through the boundary integrals `∫_ℝ ⟪φ(s), w(s)⟫ ds`. This file proves
the fundamental lemma for these pairings: a field `w` continuous on `ℝ ∩ Ω` all of whose boundary
pairings vanish is pointwise orthogonal to `Λ` on `ℝ ∩ Ω`
(`TauCeti.mem_orthogonal_of_forall_integral_ofReal_inner_eq_zero`).
-/

public section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Ω : Opens ℂ}
  {Λ : Submodule ℝ V}

/-- The **fundamental lemma along the real axis** for test functions with boundary values in `Λ`:
if `w` is continuous on `ℝ ∩ Ω` and `∫_ℝ ⟪φ(s), w(s)⟫ ds = 0` for every `φ ∈ 𝓓(Ω, V)` with values
in `Λ` on `ℝ`, then `w(s) ∈ Λᗮ` for every real `s ∈ Ω`. If `⟪v, w(s₀)⟫ ≠ 0` for some `v ∈ Λ`,
test against a bump `ψ ⟪v, w(s₀)⟫ v` around `s₀`. -/
theorem mem_orthogonal_of_forall_integral_ofReal_inner_eq_zero {w : ℝ → V}
    (hw : ContinuousOn w (((↑) : ℝ → ℂ) ⁻¹' Ω))
    (h : ∀ φ : 𝓓(Ω, V), (∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) → ∫ s : ℝ, ⟪(φ : ℂ → V) s, w s⟫_ℝ = 0)
    {s₀ : ℝ} (hs₀ : (s₀ : ℂ) ∈ Ω) : w s₀ ∈ Λᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 fun v hv => ?_
  set g : ℝ → ℝ := fun s => ⟪v, w s⟫_ℝ
  have hO : IsOpen (((↑) : ℝ → ℂ) ⁻¹' Ω) := Ω.isOpen.preimage continuous_ofReal
  have hg : ContinuousOn g (((↑) : ℝ → ℂ) ⁻¹' Ω) := continuousOn_const.inner hw
  by_contra hc
  have hpos : ∀ᶠ z in 𝓝 (s₀ : ℂ), 0 < g s₀ * g z.re :=
    (continuousAt_const.mul ((hg.continuousAt (hO.mem_nhds hs₀)).comp_of_eq
      continuous_re.continuousAt (ofReal_re s₀))).eventually (lt_mem_nhds (mul_self_pos.2 hc))
  obtain ⟨ψ, hψΩ, hψc, hψ, hψr, hψ1⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (inter_mem (Ω.isOpen.mem_nhds hs₀) hpos)
  let φ : 𝓓(Ω, V) := ⟨fun z => ψ z • g s₀ • v, hψ.smul contDiff_const, hψc.smul_right,
    (tsupport_smul_subset_left _ _).trans (hψΩ.trans inter_subset_left)⟩
  have hF (s : ℝ) : ⟪(φ : ℂ → V) s, w s⟫_ℝ = ψ s * (g s₀ * g s) := by
    simp only [φ, TestFunction.coe_mk, real_inner_smul_left, g]
  have hB := h φ fun s => Λ.smul_mem _ (Λ.smul_mem _ hv)
  simp_rw [hF] at hB
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (continuous_of_tsupport fun s hs => ?_)
    (hψc.comp_isClosedEmbedding isometry_ofReal.isClosedEmbedding).mul_right
    (fun s => ?_) (x := s₀) ?_).ne' hB
  · have hsΩ : s ∈ ((↑) : ℝ → ℂ) ⁻¹' Ω := (hψΩ (tsupport_comp_subset_preimage ψ
      continuous_ofReal (tsupport_mul_subset_left hs))).1
    exact (hψ.continuous.comp continuous_ofReal).continuousAt.mul
      (continuousAt_const.mul (hg.continuousAt (hO.mem_nhds hsΩ)))
  · rw [Pi.zero_apply]
    by_cases hs : ψ s = 0
    · simp [hs]
    · exact mul_nonneg (hψr (mem_range_self _)).1 (le_of_lt (hψΩ (subset_tsupport _ hs)).2)
  · simpa [hψ1, g] using hc

end TauCeti
