/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Topology.Instances.AddCircle.Lift

/-!
# Lifts of circle diffeomorphisms and of circle-valued homotopies

Every `C^n` diffeomorphism `φ` of the circle `AddCircle T`, `n ≠ 0`, has a `C^n` lift
`F : ℝ → ℝ`, `φ x = F x`, with either `F (x + T) = F x + T` and `F' > 0` (the
orientation-preserving case) or `F (x + T) = F x - T` and `F' < 0` (the orientation-reversing
case). A continuous lift exists by `AddCircle.exists_continuous_lift`, and it is `C^n` by
`AddCircle.contDiff_of_comp_coe_eq`. A lift `G` of `φ⁻¹` satisfies `G ∘ F = id + c`
(`Homeomorph.exists_addCircle_lift_symm_comp_eq_add`), so `G' (F x) F' x = 1` and `F'` never
vanishes, while the lift of a homeomorphism is monotone of degree one or antitone of degree `-1`
(`AddCircle.strictMono_or_strictAnti_of_lift`).

The projection `ℝ → AddCircle T` is a covering map and a smooth local diffeomorphism, so smooth
circle-valued homotopies lift smoothly as well. A `C^n` map `g : [0, 1] × M → AddCircle T` whose
restriction to time zero lifts to a continuous `f : M → ℝ` has a `C^n` lift `G` with
`G (0, x) = f x` (`AddCircle.exists_contMDiff_lift_unitInterval_prod`): Mathlib's homotopy lifting
for covering maps (`IsCoveringMap.liftHomotopy`) gives a continuous lift, and a continuous lift of
a `C^n` map through a `C^n` local diffeomorphism is `C^n`.

Near `0` the projection `ℝ → AddCircle T` also has a smooth section defined on the whole circle
(`AddCircle.exists_contMDiff_coe_eq_of_norm_lt`): the chart at `0`, cut off by a smooth bump
function.

## Main declarations

* `AddCircle.deriv_pos_or_deriv_neg_of_lift`: a continuous lift of a `C^n` diffeomorphism of the
  circle, `n ≠ 0`, has degree one and positive derivative, or degree `-1` and negative derivative.
* `Diffeomorph.exists_addCircle_lift`: every `C^n` diffeomorphism of the circle, `n ≠ 0`, has a
  `C^n` lift of one of these two kinds.
* `AddCircle.exists_contMDiff_lift_unitInterval_prod`: smooth homotopy lifting for the circle.
* `AddCircle.exists_contMDiff_coe_eq_of_norm_lt`: a smooth real function on the circle which is
  a section of the projection `ℝ → AddCircle T` near `0`.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.1, for lifts of circle
  homeomorphisms.
* A. Hatcher, *Algebraic Topology*, Proposition 1.30, for the homotopy lifting property of
  covering maps.
-/

public section

open scoped Manifold ContDiff Topology

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)] {n : ℕ∞ω} {F : ℝ → ℝ}

/-- **Lifts of circle diffeomorphisms.** A continuous lift `F` of a `C^n` diffeomorphism `φ` of
`AddCircle T`, `n ≠ 0`, either satisfies `F (x + T) = F x + T` and has positive derivative (the
orientation-preserving case), or satisfies `F (x + T) = F x - T` and has negative derivative (the
orientation-reversing case). Such a lift is `C^n` by `AddCircle.contDiff_of_comp_coe_eq`. -/
theorem deriv_pos_or_deriv_neg_of_lift {φ : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T}
    (hn : n ≠ 0) (hF : Continuous F) (hφ : ∀ x : ℝ, φ x = F x) :
    ((∀ x, F (x + T) = F x + T) ∧ ∀ x, 0 < deriv F x) ∨
      ((∀ x, F (x + T) = F x - T) ∧ ∀ x, deriv F x < 0) := by
  have hFs : ContDiff ℝ n F := contDiff_of_comp_coe_eq (funext hφ) hF φ.contMDiff
  obtain ⟨G, c, hG, hψ, hc⟩ := φ.toHomeomorph.exists_addCircle_lift_symm_comp_eq_add hF hφ
  have hGs : ContDiff ℝ n G := contDiff_of_comp_coe_eq (funext hψ) hG φ.symm.contMDiff
  -- `G ∘ F` is a translation, so `G' (F x) * F' x = 1`
  have hne (x : ℝ) : deriv F x ≠ 0 := fun h ↦ by
    have h₁ : HasDerivAt (G ∘ F) (deriv G (F x) * deriv F x) x :=
      ((hGs.differentiable hn) (F x)).hasDerivAt.comp x ((hFs.differentiable hn) x).hasDerivAt
    have h₂ : HasDerivAt (G ∘ F) 1 x := by
      rw [show G ∘ F = fun y ↦ y + c from funext hc]
      exact (hasDerivAt_id x).add_const c
    have := h₁.unique h₂
    rw [h, mul_zero] at this
    exact zero_ne_one this
  rcases strictMono_or_strictAnti_of_lift (φ := φ.toHomeomorph) hF hφ with ⟨hm, hper⟩ | ⟨ha, hper⟩
  · exact .inl ⟨hper, fun x ↦ hm.monotone.deriv_nonneg.lt_of_ne' (hne x)⟩
  · exact .inr ⟨hper, fun x ↦ ha.antitone.deriv_nonpos.lt_of_ne (hne x)⟩

section Homotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **Smooth homotopy lifting for the circle.** A `C^n` map `g : [0, 1] × M → AddCircle T` whose
restriction to time zero lifts to a continuous real function `f` has a `C^n` real lift `G`,
`g q = G q`, with `G (0, x) = f x`. -/
theorem exists_contMDiff_lift_unitInterval_prod {g : unitInterval × M → AddCircle T}
    (hg : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) n g) {f : M → ℝ} (hf : Continuous f)
    (h₀ : ∀ x, g (0, x) = f x) :
    ∃ G : unitInterval × M → ℝ, ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ) n G ∧ (∀ q, g q = G q) ∧
      ∀ x, G (0, x) = f x := by
  have cov := isCoveringMap_coe T
  have hlift := cov.liftHomotopy_lifts ⟨g, hg.continuous⟩ ⟨f, hf⟩ h₀
  refine ⟨cov.liftHomotopy ⟨g, hg.continuous⟩ ⟨f, hf⟩ h₀, ?_,
    fun q ↦ (congr_fun hlift q).symm, cov.liftHomotopy_zero _ _ h₀⟩
  -- The continuous lift is `C^n` because the projection is a `C^n` local diffeomorphism.
  exact ContMDiff.of_comp_isLocalDiffeomorph (isLocalDiffeomorph_coe T n)
    (ContinuousMap.continuous _) (by rw [hlift]; exact hg)

end Homotopy

/-- **A smooth local section of the projection near zero.** There is a smooth real function `σ` on
the circle and a radius `δ > 0` such that `σ θ` is a real representative of `θ` whenever
`‖θ‖ < δ`. -/
theorem exists_contMDiff_coe_eq_of_norm_lt :
    ∃ σ : AddCircle T → ℝ, ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ σ ∧
      ∃ δ > 0, ∀ θ : AddCircle T, ‖θ‖ < δ → ((σ θ : ℝ) : AddCircle T) = θ := by
  -- Cut off the chart at `0` by a smooth bump function, which is `1` near `0`.
  let b := Classical.arbitrary (SmoothBumpFunction 𝓘(ℝ) (0 : AddCircle T))
  have hσ : ∀ᶠ θ in 𝓝 (0 : AddCircle T), ((b θ • chartAt ℝ (0 : AddCircle T) θ : ℝ) :
      AddCircle T) = θ := by
    filter_upwards [b.eventuallyEq_one,
      (chartAt ℝ (0 : AddCircle T)).open_source.mem_nhds (mem_chart_source ℝ 0)] with θ h₁ h₂
    rw [h₁, Pi.one_apply, one_smul]
    exact coe_apply_of_mem_atlas (chart_mem_atlas ℝ _) h₂
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hσ
  exact ⟨fun θ ↦ b θ • chartAt ℝ (0 : AddCircle T) θ, b.contMDiff_smul contMDiffOn_chart, δ, hδ,
    fun θ hθ ↦ h (by rwa [dist_zero_right])⟩

end AddCircle

namespace Diffeomorph

variable {T : ℝ} [Fact (0 < T)] {n : ℕ∞ω}

/-- **Every circle diffeomorphism has a lift.** A `C^n` diffeomorphism `φ` of `AddCircle T`,
`n ≠ 0`, has a `C^n` lift `F`, `φ x = F x`, which either satisfies `F (x + T) = F x + T` and has
positive derivative, or satisfies `F (x + T) = F x - T` and has negative derivative. -/
theorem exists_addCircle_lift (φ : AddCircle T ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle T) (hn : n ≠ 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ n F ∧ (∀ x : ℝ, φ x = F x) ∧
      (((∀ x, F (x + T) = F x + T) ∧ ∀ x, 0 < deriv F x) ∨
        ((∀ x, F (x + T) = F x - T) ∧ ∀ x, deriv F x < 0)) := by
  obtain ⟨F, hF, hφ⟩ := AddCircle.exists_continuous_lift φ.continuous
  exact ⟨F, AddCircle.contDiff_of_comp_coe_eq (funext hφ) hF φ.contMDiff, hφ,
    AddCircle.deriv_pos_or_deriv_neg_of_lift hn hF hφ⟩

end Diffeomorph
