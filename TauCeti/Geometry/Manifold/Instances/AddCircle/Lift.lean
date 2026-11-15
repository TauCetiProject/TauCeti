/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Instances.AddCircle.Lift

/-!
# Lifts of circle diffeomorphisms

Every `C^n` diffeomorphism `φ` of the circle `AddCircle T`, `n ≠ 0`, has a `C^n` lift
`F : ℝ → ℝ`, `φ x = F x`, with either `F (x + T) = F x + T` and `F' > 0` (the
orientation-preserving case) or `F (x + T) = F x - T` and `F' < 0` (the orientation-reversing
case). A continuous lift exists by `AddCircle.exists_continuous_lift`, and it is `C^n` by
`AddCircle.contDiff_of_comp_coe_eq`. A lift `G` of `φ⁻¹` satisfies `G ∘ F = id + c`
(`Homeomorph.exists_addCircle_lift_symm_comp_eq_add`), so `G' (F x) F' x = 1` and `F'` never
vanishes, while the lift of a homeomorphism is monotone of degree one or antitone of degree `-1`
(`AddCircle.strictMono_or_strictAnti_of_lift`).

## Main declarations

* `AddCircle.deriv_pos_or_deriv_neg_of_lift`: a continuous lift of a `C^n` diffeomorphism of the
  circle, `n ≠ 0`, has degree one and positive derivative, or degree `-1` and negative derivative.
* `Diffeomorph.exists_addCircle_lift`: every `C^n` diffeomorphism of the circle, `n ≠ 0`, has a
  `C^n` lift of one of these two kinds.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.1, for lifts of circle
  homeomorphisms.
-/

public section

open scoped Manifold ContDiff

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
