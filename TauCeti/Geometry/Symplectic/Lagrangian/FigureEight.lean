/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Immersion
public import TauCeti.Geometry.Symplectic.StandardCompatible
import TauCeti.Geometry.Manifold.Immersion.Differential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The figure-eight Lagrangian immersion of the circle

A Lagrangian immersion is a different notion from a Lagrangian embedding: it is the
parametrization that carries the Lagrangian structure, and its image may have self-intersections.
This file exhibits the simplest example. In the plane `ℝ × ℝ`, with its standard symplectic form
`dx ∧ dy` (`TauCeti.stdSymplecticForm`, read as a constant two-form), every immersed
curve is a Lagrangian immersion
(`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_of_finrank_eq_one`). The
**figure-eight**

`γ : ℝ / 2πℤ → ℝ × ℝ`, `γ(t) = (sin t, sin t cos t)`

(`TauCeti.figureEight`) is a smooth immersion, with velocity `(cos t, cos 2t)`, which never
vanishes. So it is a Lagrangian immersion (`TauCeti.isLagrangianImmersion_figureEight`). It has
exactly one double point: `γ(s) = γ(t)` for `s ≠ t` exactly when `{s, t} = {0, π}`, both of which
are sent to the origin (`TauCeti.figureEight_eq_figureEight_iff`). Hence it is not injective, and
not a Lagrangian embedding (`TauCeti.not_isLagrangianEmbedding_figureEight`).

The self-intersection is part of the data that symplectomorphisms preserve: if `ψ` is a
symplectomorphism of the plane, then `ψ ∘ γ` is again a Lagrangian immersion
(`TauCeti.isLagrangianImmersion_comp_figureEight`), and its double points are those of `γ`
(`TauCeti.comp_figureEight_eq_comp_figureEight_iff`). A version of these statements that replaced
`γ` by its image, the figure-eight subset of the plane, would lose this: that subset is not a
submanifold at the origin.

## Main definitions

* `TauCeti.figureEight`: the figure-eight `t ↦ (sin t, sin t cos t)` on `AddCircle (2π)`.

## Main results

* `TauCeti.isImmersion_figureEight`: the figure-eight is a smooth immersion.
* `TauCeti.isLagrangianImmersion_figureEight`: it is a Lagrangian immersion.
* `TauCeti.figureEight_eq_figureEight_iff`: its only double point is the pair `{0, π}`.
* `TauCeti.not_isLagrangianEmbedding_figureEight`: it is not a Lagrangian embedding.
* `TauCeti.isLagrangianImmersion_comp_figureEight`,
  `TauCeti.comp_figureEight_eq_comp_figureEight_iff`: its image under a symplectomorphism is a
  Lagrangian immersion with the same double point.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3 (immersed and embedded Lagrangian submanifolds).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4.
-/

public section

noncomputable section

open Real Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

/-- The period `2π` of the figure-eight is positive. -/
local instance figureEightTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The parametrization `t ↦ (sin t, sin t cos t)` of the figure-eight has period `2π`. -/
private theorem periodic_sin_sin_mul_cos :
    Function.Periodic (fun t : ℝ ↦ (sin t, sin t * cos t)) (2 * π) := fun t ↦ by
  simp only [sin_add_two_pi, cos_add_two_pi]

/-- The **figure-eight** `t ↦ (sin t, sin t cos t)`, a closed curve in the plane parametrized by the
circle `AddCircle (2π)`. It passes through the origin at `t = 0` and at `t = π`. -/
def figureEight : AddCircle (2 * π) → ℝ × ℝ :=
  periodic_sin_sin_mul_cos.lift

/-- The figure-eight at the class of `t` is `(sin t, sin t cos t)`. -/
@[simp]
theorem figureEight_coe (t : ℝ) : figureEight t = (sin t, sin t * cos t) :=
  periodic_sin_sin_mul_cos.lift_coe t

/-- The figure-eight passes through the origin at `t = 0`. -/
@[simp]
theorem figureEight_zero : figureEight 0 = 0 := by
  simpa [Prod.mk_zero_zero] using figureEight_coe 0

/-- The figure-eight passes through the origin again at `t = π`. -/
theorem figureEight_pi : figureEight (π : ℝ) = 0 := by
  simp [figureEight_coe]

/-! `Real.Angle` is by definition `AddCircle (2 * π)`, with the same coercion from `ℝ`. The next
three lemmas transfer Mathlib's statements about angles to the points of the circle, so that this
definitional identification is used only here. -/

/-- The class of `s` in the circle lies in `{0, π}` exactly when `sin s = 0`. -/
private theorem coe_mem_zero_pi_iff (s : ℝ) :
    (s : AddCircle (2 * π)) ∈ ({0, ((π : ℝ) : AddCircle (2 * π))} : Set _) ↔ sin s = 0 :=
  (Real.Angle.sin_eq_zero_iff (θ := s)).symm.trans (by rw [Real.Angle.sin_coe])

/-- Two reals with the same sine and cosine have the same class in the circle. -/
private theorem coe_eq_coe_of_cos_eq_of_sin_eq {s t : ℝ} (hc : cos s = cos t)
    (hs : sin s = sin t) : (s : AddCircle (2 * π)) = t :=
  Real.Angle.cos_sin_inj hc hs

/-- The class of `π` in the circle is not zero. -/
private theorem coe_pi_ne_zero : ((π : ℝ) : AddCircle (2 * π)) ≠ 0 :=
  Real.Angle.pi_ne_zero

/-- The figure-eight is smooth. -/
theorem contMDiff_figureEight : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ figureEight :=
  periodic_sin_sin_mul_cos.contMDiff_lift (contDiff_sin.prodMk (contDiff_sin.mul contDiff_cos))

/-- The velocity `(cos t, cos t cos t - sin t sin t) = (cos t, cos 2t)` of the figure-eight never
vanishes: where `cos t = 0`, the second component is `-sin² t = -1`. -/
private theorem cos_sin_mul_cos_deriv_ne_zero (t : ℝ) :
    ((cos t, cos t * cos t + sin t * -sin t) : ℝ × ℝ) ≠ 0 := by
  intro h
  have h₁ : cos t = 0 := congrArg Prod.fst h
  have h₂ : cos t * cos t + sin t * -sin t = 0 := congrArg Prod.snd h
  nlinarith [sin_sq_add_cos_sq t]

/-- The differential of the figure-eight is injective at every point. -/
theorem injective_mfderiv_figureEight (x : AddCircle (2 * π)) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) figureEight x) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  -- On the line, the figure-eight has derivative `c = (cos t, cos t cos t + sin t (-sin t))`, so
  -- its differential is `u ↦ u • c` with `c ≠ 0`.
  have hd : HasDerivAt (figureEight ∘ ((↑) : ℝ → AddCircle (2 * π)))
      ((cos t, cos t * cos t + sin t * -sin t) : ℝ × ℝ) t :=
    (hasDerivAt_sin t).prodMk ((hasDerivAt_sin t).mul (hasDerivAt_cos t))
  rw [← AddCircle.mfderiv_comp_coe, hd.hasFDerivAt.hasMFDerivAt.mfderiv]
  have hinj : Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ
      ((cos t, cos t * cos t + sin t * -sin t) : ℝ × ℝ)) := fun u v huv ↦
    smul_left_injective ℝ (cos_sin_mul_cos_deriv_ne_zero t) (by simpa using huv)
  -- The tangent spaces of the line and of the plane are `ℝ` and `ℝ × ℝ` by definition.
  exact hinj

/-- **The figure-eight is an immersion.** -/
theorem isImmersion_figureEight : IsImmersion 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ figureEight :=
  contMDiff_figureEight.isImmersion_of_injective_mfderiv (by simp) injective_mfderiv_figureEight

/-- **The figure-eight is a Lagrangian immersion** of the circle into the plane with its standard
symplectic form, as every immersed curve in a surface is. -/
theorem isLagrangianImmersion_figureEight :
    (SymplecticForm.isNondegenerate_constSmooth (stdSymplecticForm (V := ℝ))).IsLagrangianImmersion
      𝓘(ℝ) figureEight :=
  SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_of_finrank_eq_one isImmersion_figureEight
    (finrank_self ℝ) (by simp)

/-- **The double point of the figure-eight.** Two points of the circle have the same image
exactly when they are equal or both lie in `{0, π}`, which are sent to the origin. -/
theorem figureEight_eq_figureEight_iff {x y : AddCircle (2 * π)} :
    figureEight x = figureEight y ↔
      x = y ∨ (x ∈ ({0, ((π : ℝ) : AddCircle (2 * π))} : Set _) ∧
        y ∈ ({0, ((π : ℝ) : AddCircle (2 * π))} : Set _)) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  constructor
  · intro h
    simp only [figureEight_coe, Prod.mk.injEq] at h
    obtain ⟨hs, hsc⟩ := h
    by_cases h₀ : sin s = 0
    · -- Both points are sent to the origin, so both lie in `{0, π}`.
      exact Or.inr ⟨(coe_mem_zero_pi_iff s).2 h₀, (coe_mem_zero_pi_iff t).2 (hs ▸ h₀)⟩
    · -- Away from the origin the second coordinate recovers the cosine.
      rw [← hs] at hsc
      exact Or.inl (coe_eq_coe_of_cos_eq_of_sin_eq (mul_left_cancel₀ h₀ hsc) hs)
  · rintro (h | ⟨hx, hy⟩)
    · rw [h]
    · have hx' : figureEight (s : AddCircle (2 * π)) = 0 := by
        rcases hx with hx | hx <;> rw [hx] <;> simp
      have hy' : figureEight (t : AddCircle (2 * π)) = 0 := by
        rcases hy with hy | hy <;> rw [hy] <;> simp
      rw [hx', hy']

/-- The figure-eight is not injective: `0` and `π` are distinct points of the circle with the same
image, the origin. -/
theorem not_injective_figureEight : ¬Function.Injective figureEight := fun h ↦
  coe_pi_ne_zero (h (figureEight_pi.trans figureEight_zero.symm))

/-- **The figure-eight is not a Lagrangian embedding**: it is not injective. -/
theorem not_isLagrangianEmbedding_figureEight :
    ¬(SymplecticForm.isNondegenerate_constSmooth
      (stdSymplecticForm (V := ℝ))).IsLagrangianEmbedding 𝓘(ℝ) figureEight := fun h ↦
  not_injective_figureEight h.isEmbedding.injective

variable {ψ : (ℝ × ℝ) ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ ℝ × ℝ}

/-- **Symplectomorphisms carry the figure-eight to a Lagrangian immersion.** If a diffeomorphism
`ψ` of the plane preserves the standard symplectic form, then `ψ ∘ γ` is a Lagrangian immersion. -/
theorem isLagrangianImmersion_comp_figureEight
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (stdSymplecticForm (V := ℝ)).constSmooth =
      (stdSymplecticForm (V := ℝ)).constSmooth) :
    (SymplecticForm.isNondegenerate_constSmooth
      (stdSymplecticForm (V := ℝ))).IsLagrangianImmersion 𝓘(ℝ) (ψ ∘ figureEight) :=
  (Diffeomorph.isLagrangianImmersion_diffeomorph_comp_iff ψ hψ).2
    isLagrangianImmersion_figureEight

/-- **The double point survives a diffeomorphism.** For a diffeomorphism `ψ` of the plane,
`ψ ∘ γ` has the double point of the figure-eight `γ` and no other: two points of the circle have
the same image exactly when they are equal or both lie in `{0, π}`. -/
theorem comp_figureEight_eq_comp_figureEight_iff {x y : AddCircle (2 * π)} :
    ψ (figureEight x) = ψ (figureEight y) ↔
      x = y ∨ (x ∈ ({0, ((π : ℝ) : AddCircle (2 * π))} : Set _) ∧
        y ∈ ({0, ((π : ℝ) : AddCircle (2 * π))} : Set _)) :=
  ψ.injective.eq_iff.trans figureEight_eq_figureEight_iff

end TauCeti
