/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.Weyl.Integration
import TauCeti.RepresentationTheory.Compact.Circle
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Weyl integration over the full maximal torus of `SU(2)`

The Weyl-chamber formula integrates angles from `0` to `π`. Here it is expressed over a
whole period, over the additive circle of period `2π`, and over the unit circle parametrizing
the diagonal maximal torus, as well as over the torus subgroup itself. The whole torus counts
each regular conjugacy class twice, so
its Haar probability measure is weighted by half the squared Weyl denominator
`|z - z⁻¹|²`. The singular elements `z = ±1` cause no division by a vanishing denominator.

These are equivalent forms of `TauCeti.SU2.weyl_integration_formula` for continuous class
functions. The circle formulations allow their integrals to be expressed in the same coordinates
as Fourier analysis on the torus.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 17–18.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98
  (1985), Chapter IV, §1.
-/

public section

open MeasureTheory

namespace TauCeti.SU2

/-- **Weyl integration over a full period.** The density on `[0, 2π]` is
`(4π)⁻¹ · 4 sin²θ`, half the density on the Weyl chamber. -/
theorem weyl_integration_formula_full_period {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / (4 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun θ ↦ f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
  have hF : Continuous F := hf.comp continuous_torusExp |>.mul
    (Complex.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sin.pow 2)))
  have hreflect (θ : ℝ) : F (2 * Real.pi - θ) = F θ := by
    have ht : torusExp (2 * Real.pi - θ) = torusHom (Circle.exp θ)⁻¹ := by
      rw [sub_eq_add_neg, torusExp_add, torusExp_def, Circle.exp_two_pi, map_one,
        one_mul, torusExp_neg, torusExp_def, map_inv]
    simp only [F, ht, Real.sin_two_pi_sub, neg_sq]
    rw [← weylElement_conj_torusHom, hconj, torusExp_def]
  have hhalf : ∫ θ in Real.pi..2 * Real.pi, F θ = ∫ θ in (0 : ℝ)..Real.pi, F θ := by
    calc
      _ = ∫ θ in Real.pi..2 * Real.pi, F (2 * Real.pi - θ) :=
        intervalIntegral.integral_congr fun θ _ ↦ (hreflect θ).symm
      _ = ∫ θ in (0 : ℝ)..Real.pi, F θ := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
  have hfull : ∫ θ in (0 : ℝ)..2 * Real.pi, F θ =
      2 * ∫ θ in (0 : ℝ)..Real.pi, F θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _)
      (hF.intervalIntegrable _ _), hhalf]
    ring
  rw [weyl_integration_formula hf hconj]
  rw [hfull]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  dsimp [F]
  field_simp
  ring

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- **Weyl integration on the additive circle.** With Haar probability measure on
`ℝ / (2πℤ)`, the density is half the squared Weyl denominator. -/
theorem weyl_integration_formula_addCircle {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / 2 : ℂ) *
      ∫ θ : AddCircle (2 * Real.pi),
        f (torusHom (AddCircle.toCircle θ)) *
          (Complex.normSq (((AddCircle.toCircle θ) : ℂ) - ↑(AddCircle.toCircle θ)⁻¹) : ℂ)
        ∂AddCircle.haarAddCircle := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage _ 0]
  simp only [zero_add, Complex.real_smul]
  have hparam (θ : ℝ) : AddCircle.toCircle (θ : AddCircle (2 * Real.pi)) = Circle.exp θ := by
    rw [AddCircle.toCircle_apply_mk, div_self (by positivity), one_mul]
  have normSq_exp_sub_inv (θ : ℝ) :
      Complex.normSq ((Circle.exp θ : ℂ) - ↑(Circle.exp θ)⁻¹) = 4 * Real.sin θ ^ 2 := by
    rw [Circle.coe_inv_eq_conj, Circle.coe_exp]
    simp [Complex.normSq_apply, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    ring
  simp_rw [hparam, normSq_exp_sub_inv, ← torusExp_def]
  rw [weyl_integration_formula_full_period hf hconj]
  push_cast
  ring

/-- **Weyl integration over the full torus, parametrized by `Circle`.** Normalized Haar
measure on the circle carries the density `|z - z⁻¹|² / 2`. -/
theorem weyl_integration_formula_circle {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / 2 : ℂ) *
      ∫ z : Circle, f (torusHom z) * (Complex.normSq ((z : ℂ) - ↑z⁻¹) : ℂ)
        ∂haarProb Circle := by
  let e : Multiplicative (AddCircle (2 * Real.pi)) →* Circle :=
    AddCircle.toCircle_addChar.toMonoidHom
  have he : MeasurePreserving e (haarProb (Multiplicative (AddCircle (2 * Real.pi))))
      (haarProb Circle) := MonoidHom.measurePreserving
    AddCircle.continuous_toCircle
    (by
      intro z
      obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := 2 * Real.pi)
        (by positivity)).surjective z
      exact ⟨Multiplicative.ofAdd θ, (AddCircle.homeomorphCircle_apply _ θ).symm.trans hθ⟩)
    (by simp)
  have hmap := he.comp (measurePreserving_ofAdd_haarAddCircle (T := 2 * Real.pi))
  have hmeas : MeasurableEmbedding (fun θ : AddCircle (2 * Real.pi) ↦
      AddCircle.toCircle θ) := by
    convert (AddCircle.homeomorphCircle (T := 2 * Real.pi) (by positivity)).measurableEmbedding
      using 1
    funext θ
    exact (AddCircle.homeomorphCircle_apply _ θ).symm
  rw [weyl_integration_formula_addCircle hf hconj]
  congr 1
  simpa only [e, Function.comp_apply, AddChar.toMonoidHom_apply, AddCircle.toCircle_addChar,
    AddChar.coe_mk, toAdd_ofAdd] using hmap.integral_comp hmeas
      (fun z : Circle ↦ f (torusHom z) * (Complex.normSq ((z : ℂ) - ↑z⁻¹) : ℂ))

/-- **Weyl integration on the maximal torus itself.** The difference of the diagonal
entries is the Weyl denominator, and its squared modulus has Haar average two. -/
theorem weyl_integration_formula_torus {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / 2 : ℂ) *
      ∫ t : torus, f (t : SU2) *
        (Complex.normSq (((t : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 -
          ((t : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ) ∂haarProb torus := by
  have hmap : MeasurePreserving torusContinuousMulEquiv (haarProb Circle)
      (haarProb torus) := MonoidHom.measurePreserving
    (f := torusContinuousMulEquiv.toMulEquiv.toMonoidHom)
    (μ := haarProb Circle) (ν := haarProb torus)
    torusContinuousMulEquiv.continuous torusContinuousMulEquiv.surjective (by simp)
  rw [weyl_integration_formula_circle hf hconj]
  congr 1
  simpa only [torusContinuousMulEquiv_apply, coe_torusHom, torusMatrix_apply_zero_zero,
    torusMatrix_apply_one_one, Circle.coe_inv] using
    hmap.integral_comp torusContinuousMulEquiv.toHomeomorph.measurableEmbedding
      (fun t : torus ↦ f (t : SU2) *
        (Complex.normSq (((t : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 -
          ((t : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 1 1) : ℂ))

end TauCeti.SU2
