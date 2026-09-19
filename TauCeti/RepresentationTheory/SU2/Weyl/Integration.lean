/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Invariants
import TauCeti.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.SU2.Exhaustion
public import TauCeti.RepresentationTheory.SU2.Weyl.Orthogonality

/-!
# The Weyl integration formula for `SU(2)`

For a continuous class function `f` on `SU(2)`, integration against the Haar probability measure
reduces to an integral over the Weyl chamber `[0, π]` of the maximal torus, against the Weyl
density `(2π)⁻¹ · 4 sin²θ dθ`:

`∫ f dμ = (2π)⁻¹ ∫₀^π f (diag (e^{iθ}, e^{-iθ})) · 4 sin²θ dθ`.

The Weyl factor `4 sin²θ = |e^{iθ} - e^{-iθ}|²` is the squared modulus of the Weyl denominator.

## Purpose

The formula applies to continuous conjugation-invariant functions and uses Haar probability
measure on `SU(2)`. Its Weyl-chamber density has total mass one, as recorded by
`TauCeti.SU2.weyl_integration_formula_normalized`. Specializing the formula to products of
symmetric-power characters gives their Haar orthonormality in
`TauCeti.SU2.integral_character_symPower_mul_conj`.

## Main results

* `TauCeti.SU2.integral_character_symPower`: `∫ χ_d dμ = δ_{d0}`.
* `TauCeti.SU2.weyl_integration_formula`: **the Weyl integration formula for `SU(2)`**, for
  continuous class functions.
* `TauCeti.SU2.integral_character_symPower_mul_conj`: **the characters of `SU(2)` are
  orthonormal**, `∫ χ_m · conj χ_n dμ = δ_{mn}`.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapters 17-18.
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, §1.
-/

public section

open MeasureTheory

namespace TauCeti

namespace SU2

/-! ### The Haar integral of a character -/

/-- **The Haar integral of the character of `Symᵈ(ℂ²)` is `δ_{d0}`.** It is the dimension of the
invariants: the whole line for the trivial representation `Sym⁰(ℂ²)`, and nothing otherwise,
since `Symᵈ(ℂ²)` is irreducible of dimension `d + 1`. -/
@[simp]
theorem integral_character_symPower (d : ℕ) :
    ∫ g, (symPower d).character g ∂haarProb SU2 = if d = 0 then 1 else 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · simp only [hd, ↓reduceIte]
    have hbot := Representation.IsIrreducible.invariants_eq_bot_of_finrank_ne_one
      (isIrreducible_symPowerModel d) (by rw [finrank_euclideanSpace_fin]; omega)
    -- Mathlib's `ContRepresentation.invariants` and `Representation.invariants` of the underlying
    -- representation are distinct submodules whose memberships both unfold to `∀ g, π g v = v`.
    rw [← (ContRepresentation.integral_character_eq_zero_iff (symPowerModel d)
      (continuous_symPowerModel d)).2 ((Submodule.eq_bot_iff _).2 fun v hv =>
        (Submodule.eq_bot_iff _).1 hbot v hv)]
    simp

/-! ### The Weyl-chamber functional -/

/-- The integrand of the Weyl-chamber side is continuous. -/
private theorem continuous_weylIntegrand (f : C(SU2, ℂ)) :
    Continuous fun θ : ℝ => f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) :=
  (f.continuous.comp continuous_torusExp).mul
    (Complex.continuous_ofReal.comp (continuous_const.mul (Real.continuous_sin.pow 2)))

/-- The Weyl-chamber side of the integration formula, as a continuous linear functional on
`C(SU(2), ℂ)` of norm at most one. -/
private noncomputable def weylFunctional : C(SU2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        rw [intervalIntegral.integral_add ((continuous_weylIntegrand f).intervalIntegrable _ _)
          ((continuous_weylIntegrand g).intervalIntegrable _ _), mul_add]
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
          intervalIntegral.integral_const_mul]
        ring }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      have hpi : 0 < Real.pi := Real.pi_pos
      have hbound : ‖∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)‖
          ≤ ‖f‖ * (2 * Real.pi) := by
        refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans ?_
        have hmass : ∫ θ in (0 : ℝ)..Real.pi, 4 * Real.sin θ ^ 2 = 2 * Real.pi := by
          rw [intervalIntegral.integral_const_mul, integral_sin_sq]
          simp only [Real.sin_zero, Real.sin_pi, zero_mul, sub_zero]
          ring
        rw [← hmass, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_mono_on hpi.le
          ((continuous_weylIntegrand f).norm.intervalIntegrable _ _)
          ((continuous_const.mul
            (continuous_const.mul (Real.continuous_sin.pow 2))).intervalIntegrable _ _)
          fun θ _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (by positivity)
      rw [norm_mul, norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hpi.le]
      calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..Real.pi,
              f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ)‖
          ≤ 1 / (2 * Real.pi) * (‖f‖ * (2 * Real.pi)) := by gcongr
        _ = ‖f‖ := by field_simp

private theorem weylFunctional_apply (f : C(SU2, ℂ)) :
    weylFunctional f = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) :=
  (rfl)

/-- On the character of `Symᵈ(ℂ²)` the Weyl-chamber functional is `δ_{d0}`: this is the pairing
against `χ_0 = 1` in the orthonormality relation over the Weyl chamber. -/
private theorem weylFunctional_symPowerCharacter (d : ℕ) :
    weylFunctional (symPowerCharacter d) = if d = 0 then 1 else 0 := by
  have h := character_symPower_orthonormal_torusExp d 0
  simp only [character_symPower_zero, map_one, mul_one] at h
  rw [weylFunctional_apply]
  simpa only [symPowerCharacter_apply] using h

/-! ### The Weyl integration formula -/

/-- **The Weyl integration formula for `SU(2)`.** For a continuous class function `f` on `SU(2)`,
the integral of `f` against the Haar probability measure is the integral over the Weyl chamber
`[0, π]` of the maximal torus against the Weyl density `(2π)⁻¹ · 4 sin²θ dθ`:

`∫ f dμ = (2π)⁻¹ ∫₀^π f (diag (e^{iθ}, e^{-iθ})) · 4 sin²θ dθ`.

The Weyl factor `4 sin²θ = |e^{iθ} - e^{-iθ}|²` is the squared modulus of the Weyl denominator,
and the density has total mass one (`TauCeti.SU2.weyl_integration_formula_normalized`). -/
theorem weyl_integration_formula {f : SU2 → ℂ} (hf : Continuous f)
    (hconj : ∀ u g : SU2, f (u * g * u⁻¹) = f g) :
    ∫ g, f g ∂haarProb SU2 = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..Real.pi, f (torusExp θ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  let F : C(SU2, ℂ) := ⟨f, hf⟩
  let D : C(SU2, ℂ) →L[ℂ] ℂ := haarAverage SU2 - weylFunctional
  have hspan : characterSpan ≤ LinearMap.ker (D : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    characterSpan_le_iff.2 fun d => LinearMap.mem_ker.2 <| by
      simp only [D, ContinuousLinearMap.coe_coe, sub_apply,
        haarAverage_apply, weylFunctional_symPowerCharacter, symPowerCharacter_apply,
        integral_character_symPower, sub_self]
  have hF : F ∈ LinearMap.ker (D : C(SU2, ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
      (mem_topologicalClosure_characterSpan_iff.2 hconj)
  have hD := LinearMap.mem_ker.1 hF
  simp only [D, ContinuousLinearMap.coe_coe, sub_apply,
    haarAverage_apply, sub_eq_zero] at hD
  exact hD.trans (weylFunctional_apply F)

/-- **The characters of `SU(2)` are orthonormal against Haar measure:**
`∫ χ_m · conj χ_n dμ = δ_{mn}` for the characters `χ_d` of the symmetric powers `Symᵈ(ℂ²)`.

The Weyl integration formula `TauCeti.SU2.weyl_integration_formula` moves the integral to the
Weyl chamber, where it is `TauCeti.SU2.character_symPower_orthonormal_torusExp`. -/
@[simp]
theorem integral_character_symPower_mul_conj (m n : ℕ) :
    ∫ g, (symPower m).character g * (starRingEnd ℂ) ((symPower n).character g) ∂haarProb SU2
      = if m = n then 1 else 0 := by
  rw [weyl_integration_formula
    (f := fun g => (symPower m).character g * (starRingEnd ℂ) ((symPower n).character g))
    ((continuous_character_symPower m).mul
      (Complex.continuous_conj.comp (continuous_character_symPower n)))
    fun u g => by rw [Representation.char_conj, Representation.char_conj]]
  exact character_symPower_orthonormal_torusExp m n

end SU2

end TauCeti
