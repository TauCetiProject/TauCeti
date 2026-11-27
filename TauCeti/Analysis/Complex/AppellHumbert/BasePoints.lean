/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.PoincareSeries
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Multiples without base points

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional complex
normed space `V`, with Riemann form `E` (`TauCeti.AppellHumbertData`). If `E` is positive, then for
every `n ≥ 2` the theta functions of the multiple `n D = (n B, χⁿ)` have no common zero
(`TauCeti.AppellHumbertData.IsPositive.exists_mem_thetaSpace_nsmul_apply_ne_zero`). Write
`n = m + 1` and take a nonzero theta function `f` of `D`. For every `a ∈ V` the product of the
twisted translates of `f ^ m` by `a` and of `f` by `-m a` is a theta function of `n D`: the twists
of the semicharacters, `exp (± 2πi m E (a, ·))`, cancel. At a common zero `z` this product, up to a
nowhere vanishing factor `f (z + a) ^ m f (z - m a)`, vanishes for every `a`; this is a product of
two entire functions of `a`, neither identically zero
(`AnalyticOnNhd.eqOn_zero_or_eqOn_zero_of_mul_eq_zero`).

## Provenance

Adapted from `New.ThetaTori.eq_zero_of_differentiable_of_mul_eq_zero` and
`New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero` (file
`src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
The phases are restated for the Riemann form `E = Im H`.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  Section 4.5 (base-point freeness of `L^n`, `n ≥ 2`).
* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, §17.
-/

public section

open Complex Set Filter
open scoped Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}

variable {D : AppellHumbertData L}

/-- The twists of the semicharacters of `m D` by `a` and of `D` by `-m a` cancel. -/
private theorem riemannChar_nsmul_mul_riemannChar_neg (m : ℕ) (a : V) :
    (m • D).riemannChar a * D.riemannChar (-(m • a)) = 1 := by
  ext l
  have h0 : (m • D).riemannForm a l + D.riemannForm (-(m • a)) l = 0 := by
    rw [riemannForm_nsmul]
    simp
  rw [mul_apply, riemannChar_apply, riemannChar_apply, ← Circle.exp_add, ← mul_add, h0, mul_zero,
    Circle.exp_zero, one_apply]

/-- **Multiples without base points.** For an Appell–Humbert datum `D` with positive Riemann form
and `n ≥ 2`, the theta functions of `n D` have no common zero: for every `z` some theta function of
`n D` does not vanish at `z`. -/
theorem IsPositive.exists_mem_thetaSpace_nsmul_apply_ne_zero [FiniteDimensional ℂ V]
    [DiscreteTopology L] [IsZLattice ℝ L] (hD : D.IsPositive) {n : ℕ} (hn : 2 ≤ n) (z : V) :
    ∃ f ∈ (n • D).thetaSpace, f z ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  obtain ⟨f, hf, hf_ne⟩ := hD.exists_mem_thetaSpace_ne_zero
  have hf_diff := differentiable_of_mem_thetaSpace hf
  by_contra! h_zero
  -- For each `a`, the product of the translates of `f ^ m` by `a` and of `f` by `-m a`.
  have h_mem (a : V) : (m • D).twistedTranslate a (f ^ m) * D.twistedTranslate (-(m • a)) f ∈
      ((m + 1) • D).thetaSpace := by
    have h := mul_mem_thetaSpace_add
      (twistedTranslate_mem_thetaSpace (pow_mem_thetaSpace_nsmul hf m) a)
      (twistedTranslate_mem_thetaSpace hf (-(m • a)))
    refine (mem_thetaSpace_iff _).mpr ⟨differentiable_of_mem_thetaSpace h, fun l z ↦ ?_⟩
    have hχ := congrArg (fun ψ : AddChar L Circle ↦ (ψ l : ℂ))
      (riemannChar_nsmul_mul_riemannChar_neg (D := D) m a)
    simp only [mul_apply, Circle.coe_mul, one_apply, Circle.coe_one] at hχ
    rw [apply_add_of_mem_thetaSpace h, factor_add, factor_add, factor_add, factor_nsmul,
      factor_nsmul, factor_ofAddChar, factor_ofAddChar, pow_succ]
    linear_combination (D.factor l z ^ m * D.factor l z *
      ((m • D).twistedTranslate a (f ^ m) * D.twistedTranslate (-(m • a)) f) z) * hχ
  -- At `z` the product is `f (z + a) ^ m * f (z - m a)` times a nonzero exponential.
  set F₁ : V → ℂ := fun a ↦ f (z + a) ^ m
  set F₂ : V → ℂ := fun a ↦ f (z - (m : ℂ) • a)
  have hF₁ : Differentiable ℂ F₁ := by fun_prop
  have hF₂ : Differentiable ℂ F₂ := by fun_prop
  have h_mul : F₁ * F₂ = 0 := by
    funext a
    have := h_zero _ (h_mem a)
    simp only [Pi.mul_apply, twistedTranslate_apply, Pi.pow_apply, mul_eq_zero, exp_ne_zero,
      false_or] at this
    simp only [F₁, F₂, Pi.mul_apply, Pi.zero_apply, Nat.cast_smul_eq_nsmul, sub_eq_add_neg]
    rcases this with h | h <;> simp [h]
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hf_ne
  have hw' : f w ≠ 0 := hw
  have h_left : F₁ ≠ 0 :=
    Function.ne_iff.mpr ⟨w - z, by simpa [F₁] using pow_ne_zero m hw'⟩
  -- So `F₂ = 0`, but `a ↦ z - m a` is surjective, so `f` would vanish at `w`.
  have h_right : F₂ = 0 := by
    have h_or := AnalyticOnNhd.eqOn_zero_or_eqOn_zero_of_mul_eq_zero
      (fun x _ ↦ hF₁.differentiableOn.analyticAt_of_finiteDimensional univ_mem)
      (fun x _ ↦ hF₂.differentiableOn.analyticAt_of_finiteDimensional univ_mem)
      isPreconnected_univ isOpen_univ fun x _ ↦ congrFun h_mul x
    rw [eqOn_univ, eqOn_univ] at h_or
    exact h_or.resolve_left h_left
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have := congrFun h_right ((m : ℂ)⁻¹ • (z - w))
  simp only [F₂, smul_smul, mul_inv_cancel₀ hm', one_smul, sub_sub_cancel, Pi.zero_apply] at this
  exact hw' this

end TauCeti.AppellHumbertData
