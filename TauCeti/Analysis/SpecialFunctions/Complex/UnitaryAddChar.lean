/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Lie.Exponential.Units.Complex

/-!
# Continuous unitary characters of finite-dimensional real vector spaces

Every continuous additive character `χ : E → ℂ` of a finite-dimensional real vector space with
values of modulus one is `x ↦ exp (ℓ x * i)` for a continuous linear functional `ℓ`
(`AddChar.exists_eq_exp_mul_I`). Along each line `t ↦ χ (t • x)` is a continuous one-parameter
subgroup of `ℂˣ`, hence an exponential `t ↦ exp (t * s x)`
(`TauCeti.existsUnique_eq_expUnitHom_complex`); uniqueness of the exponent makes `x ↦ s x` real
linear, and unitarity makes it purely imaginary.

In particular such a character is smooth with bounded derivatives, so it has temperate growth
(`AddChar.hasTemperateGrowth`), and multiplication by it preserves Schwartz functions. This is
what makes translations and modulations by a unitary character act on the Schwartz space of a
real vector space, as in the Schrödinger model of the Heisenberg group.

## Main results

* `AddChar.exists_eq_exp_mul_I`: a continuous unitary character of a finite-dimensional real
  vector space is `x ↦ exp (ℓ x * i)` for a continuous linear functional `ℓ`.
* `AddChar.hasTemperateGrowth`: such a character has temperate growth.
-/

public section

open Complex TauCeti

namespace AddChar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of a continuous character `χ` of `E` to the line through `x`, as a continuous
one-parameter subgroup `t ↦ χ (t • x)` of `ℂˣ`. -/
private noncomputable def lineHom (χ : AddChar E ℂ) (hχ : Continuous χ)
    (h0 : ∀ x, χ x ≠ 0) (x : E) : Multiplicative ℝ →ₜ* ℂˣ where
  toFun t := Units.mk0 (χ (t.toAdd • x)) (h0 _)
  map_one' := Units.ext <| by simp
  map_mul' s t := Units.ext <| by simp [add_smul, map_add_eq_mul]
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.2 <| by
    simpa [Function.comp_def] using hχ.comp ((continuous_toAdd).smul continuous_const)

private theorem coe_lineHom_apply (χ : AddChar E ℂ) (hχ : Continuous χ) (h0 : ∀ x, χ x ≠ 0)
    (x : E) (t : Multiplicative ℝ) : (lineHom χ hχ h0 x t : ℂ) = χ (t.toAdd • x) :=
  (rfl)

/-- **Continuous unitary characters are exponentials.** A continuous additive character `χ` of
a finite-dimensional real vector space with values of modulus one is `x ↦ exp (ℓ x * i)` for a
continuous linear functional `ℓ`. -/
theorem exists_eq_exp_mul_I [FiniteDimensional ℝ E] (χ : AddChar E ℂ) (hχ : Continuous χ)
    (h1 : ∀ x, ‖χ x‖ = 1) : ∃ ℓ : E →L[ℝ] ℝ, ∀ x, χ x = exp (ℓ x * I) := by
  have h0 (x : E) : χ x ≠ 0 := fun h ↦ by simpa [h] using h1 x
  -- The exponent of `χ` along the line through `x`.
  choose s hs using fun x ↦ (existsUnique_eq_expUnitHom_complex (lineHom χ hχ h0 x)).exists
  have hst (x : E) (t : ℝ) : χ (t • x) = exp (t * s x) := by
    have := congrArg Units.val (DFunLike.congr_fun (hs x) (.ofAdd t))
    rwa [coe_lineHom_apply, coe_expUnitHom_complex, toAdd_ofAdd] at this
  -- Uniqueness of the exponent makes `s` additive and real homogeneous.
  have huniq {x : E} {c : ℂ} (h : ∀ t : ℝ, χ (t • x) = exp (t * c)) : s x = c :=
    (existsUnique_eq_expUnitHom_complex (lineHom χ hχ h0 x)).unique (hs x) <|
      ContinuousMonoidHom.ext fun t ↦ Units.ext <| by
        rw [coe_lineHom_apply, h, ← coe_expUnitHom_complex, ofAdd_toAdd]
  let S : E →ₗ[ℝ] ℂ :=
    { toFun := s
      map_add' x y := huniq fun t ↦ by
        rw [smul_add, map_add_eq_mul, hst, hst, ← exp_add, mul_add]
      map_smul' c x := huniq fun t ↦ by
        rw [smul_smul, hst, RingHom.id_apply, real_smul, ofReal_mul, mul_assoc] }
  -- Unitarity makes `s` purely imaginary.
  have hre (x : E) : (s x).re = 0 := by
    have := h1 x
    rwa [← one_smul ℝ x, hst, ofReal_one, one_mul, norm_exp, Real.exp_eq_one_iff] at this
  refine ⟨(imLm.comp S).toContinuousLinearMap, fun x ↦ ?_⟩
  have hx : s x = (s x).im * I := by
    apply Complex.ext <;> simp [hre]
  rw [← one_smul ℝ x, hst, ofReal_one, one_mul, one_smul]
  conv_lhs => rw [hx]
  simp [S]

/-- **Continuous unitary characters have temperate growth**: a continuous additive character
of a finite-dimensional real vector space with values of modulus one is a function of temperate
growth, so multiplication by it preserves Schwartz functions. -/
theorem hasTemperateGrowth [FiniteDimensional ℝ E] (χ : AddChar E ℂ) (hχ : Continuous χ)
    (h1 : ∀ x, ‖χ x‖ = 1) : (χ : E → ℂ).HasTemperateGrowth := by
  obtain ⟨ℓ, hℓ⟩ := χ.exists_eq_exp_mul_I hχ h1
  rw [funext hℓ]
  exact hasTemperateGrowth_exp_mul_I.comp ℓ.hasTemperateGrowth

end AddChar
