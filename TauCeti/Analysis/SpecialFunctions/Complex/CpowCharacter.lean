/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Complex powers of positive-valued characters

This file turns a continuous monoid homomorphism to the units of the nonnegative reals into a
complex-valued character by taking a fixed complex power.

## Main definitions

* `MonoidHom.cpowCharacter`: the character `x ↦ (f x) ^ s` associated to a continuous
  homomorphism `f : G →* ℝ≥0ˣ` and an exponent `s : ℂ`.
* `TauCeti.normCpowCharacter`: the character `x ↦ ‖x‖ ^ s` of the units of a seminormed ring
  with multiplicative norm.
-/

public section
noncomputable section

namespace TauCeti

open Complex
open scoped NNReal

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- The character `x ↦ (f x) ^ s` associated to a continuous positive-valued homomorphism
`f : G →* ℝ≥0ˣ` and a complex exponent `s`. -/
def _root_.MonoidHom.cpowCharacter (f : G →* ℝ≥0ˣ) (hf : Continuous f) (s : ℂ) : G →ₜ* ℂˣ where
  toFun x := Units.mk0 ((((f x : ℝ≥0) : ℝ) : ℂ) ^ s) <| by simp
  map_one' := Units.ext <| by simp
  map_mul' x y := Units.ext <| by
    simpa using mul_cpow_ofReal_nonneg (f x : ℝ≥0).coe_nonneg (f y : ℝ≥0).coe_nonneg s
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr <|
    (by fun_prop : Continuous fun x ↦ (((f x : ℝ≥0) : ℝ) : ℂ)).cpow continuous_const
      fun x ↦ ofReal_mem_slitPlane.2 <| NNReal.coe_pos.2 <| pos_iff_ne_zero.2 (f x).ne_zero

/-- Evaluating `f.cpowCharacter hf s` at `x` gives `(f x) ^ s`. -/
@[simp]
theorem _root_.MonoidHom.coe_cpowCharacter_apply (f : G →* ℝ≥0ˣ) (hf : Continuous f) (s : ℂ)
    (x : G) :
    (f.cpowCharacter hf s x : ℂ) = (((f x : ℝ≥0) : ℝ) : ℂ) ^ s :=
  (rfl)

/-- The absolute value of `f.cpowCharacter hf s` at `x` is `(f x) ^ re s`. -/
theorem _root_.MonoidHom.norm_coe_cpowCharacter_apply (f : G →* ℝ≥0ˣ) (hf : Continuous f)
    (s : ℂ) (x : G) :
    ‖(f.cpowCharacter hf s x : ℂ)‖ = ((f x : ℝ≥0) : ℝ) ^ s.re := by
  rw [MonoidHom.coe_cpowCharacter_apply,
    norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (f x).ne_zero.bot_lt)]

/-- The exponent `0` gives the trivial character. -/
@[simp]
theorem _root_.MonoidHom.cpowCharacter_zero (f : G →* ℝ≥0ˣ) (hf : Continuous f) :
    f.cpowCharacter hf 0 = 1 :=
  ContinuousMonoidHom.ext fun _ ↦ Units.ext <| by simp

/-- Adding exponents multiplies the associated characters. -/
@[simp]
theorem _root_.MonoidHom.cpowCharacter_add (f : G →* ℝ≥0ˣ) (hf : Continuous f) (s t : ℂ) :
    f.cpowCharacter hf (s + t) = f.cpowCharacter hf s * f.cpowCharacter hf t :=
  ContinuousMonoidHom.ext fun x ↦ Units.ext <| by
    simp [cpow_add _ _ (ofReal_ne_zero.2 (NNReal.coe_ne_zero.mpr (f x).ne_zero))]

section NormCpow

variable (𝕜 : Type*) [SeminormedRing 𝕜] [NormOneClass 𝕜] [NormMulClass 𝕜]

/-- The character `x ↦ ‖x‖ ^ s` of the units of a seminormed ring with multiplicative norm, for
a complex exponent `s`. -/
def normCpowCharacter (s : ℂ) : 𝕜ˣ →ₜ* ℂˣ :=
  (Units.map nnnormHom.toMonoidHom).cpowCharacter
    (Units.isEmbedding_val₀.continuous_iff.mpr <| continuous_nnnorm.comp Units.continuous_val) s

/-- Evaluating `normCpowCharacter 𝕜 s` at `x` gives `‖x‖ ^ s`. -/
@[simp]
theorem coe_normCpowCharacter_apply (s : ℂ) (x : 𝕜ˣ) :
    (normCpowCharacter 𝕜 s x : ℂ) = (‖(x : 𝕜)‖ : ℂ) ^ s := by
  simp [normCpowCharacter]

/-- The absolute value of `normCpowCharacter 𝕜 s` at `x` is `‖x‖ ^ re s`. -/
theorem norm_coe_normCpowCharacter_apply (s : ℂ) (x : 𝕜ˣ) :
    ‖(normCpowCharacter 𝕜 s x : ℂ)‖ = ‖(x : 𝕜)‖ ^ s.re :=
  MonoidHom.norm_coe_cpowCharacter_apply _ _ s x

/-- The exponent `0` gives the trivial character. -/
@[simp]
theorem normCpowCharacter_zero : normCpowCharacter 𝕜 0 = 1 :=
  MonoidHom.cpowCharacter_zero _ _

/-- Adding exponents multiplies the characters. -/
@[simp]
theorem normCpowCharacter_add (s t : ℂ) :
    normCpowCharacter 𝕜 (s + t) = normCpowCharacter 𝕜 s * normCpowCharacter 𝕜 t :=
  MonoidHom.cpowCharacter_add _ _ s t

end NormCpow

end TauCeti
