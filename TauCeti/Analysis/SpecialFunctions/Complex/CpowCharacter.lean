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

This file turns a continuous monoid homomorphism to the positive nonnegative reals into a
complex-valued character by taking a fixed complex power.

## Main definitions

* `TauCeti.cpowCharacter`: the character `x ↦ (f x) ^ s` associated to a continuous
  homomorphism `f : G →* ℝ≥0ˣ` and an exponent `s : ℂ`.
-/

public section
noncomputable section

namespace TauCeti

open Complex

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- The character `x ↦ (f x) ^ s` associated to a continuous positive-valued homomorphism
`f : G →* ℝ≥0ˣ` and a complex exponent `s`. -/
def cpowCharacter (f : G →* NNRealˣ) (hf : Continuous f) (s : ℂ) : G →ₜ* ℂˣ where
  toFun x := Units.mk0 ((((f x : NNReal) : ℝ) : ℂ) ^ s) <| by simp
  map_one' := Units.ext <| by simp
  map_mul' x y := Units.ext <| by
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, ofReal_mul, Units.val_mk0]
    exact mul_cpow_ofReal_nonneg (NNReal.coe_nonneg (f x : NNReal))
      (NNReal.coe_nonneg (f y : NNReal)) s
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr <|
    (continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hf))).cpow
      continuous_const fun x ↦ ofReal_mem_slitPlane.2 <| by
        simpa only [Function.comp_apply] using NNReal.coe_pos.mpr (f x).ne_zero.bot_lt

/-- Evaluating `cpowCharacter f hf s` at `x` gives `(f x) ^ s`. -/
@[simp]
theorem coe_cpowCharacter_apply (f : G →* NNRealˣ) (hf : Continuous f) (s : ℂ) (x : G) :
    (cpowCharacter f hf s x : ℂ) = (((f x : NNReal) : ℝ) : ℂ) ^ s :=
  by
    unfold cpowCharacter
    rfl

/-- The exponent `0` gives the trivial character. -/
@[simp]
theorem cpowCharacter_zero (f : G →* NNRealˣ) (hf : Continuous f) :
    cpowCharacter f hf 0 = 1 :=
  ContinuousMonoidHom.ext fun _ ↦ Units.ext <| by simp

/-- Adding exponents multiplies the associated characters. -/
theorem cpowCharacter_add (f : G →* NNRealˣ) (hf : Continuous f) (s t : ℂ) :
    cpowCharacter f hf (s + t) = cpowCharacter f hf s * cpowCharacter f hf t :=
  ContinuousMonoidHom.ext fun x ↦ Units.ext <| by
    simp [cpow_add _ _ (ofReal_ne_zero.2 (NNReal.coe_ne_zero.mpr (f x).ne_zero))]

end TauCeti
