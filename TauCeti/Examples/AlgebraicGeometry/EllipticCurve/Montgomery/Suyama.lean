/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama.Point
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of Suyama's ellipticity criterion

The rational parameter `6` gives an elliptic model, whereas `5` gives a singular one despite
having a nonzero denominator. Modulo `11`, the parameter `2` has nonzero `B` but yields a
singular model: the factor `9σ² - 25` is indispensable. The final example exercises the
criterion in characteristic three. Further examples check the polynomial seed pair and its
projective coordinate, including at a nonsingular point of a singular model.
-/

namespace TauCeti.Montgomery

-- A non-exceptional rational parameter.
example : (model (suyamaA (6 : ℚ)) (suyamaB (6 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

-- A nonzero denominator does not guarantee ellipticity.
example : ¬ (model (suyamaA (5 : ℚ)) (suyamaB (5 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

section Eleven

variable [Fact (Nat.Prime 11)]

-- Here the obstruction comes from A² - 4, not from B.
example : suyamaB (2 : ZMod 11) = 9 := by
  rw [suyamaB_eq (by decide +revert) (by decide +revert) (by decide +revert)]
  simp only [suyamaU_def, suyamaV_def]
  apply (div_eq_iff (by decide +revert)).mpr
  decide +revert

example : ¬ (model (suyamaA (2 : ZMod 11)) (suyamaB (2 : ZMod 11))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by decide +revert) (by decide +revert) (by decide +revert)]
  decide +revert

end Eleven

-- Characteristic three is included, with no additional hypothesis.
example : ¬ (model (suyamaA (1 : ZMod 3)) (suyamaB (1 : ZMod 3))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by decide) (by decide) (by decide)]
  norm_num

-- The polynomial pair for σ = 6 is a representative of the supplied native point.
example (hB : suyamaB (6 : ℚ) ≠ 0) :
    (⟨31 ^ 3, 24 ^ 3⟩ : Pair ℚ).cross
      (coordinates (suyamaA 6) (suyamaB 6) (suyamaPoint (by norm_num) hB)) = 0 := by
  convert cross_coordinates_suyamaPoint (by norm_num) hB using 1
  norm_num [suyamaU_def, suyamaV_def]

-- σ = 3 gives A = 2, so the model is singular, but its supplied point still exists.
example : ¬ (model (suyamaA (3 : ℚ)) (suyamaB (3 : ℚ))).IsElliptic := by
  rw [isElliptic_model_suyama_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

example : ∃ hB : suyamaB (3 : ℚ) ≠ 0,
    projectiveX (suyamaA 3) hB (suyamaPoint (by norm_num) hB) =
      (⟨4 ^ 3, 12 ^ 3⟩ : Pair ℚ).toProj (by simp [Pair.eq_zero_iff]) := by
  have hB : suyamaB (3 : ℚ) ≠ 0 := by
    rw [suyamaB_eq (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hB, ?_⟩
  convert projectiveX_suyamaPoint (by norm_num) hB using 1
  norm_num [suyamaU_def, suyamaV_def]

end TauCeti.Montgomery
