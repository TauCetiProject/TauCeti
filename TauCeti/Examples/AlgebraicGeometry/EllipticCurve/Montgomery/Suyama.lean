/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama
import Mathlib.Algebra.Field.ZMod

/-!
# Examples of Suyama's ellipticity criterion

The rational parameter `6` gives an elliptic model, whereas `5` gives a singular one despite
having a nonzero denominator. Modulo `11`, the parameter `2` has nonzero `B` but yields a
singular model: the factor `9σ² - 25` is indispensable. The final example exercises the
criterion in characteristic three.
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

end TauCeti.Montgomery
