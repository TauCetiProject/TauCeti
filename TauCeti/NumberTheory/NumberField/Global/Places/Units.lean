/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Places.Basic

/-!
# Finite absolute values and units

The unit condition at a finite place can be read either from its normalized absolute value
or from its discrete valuation. This comparison identifies the vanishing finite coordinates
of logarithmic maps with the valuation condition defining S-units.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

/-- A finite normalized absolute value is `1` exactly when the valuation is `1`. -/
theorem normalizedAbsValue_inl_eq_one_iff (y : K) :
    normalizedAbsValue (Sum.inl v) y = 1 ↔ v.valuation K y = 1 := by
  rw [normalizedAbsValue_inl, NumberField.HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_eq_one_iff _
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne_zero
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

end TauCeti.GlobalNumberFields
