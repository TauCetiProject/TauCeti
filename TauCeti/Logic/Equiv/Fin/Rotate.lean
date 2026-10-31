/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Rotating finite indices

The rotation `finRotate m` of `Fin m` commutes with the identification `finCongr` of `Fin m` and
`Fin m'` along an equality `m = m'`, for moving between lengths written in different forms.

## Main results

* `TauCeti.finCongr_finRotate`: rotation commutes with `finCongr`.
-/

public section

namespace TauCeti

/-- Rotation commutes with the identification `Fin m ≃ Fin m'` along an equality `m = m'`. -/
theorem finCongr_finRotate {m m' : ℕ} (hm : m = m') (i : Fin m) :
    finCongr hm (finRotate m i) = finRotate m' (finCongr hm i) := by
  subst hm
  rfl

end TauCeti
