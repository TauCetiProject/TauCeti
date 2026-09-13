/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.GaussCode.PDCode

/-!
# Naturality of Gauss-to-PD crossing signs

The Gauss-to-PD correspondence preserves the crossing-sign data.  Combining that fact with the
reflection laws at both presentations gives the reflection naturality theorem used by later
invariants.
-/

public section

namespace TauCeti.BasedOrientedGaussCode

variable {n : ℕ}

/-- Reflection negates the crossing signs after converting a Gauss code to a PD-code. -/
@[simp] theorem toOrientedPDCode_mirror_crossingSign (D : BasedOrientedGaussCode n) (c : Fin n) :
    D.mirror.toOrientedPDCode.crossingSign c =
      -D.toOrientedPDCode.crossingSign c := by
  rw [toOrientedPDCode_crossingSign, toOrientedPDCode_crossingSign,
    sign_mirror]
  simp

/-- Reflection negates the writhe after converting a Gauss code to a PD-code. -/
@[simp] theorem toOrientedPDCode_mirror_writhe (D : BasedOrientedGaussCode n) :
    D.mirror.toOrientedPDCode.writhe = -D.toOrientedPDCode.writhe := by
  rw [toOrientedPDCode_writhe, toOrientedPDCode_writhe]
  simp [writhe_mirror]

end TauCeti.BasedOrientedGaussCode
