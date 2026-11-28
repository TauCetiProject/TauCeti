/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Bridge from `SL₂` transvections to `GL₂.upperRightHom`

Relates upper-right transvections in `SL(2, R)` under `Matrix.SpecialLinearGroup.mapGL S` to
`Matrix.GeneralLinearGroup.upperRightHom`. Keeping this bridge separate avoids pulling
`Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo` into
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic`.

## Main results

* `Matrix.SpecialLinearGroup.mapGL_transvection_eq_upperRightHom`: `mapGL S` sends an upper-right
  transvection in `SL(2, R)` to `GeneralLinearGroup.upperRightHom (algebraMap R S w)`.
-/

public section

namespace Matrix.SpecialLinearGroup

/-- Under `mapGL S`, an upper-right transvection in `SL₂(R)` becomes `upperRightHom`. -/
lemma mapGL_transvection_eq_upperRightHom {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (w : R) :
    mapGL S (transvection (zero_ne_one' (Fin 2)) w) =
      GeneralLinearGroup.upperRightHom (algebraMap R S w) := by
  apply Units.ext; rw [coe_mapGL_fin_two]; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection, Matrix.transvection, GeneralLinearGroup.upperRightHom]

end Matrix.SpecialLinearGroup

end
