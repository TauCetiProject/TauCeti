/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.SpecialLinearGroup.Lifting

/-!
# Regression examples: the lifting lemma at `ℓ = 3`

These examples check from a downstream module that

* the lifting lemma modulo `ℓ²` applies at `ℓ = 3`: a closed subgroup of `SL₂(ℤ₃)` or `GL₂(ℤ₃)`
  that surjects modulo `9` is everything;
* the residual argument for `ℓ ≥ 5` breaks at `ℓ = 3`: there the first congruence layer is reached
  by cubing a lift of `[[1, 1], [0, 1]]`, but the lift `[[1, 1], [-3, -2]]` to `SL₂(ℤ/9)` has cube
  `1`. This is why `3`-adic surjectivity is read modulo `9`.
-/

open Matrix PadicInt TauCeti

open scoped MatrixGroups

example (H : Subgroup SL(2, ℤ_[3])) (hH : IsClosed (H : Set SL(2, ℤ_[3])))
    (hmap : H.map (SpecialLinearGroup.map (toZModPow (p := 3) 2)) = ⊤) : H = ⊤ :=
  eq_top_of_isClosed_of_map_toZModPow_two_eq_top (by decide) hH hmap

example (H : Subgroup (GL (Fin 2) ℤ_[3])) (hH : IsClosed (H : Set (GL (Fin 2) ℤ_[3])))
    (hmap : H.map (GeneralLinearGroup.map (toZModPow (p := 3) 2)) = ⊤) : H = ⊤ :=
  eq_top_of_isClosed_of_map_generalLinearGroupMap_toZModPow_two_eq_top (by decide) hH hmap

/-- The lift `[[1, 1], [-3, -2]]` of `[[1, 1], [0, 1]]` lies in `SL₂(ℤ/9)`. -/
example : (!![1, 1; -3, -2] : Matrix (Fin 2) (Fin 2) (ZMod 9)).det = 1 := by
  decide

/-- The lift `[[1, 1], [-3, -2]]` has cube `1` in `SL₂(ℤ/9)`. -/
example : (!![1, 1; -3, -2] : Matrix (Fin 2) (Fin 2) (ZMod 9)) ^ 3 = 1 := by
  decide

/-- The lift `[[1, 1], [-3, -2]]` reduces modulo `3` to `[[1, 1], [0, 1]]`. -/
example : (!![1, 1; -3, -2] : Matrix (Fin 2) (Fin 2) (ZMod 9)).map (ZMod.castHom (by norm_num :
    3 ∣ 9) (ZMod 3)) = !![1, 1; 0, 1] := by
  decide
