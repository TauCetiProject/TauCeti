/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.ProjectiveImageSandwich.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Examples of the finite-field projective image condition

Concrete checks of `TauCeti.IsProjectiveImageSandwich`.

* The identity representation of `GL(2, 𝔽₇)` satisfies the condition for `p = 7`, `a = 1` and
  `n = 3`: its projective image is all of `PGL(2, 𝔽₇)`, and `7 > max(5, 5)`.
* Extension of scalars from `GL(2, 𝔽₇)` to `GL(2, K)`, for `K` an algebraic closure of `𝔽₇`,
  satisfies the same condition; this is the setting of Newton–Thorne, where `K` is an algebraic
  closure of `𝔽_p`.
* The identity representation of `GL(2, 𝔽₈)` satisfies the condition for `p = 2`, `a = 3` and
  `n = 4`, since `8 > 7`; here `p ≤ n`, so the condition does not force `p > n`.
* Over `𝔽₅` the strict bound `#k > 5` always fails, and `a = 0` is impossible for every field.
-/

public section

namespace TauCeti.ProjectiveImageSandwichExamples

open Matrix

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The identity representation of `GL(2, 𝔽₇)` satisfies the condition for `p = 7`, `a = 1`,
`n = 3`. -/
theorem isProjectiveImageSandwich_id_zmod_seven :
    IsProjectiveImageSandwich 7 1 3 (RingHom.id (ZMod 7)) (MonoidHom.id (GL (Fin 2) (ZMod 7))) := by
  simpa [GeneralLinearGroup.map_id] using
    isProjectiveImageSandwich_generalLinearGroupMap (p := 7) (a := 1) (by decide) (by norm_num)
      (by simp) (by norm_num) (RingHom.id (ZMod 7))

/-- Extension of scalars from `GL(2, 𝔽₇)` to `GL(2, K)`, for `K` an algebraic closure of `𝔽₇`,
satisfies the condition for `p = 7`, `a = 1`, `n = 3`. -/
theorem isProjectiveImageSandwich_algebraicClosure_zmod_seven :
    IsProjectiveImageSandwich 7 1 3 (algebraMap (ZMod 7) (AlgebraicClosure (ZMod 7)))
      (GeneralLinearGroup.map (n := Fin 2) (algebraMap (ZMod 7) (AlgebraicClosure (ZMod 7)))) :=
  isProjectiveImageSandwich_generalLinearGroupMap (p := 7) (a := 1) (by decide) (by norm_num)
    (by simp) (by norm_num) _

/-- The identity representation of `GL(2, 𝔽₈)` satisfies the condition for `p = 2`, `a = 3`,
`n = 4`, although `p ≤ n`. -/
theorem isProjectiveImageSandwich_id_galoisField_two_three :
    IsProjectiveImageSandwich 2 3 4 (RingHom.id (GaloisField 2 3))
      (MonoidHom.id (GL (Fin 2) (GaloisField 2 3))) := by
  simpa [GeneralLinearGroup.map_id] using
    isProjectiveImageSandwich_generalLinearGroupMap Nat.prime_two (by norm_num)
      (GaloisField.card 2 3 (by norm_num)) (by norm_num) (RingHom.id (GaloisField 2 3))

/-- Over `𝔽₅` the strict field-size bound fails, whatever `p`, `a`, `n` and `ρ`. -/
theorem not_isProjectiveImageSandwich_zmod_five {G K : Type*} [Group G] [CommRing K] {p a n : ℕ}
    (ι : ZMod 5 →+* K) (ρ : G →* GL (Fin 2) K) : ¬ IsProjectiveImageSandwich p a n ι ρ :=
  not_isProjectiveImageSandwich_of_natCard_le_five (by simp) ι ρ

/-- The exponent `a = 0` is impossible. -/
theorem not_isProjectiveImageSandwich_zero {G k K : Type*} [Group G] [Field k] [CommRing K]
    {p n : ℕ} (ι : k →+* K) (ρ : G →* GL (Fin 2) K) : ¬ IsProjectiveImageSandwich p 0 n ι ρ :=
  fun h ↦ by simpa using h.one_le_exponent

end TauCeti.ProjectiveImageSandwichExamples
