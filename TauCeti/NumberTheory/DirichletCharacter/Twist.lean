/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.Data.Nat.GCD

/-!
# Principal products of Dirichlet characters

A character can be cancelled by twisting it by a character of a prescribed level exactly when
its conductor divides that level. In particular, this identifies when twisting a family of
Dirichlet L-functions can introduce a pole at `1`.
-/

public section

namespace DirichletCharacter

/-- There is a character modulo `q` whose product with `ψ` is principal at the least common
multiple of the levels if and only if `ψ` has conductor dividing `q`. -/
theorem exists_mul_eq_one_iff_conductor_dvd {R : Type*} [CommMonoidWithZero R]
    {d q : ℕ} [NeZero d] (ψ : DirichletCharacter R d) :
    (∃ χ : DirichletCharacter R q, χ.mul ψ = 1) ↔ ψ.conductor ∣ q := by
  obtain rfl | _ := eq_zero_or_neZero q
  · refine iff_of_true ?_ (dvd_zero _)
    refine ⟨(changeLevel (dvd_zero d) ψ)⁻¹, ?_⟩
    simp only [DirichletCharacter.mul, map_inv, ← changeLevel_trans, inv_mul_cancel]
  constructor
  · rintro ⟨χ, h⟩
    rw [DirichletCharacter.mul] at h
    have heq := eq_inv_of_mul_eq_one_right h
    rw [← map_inv] at heq
    rw [← conductor_changeLevel ψ (Nat.dvd_lcm_right q d), heq,
      conductor_changeLevel, conductor_inv]
    exact χ.conductor_dvd_level
  · intro h
    refine ⟨(changeLevel h) ψ.primitiveCharacter⁻¹, ?_⟩
    have hlevel : changeLevel (Nat.dvd_lcm_right q d) ψ =
        changeLevel (h.trans (Nat.dvd_lcm_left q d)) ψ.primitiveCharacter := by
      rw [changeLevel_trans ψ.primitiveCharacter ψ.conductor_dvd_level,
        changeLevel_primitiveCharacter]
    rw [DirichletCharacter.mul, ← changeLevel_trans, map_inv, ← hlevel, inv_mul_cancel]

end DirichletCharacter
