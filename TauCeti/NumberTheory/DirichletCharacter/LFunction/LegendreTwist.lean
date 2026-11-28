/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char

/-!
# L-functions of Legendre twists at coprime levels

At a prime level the Jacobi character is the Legendre character. For coprime levels,
Mathlib's product of characters at the least common multiple therefore has the same
L-function as `DirichletCharacter.legendreTwist` at the product level.
-/

public section

namespace DirichletCharacter

/-- At coprime levels the product with the Jacobi character of a prime `d` has the same
L-function as the Legendre twist. The equality is between the continued functions and holds
also at `s = 1`. -/
theorem LFunction_mul_jacobiChar_eq_legendreTwist {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) (hqd : q.Coprime d) :
    letI : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
    letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne d)⟩
    (χ.mul (TauCeti.jacobiChar ℂ d)).LFunction = (χ.legendreTwist d).LFunction := by
  let _ : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  let _ : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne d)⟩
  unfold DirichletCharacter.mul
  -- Substitute in the common level before comparing the two products of induced characters.
  suffices ∀ (m : ℕ) [NeZero m], m = q * d → ∀ (hq : q ∣ m) (hdm : d ∣ m),
      (χ.changeLevel hq * (TauCeti.jacobiChar ℂ d).changeLevel hdm).LFunction =
        (χ.legendreTwist d).LFunction by
    exact this _ hqd.lcm_eq_mul (Nat.dvd_lcm_left ..) (Nat.dvd_lcm_right ..)
  intro m _ rfl hq hdm
  rw [TauCeti.jacobiChar_eq_ringHomComp_quadraticChar, legendreTwist_def]

end DirichletCharacter
