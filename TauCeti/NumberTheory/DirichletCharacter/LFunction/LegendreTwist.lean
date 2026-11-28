/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.Data.Nat.Prime.Finset
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# L-functions of Legendre twists

The quadratic twist used in prime selection is the common-level product with a Jacobi
character. Raising its level from the least common multiple to the product introduces no
new Euler factors, so its L-function agrees with that of the product-level Legendre twist
away from the possible principal pole. For coprime levels the least common multiple is
already the product, so the continued functions agree everywhere.
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

/-- The product-level Legendre twist and the common-level product with the Jacobi character
have the same L-function away from the possible principal pole. No coprimality is required. -/
theorem LFunction_legendreTwist_eq_mul_jacobiChar {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : χ.mul (TauCeti.jacobiChar ℂ d) ≠ 1 ∨ s ≠ 1) :
    (χ.legendreTwist d).LFunction s = (χ.mul (TauCeti.jacobiChar ℂ d)).LFunction s := by
  have hprimes : (q * d).primeFactors = (q.lcm d).primeFactors := by
    rw [Nat.primeFactors_mul (NeZero.ne q) (NeZero.ne d),
      Nat.primeFactors_lcm (NeZero.ne q) (NeZero.ne d)]
  have htwist : (χ.mul (TauCeti.jacobiChar ℂ d)).changeLevel (Nat.lcm_dvd_mul q d) =
      χ.legendreTwist d := by
    rw [legendreTwist_def, TauCeti.jacobiChar_eq_ringHomComp_quadraticChar (R := ℂ) d]
    simp only [DirichletCharacter.mul, map_mul, ← changeLevel_trans]
  rw [← htwist]
  exact LFunction_changeLevel_eq_of_primeFactors_eq _ _ hprimes hs

end DirichletCharacter
