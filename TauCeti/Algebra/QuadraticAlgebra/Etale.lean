/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.Algebra.QuadraticAlgebra.Split
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Algebra.Ring.Fin
import Mathlib.Tactic.Ring

/-!
# Rational quadratic étale algebras

A rational quadratic algebra with nonzero discriminant is étale. In the form
`ℚ[t]/(t² - D)` with `D ≠ 0`, it is a separable quadratic field for nonsquare `D`
and a product of two copies of `ℚ` for square `D`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

namespace QuadraticAlgebra

private theorem etale_rat_prod : Algebra.Etale ℚ (ℚ × ℚ) := by
  let e : (Fin 2 → ℚ) ≃ₐ[ℚ] ℚ × ℚ :=
    { RingEquiv.piFinTwo (fun _ : Fin 2 ↦ ℚ) with commutes' := fun _ ↦ rfl }
  exact Algebra.Etale.of_equiv e

private theorem etale_of_ne_zero (D : ℚ) (hD : D ≠ 0) :
    Algebra.Etale ℚ (QuadraticAlgebra ℚ D 0) := by
  let : Module.FinitePresentation ℚ (QuadraticAlgebra ℚ D 0) :=
    Module.finitePresentation_of_finite ℚ _
  by_cases hsq : IsSquare D
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hs
      exact hD hs
    let u : ℚˣ := Units.mk0 s hs0
    have hDQ : D = (u : ℚ) ^ 2 := by simpa only [u, Units.val_mk0, pow_two] using hs
    let : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)
    let e := TauCeti.QuadraticAlgebra.algEquivProdOfSq u hDQ
    let : Algebra.Etale ℚ (ℚ × ℚ) := etale_rat_prod
    exact Algebra.Etale.of_equiv e.symm
  · let : Fact (¬ IsSquare D) := ⟨hsq⟩
    let : Algebra.FormallyEtale ℚ (QuadraticAlgebra ℚ D 0) :=
      Algebra.FormallyEtale.of_isSeparable ℚ _
    exact ⟨inferInstance, inferInstance⟩

/-- A rational quadratic algebra with nonzero discriminant is étale. -/
theorem etale_of_discr_ne_zero {a b : ℚ} (hd : discr a b ≠ 0) :
    Algebra.Etale ℚ (QuadraticAlgebra ℚ a b) := by
  let D : ℚ := a + b ^ 2 / 4
  have hD : D ≠ 0 := by
    intro h
    apply hd
    simp only [discr_def]
    have h' : 4 * D = b ^ 2 + 4 * a := by dsimp [D]; ring
    rw [← h', h, mul_zero]
  let e : QuadraticAlgebra ℚ a b ≃ₐ[ℚ] QuadraticAlgebra ℚ D 0 :=
    changeGeneratorEquiv D 0 1 (b / 2)
      (by dsimp [D]; ring) (by simp; ring)
  let : Algebra.Etale ℚ (QuadraticAlgebra ℚ D 0) := etale_of_ne_zero D hD
  exact Algebra.Etale.of_equiv e.symm

end QuadraticAlgebra
