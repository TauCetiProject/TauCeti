/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Basic
import TauCeti.RingTheory.MvPolynomial.PowerSubstitution

/-!
# Native examples of power substitution and Frobenius graphs

The field with four elements is the actual quadratic algebra over `ZMod 2` with generator
`c` satisfying `c² + c + 1 = 0`. Its Frobenius graphs distinguish a strict degree bound from
its equality endpoint, and show why a first jet can succeed when all values vanish. Further
examples over `ℤ`, `ZMod 3` and `ZMod 2` compute exponent-zero collisions, weighted monomials
and coefficients, evaluation on the substitution graph, and compatibility of evaluated Hasse
jets, including the boundary where a higher substituted jet survives.
-/

public section

open MvPolynomial Finsupp

namespace TauCeti.PowerSubstitutionExamples

/-- The native four-element field supplies the strict three-point graph bound, the two-point
counterexample at equality, and the four-point case where the first jet succeeds although all
values vanish. The four conjuncts retain the carrier and three degree-bound checks. -/
example :
    let K := QuadraticAlgebra (ZMod 2) 1 1
    let c : K := QuadraticAlgebra.omega
    let F : MvPolynomial (Fin 2) K := X 0 + X 1
    let S₃ : Finset K := {0, 1, c}
    let S₂ : Finset K := {0, 1}
    let S₄ : Finset K := {0, 1, c, c + 1}
    (IsField K ∧ Nat.card K = 4 ∧ c ≠ 0 ∧ c ≠ 1 ∧ c ^ 2 + c + 1 = 0) ∧
    ((powerSubstitution 2 F).natDegree = 2 ∧
      (powerSubstitution 2 F).natDegree < S₃.card * (0 + 1) ∧
      ∃ a ∈ S₃, ∃ k ≤ 0, eval ![a, a ^ 2 ^ 1] (hasseDeriv (single 0 k) F) ≠ 0) ∧
    (F ≠ 0 ∧ F.degreeOf 0 < 2 ∧
      (powerSubstitution 2 F).natDegree = S₂.card * (0 + 1) ∧
      ∀ a ∈ S₂, eval ![a, a ^ 2] F = 0) ∧
    (F ≠ 0 ∧ F.degreeOf 0 < 4 ∧ (powerSubstitution 4 F).natDegree = 4 ∧
      (∀ a : K, eval ![a, a ^ 4] F = 0) ∧
      ¬(powerSubstitution 4 F).natDegree < S₄.card * (0 + 1) ∧
      (powerSubstitution 4 F).natDegree < S₄.card * (1 + 1) ∧
      (∀ a : K, eval ![a, a ^ 4] (pderiv (0 : Fin 2) F) = 1) ∧
      ∃ a ∈ S₄, ∃ k ≤ 1, eval ![a, a ^ 2 ^ 2] ((pderiv (0 : Fin 2))^[k] F) ≠ 0) := by
  intro K c F S₃ S₂ S₄
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩
  let : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hF : F ≠ 0 := fun h ↦ (one_ne_zero : (1 : K) ≠ 0)
    (by simpa [F] using congrArg (eval ![(0 : K), 1]) h)
  have hZ : F.degreeOf 0 < 2 :=
    (degreeOf_add_le 0 (X 0 : MvPolynomial (Fin 2) K) (X 1)).trans_lt
      (by norm_num [degreeOf_X])
  have hdeg (q : ℕ) (hq : 1 < q) : (powerSubstitution q F).natDegree = q := by
    simpa [F] using (Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (p := (Polynomial.X : Polynomial K)) (q := Polynomial.X ^ q) (by simpa using hq)).trans
        (Polynomial.natDegree_X_pow q)
  refine ⟨⟨Field.toIsField _, by simpa [Nat.card_prod] using
    (Nat.card_congr (QuadraticAlgebra.equivProd (1 : ZMod 2) 1)),
    by decide, by decide, by decide⟩, ?_, ?_, ?_⟩
  · have hbound : (powerSubstitution 2 F).natDegree < S₃.card * (0 + 1) := by
      norm_num [hdeg 2 (by decide), show S₃.card = 3 by decide]
    exact ⟨hdeg 2 (by decide), hbound,
      exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 1) hF hZ (by decide) hbound⟩
  · refine ⟨hF, hZ, by simpa [S₂] using hdeg 2 (by decide), ?_⟩
    simpa [S₂, F] using (by decide : (1 : K) + 1 = 0)
  · have hcard : S₄.card = 4 := by decide
    have hZ₄ : F.degreeOf 0 < 4 := hZ.trans (by decide : 2 < 4)
    have hbound : (powerSubstitution 4 F).natDegree < S₄.card * (1 + 1) := by
      norm_num [hdeg 4 (by decide), hcard]
    refine ⟨hF, hZ₄, hdeg 4 (by decide), ?_, by norm_num [hdeg 4 (by decide), hcard],
      hbound, by simp [F], ?_⟩
    · rintro ⟨r, i⟩
      simpa [F] using (by decide : ∀ r i : ZMod 2,
        (⟨r, i⟩ : QuadraticAlgebra (ZMod 2) 1 1) + ⟨r, i⟩ ^ 4 = 0) r i
    · exact exists_nonzero_ordinary_jet_on_frobenius_graph (p := 2) (e := 2)
        (by decide) hF hZ₄ (by decide) hbound

/-- At `q = 2`, the value at the generator distinguishes the third graph point from `0, 1`. -/
example :
    let c : QuadraticAlgebra (ZMod 2) 1 1 := QuadraticAlgebra.omega
    let F : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1) := X 0 + X 1
    eval ![0, 0] F = 0 ∧ eval ![1, 1] F = 0 ∧ eval ![c, c ^ 2] F = 1 := by
  intro c F
  have hvalues : (0 : QuadraticAlgebra (ZMod 2) 1 1) + 0 = 0 ∧
      (1 : QuadraticAlgebra (ZMod 2) 1 1) + 1 = 0 ∧ c + c ^ 2 = 1 := by decide
  simpa [F] using hvalues

/-- For the generator `c` outside the prime field, the first Hasse derivative of
`(c Z W)(X, X²)` over the four-element field is `c X²`. -/
example :
    let c : QuadraticAlgebra (ZMod 2) 1 1 := QuadraticAlgebra.omega
    Polynomial.hasseDeriv 1 (powerSubstitution 2 (C c * X 0 * X 1)) =
      Polynomial.C c * Polynomial.X ^ 2 := by
  intro c
  rw [Polynomial.hasseDeriv_one',
    derivative_powerSubstitution_of_natCast_eq_zero
      (by decide : (2 : QuadraticAlgebra (ZMod 2) 1 1) = 0)]
  simp

/-- With exponent zero, two distinct polynomials of `Z`-degree below one have the same image.
Thus a strip independent of the actual substitution exponent cannot give injectivity. -/
example : (X 1 : MvPolynomial (Fin 2) ℤ) ≠ 1 ∧
    (X 1 : MvPolynomial (Fin 2) ℤ).degreeOf 0 < 1 ∧
    (1 : MvPolynomial (Fin 2) ℤ).degreeOf 0 < 1 ∧
    powerSubstitution 0 (X 1 : MvPolynomial (Fin 2) ℤ) = powerSubstitution 0 1 := by
  exact ⟨fun h ↦ (zero_ne_one : (0 : ℤ) ≠ 1) (by simpa using congrArg (eval ![(0 : ℤ), 0]) h),
    by simp [degreeOf_X], by simp, by simp⟩

/-- At exponent two, the images and the coefficient of `Z W` retain their weighted exponents.
-/
example : powerSubstitution 2 (X 0 + X 1 : MvPolynomial (Fin 2) ℤ) =
      Polynomial.X + Polynomial.X ^ 2 ∧
    powerSubstitution 2 (X 0 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) =
      Polynomial.X + Polynomial.X ^ 3 ∧
    (powerSubstitution 2 (X 0 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ)).coeff 3 = 1 := by
  norm_num [← pow_succ', Polynomial.coeff_X]

/-- At exponent three the two mixed monomials have weights five and seven, within the
partial-degree bound `2 + 3 · 2 = 8`. -/
example :
    let F : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2
    powerSubstitution 3 F = Polynomial.X ^ 5 + Polynomial.X ^ 7 ∧
      (powerSubstitution 3 F).natDegree = 7 ∧ (powerSubstitution 3 F).natDegree ≤ 8 := by
  intro F
  have hmap : powerSubstitution 3 F = Polynomial.X ^ 5 + Polynomial.X ^ 7 := by
    norm_num [F, ← pow_mul, ← pow_add, ← pow_succ']
  have hdeg : (powerSubstitution 3 F).natDegree = 7 := by
    simpa only [hmap] using ((Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (p := (Polynomial.X : Polynomial ℤ) ^ 5) (q := Polynomial.X ^ 7)
      (by norm_num [Polynomial.natDegree_X_pow])).trans (Polynomial.natDegree_X_pow 7))
  exact ⟨hmap, hdeg, by omega⟩

/-- Evaluation at `3` uses the graph point `(3, 9)` and gives `27`. -/
example : (powerSubstitution 2 (X 0 * X 1 : MvPolynomial (Fin 2) ℤ)).eval 3 = 27 ∧
    eval ![3, 9] (X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = 27 := by
  norm_num

/-- For `Z²` on the graph point `(2, 2³)` over `ZMod 3`, the first Hasse jets computed
after and before power substitution both evaluate to `1`. -/
example :
    (Polynomial.hasseDeriv 1
      (powerSubstitution 3 (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)))).eval 2 = 1 ∧
      eval ![2, 2 ^ 3] (hasseDeriv (single 0 1)
        (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
  have hvalue : (Polynomial.hasseDeriv 1
      (powerSubstitution 3 (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)))).eval 2 = (4 : ZMod 3) := by
    norm_num [Polynomial.hasseDeriv_one']
  have hleft := hvalue.trans (by decide : (4 : ZMod 3) = 1)
  exact ⟨hleft, (eval_hasseDeriv_powerSubstitution (p := 3) (e := 1) (k := 1)
    (by decide) 2 (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))).symm.trans hleft⟩

/-- The order-two Hasse derivative of the weight-five monomial is `X³` in characteristic three.
-/
example :
    Polynomial.hasseDeriv 2
      (powerSubstitution 3 (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) =
        Polynomial.X ^ 3 ∧
      powerSubstitution 3 (hasseDeriv (single 0 2)
        (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) = Polynomial.X ^ 3 := by
  have hchoose : (Nat.choose 5 2 : ZMod 3) = 1 := by decide
  norm_num [X_pow_eq_monomial, X, monomial_pow, monomial_mul_monomial,
    Polynomial.monomial_mul_monomial, Polynomial.X_pow_eq_monomial,
    hasseDeriv_monomial, prod_single_index, ← single_tsub,
    Polynomial.hasseDeriv_monomial, hchoose]

/-- At `q = 4`, the first jet of `Z W` has weight four. The second jet of `W` is still
zero after substitution, but the fourth is one although every positive `Z`-jet of `W` is zero. -/
example :
    Polynomial.hasseDeriv 1
        (powerSubstitution 4 (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) = Polynomial.X ^ 4 ∧
      Polynomial.hasseDeriv 2
        (powerSubstitution 4 (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 ∧
      powerSubstitution 4
        (hasseDeriv (single 0 2) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 ∧
      Polynomial.hasseDeriv 4
        (powerSubstitution 4 (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 1 ∧
      powerSubstitution 4
        (hasseDeriv (single 0 4) (X 1 : MvPolynomial (Fin 2) (ZMod 2))) = 0 := by
  have hfive : (5 : ZMod 2) = 1 := by decide
  have hchoose₂ : (Nat.choose 4 2 : ZMod 2) = 0 := by decide
  have hfirst : Polynomial.hasseDeriv 1
      (powerSubstitution 4 (X 0 * X 1 : MvPolynomial (Fin 2) (ZMod 2))) =
        Polynomial.monomial 4 (5 : ZMod 2) := by
    norm_num [X, monomial_mul_monomial, Polynomial.monomial_mul_monomial,
      Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  simp only [hfirst, hfive]
  norm_num [X, monomial_mul_monomial, Polynomial.monomial_mul_monomial,
    Polynomial.X_pow_eq_monomial, hasseDeriv_monomial, prod_single_index,
    Polynomial.hasseDeriv_monomial, hchoose₂]

/-- Over `ZMod 3`, the polynomial `Z W + Z` has first substituted Hasse jet `X³ + 1`
and zero second jet, matching the two partial Hasse jets before substitution. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 3) := X 0 * X 1 + X 0
    powerSubstitution 3 F = Polynomial.X ^ 4 + Polynomial.X ∧
      Polynomial.hasseDeriv 1 (powerSubstitution 3 F) = Polynomial.X ^ 3 + 1 ∧
      Polynomial.hasseDeriv 2 (powerSubstitution 3 F) = 0 ∧
      powerSubstitution 3 (hasseDeriv (single 0 1) F) = Polynomial.X ^ 3 + 1 ∧
      powerSubstitution 3 (hasseDeriv (single 0 2) F) = 0 := by
  intro F
  have hmap : powerSubstitution 3 F = Polynomial.X ^ 4 + Polynomial.X := by
    norm_num [F, ← pow_succ']
  have hfirst : powerSubstitution 3 (hasseDeriv (single 0 1) F) =
      Polynomial.X ^ 3 + 1 := by
    norm_num [F, X, monomial_mul_monomial, Polynomial.monomial_mul_monomial,
      Polynomial.X_pow_eq_monomial, hasseDeriv_monomial, prod_single_index]
  have hsecond : powerSubstitution 3 (hasseDeriv (single 0 2) F) = 0 := by
    norm_num [F, X, monomial_mul_monomial, hasseDeriv_monomial, prod_single_index]
  exact ⟨hmap, (hasseDeriv_powerSubstitution (p := 3) (e := 1) (k := 1)
    (by decide) F).trans hfirst, (hasseDeriv_powerSubstitution (p := 3) (e := 1) (k := 2)
      (by decide) F).trans hsecond, hfirst, hsecond⟩

end TauCeti.PowerSubstitutionExamples
