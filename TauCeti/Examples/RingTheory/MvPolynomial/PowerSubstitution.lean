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
its equality endpoint, and show why a first jet can succeed when all values vanish.
-/

public section

open MvPolynomial Finsupp

namespace TauCeti.PowerSubstitutionExamples

/-- The carrier is a field with four elements and the indicated nontrivial generator. -/
example : IsField (QuadraticAlgebra (ZMod 2) 1 1) ∧ Nat.card (QuadraticAlgebra (ZMod 2) 1 1) = 4 ∧
    (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod 2) 1 1) ≠ 0 ∧
    (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod 2) 1 1) ≠ 1 ∧
    (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod 2) 1 1) ^ 2 +
      QuadraticAlgebra.omega + 1 = 0 := by
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩
  exact ⟨Field.toIsField _, by simpa [Nat.card_prod] using
    (Nat.card_congr (QuadraticAlgebra.equivProd (1 : ZMod 2) 1)),
    by decide, by decide, by decide⟩

/-- At `q = 2`, the value at the generator distinguishes the third graph point from `0, 1`. -/
example :
    let c : QuadraticAlgebra (ZMod 2) 1 1 := QuadraticAlgebra.omega
    let F : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1) := X 0 + X 1
    eval ![0, 0] F = 0 ∧ eval ![1, 1] F = 0 ∧ eval ![c, c ^ 2] F = 1 := by
  norm_num; decide

/-- The three-point graph has degree `2 < 3`, so the native Hasse nonvanishing theorem applies.
The preceding computation identifies its nonzero value at the generator. -/
example :
    let c : QuadraticAlgebra (ZMod 2) 1 1 := QuadraticAlgebra.omega
    let S : Finset (QuadraticAlgebra (ZMod 2) 1 1) := {0, 1, c}
    let F : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1) := X 0 + X 1
    (powerSubstitution 2 F).natDegree = 2 ∧
      (powerSubstitution 2 F).natDegree < S.card * (0 + 1) ∧
      ∃ a ∈ S, ∃ k ≤ 0, eval ![a, a ^ 2 ^ 1] (hasseDeriv (single 0 k) F) ≠ 0 := by
  intro c S F
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩
  let : CharP (QuadraticAlgebra (ZMod 2) 1 1) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (QuadraticAlgebra (ZMod 2) 1 1)).injective 2
  have hdeg : (powerSubstitution 2 F).natDegree = 2 := by
    simpa [F] using ((Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (p := (Polynomial.X : Polynomial (QuadraticAlgebra (ZMod 2) 1 1))) (q := Polynomial.X ^ 2)
      (by simp)).trans
        (Polynomial.natDegree_X_pow 2))
  have hcard : S.card = 3 := by decide
  have hbound : (powerSubstitution 2 F).natDegree < S.card * (0 + 1) := by omega
  exact ⟨hdeg, hbound, exists_nonzero_hasse_jet_on_frobenius_graph (p := 2) (e := 1)
    (fun h ↦ (one_ne_zero : (1 : QuadraticAlgebra (ZMod 2) 1 1) ≠ 0)
      (by simpa [F] using congrArg (eval ![(0 : QuadraticAlgebra (ZMod 2) 1 1), 1]) h))
    ((degreeOf_add_le 0 (X 0 : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1)) (X 1)).trans_lt
      (by norm_num [degreeOf_X]))
    (by decide) hbound⟩

/-- Equality at the degree endpoint does not suffice, even with a nonzero polynomial of
`Z`-degree below two: the two values on `S = {0, 1}` both vanish. -/
example :
    let S : Finset (QuadraticAlgebra (ZMod 2) 1 1) := {0, 1}
    let F : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1) := X 0 + X 1
    F ≠ 0 ∧ F.degreeOf 0 < 2 ∧
      (powerSubstitution 2 F).natDegree = S.card * (0 + 1) ∧
      ∀ a ∈ S, eval ![a, a ^ 2] F = 0 := by
  intro S F
  refine ⟨(fun h ↦ (one_ne_zero : (1 : QuadraticAlgebra (ZMod 2) 1 1) ≠ 0)
      (by simpa [F] using congrArg (eval ![(0 : QuadraticAlgebra (ZMod 2) 1 1), 1]) h)),
    (degreeOf_add_le 0 (X 0 : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1)) (X 1)).trans_lt
      (by norm_num [degreeOf_X]), ?_, ?_⟩
  · simpa [S, F] using ((Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (p := (Polynomial.X : Polynomial (QuadraticAlgebra (ZMod 2) 1 1))) (q := Polynomial.X ^ 2)
      (by simp)).trans
        (Polynomial.natDegree_X_pow 2))
  · simpa [S, F] using (by decide : (1 : QuadraticAlgebra (ZMod 2) 1 1) + 1 = 0)

/-- On all four points with `q = 4`, the values vanish at degree equality, but the first jet
is one everywhere and the ordinary nonvanishing theorem applies with order bound one. -/
example :
    let S : Finset (QuadraticAlgebra (ZMod 2) 1 1) :=
      {0, 1, QuadraticAlgebra.omega, QuadraticAlgebra.omega + 1}
    let F : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1) := X 0 + X 1
    F ≠ 0 ∧ F.degreeOf 0 < 4 ∧ (powerSubstitution 4 F).natDegree = 4 ∧
      (∀ a : QuadraticAlgebra (ZMod 2) 1 1, eval ![a, a ^ 4] F = 0) ∧
      ¬(powerSubstitution 4 F).natDegree < S.card * (0 + 1) ∧
      (powerSubstitution 4 F).natDegree < S.card * (1 + 1) ∧
      (∀ a : QuadraticAlgebra (ZMod 2) 1 1, eval ![a, a ^ 4] (pderiv (0 : Fin 2) F) = 1) ∧
      ∃ a ∈ S, ∃ k ≤ 1, eval ![a, a ^ 2 ^ 2] ((pderiv (0 : Fin 2))^[k] F) ≠ 0 := by
  intro S F
  let : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide⟩
  let : CharP (QuadraticAlgebra (ZMod 2) 1 1) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (QuadraticAlgebra (ZMod 2) 1 1)).injective 2
  have hdeg : (powerSubstitution 4 F).natDegree = 4 := by
    simpa [F] using ((Polynomial.natDegree_add_eq_right_of_natDegree_lt
      (p := (Polynomial.X : Polynomial (QuadraticAlgebra (ZMod 2) 1 1))) (q := Polynomial.X ^ 4)
      (by simp)).trans
        (Polynomial.natDegree_X_pow 4))
  have hcard : S.card = 4 := by decide
  have hbound : (powerSubstitution 4 F).natDegree < S.card * (1 + 1) := by omega
  have hZ : F.degreeOf 0 < 4 :=
    (degreeOf_add_le 0 (X 0 : MvPolynomial (Fin 2) (QuadraticAlgebra (ZMod 2) 1 1)) (X 1)).trans_lt
      (by norm_num [degreeOf_X])
  refine ⟨(fun h ↦ (one_ne_zero : (1 : QuadraticAlgebra (ZMod 2) 1 1) ≠ 0)
      (by simpa [F] using congrArg (eval ![(0 : QuadraticAlgebra (ZMod 2) 1 1), 1]) h)),
    hZ, hdeg, ?_, by omega, hbound, by simp [F], ?_⟩
  · simpa [F] using (fun a : QuadraticAlgebra (ZMod 2) 1 1 ↦
      (by decide : ∀ r i : ZMod 2,
        (⟨r, i⟩ : QuadraticAlgebra (ZMod 2) 1 1) + ⟨r, i⟩ ^ 4 = 0) a.re a.im)
  · exact exists_nonzero_ordinary_jet_on_frobenius_graph (p := 2) (e := 2) (by decide)
      (fun h ↦ (one_ne_zero : (1 : QuadraticAlgebra (ZMod 2) 1 1) ≠ 0)
      (by simpa [F] using congrArg (eval ![(0 : QuadraticAlgebra (ZMod 2) 1 1), 1]) h))
      hZ (by decide) hbound

/-- A coefficient outside the prime field gives the same derivative identity over the native
four-element field; no bound on the coefficient field cardinality enters. -/
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

/-- Evaluation of the first jet at `2` uses the translated Hasse weight: both sides are
`4 = 1` in `ZMod 3`, rather than the incorrect value `2`. -/
example :
    (Polynomial.hasseDeriv 1
      (powerSubstitution 3 (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3)))).eval 2 = 1 ∧
      eval ![2, 2 ^ 3] (hasseDeriv (single 0 1)
        (X 0 ^ 2 : MvPolynomial (Fin 2) (ZMod 3))) = 1 := by
  norm_num [Polynomial.hasseDeriv_one', X_pow_eq_monomial, hasseDeriv_monomial,
    eval_monomial, prod_single_index, ← single_tsub]; decide

/-- The order-two Hasse derivative of the weight-five monomial is `X³` in characteristic three.
-/
example :
    Polynomial.hasseDeriv 2
      (powerSubstitution 3 (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) =
        Polynomial.X ^ 3 ∧
      powerSubstitution 3 (hasseDeriv (single 0 2)
        (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) (ZMod 3))) = Polynomial.X ^ 3 := by
  norm_num [X_pow_eq_monomial, X, monomial_pow, monomial_mul_monomial,
    Polynomial.monomial_mul_monomial, Polynomial.X_pow_eq_monomial,
    hasseDeriv_monomial, prod_single_index, ← single_tsub,
    Polynomial.hasseDeriv_monomial, Nat.choose]
  exact congrArg (Polynomial.monomial 3) (by decide)

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
  norm_num [X, monomial_mul_monomial, Polynomial.monomial_mul_monomial,
    Polynomial.X_pow_eq_monomial, hasseDeriv_monomial, prod_single_index,
    Polynomial.hasseDeriv_monomial, Nat.choose]
  exact ⟨congrArg (Polynomial.monomial 4) (by decide), by decide⟩

/-- The running characteristic-three example has first jet `X³ + 1` and zero second jet,
matching the two partial Hasse jets before substitution. -/
example :
    let F : MvPolynomial (Fin 2) (ZMod 3) := X 0 * X 1 + X 0
    powerSubstitution 3 F = Polynomial.X ^ 4 + Polynomial.X ∧
      Polynomial.hasseDeriv 1 (powerSubstitution 3 F) = Polynomial.X ^ 3 + 1 ∧
      Polynomial.hasseDeriv 2 (powerSubstitution 3 F) = 0 ∧
      powerSubstitution 3 (hasseDeriv (single 0 1) F) = Polynomial.X ^ 3 + 1 ∧
      powerSubstitution 3 (hasseDeriv (single 0 2) F) = 0 := by
  norm_num [X, monomial_mul_monomial, Polynomial.monomial_mul_monomial,
    Polynomial.X_pow_eq_monomial, hasseDeriv_monomial, prod_single_index,
    Polynomial.hasseDeriv_monomial, Nat.choose]
  exact ⟨Polynomial.monomial_one_one_eq_X,
    congrArg (Polynomial.monomial 3) (by decide), by decide⟩

end TauCeti.PowerSubstitutionExamples
