/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import TauCeti.NumberTheory.LawrenceSawin.Exceptional.Pair
import Mathlib.Tactic.Linarith

/-!
# Exceptional threefold degrees

For a positive pair `(a, b)`, the binomial coefficient `(a+b).choose a` is six times
`(a+b-2).choose (a-1)` exactly when the Lawrence–Sawin Pell equation holds. Thus
each exceptional pair has a positive normalized degree and representation dimension
six times that degree. See Lawrence and Sawin, *The Shafarevich conjecture for
hypersurfaces in abelian varieties*, Theorem 3.5 and Appendix B.
-/

public section

namespace TauCeti

private theorem choose_mul_endpoints {a b : ℕ} (ha : 0 < a) :
    (a + b).choose a * (a * b) =
      ((a + b) * (a + b - 1)) * (a + b - 2).choose (a - 1) := by
  by_cases hbase : a + b = 1
  · simp [show a = 1 by omega, show b = 0 by omega]
  have h₁ := Nat.add_one_mul_choose_eq (a + b - 1) (a - 1)
  rw [show a + b - 1 + 1 = a + b by omega, show a - 1 + 1 = a by omega] at h₁
  have h₂ := Nat.choose_mul_succ_eq (a + b - 2) (a - 1)
  rw [show a + b - 2 + 1 = a + b - 1 by omega,
    show a + b - 1 - (a - 1) = b by omega] at h₂
  calc
    _ = ((a + b).choose a * a) * b := by rw [Nat.mul_assoc]
    _ = (a + b) * ((a + b - 1).choose (a - 1) * b) := by rw [← h₁, Nat.mul_assoc]
    _ = _ := by rw [← h₂]; ac_rfl

/-- For positive endpoints, the six-to-one binomial ratio is equivalent to the
inhomogeneous Pell equation of Lawrence and Sawin. -/
theorem choose_eq_six_mul_iff_pell {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a + b).choose a = 6 * (a + b - 2).choose (a - 1) ↔
      (a : ℤ) ^ 2 - 4 * a * b + (b : ℤ) ^ 2 = a + b := by
  have hp : 0 < (a + b - 2).choose (a - 1) := Nat.choose_pos (by omega)
  have hratio := choose_mul_endpoints (b := b) ha
  have hsub : (↑(a + b - 1) : ℤ) = a + b - 1 := by omega
  have hprod : (a + b) * (a + b - 1) = 6 * (a * b) ↔
      (a : ℤ) ^ 2 - 4 * a * b + (b : ℤ) ^ 2 = a + b := by
    rw [← Nat.cast_inj (R := ℤ)]
    push_cast
    rw [hsub]
    constructor <;> intro h <;> linarith only [h]
  rw [← hprod]
  constructor
  · intro h
    apply Nat.mul_right_cancel hp
    rw [← hratio, h]
    ac_rfl
  · intro h
    apply Nat.mul_right_cancel (Nat.mul_pos ha hb)
    rw [hratio, h]
    ac_rfl

/-- The normalized threefold degree of the `j`th Lawrence–Sawin pair.
The geometric exception set starts at index one. -/
def exceptionalDegree (j : ℕ) : ℕ :=
  Nat.choose ((exceptionalPair j).1 + (exceptionalPair j).2) (exceptionalPair j).1 / 6

/-- For each exceptional pair, the two binomial coefficients have ratio six. -/
theorem exceptionalPair_choose_eq_six_mul (j : ℕ) :
    ((exceptionalPair j).1 + (exceptionalPair j).2).choose (exceptionalPair j).1 =
      6 * ((exceptionalPair j).1 + (exceptionalPair j).2 - 2).choose
        ((exceptionalPair j).1 - 1) :=
  (choose_eq_six_mul_iff_pell (exceptionalPair_fst_pos j)
    (exceptionalPair_snd_pos j)).2 (exceptionalPair_invariant j)

/-- The degree equals the smaller binomial coefficient, with no division. -/
theorem exceptionalDegree_eq_choose (j : ℕ) :
    exceptionalDegree j =
      ((exceptionalPair j).1 + (exceptionalPair j).2 - 2).choose ((exceptionalPair j).1 - 1) := by
  rw [exceptionalDegree, exceptionalPair_choose_eq_six_mul]
  exact Nat.mul_div_cancel_left _ (by decide)

/-- The representation dimension is six times the normalized degree. -/
theorem six_mul_exceptionalDegree (j : ℕ) :
    6 * exceptionalDegree j =
      ((exceptionalPair j).1 + (exceptionalPair j).2).choose (exceptionalPair j).1 := by
  rw [exceptionalDegree_eq_choose, exceptionalPair_choose_eq_six_mul]

/-- Six divides the representation dimension for every exceptional pair. -/
theorem six_dvd_exceptionalPair_choose (j : ℕ) :
    6 ∣ ((exceptionalPair j).1 + (exceptionalPair j).2).choose (exceptionalPair j).1 :=
  ⟨exceptionalDegree j, (six_mul_exceptionalDegree j).symm⟩

/-- Every normalized degree is positive, including the formal seed degree. -/
theorem exceptionalDegree_pos (j : ℕ) : 0 < exceptionalDegree j := by
  rw [exceptionalDegree_eq_choose]
  have ha := exceptionalPair_fst_pos j
  have hb := exceptionalPair_snd_pos j
  exact Nat.choose_pos (by omega)

/-- The seed contributes degree one at exponent one. -/
theorem exceptionalDegree_zero : exceptionalDegree 0 = 1 := by
  decide

/-- The first geometric exception has normalized degree 8855. -/
theorem exceptionalDegree_one : exceptionalDegree 1 = 8855 := by
  change Nat.choose 25 5 / 6 = 8855
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide

/-- The next exceptional pair `(20, 76)` has the indicated normalized degree. -/
theorem exceptionalDegree_two : exceptionalDegree 2 = 36030431772522503316 := by
  change Nat.choose 96 20 / 6 = 36030431772522503316
  rw [Nat.choose_eq_factorial_div_factorial (by decide)]
  decide

end TauCeti
