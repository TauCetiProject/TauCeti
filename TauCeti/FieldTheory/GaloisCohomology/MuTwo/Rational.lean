/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.Multiquadratic.Prime.Radicands

/-!
# Rational Kummer classes

The Kummer isomorphism identifies `H¹(G_ℚ, 𝔽₂)` with rational square classes. This file
computes with that identification on the canonical continuous-cohomology carrier: two units
give the same class exactly when their product is nonnegative and every prime valuation of
that product is even. Every class has a squarefree integer representative, and classes of
distinct rational primes form a linearly independent family.

The class of a prime is represented by the continuous square-root character: its value at
`g` is zero when `g` fixes a chosen square root, and one otherwise. This normalization is
`kummerCocycleModTwo_apply`; its canonical class is identified by
`kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq`. The computations here in particular show
that these classes are nonzero over a genuinely infinite profinite Galois group.

The arithmetic inputs are Mathlib's `Rat.isSquare_iff_even_factorization`, the squarefree
decomposition `Rat.exists_squarefree_int_mul_sq`, and the distinct-prime square-class
independence theorem `TauCeti.Multiquadratic.not_isSquare_prod_primes_of_injective`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1), and the Kummer isomorphism following it.
-/

public noncomputable section

namespace TauCeti

/-- Rational units give the same Kummer class exactly when their product is nonnegative
and all its prime valuations are even. Negative valuations are allowed. -/
theorem kummerClass_eq_kummerClass_iff_nonneg_and_even_padicValRat (a b : ℚˣ) :
    kummerClass a = kummerClass b ↔
      0 ≤ (a : ℚ) * b ∧ ∀ p : ℕ, p.Prime → Even (padicValRat p ((a : ℚ) * b)) := by
  rw [kummerClass_eq_kummerClass_iff_isSquare_mul, ← isSquare_units_val_iff,
    Units.val_mul, Rat.isSquare_iff_even_factorization]

/-- Every mod-two continuous cohomology class of the absolute Galois group of `ℚ` is the
Kummer class of a nonzero squarefree integer, including the zero class represented by `1`. -/
theorem exists_squarefree_int_kummerClass
    (x : cohomF2 (AbsoluteGaloisGroup ℚ) 1) :
    ∃ (d : ℤ) (hd : (d : ℚ) ≠ 0), Squarefree d ∧
      kummerClass (Units.mk0 (d : ℚ) hd) = x := by
  let a := Additive.toMul (Quotient.out ((kummerSquareClassEquiv ℚ).symm x))
  have ha : kummerClass a = x := by
    rw [← kummerSquareClassEquiv_squareClass]
    simp [a]
  obtain ⟨d, c, hd, hc, hdec⟩ := Rat.exists_squarefree_int_mul_sq a.ne_zero
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  let u := Units.mk0 (d : ℚ) hd0
  let v := Units.mk0 c hc
  have huv : a = u * v ^ 2 := Units.ext (by simpa [u, v] using hdec)
  have hv : kummerClass (v ^ 2) = 0 :=
    (kummerClass_eq_zero_iff_square ℚ).2 (Subgroup.mem_square.2 ⟨v, pow_two v⟩)
  refine ⟨d, hd0, hd, ?_⟩
  simpa only [huv, kummerClass_mul, hv, add_zero] using ha

/-- The Kummer classes of any injective family of rational primes are linearly independent
over `𝔽₂`. The indexing type may be infinite. -/
theorem linearIndependent_kummerClass_rat_primes {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent (ZMod 2)
      (fun i ↦ kummerClass (Units.mk0 (p i : ℚ) (Nat.cast_ne_zero.mpr (hp i).ne_zero))) := by
  classical
  rw [linearIndependent_kummerClass_iff]
  intro T hT hsq
  have hval := isSquare_units_val_iff.2 hsq
  simp only [Units.coe_prod, Units.val_mk0] at hval
  exact Multiquadratic.not_isSquare_prod_primes_of_injective
    p hp hinj T hT hval

/-- The classes of `2` and `3` are independent; in particular the square-root characters
of `ℚ(√2)` and `ℚ(√3)` give two independent continuous cohomology classes. -/
theorem linearIndependent_kummerClass_two_three : LinearIndependent (ZMod 2)
    (fun i : Fin 2 ↦ kummerClass
      (Units.mk0 ((![2, 3] : Fin 2 → ℕ) i : ℚ) (by fin_cases i <;> norm_num))) := by
  apply linearIndependent_kummerClass_rat_primes
  · intro i
    fin_cases i
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

end TauCeti
