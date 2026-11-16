/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.Data.Rat.SquarefreePart
import TauCeti.NumberTheory.SumTwoSquares

/-!
# The rational Hilbert symbol `(-1, ·)_ℚ` and the norm subgroup of `ℚ(i)`

Over a nonarchimedean local field or over `ℝ`, the norm-equation Hilbert symbol
`TauCeti.hilbertSymbol` is bimultiplicative because every quadratic norm subgroup has index
dividing two (`TauCeti.hilbertSymbol_mul_iff_quadraticNormSubgroup_index_dvd_two`). Over a
general field this fails, and `K = ℚ` with `a = -1` gives an elementary counterexample.

For `a = -1`, the norm equation `b = x² - (-1) y² = x² + y²` over `ℚ` is solved by Fermat's
two-square criterion (`Rat.eq_sq_add_sq_iff`): a rational unit `b ∈ ℚˣ` lies in
`TauCeti.quadraticNormSubgroup (-1 : ℚ)` — equivalently, `(-1, b)_ℚ = 1` — if and only if `b > 0`
and `padicValRat p b` is even at every prime `p ≡ 3 (mod 4)`. In particular:

* for a squarefree integer `d`, `(-1, d)_ℚ = 1` if and only if `d > 0` and no prime
  `p ≡ 3 (mod 4)` divides `d`;
* for a prime `p`, `(-1, p)_ℚ = -1` if `p ≡ 3 (mod 4)` and `1` otherwise;
* for any two distinct primes `p, q ≡ 3 (mod 4)` (such as `3` and `7`, with product `21`),
  none of `p`, `q`, or `p q` is a sum of two rational squares, so
  `(-1, p q)_ℚ = -1 ≠ 1 = (-1, p)_ℚ (-1, q)_ℚ`;
* the primes `p ≡ 3 (mod 4)` represent pairwise distinct cosets in
  `ℚˣ ⧸ quadraticNormSubgroup (-1 : ℚ)`, so by Dirichlet's theorem on primes in arithmetic
  progressions the Gaussian norm subgroup has infinite index in `ℚˣ` (`index = 0`), and its
  sign indicator `(-1, ·)_ℚ` is not a homomorphism.

## Main results

* `TauCeti.hilbertSymbol_neg_one_rat_eq_one_iff`,
  `TauCeti.hilbertSymbol_neg_one_rat_eq_neg_one_iff`: exact evaluation criteria for `(-1, b)_ℚ`.
* `TauCeti.mem_quadraticNormSubgroup_neg_one_rat_iff`: Fermat's two-square criterion for
  membership in `quadraticNormSubgroup (-1 : ℚ)`.
* `TauCeti.hilbertSymbol_neg_one_intCast_rat_eq_one_iff_of_squarefree`,
  `TauCeti.hilbertSymbol_neg_one_intCast_rat_eq_neg_one_iff_of_squarefree`: specialization to
  squarefree integers via `Rat.prime_dvd_squarefreePart_iff`.
* `TauCeti.hilbertSymbol_neg_one_natCast_rat_of_prime`: `(-1, p)_ℚ = if p % 4 = 3 then -1 else 1`.
* `TauCeti.hilbertSymbol_neg_one_rat_mul_ne_of_prime_mod_four_eq_three`: failure of
  multiplicativity on every pair of distinct primes `p, q ≡ 3 (mod 4)`.
* `TauCeti.mk_quotient_quadraticNormSubgroup_neg_one_rat_eq_iff`,
  `TauCeti.infinite_quotient_quadraticNormSubgroup_neg_one_rat`,
  `TauCeti.index_quadraticNormSubgroup_neg_one_rat`: the quotient by the Gaussian norm subgroup
  is infinite.
* `TauCeti.not_forall_hilbertSymbol_neg_one_rat_mul_right`: `(-1, ·)_ℚ` is not multiplicative.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Chapter XX
  (sums of two squares).
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, §2 and Chapter VI, §2.
-/

public section

namespace TauCeti

/-! ### The Gaussian rational norm subgroup and `(-1, ·)_ℚ` -/

/-- Over `ℚ`, `(-1, b)_ℚ = 1` if and only if `b` is positive and has even `p`-adic valuation at
every prime `p ≡ 3 (mod 4)`. -/
theorem hilbertSymbol_neg_one_rat_eq_one_iff (b : ℚˣ) :
    hilbertSymbol (-1 : ℚˣ) b = 1 ↔
      0 < (b : ℚ) ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p (b : ℚ)) := by
  rw [hilbertSymbol_eq_one_iff]
  simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, sub_neg_eq_add,
    Rat.eq_sq_add_sq_iff]
  exact and_congr_left fun _ ↦ le_iff_lt_or_eq.trans (or_iff_left b.ne_zero.symm)

/-- A rational unit belongs to `quadraticNormSubgroup (-1 : ℚ)` (that is, is a sum of two rational
squares) if and only if it is positive and has even `p`-adic valuation at every prime
`p ≡ 3 (mod 4)`. -/
theorem mem_quadraticNormSubgroup_neg_one_rat_iff (b : ℚˣ) :
    b ∈ quadraticNormSubgroup (-1 : ℚ) ↔
      0 < (b : ℚ) ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p (b : ℚ)) := by
  have h := hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (-1 : ℚˣ) b
  rw [Units.val_neg, Units.val_one] at h
  exact h.symm.trans (hilbertSymbol_neg_one_rat_eq_one_iff b)

/-- Over `ℚ`, `(-1, b)_ℚ = -1` if and only if `b` is negative or some prime `p ≡ 3 (mod 4)`
divides `b` to an odd power. -/
theorem hilbertSymbol_neg_one_rat_eq_neg_one_iff (b : ℚˣ) :
    hilbertSymbol (-1 : ℚˣ) b = -1 ↔
      (b : ℚ) < 0 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ Odd (padicValRat p (b : ℚ)) := by
  rw [← Int.units_ne_iff_eq_neg, Ne, hilbertSymbol_neg_one_rat_eq_one_iff, not_and_or, not_lt,
    le_iff_lt_or_eq, or_iff_left b.ne_zero]
  push Not
  simp

/-! ### Squarefree integers and primes -/

/-- Over `ℚ`, for a squarefree integer `d`, `(-1, d)_ℚ = 1` if and only if `d` is positive and no
prime `p ≡ 3 (mod 4)` divides `d`. -/
theorem hilbertSymbol_neg_one_intCast_rat_eq_one_iff_of_squarefree {d : ℤ} (hd : Squarefree d) :
    hilbertSymbol (-1 : ℚˣ) (Units.mk0 (d : ℚ) (Int.cast_ne_zero.mpr hd.ne_zero)) = 1 ↔
      0 < d ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p % 4 ≠ 3 := by
  rw [hilbertSymbol_neg_one_rat_eq_one_iff, Units.val_mk0, Int.cast_pos]
  refine and_congr_right fun _ ↦ forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  rw [← Int.not_odd_iff_even,
    ← Rat.prime_dvd_squarefreePart_iff (Int.cast_ne_zero.mpr hd.ne_zero),
    Rat.squarefreePart_intCast_of_squarefree hd]
  tauto

/-- Over `ℚ`, for a squarefree integer `d`, `(-1, d)_ℚ = -1` if and only if `d` is negative or
some prime `p ≡ 3 (mod 4)` divides `d`. -/
theorem hilbertSymbol_neg_one_intCast_rat_eq_neg_one_iff_of_squarefree {d : ℤ}
    (hd : Squarefree d) :
    hilbertSymbol (-1 : ℚˣ) (Units.mk0 (d : ℚ) (Int.cast_ne_zero.mpr hd.ne_zero)) = -1 ↔
      d < 0 ∨ ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ d ∧ p % 4 = 3 := by
  rw [← Int.units_ne_iff_eq_neg, Ne,
    hilbertSymbol_neg_one_intCast_rat_eq_one_iff_of_squarefree hd,
    not_and_or, not_lt, le_iff_lt_or_eq, or_iff_left hd.ne_zero]
  push Not
  rfl

/-- Over `ℚ`, for every prime `p`, `(-1, p)_ℚ` is `-1` when `p ≡ 3 (mod 4)` and `1` otherwise. -/
theorem hilbertSymbol_neg_one_natCast_rat_of_prime {p : ℕ} (hp : p.Prime) :
    hilbertSymbol (-1 : ℚˣ) (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) =
      if p % 4 = 3 then -1 else 1 := by
  have hsf : Squarefree (p : ℤ) := (Nat.prime_iff_prime_int.mp hp).squarefree
  have hu : Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) =
      Units.mk0 ((p : ℤ) : ℚ) (Int.cast_ne_zero.mpr hsf.ne_zero) := Units.ext (by simp)
  rw [hu]
  split_ifs with hp4
  · exact (hilbertSymbol_neg_one_intCast_rat_eq_neg_one_iff_of_squarefree hsf).mpr
      (Or.inr ⟨p, hp, dvd_rfl, hp4⟩)
  · refine (hilbertSymbol_neg_one_intCast_rat_eq_one_iff_of_squarefree hsf).mpr
      ⟨Int.natCast_pos.mpr hp.pos, fun q hq hqp ↦ ?_⟩
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (Int.natCast_dvd_natCast.mp hqp)
    exact hqeq ▸ hp4

/-- For any two distinct primes `p, q ≡ 3 (mod 4)`, the rational Hilbert symbol `(-1, ·)_ℚ` fails
to be multiplicative on `p` and `q`: `(-1, p * q)_ℚ ≠ (-1, p)_ℚ * (-1, q)_ℚ`. -/
theorem hilbertSymbol_neg_one_rat_mul_ne_of_prime_mod_four_eq_three {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp4 : p % 4 = 3) (hq4 : q % 4 = 3) :
    hilbertSymbol (-1 : ℚˣ)
        (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) *
          Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero)) ≠
      hilbertSymbol (-1 : ℚˣ) (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)) *
        hilbertSymbol (-1 : ℚˣ) (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero)) := by
  have hp_sym := hilbertSymbol_neg_one_natCast_rat_of_prime hp
  have hq_sym := hilbertSymbol_neg_one_natCast_rat_of_prime hq
  rw [ite_eq_left hp4] at hp_sym
  rw [ite_eq_left hq4] at hq_sym
  have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr fun h ↦
    hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hsf : Squarefree ((p * q : ℕ) : ℤ) :=
    Int.squarefree_natCast.mpr ((Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hq.squarefree⟩)
  have hmul :
      Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) *
          Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero) =
        Units.mk0 (((p * q : ℕ) : ℤ) : ℚ) (Int.cast_ne_zero.mpr hsf.ne_zero) :=
    Units.ext (by simp)
  have hpq_sym : hilbertSymbol (-1 : ℚˣ)
      (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero) *
        Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero)) = -1 := by
    rw [hmul, hilbertSymbol_neg_one_intCast_rat_eq_neg_one_iff_of_squarefree hsf]
    exact Or.inr ⟨p, hp, by simp, hp4⟩
  rw [hp_sym, hq_sym, hpq_sym]
  decide

/-! ### Infinite norm index and failure of bimultiplicativity -/

/-- Two rational units lie in the same coset of `quadraticNormSubgroup (-1 : ℚ)` if and only if
their quotient is positive and their `p`-adic valuations have the same parity at every prime
`p ≡ 3 (mod 4)`. -/
theorem mk_quotient_quadraticNormSubgroup_neg_one_rat_eq_iff (a b : ℚˣ) :
    (QuotientGroup.mk a : ℚˣ ⧸ quadraticNormSubgroup (-1 : ℚ)) = QuotientGroup.mk b ↔
      0 < (a : ℚ) / (b : ℚ) ∧
        ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (padicValRat p (a : ℚ) - padicValRat p (b : ℚ)) := by
  rw [QuotientGroup.eq_iff_div_mem, mem_quadraticNormSubgroup_neg_one_rat_iff,
    Units.val_div_eq_div_val]
  refine and_congr_right fun _ ↦ forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.div a.ne_zero b.ne_zero]

/-- The quotient `ℚˣ ⧸ quadraticNormSubgroup (-1 : ℚ)` is infinite, so the Gaussian norm subgroup
has infinite index in `ℚˣ`. -/
theorem infinite_quotient_quadraticNormSubgroup_neg_one_rat :
    Infinite (ℚˣ ⧸ quadraticNormSubgroup (-1 : ℚ)) := by
  have hinf : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    convert Nat.infinite_setOfPred_prime_and_modEq (q := 4) (a := 3)
      (by decide) (by decide) using 1
    ext p
    simp [Nat.ModEq]
  have : Infinite {p : ℕ // p.Prime ∧ p % 4 = 3} := hinf.to_subtype
  let f : {p : ℕ // p.Prime ∧ p % 4 = 3} → ℚˣ ⧸ quadraticNormSubgroup (-1 : ℚ) :=
    fun p ↦ QuotientGroup.mk (Units.mk0 (p.1 : ℚ) (Nat.cast_ne_zero.mpr p.2.1.ne_zero))
  refine Infinite.of_injective f fun p q hpq ↦ ?_
  by_contra hne
  have hne' : p.1 ≠ q.1 := fun h ↦ hne (Subtype.ext h)
  have heven := ((mk_quotient_quadraticNormSubgroup_neg_one_rat_eq_iff _ _).mp hpq).2
    p.1 p.2.1 p.2.2
  have : Fact p.1.Prime := ⟨p.2.1⟩
  have hv1 : padicValRat p.1 (p.1 : ℚ) = 1 := padicValRat.self p.2.1.one_lt
  have hndvd : ¬p.1 ∣ q.1 := fun h ↦ hne' ((Nat.prime_dvd_prime_iff_eq p.2.1 q.2.1).mp h)
  have hv2 : padicValRat p.1 (q.1 : ℚ) = 0 := by
    rw [padicValRat.of_nat, multiplicity_eq_zero_of_not_dvd hndvd, Nat.cast_zero]
  simp only [Units.val_mk0, hv1, hv2, sub_zero] at heven
  exact Int.not_even_one heven

/-- The `Subgroup.index` of `quadraticNormSubgroup (-1 : ℚ)` in `ℚˣ` is `0` (infinite index). -/
@[simp]
theorem index_quadraticNormSubgroup_neg_one_rat :
    (quadraticNormSubgroup (-1 : ℚ)).index = 0 :=
  Subgroup.index_eq_zero_iff_infinite.mpr infinite_quotient_quadraticNormSubgroup_neg_one_rat

/-- The rational Hilbert symbol `(-1, ·)_ℚ` is not multiplicative in its second argument. -/
theorem not_forall_hilbertSymbol_neg_one_rat_mul_right :
    ¬∀ b c : ℚˣ,
      hilbertSymbol (-1 : ℚˣ) (b * c) = hilbertSymbol (-1 : ℚˣ) b * hilbertSymbol (-1 : ℚˣ) c :=
  fun h ↦ hilbertSymbol_neg_one_rat_mul_ne_of_prime_mod_four_eq_three
    Nat.prime_three (by decide : Nat.Prime 7) (by decide) rfl rfl (h _ _)

/-! ### Worked examples: `3`, `7`, and `21` -/

/-- `3` is not a sum of two rational squares, so `(-1, 3)_ℚ = -1`. -/
example : hilbertSymbol (-1 : ℚˣ) (Units.mk0 (3 : ℚ) (by norm_num)) = -1 := by
  have hu : Units.mk0 (3 : ℚ) (by norm_num) =
      Units.mk0 ((3 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr Nat.prime_three.ne_zero) :=
    Units.ext (by norm_num)
  rw [hu, hilbertSymbol_neg_one_natCast_rat_of_prime Nat.prime_three]
  decide

/-- `7` is not a sum of two rational squares, so `(-1, 7)_ℚ = -1`. -/
example : hilbertSymbol (-1 : ℚˣ) (Units.mk0 (7 : ℚ) (by norm_num)) = -1 := by
  have h7 : Nat.Prime 7 := by decide
  have hu : Units.mk0 (7 : ℚ) (by norm_num) =
      Units.mk0 ((7 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr h7.ne_zero) :=
    Units.ext (by norm_num)
  rw [hu, hilbertSymbol_neg_one_natCast_rat_of_prime h7]
  decide

/-- `21 = 3 · 7` is not a sum of two rational squares either, so `(-1, 21)_ℚ = -1`. -/
example : hilbertSymbol (-1 : ℚˣ) (Units.mk0 (21 : ℚ) (by norm_num)) = -1 := by
  have hsf : Squarefree (21 : ℤ) :=
    Int.squarefree_natCast.mpr
      ((Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).mpr
        ⟨Nat.prime_three.squarefree, (by decide : Nat.Prime 7).squarefree⟩)
  have hu : Units.mk0 (21 : ℚ) (by norm_num) =
      Units.mk0 ((21 : ℤ) : ℚ) (Int.cast_ne_zero.mpr hsf.ne_zero) :=
    Units.ext (by norm_num)
  rw [hu, hilbertSymbol_neg_one_intCast_rat_eq_neg_one_iff_of_squarefree hsf]
  exact Or.inr ⟨3, Nat.prime_three, by decide, rfl⟩

/-- At `3` and `7`, `(-1, 3 · 7)_ℚ ≠ (-1, 3)_ℚ (-1, 7)_ℚ`: the sign indicator of the Gaussian
norm subgroup is not a homomorphism. -/
example :
    hilbertSymbol (-1 : ℚˣ)
        (Units.mk0 (3 : ℚ) (by norm_num) * Units.mk0 (7 : ℚ) (by norm_num)) ≠
      hilbertSymbol (-1 : ℚˣ) (Units.mk0 (3 : ℚ) (by norm_num)) *
        hilbertSymbol (-1 : ℚˣ) (Units.mk0 (7 : ℚ) (by norm_num)) := by
  have h7 : Nat.Prime 7 := by decide
  have hu3 : Units.mk0 (3 : ℚ) (by norm_num) =
      Units.mk0 ((3 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr Nat.prime_three.ne_zero) :=
    Units.ext (by norm_num)
  have hu7 : Units.mk0 (7 : ℚ) (by norm_num) =
      Units.mk0 ((7 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr h7.ne_zero) :=
    Units.ext (by norm_num)
  rw [hu3, hu7]
  exact hilbertSymbol_neg_one_rat_mul_ne_of_prime_mod_four_eq_three
    Nat.prime_three h7 (by decide) rfl rfl

/-- The sign indicator of `quadraticNormSubgroup (-1 : ℚ)` is not multiplicative, and the index of
that subgroup does not divide `2`. -/
example :
    (¬∀ b c : ℚˣ,
        (quadraticNormSubgroup (-1 : ℚ)).signIndicator (b * c) =
          (quadraticNormSubgroup (-1 : ℚ)).signIndicator b *
            (quadraticNormSubgroup (-1 : ℚ)).signIndicator c) ∧
      ¬((quadraticNormSubgroup (-1 : ℚ)).index ∣ 2) := by
  refine ⟨fun h ↦ not_forall_hilbertSymbol_neg_one_rat_mul_right fun b c ↦ ?_, by simp⟩
  simp only [hilbertSymbol_eq_signIndicator, Units.val_neg, Units.val_one]
  exact h b c

/-- Bimultiplicativity of the Hilbert symbol fails over `ℚ`, both on units and on square
classes. -/
example :
    (¬∀ a b c : ℚˣ, hilbertSymbol a (b * c) = hilbertSymbol a b * hilbertSymbol a c) ∧
      ¬∀ x y z : SquareClassGroup ℚ,
        hilbertSymbolOnSquareClasses x (y + z) =
          hilbertSymbolOnSquareClasses x y * hilbertSymbolOnSquareClasses x z := by
  refine ⟨fun h ↦ not_forall_hilbertSymbol_neg_one_rat_mul_right (h (-1)), fun h ↦ ?_⟩
  refine not_forall_hilbertSymbol_neg_one_rat_mul_right fun b c ↦ ?_
  have h' := h (squareClass (-1)) (squareClass b) (squareClass c)
  rwa [← squareClass_mul, hilbertSymbolOnSquareClasses_squareClass,
    hilbertSymbolOnSquareClasses_squareClass, hilbertSymbolOnSquareClasses_squareClass] at h'

end TauCeti
