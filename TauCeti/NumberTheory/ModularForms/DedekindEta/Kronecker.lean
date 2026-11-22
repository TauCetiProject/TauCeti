/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Ring.Int.Parity
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.Data.Int.MulPred
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.LegendreSymbol.ZModChar

/-!
# The Kronecker-symbol form of the eta multiplier

`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation` defines the eta multiplier
`ε(γ) = TauCeti.ModularForm.etaMultiplier γ`, the 24th root of unity with
`η(γ τ) = ε(γ) √(c τ + d) η(τ)` on the upper half-plane for the principal square root, and
evaluates it through the Dedekind sum `s(d, c)`. That value does not exhibit the quadratic
character hidden in `ε`. This file proves the **Kronecker-symbol form** of the multiplier: for
`γ = (a b; c d) ∈ SL(2, ℤ)` and `e(x) = exp(2 π i x)`,

* if `c` is odd, `ε(γ) = (d / |c|) · e(((a + d) c - b d (c² - 1) - 3 c) / 24)` (where `|c| = c`
  for `c ≥ 0`, and `(d / c)` itself needs `c > 0` since at `γ = (-1 0; -1 -1)` its right side
  is `-ε(γ)`);
* if `c` is even, `ε(γ) = (c / d) · e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`,

where `(· / ·)` is the Kronecker symbol `TauCeti.kroneckerSym`. For odd `c > 0` the symbol `(d / c)`
is the Jacobi symbol at `c`; for even `c` the entry `d` is odd, possibly negative. The even formula
holds for every even `c`, including `c < 0` and `c = 0`. This form, rather than the Dedekind-sum
value, is what reads off the quadratic character of an eta quotient on `Γ₀(N)`.

## Implementation notes

Both sides are compared through the generator laws of `ε`, without Dedekind sums.
For odd `c > 0` we argue by strong induction on `c`. A translation `γ Tⁿ` multiplies `ε` by
`e(n / 24)` and moves `d` to an odd representative `d'` of its class modulo `c` with `|d'| < c`;
the Kronecker form changes by the same factor, since `(c n + d / c) = (d / c)` and
`24 ∣ c (c² - 1)`. Then the inversion `γ S = (b -a; d -c)` (for `d > 0`) or
`-(γ S) = (-b a; -d c)` (for `d < 0`) has odd lower-left entry `|d| < c`, and multiplies `ε` by
`e(∓1/8)`. On the Kronecker side the two symbols are related by quadratic reciprocity and its first
supplement. At `c = 1` both sides are `e((a + d) / 24 - 1 / 8)`. For even `c > 0` a single
inversion reaches the odd case; `c < 0` reduces to `-γ`, where `ε(γ) = i ε(-γ)`, and `c = 0` is
`γ = ± Tᵇ`. Each step leaves a congruence modulo `24` between polynomials in the entries, subject
to `a d - b c = 1`; these are checked modulo `8` and modulo `3` by evaluation. For odd `c < 0`,
reducing to `-γ` via `etaMultiplier_neg_of_c_neg` introduces a sign factor `χ₄` from negating the
Kronecker symbol that cancels the `-6 c` numerator shift, giving the `(d / |c|)` formula on all odd
`c`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c`: the Kronecker form
  for odd `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_even_c`: the Kronecker form for even
  `c`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c`: the Kronecker form with
  `(d / |c|)` for every odd `c` (positive or negative).
* `TauCeti.ModularForm.etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg`,
  `TauCeti.ModularForm.etaMultiplier_eq_ite_kroneckerSym_mul_cexp`: unified Kronecker-symbol
  formula for `c ≥ 0` and on all of `SL(2, ℤ)`.
* `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six`,
  `TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_isCoprime_c_six`:
  simplified formula `ε(γ) = (d / |c|) e^{π i (a + d - 3) c / 12}` when `c` is prime to `6`.

## References

* F. Strömberg, *Computation of Maass waveforms with non-trivial multiplier systems*,
  Math. Comp. 77 (2008), 2375–2416 (arXiv:math/0611146, 2006), Remark 2.5, equation (2.5).
* H. Rademacher, *Zur Theorie der Modulfunktionen*, J. Reine Angew. Math. 167 (1932), 312–336.
* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., Theorem 3.4,
  for the Euclidean-algorithm induction on `c`.
-/

public section

open Complex ModularGroup TauCeti.ModularGroup ZMod
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Twenty-fourth roots of unity -/

/-- `e(m / 24) = exp(2 π i m / 24)`. -/
private noncomputable def e24 (m : ℤ) : ℂ :=
  cexp (2 * π * I * m / 24)

private theorem e24_add (m n : ℤ) : e24 (m + n) = e24 m * e24 n := by
  simp only [e24, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem e24_ne_zero (m : ℤ) : e24 m ≠ 0 :=
  Complex.exp_ne_zero _

private theorem e24_congr {m n : ℤ} (h : m ≡ n [ZMOD 24]) : e24 m = e24 n := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  rw [show n = m + 24 * k by omega, e24_add]
  have h1 : e24 (24 * k) = 1 := by
    rw [e24, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    ring
  rw [h1, mul_one]

private theorem e24_twelve_mul (k : ℕ) : e24 (12 * k) = (-1) ^ k := by
  rw [e24, ← Complex.exp_pi_mul_I, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  ring

private theorem e24_neg_three : e24 (-3) = cexp (-(π * I / 4)) := by
  rw [e24]
  congr 1
  push_cast
  ring

private theorem e24_six : e24 6 = I := by
  rw [e24, show 2 * π * I * ((6 : ℤ) : ℂ) / 24 = π / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]

private theorem e24_neg_six : e24 (-6) = -I := by
  rw [e24_congr (show (-6 : ℤ) ≡ 12 * (1 : ℕ) + 6 [ZMOD 24] by decide), e24_add, e24_twelve_mul,
    e24_six, pow_one, neg_one_mul]

/-! ### Congruences modulo `24` -/

/-- The exponent of the Kronecker form for odd `c`. -/
private def oddExp {R : Type*} [CommRing R] (a b c d : R) : R :=
  (a + d) * c - b * d * (c ^ 2 - 1) - 3 * c

/-- The exponent of the Kronecker form for even `c`. -/
private def evenExp {R : Type*} [CommRing R] (a b c d : R) : R :=
  (a + d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3 - 3 * c * d

private theorem intCast_oddExp {R : Type*} [CommRing R] (a b c d : ℤ) :
    ((oddExp a b c d : ℤ) : R) = oddExp (a : R) b c d := by
  simp [oddExp]

private theorem intCast_evenExp {R : Type*} [CommRing R] (a b c d : ℤ) :
    ((evenExp a b c d : ℤ) : R) = evenExp (a : R) b c d := by
  simp [evenExp]

private theorem modEq_twentyFour {x y : ℤ} (h8 : (x : ZMod 8) = y) (h3 : (x : ZMod 3) = y) :
    x ≡ y [ZMOD 24] := by
  have h := (Int.modEq_and_modEq_iff_modEq_mul (m := 8) (n := 3) (by decide)).mp
    ⟨(ZMod.intCast_eq_intCast_iff _ _ 8).mp h8, (ZMod.intCast_eq_intCast_iff _ _ 3).mp h3⟩
  norm_num at h
  exact h

-- Each inversion step below is a congruence modulo `8` or `3` between polynomials in four
-- integer variables, subject to the determinant identity `hdet`. This local tactic casts `hdet`
-- to `ZMod n`, generalizes the four variables and checks every residue.
local macro "decide_zmod " n:num hdet:ident a:ident b:ident c:ident d:ident : tactic =>
  `(tactic| (
    have h := congrArg (Int.cast : ℤ → ZMod $n) $hdet
    push_cast at h
    generalize ($a : ZMod $n) = A, ($b : ZMod $n) = B, ($c : ZMod $n) = C, ($d : ZMod $n) = D
      at h ⊢
    revert A B C D
    decide +kernel))

/-- The translation step: replacing `(b, d)` by `(a n + b, c n + d)` adds `n` to the exponent. -/
private theorem oddExp_translate_modEq {a b c d : ℤ} (n : ℤ) (hdet : a * d - b * c = 1)
    (hc : Odd c) : oddExp a (a * n + b) c (c * n + d) ≡ n + oddExp a b c d [ZMOD 24] := by
  obtain ⟨k, hk⟩ := Int.twentyFour_dvd_mul_sq_sub_one_of_odd hc
  refine Int.modEq_iff_dvd.mpr ⟨k * n * (a * n + 2 * b), ?_⟩
  simp only [oddExp]
  linear_combination (n * (a * n + 2 * b)) * hk + ((c ^ 2 - 1) * n) * hdet

/-- The inversion step for odd `c` and `d > 0`. -/
private theorem oddExp_inversion_modEq {a b u v : ℤ}
    (hdet : a * (2 * v + 1) - b * (2 * u + 1) = 1) :
    3 + 12 * v + 12 * (u * v) + oddExp b (-a) (2 * v + 1) (-(2 * u + 1)) ≡
      oddExp a b (2 * u + 1) (2 * v + 1) [ZMOD 24] := by
  refine modEq_twentyFour ?_ ?_ <;> push_cast [intCast_oddExp]
  · decide_zmod 8 hdet a b u v
  · decide_zmod 3 hdet a b u v

/-- The inversion step for odd `c` and `d < 0`. -/
private theorem oddExp_neg_inversion_modEq {a b u w : ℤ}
    (hdet : a * -(2 * w + 1) - b * (2 * u + 1) = 1) :
    -3 + oddExp (-b) a (2 * w + 1) (2 * u + 1) ≡
      12 * u + 12 * (w * u) + oddExp a b (2 * u + 1) (-(2 * w + 1)) [ZMOD 24] := by
  refine modEq_twentyFour ?_ ?_ <;> push_cast [intCast_oddExp]
  · decide_zmod 8 hdet a b u w
  · decide_zmod 3 hdet a b u w

/-- The inversion step for even `c` and `d > 0`. -/
private theorem evenExp_inversion_modEq {a b m v : ℤ}
    (hdet : a * (2 * v + 1) - b * (2 * m) = 1) :
    3 + 12 * v + oddExp b (-a) (2 * v + 1) (-(2 * m)) ≡
      evenExp a b (2 * m) (2 * v + 1) [ZMOD 24] := by
  refine modEq_twentyFour ?_ ?_ <;> push_cast [intCast_oddExp, intCast_evenExp]
  · decide_zmod 8 hdet a b m v
  · decide_zmod 3 hdet a b m v

/-- The inversion step for even `c` and `d < 0`. -/
private theorem evenExp_neg_inversion_modEq {a b m w : ℤ}
    (hdet : a * -(2 * w + 1) - b * (2 * m) = 1) :
    -3 + oddExp (-b) a (2 * w + 1) (2 * m) ≡ evenExp a b (2 * m) (-(2 * w + 1)) [ZMOD 24] := by
  refine modEq_twentyFour ?_ ?_ <;> push_cast [intCast_oddExp, intCast_evenExp]
  · decide_zmod 8 hdet a b m w
  · decide_zmod 3 hdet a b m w

/-! ### The steps on the Kronecker side -/

/-- The translation step for odd `c`: replacing `(b, d)` by `(a n + b, c n + d)` multiplies the
Kronecker form by `e(n / 24)`. -/
private theorem kroneckerOdd_translate {a b c d : ℤ} (n : ℤ) (hdet : a * d - b * c = 1)
    (hc : 0 < c) (hodd : Odd c) :
    (kroneckerSym (c * n + d) c : ℂ) * e24 (oddExp a (a * n + b) c (c * n + d)) =
      e24 n * (kroneckerSym d c * e24 (oddExp a b c d)) := by
  have hsym : kroneckerSym (c * n + d) c = kroneckerSym d c := by
    lift c to ℕ using hc.le
    have hodd' : Odd c := (Int.odd_natCast c).mp hodd
    rw [kroneckerSym_eq_jacobiSym _ hodd', kroneckerSym_eq_jacobiSym _ hodd']
    exact jacobiSym.mod_left' (Int.mul_add_emod_self_left _ _ _)
  rw [hsym, e24_congr (oddExp_translate_modEq n hdet hodd), e24_add]
  ring

/-- Quadratic reciprocity and its first supplement in `e24` form: for `c = 2 u + 1` and
`d = 2 v + 1`, `(-c / d) = e((12 v + 12 u v) / 24) · (d / c)`. -/
private theorem jacobiSym_neg_eq_e24_mul (u v : ℕ) :
    (jacobiSym (-((2 * u + 1 : ℕ) : ℤ)) (2 * v + 1) : ℂ) =
      e24 (12 * v) * e24 (12 * (u * v)) * jacobiSym ((2 * v + 1 : ℕ) : ℤ) (2 * u + 1) := by
  have hc : Odd (2 * u + 1) := odd_two_mul_add_one u
  have hd : Odd (2 * v + 1) := odd_two_mul_add_one v
  rw [jacobiSym.neg _ hd, jacobiSym.quadratic_reciprocity hc hd, ZMod.χ₄_two_mul_add_one,
    show (2 * u + 1) / 2 = u by omega, show (2 * v + 1) / 2 = v by omega, ← Nat.cast_mul,
    e24_twelve_mul, e24_twelve_mul]
  push_cast
  ring

/-- The inversion step for odd `c` and `d > 0`, by quadratic reciprocity and its first
supplement. -/
private theorem kroneckerOdd_inversion {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : 0 < c)
    (hd : 0 < d) (hco : Odd c) (hdo : Odd d) :
    e24 3 * ((kroneckerSym (-c) d : ℂ) * e24 (oddExp b (-a) d (-c))) =
      kroneckerSym d c * e24 (oddExp a b c d) := by
  lift c to ℕ using hc.le
  lift d to ℕ using hd.le
  have hco' : Odd c := (Int.odd_natCast c).mp hco
  have hdo' : Odd d := (Int.odd_natCast d).mp hdo
  rw [kroneckerSym_eq_jacobiSym _ hdo', kroneckerSym_eq_jacobiSym _ hco']
  obtain ⟨u, rfl⟩ := hco'
  obtain ⟨v, rfl⟩ := hdo'
  rw [jacobiSym_neg_eq_e24_mul]
  push_cast at hdet ⊢
  have key := e24_congr (oddExp_inversion_modEq hdet)
  simp only [e24_add] at key
  linear_combination (jacobiSym (2 * v + 1) (2 * u + 1) : ℂ) * key

/-- The inversion step for odd `c` and `d < 0`, by quadratic reciprocity and its first
supplement. -/
private theorem kroneckerOdd_neg_inversion {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : 0 < c)
    (hd : d < 0) (hco : Odd c) (hdo : Odd d) :
    e24 (-3) * ((kroneckerSym c (-d) : ℂ) * e24 (oddExp (-b) a (-d) c)) =
      kroneckerSym d c * e24 (oddExp a b c d) := by
  lift c to ℕ using hc.le
  obtain ⟨d, rfl⟩ : ∃ d' : ℕ, d = -d' := ⟨d.natAbs, by omega⟩
  have hco' : Odd c := (Int.odd_natCast c).mp hco
  have hdo' : Odd d := (Int.odd_natCast d).mp (odd_neg.mp hdo)
  rw [neg_neg, kroneckerSym_eq_jacobiSym _ hdo', kroneckerSym_eq_jacobiSym _ hco']
  obtain ⟨u, rfl⟩ := hco'
  obtain ⟨w, rfl⟩ := hdo'
  rw [jacobiSym_neg_eq_e24_mul]
  push_cast at hdet ⊢
  have key := e24_congr (oddExp_neg_inversion_modEq hdet)
  simp only [e24_add] at key
  linear_combination (jacobiSym (2 * u + 1) (2 * w + 1) : ℂ) * key

/-- The inversion step for even `c` and `d > 0`, by the first supplement. -/
private theorem kroneckerEven_inversion {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : 0 < c)
    (hd : 0 < d) (hce : Even c) (hdo : Odd d) :
    e24 3 * ((kroneckerSym (-c) d : ℂ) * e24 (oddExp b (-a) d (-c))) =
      kroneckerSym c d * e24 (evenExp a b c d) := by
  lift d to ℕ using hd.le
  have hdo' : Odd d := (Int.odd_natCast d).mp hdo
  rw [kroneckerSym_eq_jacobiSym _ hdo', kroneckerSym_eq_jacobiSym _ hdo', jacobiSym.neg _ hdo']
  obtain ⟨m, rfl⟩ := hce
  obtain ⟨v, rfl⟩ := hdo'
  rw [ZMod.χ₄_two_mul_add_one, ← two_mul]
  rw [← two_mul] at hdet
  push_cast at hdet ⊢
  have key := e24_congr (evenExp_inversion_modEq hdet)
  simp only [e24_add] at key
  rw [← e24_twelve_mul]
  linear_combination (jacobiSym (2 * m) (2 * v + 1) : ℂ) * key

/-- The inversion step for even `c` and `d < 0`: here `(c / -d) = (c / d)` since `c > 0`. -/
private theorem kroneckerEven_neg_inversion {a b c d : ℤ} (hdet : a * d - b * c = 1) (hc : 0 < c)
    (hd : d < 0) (hce : Even c) (hdo : Odd d) :
    e24 (-3) * ((kroneckerSym c (-d) : ℂ) * e24 (oddExp (-b) a (-d) c)) =
      kroneckerSym c d * e24 (evenExp a b c d) := by
  have hsym : kroneckerSym c (-d) = kroneckerSym c d := by
    rw [kroneckerSym_of_odd _ hdo.neg, kroneckerSym_of_odd _ hdo, Int.natAbs_neg]
    simp [hc.not_gt]
  rw [hsym]
  obtain ⟨d, rfl⟩ : ∃ d' : ℤ, d = -d' := ⟨-d, by omega⟩
  obtain ⟨w, rfl⟩ := odd_neg.mp hdo
  obtain ⟨m, rfl⟩ := hce
  rw [neg_neg, ← two_mul]
  rw [← two_mul] at hdet
  have key := e24_congr (evenExp_neg_inversion_modEq hdet)
  simp only [e24_add] at key
  linear_combination (kroneckerSym (2 * m) (-(2 * w + 1)) : ℂ) * key

/-- The first supplement at an odd `d` of either sign: `(-1 / |d|) · e((6 - 6 d) / 24)` is the
sign `-1` for `d < 0` and `1` for `d > 0`. -/
private theorem χ₄_natAbs_mul_e24 {d : ℤ} (hdo : Odd d) :
    (ZMod.χ₄ (d.natAbs : ZMod 4) : ℂ) * e24 (6 - 6 * d) = if d < 0 then -1 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
  all_goals
    obtain ⟨w, rfl⟩ := (Int.odd_natCast n).mp (by simpa using hdo)
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [ZMod.χ₄_two_mul_add_one]
    push_cast
    rw [← e24_twelve_mul, ← e24_add]
  · rw [ite_eq_right (by omega), e24_congr (Int.modEq_iff_dvd.mpr ⟨0, by ring⟩ : _ ≡ 0 [ZMOD 24])]
    simpa using e24_twelve_mul 0
  · rw [ite_eq_left (by omega), e24_congr (Int.modEq_iff_dvd.mpr ⟨-w, by ring⟩ : _ ≡ 12 [ZMOD 24])]
    simpa using e24_twelve_mul 1

/-- Negation for `c < 0` and odd `d`: the even-`c` Kronecker form at `-γ = (-a -b; -c -d)`, times
`i`, is the even-`c` Kronecker form at `γ`. -/
private theorem kroneckerEven_neg {a b c d : ℤ} (hc : c < 0) (hdo : Odd d) :
    I * ((kroneckerSym (-c) (-d) : ℂ) * e24 (evenExp (-a) (-b) (-c) (-d))) =
      kroneckerSym c d * e24 (evenExp a b c d) := by
  have hexp :
      e24 6 * e24 (evenExp (-a) (-b) (-c) (-d)) = e24 (6 - 6 * d) * e24 (evenExp a b c d) := by
    simp only [← e24_add, evenExp]
    congr 1
    ring
  -- Both symbols are `J(± c | |d|)`; the sign of `(c / d)` records whether `d < 0`.
  rw [← e24_six, kroneckerSym_of_odd _ hdo.neg, kroneckerSym_of_odd _ hdo, Int.natAbs_neg,
    jacobiSym.neg _ (Int.natAbs_odd.mpr hdo), ite_eq_right (by omega)]
  simp only [hc, true_and]
  push_cast
  rw [← χ₄_natAbs_mul_e24 hdo]
  linear_combination ((ZMod.χ₄ (d.natAbs : ZMod 4) : ℂ) * jacobiSym c d.natAbs) * hexp

/-! ### The steps on the multiplier side -/

private theorem etaMultiplier_eq_e24_three_mul (γ : SL(2, ℤ)) (hd : 0 < γ 1 1) :
    etaMultiplier γ = e24 3 * etaMultiplier (γ * S) := by
  rw [etaMultiplier_mul_S γ hd, ← e24_neg_three, ← mul_assoc, ← e24_add]
  simp [e24]

private theorem etaMultiplier_eq_e24_neg_three_mul (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hd : γ 1 1 < 0) : etaMultiplier γ = e24 (-3) * etaMultiplier (-(γ * S)) := by
  have h6 : e24 (-3) * e24 (-3) = -I := by rw [← e24_add, ← e24_neg_six]; rfl
  rw [etaMultiplier_neg_of_c_neg (γ * S) (by rwa [mul_S_apply_apply_zero]),
    etaMultiplier_mul_S_of_c_pos_of_d_neg γ hc hd, ← e24_neg_three]
  linear_combination (-(I * etaMultiplier γ)) * h6 + etaMultiplier γ * I_sq

/-! ### The Kronecker form -/

/-- For odd `c > 1` coprime to `d`, some translate `c n + d` is odd with `|c n + d| < c`. -/
private theorem exists_odd_translate {c d : ℤ} (hc : 1 < c) (hodd : Odd c) (hcd : IsCoprime c d) :
    ∃ n : ℤ, Odd (c * n + d) ∧ |c * n + d| < c := by
  have hr := Int.emod_def d c
  have hr0 := Int.emod_nonneg d (show c ≠ 0 by omega)
  have hrc := Int.emod_lt_of_pos d (show 0 < c by omega)
  -- `d % c ≠ 0`, since `c ∣ d` would make `c` a unit.
  have hrne : d % c ≠ 0 := fun h ↦ by
    rcases Int.isUnit_iff.mp (hcd.isUnit_of_dvd' dvd_rfl (Int.dvd_of_emod_eq_zero h)) with h | h <;>
      omega
  rcases Int.even_or_odd (d % c) with he | ho
  · refine ⟨-(d / c) - 1, ?_⟩
    rw [show c * (-(d / c) - 1) + d = d % c - c by linarith]
    exact ⟨he.sub_odd hodd, abs_lt.mpr ⟨by omega, by omega⟩⟩
  · refine ⟨-(d / c), ?_⟩
    rw [show c * -(d / c) + d = d % c by linarith]
    exact ⟨ho, abs_lt.mpr ⟨by omega, by omega⟩⟩

/-- The inversion step for odd `c`: if `d` is odd and nonzero, the Kronecker form at `γ` follows
from the Kronecker form at the elements with lower-left entry `|d|`. -/
private theorem etaMultiplier_eq_kroneckerOdd_of_inversion (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) (hdo : Odd (γ 1 1))
    (h : ∀ g : SL(2, ℤ), g 1 0 = |γ 1 1| → Odd (g 1 0) → etaMultiplier g =
      kroneckerSym (g 1 1) (g 1 0) * e24 (oddExp (g 0 0) (g 0 1) (g 1 0) (g 1 1))) :
    etaMultiplier γ =
      kroneckerSym (γ 1 1) (γ 1 0) * e24 (oddExp (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) := by
  rcases Int.lt_or_gt_of_odd hdo with hd | hd
  · -- `d < 0`: pass to `-(γ S) = (-b a; -d c)`.
    have key := h (-(γ * S)) (by rw [neg_mul_S_apply_apply_zero, abs_of_neg hd])
      (by rwa [neg_mul_S_apply_apply_zero, odd_neg])
    simp only [neg_mul_S_apply_apply_zero, neg_mul_S_apply_apply_one] at key
    rw [etaMultiplier_eq_e24_neg_three_mul γ hc hd, key]
    exact kroneckerOdd_neg_inversion γ.fin_two_mul_sub_mul_eq_one hc hd hodd hdo
  · -- `d > 0`: pass to `γ S = (b -a; d -c)`.
    have key := h (γ * S) (by rw [mul_S_apply_apply_zero, abs_of_pos hd])
      (by rwa [mul_S_apply_apply_zero])
    simp only [mul_S_apply_apply_zero, mul_S_apply_apply_one] at key
    rw [etaMultiplier_eq_e24_three_mul γ hd, key]
    exact kroneckerOdd_inversion γ.fin_two_mul_sub_mul_eq_one hc hd hodd hdo

private theorem etaMultiplier_eq_kroneckerOdd (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ =
      kroneckerSym (γ 1 1) (γ 1 0) * e24 (oddExp (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) := by
  -- Strong induction on `c`.
  suffices H : ∀ c : ℕ, ∀ γ : SL(2, ℤ), γ 1 0 = c → Odd (γ 1 0) → etaMultiplier γ =
      kroneckerSym (γ 1 1) (γ 1 0) * e24 (oddExp (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) from
    H (γ 1 0).toNat γ (by omega) hodd
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro γ hγc hodd
  have hc0 : 0 < γ 1 0 := hγc ▸ Int.natCast_pos.mpr (Nat.pos_of_ne_zero fun h ↦ by
    simp [hγc, h] at hodd)
  obtain hc1 | hc1 := eq_or_lt_of_le (show 1 ≤ γ 1 0 by omega)
  · rw [etaMultiplier_of_c_eq_one γ hc1.symm, ← hc1]
    simp only [kroneckerSym_one_right, Int.cast_one, one_mul, e24, oddExp]
    congr 1
    push_cast
    ring
  -- Translate `d` to an odd `d' = c n + d` with `0 < |d'| < c`, and invert.
  obtain ⟨n, hn_odd, hn_lt⟩ := exists_odd_translate hc1 hodd (γ.isCoprime_row 1)
  have habs := abs_nonneg (γ 1 0 * n + γ 1 1)
  have hγ' := etaMultiplier_eq_kroneckerOdd_of_inversion (γ * T ^ n)
    (by rwa [mul_T_zpow_apply_apply_zero]) (by rwa [mul_T_zpow_apply_apply_zero])
    (by rwa [mul_T_zpow_apply_apply_one])
    (fun g hg ↦ ih |γ 1 0 * n + γ 1 1|.toNat (by rw [mul_T_zpow_apply_apply_one] at hg; omega) g
      (by rw [hg, mul_T_zpow_apply_apply_one]; omega))
  -- Undo the translation.
  rw [etaMultiplier_mul_T_zpow, mul_T_zpow_apply_apply_zero, mul_T_zpow_apply_apply_zero,
    mul_T_zpow_apply_apply_one, mul_T_zpow_apply_apply_one,
    kroneckerOdd_translate n γ.fin_two_mul_sub_mul_eq_one hc0 hodd,
    show cexp (π * I * n / 12) = e24 n by rw [e24]; congr 1; ring] at hγ'
  exact mul_left_cancel₀ (e24_ne_zero n) hγ'

private theorem etaMultiplier_eq_kroneckerEven_of_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (heven : Even (γ 1 0)) :
    etaMultiplier γ =
      kroneckerSym (γ 1 0) (γ 1 1) * e24 (evenExp (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) := by
  have hdet := γ.fin_two_mul_sub_mul_eq_one
  have hdo := γ.odd_apply_one_of_even_apply_zero heven
  rcases Int.lt_or_gt_of_odd hdo with hneg | hpos
  · rw [etaMultiplier_eq_e24_neg_three_mul γ hc hneg,
      etaMultiplier_eq_kroneckerOdd (-(γ * S)) (by rw [neg_mul_S_apply_apply_zero]; omega)
        (by rwa [neg_mul_S_apply_apply_zero, odd_neg])]
    simp only [neg_mul_S_apply_apply_zero, neg_mul_S_apply_apply_one]
    exact kroneckerEven_neg_inversion hdet hc hneg heven hdo
  · rw [etaMultiplier_eq_e24_three_mul γ hpos,
      etaMultiplier_eq_kroneckerOdd (γ * S) (by rwa [mul_S_apply_apply_zero])
        (by rwa [mul_S_apply_apply_zero])]
    simp only [mul_S_apply_apply_zero, mul_S_apply_apply_one]
    exact kroneckerEven_inversion hdet hc hpos heven hdo

private theorem etaMultiplier_eq_kroneckerEven (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    etaMultiplier γ =
      kroneckerSym (γ 1 0) (γ 1 1) * e24 (evenExp (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) := by
  rcases lt_trichotomy (γ 1 0) 0 with hneg | hzero | hpos
  · -- `c < 0`: pass to `-γ`, with `ε(γ) = i ε(-γ)`.
    have hpos : 0 < (-γ) 1 0 := by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
        using hneg
    have h := etaMultiplier_neg_of_c_pos (-γ) hpos
    rw [neg_neg] at h
    rw [h, etaMultiplier_eq_kroneckerEven_of_pos (-γ) hpos (by
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, even_neg] using heven)]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    exact kroneckerEven_neg hneg (γ.odd_apply_one_of_even_apply_zero heven)
  · -- `c = 0`: `γ = ± T ^ b`, with `d = ± 1`.
    have hdet := γ.fin_two_mul_sub_mul_eq_one
    rw [hzero, mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, hd⟩ | ⟨-, hd⟩
    · rw [etaMultiplier_of_c_eq_zero_of_d_pos γ hzero (by omega), hzero, hd,
        kroneckerSym_one_right, Int.cast_one, one_mul, e24]
      congr 1
      simp only [evenExp]
      push_cast
      ring
    · rw [etaMultiplier_of_c_eq_zero_of_d_neg γ hzero (by omega), hzero, hd,
        kroneckerSym_neg_one_right, ite_eq_right (lt_irrefl 0), Int.cast_one, one_mul,
        ← e24_neg_six]
      simp only [e24, ← Complex.exp_add]
      congr 1
      simp only [evenExp]
      push_cast
      ring
  · exact etaMultiplier_eq_kroneckerEven_of_pos γ hpos heven

/-- **The Kronecker form of the eta multiplier, odd `c`** (Strömberg, Remark 2.5): for
`γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` odd,
`ε(γ) = (d / c) · e(((a + d) c - b d (c² - 1) - 3 c) / 24)`, where `e(x) = exp(2 π i x)` and
`(d / c)` is the Kronecker symbol, here the Jacobi symbol at `c`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rw [etaMultiplier_eq_kroneckerOdd γ hc hodd, e24, oddExp]

/-- **The Kronecker form of the eta multiplier, even `c`** (Strömberg, Remark 2.5): for
`γ = (a b; c d) ∈ SL(2, ℤ)` with `c` even,
`ε(γ) = (c / d) · e(((a + d) c - b d (c² - 1) + 3 d - 3 - 3 c d) / 24)`, where
`e(x) = exp(2 π i x)` and `(c / d)` is the Kronecker symbol at the odd, possibly negative,
denominator `d`. Strömberg states it for `c > 0`; it holds for every even `c`, including `c = 0`,
where `γ = ± Tᵇ`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_of_even_c (γ : SL(2, ℤ)) (heven : Even (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 0) (γ 1 1) *
      cexp (2 * π * I * (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
        3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  rw [etaMultiplier_eq_kroneckerEven γ heven, e24, evenExp]

/-- For odd `m`, the sign factor `χ₄ m * i` cancels the `-6 m` numerator shift in
`exp(2π i (N - 6 m) / 24)`: for `m ≡ 1 (mod 4)` it is `1 * i * (-i) = 1`, and for `m ≡ 3 (mod 4)`
it is `(-1) * i * i = 1`. -/
private theorem chi4_mul_I_mul_cexp_sub_six_mul (N : ℤ) {m : ℤ} (hm : Odd m) :
    (χ₄ (m : ZMod 4) : ℂ) * I * cexp (2 * π * I * ((N - 6 * m : ℤ) : ℂ) / 24) =
      cexp (2 * π * I * (N : ℂ) / 24) := by
  rcases (by obtain ⟨t, rfl⟩ := hm; omega : m % 4 = 1 ∨ m % 4 = 3) with hm4 | hm4
  · have hχ : χ₄ (m : ZMod 4) = 1 := χ₄_int_one_mod_four hm4
    have hI : (I : ℂ) * -I = 1 := by simp
    have hdvd : (24 : ℤ) ∣ (N - 6 * m) - (N - 6) := ⟨-(m / 4), by omega⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
    have hsplit : 2 * π * I * ((N - 6 : ℤ) : ℂ) / 24 =
        -π / 2 * I + 2 * π * I * (N : ℂ) / 24 := by
      push_cast
      ring
    rw [Int.cast_ofNat] at hexp
    rw [hχ, Int.cast_one, one_mul, hexp, hsplit, Complex.exp_add,
      Complex.exp_neg_pi_div_two_mul_I, ← mul_assoc, hI, one_mul]
  · have hχ : χ₄ (m : ZMod 4) = -1 := χ₄_int_three_mod_four hm4
    have hI : (-1 : ℂ) * I * I = 1 := by simp
    have hdvd : (24 : ℤ) ∣ (N - 6 * m) - (N + 6) := ⟨-(m / 4 + 1), by omega⟩
    have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
    have hsplit : 2 * π * I * ((N + 6 : ℤ) : ℂ) / 24 =
        π / 2 * I + 2 * π * I * (N : ℂ) / 24 := by
      push_cast
      ring
    rw [Int.cast_ofNat] at hexp
    rw [hχ, Int.cast_neg, Int.cast_one, hexp, hsplit, Complex.exp_add,
      Complex.exp_pi_div_two_mul_I, ← mul_assoc, hI, one_mul]

private theorem etaMultiplier_eq_kronecker_odd_of_c_neg {γ : SL(2, ℤ)} (hc : γ 1 0 < 0)
    (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  have hneg_pos : 0 < (-γ) 1 0 := by simpa using hc
  have hodd_neg : Odd ((-γ) 1 0) := by simpa using hodd.neg
  have hodd_abs : Odd (γ 1 0).natAbs := Int.natAbs_odd.mpr hodd
  have habs : ((γ 1 0).natAbs : ℤ) = -γ 1 0 := Int.ofNat_natAbs_of_nonpos hc.le
  have hmul : etaMultiplier γ = I * etaMultiplier (-γ) := by
    rw [etaMultiplier_neg_of_c_neg γ hc, ← mul_assoc]
    simp
  have hsym : kroneckerSym (-γ 1 1) (-γ 1 0) =
      χ₄ ((-γ 1 0 : ℤ) : ZMod 4) * kroneckerSym (γ 1 1) (γ 1 0).natAbs := by
    rw [← habs, kroneckerSym_eq_jacobiSym _ hodd_abs, kroneckerSym_eq_jacobiSym _ hodd_abs,
      jacobiSym.neg _ hodd_abs, Int.cast_natCast]
  set N : ℤ := (γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0
  have hnum : (((-γ 0 0 + -γ 1 1) * -γ 1 0 - -γ 0 1 * -γ 1 1 * ((-γ 1 0) ^ 2 - 1) -
      3 * -γ 1 0 : ℤ)) = N - 6 * (-γ 1 0) := by
    simp only [N]
    ring
  rw [hmul, etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c (-γ) hneg_pos hodd_neg]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  rw [hsym, hnum, Int.cast_mul, ← chi4_mul_I_mul_cexp_sub_six_mul N hodd.neg]
  ring

/-- **Kronecker-symbol formula for odd `c`** on all of `SL(2, ℤ)`:
`ε(γ) = (d / |c|) exp(2π i ((a + d) c - b d (c² - 1) - 3 c) / 24)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c (γ : SL(2, ℤ)) (hodd : Odd (γ 1 0)) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (2 * π * I *
        (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) /
          24) := by
  rcases lt_trichotomy (γ 1 0) 0 with hc | hc | hc
  · exact etaMultiplier_eq_kronecker_odd_of_c_neg hc hodd
  · exact absurd (hc ▸ hodd) Int.not_odd_zero
  · rw [Int.natAbs_of_nonneg hc.le]
    exact etaMultiplier_eq_kroneckerSym_mul_of_c_pos_of_odd_c γ hc hodd

/-- **Kronecker-symbol formula for the eta multiplier** on all of `SL(2, ℤ)` (Strömberg,
Remark 2.5, equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)`, `ε(γ)` is given in terms of the
Kronecker symbol `(d / |c|)` when `c` is odd and `(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_ite_kroneckerSym_mul_cexp (γ : SL(2, ℤ)) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0).natAbs *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) / 24)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  by_cases hodd : Odd (γ 1 0)
  · rw [ite_eq_left hodd]
    exact etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c γ hodd
  · rw [ite_eq_right hodd]
    exact etaMultiplier_eq_kroneckerSym_mul_of_even_c γ (Int.not_odd_iff_even.mp hodd)

/-- **Kronecker-symbol formula for the eta multiplier for `c ≥ 0`** (Strömberg, Remark 2.5,
equation (2.5)): for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c ≥ 0`, `|c| = c`, so `ε(γ)` is given in
terms of `(d / c)` when `c` is odd and `(c / d)` when `c` is even. -/
theorem etaMultiplier_eq_ite_kroneckerSym_mul_cexp_of_c_nonneg (γ : SL(2, ℤ)) (hc : 0 ≤ γ 1 0) :
    etaMultiplier γ =
      if Odd (γ 1 0) then
        kroneckerSym (γ 1 1) (γ 1 0) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0 : ℤ) : ℂ) / 24)
      else
        kroneckerSym (γ 1 0) (γ 1 1) *
          cexp (2 * π * I *
            (((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) +
              3 * γ 1 1 - 3 - 3 * γ 1 0 * γ 1 1 : ℤ) : ℂ) / 24) := by
  simpa [Int.natAbs_of_nonneg hc] using etaMultiplier_eq_ite_kroneckerSym_mul_cexp γ

/-- When `c = γ 1 0` is coprime to `6`, `24 ∣ c² - 1`, so the `b d (c² - 1)` term drops out:
`ε(γ) = (d / |c|) exp(π i (a + d - 3) c / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six (γ : SL(2, ℤ))
    (hc6 : IsCoprime (γ 1 0) 6) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0).natAbs *
      cexp (π * I * (((γ 0 0 + γ 1 1 - 3) * γ 1 0 : ℤ) : ℂ) / 12) := by
  have hc' : IsCoprime (γ 1 0) (2 * 3) := hc6
  have hodd : Odd (γ 1 0) := Int.isCoprime_two_right.mp hc'.of_mul_right_left
  obtain ⟨m, hm⟩ := Int.twentyFour_dvd_sq_sub_one_of_isCoprime_six hc6
  have hdvd : (24 : ℤ) ∣ ((γ 0 0 + γ 1 1) * γ 1 0 - γ 0 1 * γ 1 1 * (γ 1 0 ^ 2 - 1) - 3 * γ 1 0) -
      (γ 0 0 + γ 1 1 - 3) * γ 1 0 :=
    ⟨-γ 0 1 * γ 1 1 * m, by linear_combination -γ 0 1 * γ 1 1 * hm⟩
  have hexp := Complex.exp_two_pi_mul_I_mul_intCast_div_eq_of_dvd_sub hdvd
  rw [Int.cast_ofNat] at hexp
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_odd_c γ hodd, hexp]
  congr 2
  ring

/-- When `c = γ 1 0 ≥ 0` is coprime to `6`, `24 ∣ c² - 1`, so the `b d (c² - 1)` term drops out:
`ε(γ) = (d / c) exp(π i (a + d - 3) c / 12)`. -/
theorem etaMultiplier_eq_kroneckerSym_mul_cexp_of_c_nonneg_of_isCoprime_c_six (γ : SL(2, ℤ))
    (hc : 0 ≤ γ 1 0) (hc6 : IsCoprime (γ 1 0) 6) :
    etaMultiplier γ = kroneckerSym (γ 1 1) (γ 1 0) *
      cexp (π * I * (((γ 0 0 + γ 1 1 - 3) * γ 1 0 : ℤ) : ℂ) / 12) := by
  rw [etaMultiplier_eq_kroneckerSym_mul_cexp_of_isCoprime_c_six γ hc6,
    Int.natAbs_of_nonneg hc]

end TauCeti.ModularForm
