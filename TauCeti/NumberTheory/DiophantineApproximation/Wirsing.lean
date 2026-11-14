/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.AlgebraicExponent
public import TauCeti.NumberTheory.DiophantineApproximation.MahlerExponent
import TauCeti.Analysis.Polynomial.SupNorm.Location
import TauCeti.Analysis.Polynomial.SupNorm.Northcott
import TauCeti.NumberTheory.GeometryOfNumbers.Vandermonde

/-!
# Wirsing's third inequality for approximation by algebraic numbers

Let `ξ` be a real number and `n` a natural number. Mahler's exponent `wₙ(ξ)` measures small
nonzero values `|P(ξ)|` of integer polynomials of degree at most `n`, whereas Koksma's exponent
`w*ₙ(ξ)` measures approximation of `ξ` by roots of such polynomials against their naive height.
Already `AlgebraicExponent` proves `w*ₙ(ξ) ≤ wₙ(ξ)`. Wirsing (1961) proved three reverse lower
bounds on `w*ₙ(ξ)` in terms of `wₙ(ξ)`; the third of these is

`wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)` (`TauCeti.div_le_algebraicApproximationExponent`),

which equals `n ≤ w*ₙ(ξ)` whenever `wₙ(ξ) = n` and holds unconditionally for every `n : ℕ` and
`ξ : ℝ` in `ℝ≥0∞`.

For `n = m + 1 ≥ 1`, `ξ` not algebraic of degree at most `n`, and `w₀ = wₙ(ξ) < ⊤`, Dirichlet's
lower bound gives `w₀ ≥ n`, so `w₀ - n + 1 = w₀ - m ≥ 1`. Given `w₀ < w'' < w'` and a large real
parameter `H`, the Vandermonde–Minkowski polynomial construction (`GeometryOfNumbers.Vandermonde`)
at the `m + 2` points `ξ, ξ + 2, …, ξ + m + 2` produces a nonzero `P ∈ ℤ[X]` of degree at most
`m + 1` with `|P(ξ)| ≤ H ^ (-w')`, `|P(ξ + 2 + k)| ≤ H` at the first `m` auxiliary points, and
`P.supNorm ≤ C₁ H ^ (w' - m)`. Because `w'' > w₀`, only finitely many integer polynomials violate
`|P(ξ)| > P.supNorm ^ (-w'')`; for large `H` this forces `P.supNorm > H ^ (w' / w'')`. Since
`w' / w'' > 1`, `P` is small relative to `P.supNorm` at all `m + 1` separated real points
`ξ, ξ + 2, …, ξ + m + 1`. Root location (`SupNorm.Location`) then places a unique simple root of
`P` within `1 / 2` of each of these `m + 1` points; the root `x` near `ξ` is real by conjugation
symmetry, satisfies `P.supNorm * |ξ - x| ≤ K₀ |P(ξ)|` because the remaining `m` roots stay at
distance at least `1` from `ξ`, and inherits `naiveHeight x ≤ 2 ^ (m + 1) P.supNorm` from Gelfond's
divisor bound (`Height.Naive`). Letting `H → ∞` and `w' ↓ w₀` yields infinitely many real algebraic
approximants for every exponent below `w₀ / (w₀ - n + 1)`.

In degree one, Dirichlet's theorem gives `1 ≤ w*ₙ(ξ) ↔ 1 ≤ n ∧ Irrational ξ`
(`TauCeti.one_le_algebraicApproximationExponent_iff`). At `wₙ(ξ) = ⊤`, the `ℝ≥0∞` quotient `⊤ / ⊤`
evaluates to `0`, so rational approximants supply the real-approximant bound `w < 1` inside
`max 1 (wₙ(ξ) / (wₙ(ξ) - n + 1))`
(`TauCeti.infinite_preimage_ofReal_algebraicApproximations_of_lt_max`),
while single-point complex root location shows `w*ₙ(ξ) = ⊤ ↔ wₙ(ξ) = ⊤`
(`TauCeti.algebraicApproximationExponent_eq_top_iff`). For algebraic `ξ` of degree `D ≤ n + 1`,
combining Wirsing's third inequality at `D - 1`, monotonicity in `n`, and Liouville's upper bound
determines both exponents unconditionally: `wₙ(ξ) = w*ₙ(ξ) = D - 1`.

## Main results

* `TauCeti.div_le_algebraicApproximationExponent`: Wirsing's third inequality
  `wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)`, with no hypothesis on `n` or `ξ`.
* `TauCeti.infinite_preimage_ofReal_algebraicApproximations_of_lt_max`: for `1 ≤ n` and irrational
  `ξ`, every real exponent strictly below `max 1 (wₙ(ξ) / (wₙ(ξ) - n + 1))` (which equals `1` when
  `wₙ(ξ) = ⊤` under `⊤ / ⊤ = 0`, and `wₙ(ξ) / (wₙ(ξ) - n + 1)` otherwise) is achieved by infinitely
  many real algebraic numbers of degree at most `n`.
* `TauCeti.algebraicApproximationExponent_eq_top_iff`: `w*ₙ(ξ) = ⊤ ↔ wₙ(ξ) = ⊤`.
* `TauCeti.one_le_algebraicApproximationExponent_iff`: `1 ≤ w*ₙ(ξ) ↔ 1 ≤ n ∧ Irrational ξ`.
* `IsAlgebraic.algebraicApproximationExponent_le`,
  `IsAlgebraic.algebraicApproximationExponent_eq_of_natDegree_minpoly_le`,
  `TauCeti.algebraicApproximationExponent_eq_of_natDegree_minpoly_eq`,
  `TauCeti.algebraicApproximationExponent_ratCast`: Liouville's upper bound for `w*ₙ(ξ)` and the
  exact value `w*ₙ(ξ) = D - 1` when `D = deg_ℚ(ξ) ≤ n + 1`.

## References

* E. Wirsing, *Approximation mit algebraischen Zahlen beschränkten Grades*, J. reine angew. Math.
  **206** (1961), 67–77, Satz 1.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge Tracts in Mathematics 160, Cambridge
  University Press (2004), §3.2 and §3.4, Theorem 3.4.
-/

public section

open Filter Polynomial
open scoped ENNReal

/-! ### Liouville's upper bound and degree-one rational lower bound -/

/-- **Liouville's bound for Koksma's exponent.** If `ξ` is a real algebraic number of degree `D`
over `ℚ`, then `w*ₙ(ξ) ≤ D - 1` for every `n`. -/
theorem IsAlgebraic.algebraicApproximationExponent_le {ξ : ℝ} (hξ : IsAlgebraic ℚ ξ) (n : ℕ) :
    TauCeti.algebraicApproximationExponent n ξ ≤ ((minpoly ℚ ξ).natDegree - 1 : ℕ) :=
  (TauCeti.algebraicApproximationExponent_le_mahlerExponent n ξ).trans (hξ.mahlerExponent_le n)

namespace TauCeti

/-- Rational numbers have Koksma exponent `0` in every degree. -/
@[simp]
theorem algebraicApproximationExponent_ratCast (n : ℕ) (q : ℚ) :
    algebraicApproximationExponent n q = 0 :=
  nonpos_iff_eq_zero.1 <|
    (algebraicApproximationExponent_le_mahlerExponent n q).trans_eq (mahlerExponent_ratCast n q)

/-- Koksma's exponent `w*ₙ(ξ)` is at least `1` if and only if `1 ≤ n` and `ξ` is irrational. -/
@[simp]
theorem one_le_algebraicApproximationExponent_iff {n : ℕ} {ξ : ℝ} :
    1 ≤ algebraicApproximationExponent n ξ ↔ 1 ≤ n ∧ Irrational ξ := by
  refine ⟨fun h ↦ ⟨Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h,
    fun ⟨q, hq⟩ ↦ by simp [← hq] at h⟩, ?_⟩
  rintro ⟨hn, hξ⟩
  have h1 : 1 + 1 ≤ algebraicApproximationExponent 1 ξ + 1 := by
    rw [algebraicApproximationExponent_one_add, one_add_one_eq_two]
    exact (two_le_irrationalityExponent_iff ξ).2 hξ
  exact ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 h1).trans
    (algebraicApproximationExponent_mono ξ hn)

/-! ### Non-vanishing, infinitude, and complex evaluation helpers -/

/-- A set on which a positive real-valued function takes arbitrarily small values is infinite. -/
private theorem infinite_of_forall_pos_of_forall_exists_lt {α : Type*} {s : Set α} {f : α → ℝ}
    (hpos : ∀ x ∈ s, 0 < f x) (hsmall : ∀ ε > 0, ∃ x ∈ s, f x < ε) : s.Infinite := by
  intro hfin
  obtain ⟨x₀, hx₀, -⟩ := hsmall 1 zero_lt_one
  obtain ⟨m, hm, hmin⟩ := s.exists_min_image f hfin ⟨x₀, hx₀⟩
  obtain ⟨y, hy, hylt⟩ := hsmall (f m) (hpos m hm)
  exact (hmin y hy).not_gt hylt

/-- Evaluating `P.map (Int.castRingHom ℂ)` at a real point `(y : ℂ)` has norm `|aeval y P|`. -/
private theorem norm_eval_map_intCast_complex (P : ℤ[X]) (y : ℝ) :
    ‖(P.map (Int.castRingHom ℂ)).eval (y : ℂ)‖ = |aeval y P| := by
  simpa [← algebraMap_int_eq, aeval_map_algebraMap] using
    congrArg norm (aeval_algebraMap_apply ℂ y P)

/-- In an injective complex root enumeration of `P ∈ ℤ[X]`, an entry strictly closer to a real
point `y` than every other entry is the cast of a real root of `P`. -/
private theorem exists_real_eq_and_aeval_eq_zero {ι : Type*} [Fintype ι] {P : ℤ[X]} {α : ι → ℂ}
    (henum : (P.map (Int.castRingHom ℂ)).IsRootEnumeration α) (hinj : Function.Injective α)
    (i : ι) {y : ℝ} (hfar : ∀ j ≠ i, ‖(y : ℂ) - α i‖ < ‖(y : ℂ) - α j‖) :
    ∃ x : ℝ, (x : ℂ) = α i ∧ aeval x P = 0 := by
  have henumZ : P.IsRootEnumeration α := by
    rwa [← algebraMap_int_eq, isRootEnumeration_map] at henum
  have him : (α i).im = 0 :=
    henumZ.im_eq_zero_of_norm_sub_lt fun j hj ↦ hfar j (hinj.ne_iff.1 hj)
  set x : ℝ := (α i).re
  have hxC : (x : ℂ) = α i := Complex.ext rfl him.symm
  refine ⟨x, hxC, ?_⟩
  have hmem : α i ∈ P.rootSet ℂ := henumZ.range_eq_rootSet ▸ Set.mem_range_self i
  have hev : aeval (x : ℂ) P = 0 := hxC ▸ (mem_rootSet'.1 hmem).2
  have hcoe : (aeval x P : ℂ) = aeval (x : ℂ) P := (aeval_algebraMap_apply ℂ x P).symm
  exact Complex.ofReal_injective (by rw [hcoe, hev, Complex.ofReal_zero])

/-- If `ξ` is not algebraic of degree at most `n`, no nonzero integer polynomial of degree at most
`n` vanishes at `ξ`. -/
private theorem aeval_ne_zero_of_not_natDegree_le {n : ℕ} {ξ : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n)) {P : ℤ[X]} (hP0 : P ≠ 0)
    (hP : P.natDegree ≤ n) : aeval ξ P ≠ 0 := fun h0 ↦
  hξ ⟨isAlgebraic_rat_of_aeval_eq_zero hP0 h0,
    (natDegree_minpoly_rat_le_of_aeval_eq_zero hP0 h0).trans hP⟩

/-- If `wₙ(ξ) < ENNReal.ofReal w''` and `ξ` is not algebraic of degree at most `n`, there is
`δ > 0` such that every nonzero `P ∈ ℤ[X]` of degree at most `n` with `|P(ξ)| < δ` satisfies
`1 < P.supNorm` and `P.supNorm ^ (-w'') < |P(ξ)|`. -/
private theorem exists_pos_forall_rpow_neg_lt_abs_aeval {n : ℕ} {ξ w'' : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n))
    (hw'' : mahlerExponent n ξ < ENNReal.ofReal w'') :
    ∃ δ > 0, ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ n → |aeval ξ P| < δ →
      1 < P.supNorm ∧ P.supNorm ^ (-w'') < |aeval ξ P| := by
  have hfin : (linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w'').Finite := by
    by_contra hinf
    rw [mahlerExponent_def] at hw''
    exact hw''.not_ge (le_linearFormExponent_of_infinite (Set.not_finite.1 hinf))
  obtain ⟨B₀, _, hB₀⟩ := hfin.isBounded.exists_pos_norm_le
  set B := max 1 B₀
  obtain ⟨δ, hδ, hgap⟩ := Polynomial.exists_pos_lt_supNorm_of_norm_aeval_lt ξ n B
  refine ⟨δ, hδ, fun P hP0 hP hlt ↦ ?_⟩
  have hne : aeval ξ P ≠ 0 := aeval_ne_zero_of_not_natDegree_le hξ hP0 hP
  have hBP : B < P.supNorm := hgap P hP hne (by simpa [Real.norm_eq_abs] using hlt)
  refine ⟨(le_max_left 1 B₀).trans_lt hBP, not_le.1 fun hle ↦ ?_⟩
  have hmem : coeffVec n P ∈ linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w'' := by
    rw [mem_linearFormApproximations, coeffVec_linearForm hP ξ, norm_coeffVec_eq_supNorm hP]
    exact ⟨abs_pos.2 hne, hle⟩
  exact hBP.not_ge
    ((norm_coeffVec_eq_supNorm hP).symm.trans_le ((hB₀ _ hmem).trans (le_max_right 1 B₀)))

/-! ### Wirsing's separated test points and single-parameter root construction -/

/-- Wirsing's `m + 2` real interpolation points `ξ, ξ + 2, ξ + 3, …, ξ + m + 2`. -/
private def wirsingPoints (m : ℕ) (ξ : ℝ) : Fin (m + 2) → ℝ :=
  Fin.cases ξ fun j ↦ ξ + 2 + (j : ℝ)

/-- Distinct Wirsing points are at distance at least `1`, and every auxiliary point is at distance
at least `2` from `ξ`. -/
private theorem wirsingPoints_sep (m : ℕ) (ξ : ℝ) :
    (Pairwise fun i j ↦ 1 ≤ |wirsingPoints m ξ i - wirsingPoints m ξ j|) ∧
      (∀ j : Fin (m + 1), 2 ≤ |wirsingPoints m ξ j.succ - ξ|) ∧
      ∀ j : Fin (m + 1), |wirsingPoints m ξ (Fin.castSucc j)| ≤ |ξ| + m + 2 := by
  refine ⟨fun i j hij ↦ ?_, fun j ↦ ?_, ?_⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact absurd rfl hij
    · simp only [wirsingPoints, Fin.cases_zero, Fin.cases_succ,
        show ξ - (ξ + 2 + (j' : ℝ)) = -(2 + (j' : ℝ)) by ring, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + (j' : ℝ))]
      linarith [Nat.cast_nonneg (α := ℝ) j']
    · simp only [wirsingPoints, Fin.cases_succ, Fin.cases_zero,
        show ξ + 2 + (i' : ℝ) - ξ = 2 + (i' : ℝ) by ring,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + (i' : ℝ))]
      linarith [Nat.cast_nonneg (α := ℝ) i']
    · have hne : (i' : ℤ) ≠ (j' : ℤ) := fun h ↦
        hij (congrArg Fin.succ (Fin.ext (Int.ofNat.inj h)))
      have habs : (1 : ℝ) ≤ |(i' : ℝ) - (j' : ℝ)| := by
        simpa [Int.cast_sub] using (Int.cast_le (R := ℝ)).2 (Int.one_le_abs (sub_ne_zero.2 hne))
      simpa [wirsingPoints, show ξ + 2 + (i' : ℝ) - (ξ + 2 + (j' : ℝ)) = i' - j' by ring] using habs
  · simp only [wirsingPoints, Fin.cases_succ, show ξ + 2 + (j : ℝ) - ξ = 2 + (j : ℝ) by ring,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 + (j : ℝ))]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  · intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · simp only [Fin.castSucc_zero, wirsingPoints, Fin.cases_zero]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    · rw [Fin.castSucc_succ, wirsingPoints, Fin.cases_succ]
      have hk : (k : ℝ) ≤ m := by exact_mod_cast k.isLt.le
      have h2k : |(2 : ℝ) + (k : ℝ)| = 2 + (k : ℝ) := abs_of_nonneg (by positivity)
      calc |ξ + 2 + (k : ℝ)| = |ξ + (2 + (k : ℝ))| := by ring_nf
        _ ≤ |ξ| + |2 + (k : ℝ)| := abs_add_le ξ (2 + (k : ℝ))
        _ = |ξ| + (2 + (k : ℝ)) := by rw [h2k]
        _ ≤ |ξ| + m + 2 := by linarith

/-- Uniform Vandermonde polynomial supply at `wirsingPoints m ξ`: there is `C₁ ≥ 1` such that for
every `H ≥ 1` and `w' ≥ m + 1`, some nonzero `P ∈ ℤ[X]` of degree at most `m + 1` satisfies
`|P(ξ)| ≤ H ^ (-w')`, `|P(β_{k+1})| ≤ H` (`k < m`), and `P.supNorm ≤ C₁ * H ^ (w' - m)`. -/
private theorem exists_ge_one_forall_exists_poly_wirsing (m : ℕ) (ξ : ℝ) :
    ∃ C₁ ≥ 1, ∀ H w' : ℝ, 1 ≤ H → (m : ℝ) + 1 ≤ w' →
      ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ m + 1 ∧ |aeval ξ P| ≤ H ^ (-w') ∧
        (∀ k : Fin m, |aeval (wirsingPoints m ξ (Fin.castSucc k).succ) P| ≤ H) ∧
        P.supNorm ≤ C₁ * H ^ (w' - m) := by
  set β := wirsingPoints m ξ
  have hinj : Function.Injective β := fun i j hij ↦ by_contra fun hne ↦ by
    have h1 : 1 ≤ |β i - β j| := (wirsingPoints_sep m ξ).1 hne
    rw [hij, sub_self, abs_zero] at h1
    linarith
  obtain ⟨CV, hCV, hmink⟩ := Polynomial.exists_one_le_forall_exists_ne_zero_abs_aeval_le_supNorm_le
    hinj
  set Ddet := |(Matrix.vandermonde β).det|
  refine ⟨CV * max 1 Ddet, one_le_mul_of_one_le_of_one_le hCV (le_max_left _ _),
    fun H w' hH1 hw' ↦ ?_⟩
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  let a : Fin (m + 2) → ℝ :=
    Fin.cases (H ^ (-w')) (Fin.lastCases (Ddet * H ^ (w' - m)) fun _ : Fin m ↦ H)
  have ha0 : 0 ≤ a := Fin.cases (Real.rpow_nonneg hH0.le _)
    (Fin.lastCases
      (by simp only [Pi.zero_apply, a, Fin.cases_succ, Fin.lastCases_last]; positivity)
      fun _ ↦ by simp only [Pi.zero_apply, a, Fin.cases_succ, Fin.lastCases_castSucc]; positivity)
  have haprod : Ddet ≤ ∏ i, a i := by
    rw [Fin.prod_univ_succ]
    simp only [a, Fin.cases_zero, Fin.cases_succ, Fin.prod_univ_castSucc, Fin.lastCases_last,
      Fin.lastCases_castSucc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow : H ^ (-w') * (H ^ m * (Ddet * H ^ (w' - m))) = Ddet := by
      rw [← Real.rpow_natCast H m]
      calc H ^ (-w') * (H ^ (m : ℝ) * (Ddet * H ^ (w' - m)))
          = Ddet * (H ^ (-w') * H ^ (m : ℝ) * H ^ (w' - m)) := by ring
        _ = Ddet * H ^ (-w' + m + (w' - m)) := by rw [← Real.rpow_add hH0, ← Real.rpow_add hH0]
        _ = Ddet := by norm_num
    exact hpow.symm.le
  have hanorm : ‖a‖ ≤ max 1 Ddet * H ^ (w' - m) := by
    have h1wm : 1 ≤ H ^ (w' - m) := Real.one_le_rpow hH1 (by linarith)
    have hHwm : H ≤ H ^ (w' - m) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hH1 (by linarith : (1 : ℝ) ≤ w' - m)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 <|
      Fin.cases ?_ (Fin.lastCases ?_ fun _ ↦ ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (ha0 0)]; dsimp [a]
      exact ((Real.rpow_le_one_of_one_le_of_nonpos hH1
        (by linarith [Nat.cast_nonneg (α := ℝ) m])).trans h1wm).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left 1 Ddet))
    · rw [Real.norm_eq_abs, abs_of_nonneg (ha0 _)]
      simp only [a, Fin.cases_succ, Fin.lastCases_last]
      exact mul_le_mul_of_nonneg_right (le_max_right 1 Ddet) (by positivity)
    · rw [Real.norm_eq_abs, abs_of_nonneg (ha0 _)]
      simp only [a, Fin.cases_succ, Fin.lastCases_castSucc]
      exact hHwm.trans (le_mul_of_one_le_left (by positivity) (le_max_left 1 Ddet))
  obtain ⟨P, hP0, hPdeg, hPeval, hPsup⟩ := hmink a ha0 haprod
  exact ⟨P, hP0, hPdeg, by simpa [β, wirsingPoints, a] using hPeval 0,
    fun k ↦ by simpa [β, a] using hPeval (Fin.castSucc k).succ,
    hPsup.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hanorm (by positivity))⟩

/-- Given a nonzero `P ∈ ℤ[X]` of degree at most `m + 1` bounded by `H ^ (-w')` at `ξ`, bounded by
`H` at the first `m` auxiliary Wirsing points, and with `P.supNorm` large enough to force roots in
all `m + 1` radius-`(1 / 2)` discs, its root near `ξ` is a real algebraic number `x` of degree at
most `m + 1` satisfying `P.supNorm * |ξ - x| ≤ (2 (|ξ| + m + 3)) ^ (m + 1) H ^ (-w')` and
`naiveHeight x ≤ 2 ^ (m + 1) P.supNorm`. -/
private theorem exists_real_root_of_poly_wirsing {m : ℕ} {ξ H w' : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ m + 1)) (hH : 1 ≤ H) (hw' : 0 ≤ w')
    {P : ℤ[X]} (hP0 : P ≠ 0) (hPdeg : P.natDegree ≤ m + 1)
    (hPξ : |aeval ξ P| ≤ H ^ (-w'))
    (hPk : ∀ k : Fin m, |aeval (wirsingPoints m ξ (Fin.castSucc k).succ) P| ≤ H)
    (hPloc : H < (1 / 2 / (4 * (|ξ| + m + 2 + 1))) ^ (m + 1) * P.supNorm) :
    ∃ x : ℝ, IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ m + 1 ∧ 0 < |ξ - x| ∧
      P.supNorm * |ξ - x| ≤ (2 * (|ξ| + m + 3)) ^ (m + 1) * H ^ (-w') ∧
      naiveHeight x ≤ 2 ^ (m + 1) * P.supNorm := by
  obtain ⟨hsep, hfar2, hbound⟩ := wirsingPoints_sep m ξ
  set γ : Fin (m + 1) → ℂ := fun j ↦ (wirsingPoints m ξ (Fin.castSucc j) : ℂ)
  set p : ℂ[X] := P.map (Int.castRingHom ℂ)
  have hpsup : p.supNorm = P.supNorm := P.supNorm_map (Int.castRingHom ℂ)
  have hγsep : Pairwise fun i j ↦ 2 * (1 / 2 : ℝ) ≤ ‖γ i - γ j‖ := fun i j hij ↦ by
    simpa [γ, ← Complex.ofReal_sub, Complex.norm_real] using
      hsep ((Fin.castSucc_injective _).ne hij)
  have hγeval (j : Fin (m + 1)) :
      ‖p.eval (γ j)‖ < (1 / 2 / (4 * (‖γ j‖ + 1))) ^ (m + 1) * p.supNorm := by
    have hjH : ‖p.eval (γ j)‖ ≤ H := by
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · simpa [p, γ, wirsingPoints, norm_eval_map_intCast_complex] using
          hPξ.trans ((Real.rpow_le_one_of_one_le_of_nonpos hH (neg_nonpos.2 hw')).trans hH)
      · simpa [p, γ, Fin.castSucc_succ, norm_eval_map_intCast_complex] using hPk k
    have hγnorm : ‖γ j‖ ≤ |ξ| + m + 2 := by simpa [γ, Complex.norm_real] using hbound j
    exact hjH.trans_lt (hpsup ▸ hPloc.trans_le (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by gcongr) _) P.supNorm_nonneg))
  obtain ⟨α, hinj, henum, _, hdist⟩ := p.exists_isRootEnumeration_of_forall_norm_eval_lt
    (by simpa [Fintype.card_fin] using Polynomial.natDegree_map_le.trans hPdeg)
    (by norm_num) (by norm_num) hγsep (by simpa [Fintype.card_fin] using hγeval)
  -- Every root `α j` (`j ≠ 0`) stays at distance `≥ 1` from `ξ`, and all have norm `≤ |ξ| + m + 3`.
  have hfar (j : Fin (m + 1)) (hj : j ≠ 0) : 1 ≤ ‖(ξ : ℂ) - α j‖ := by
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hj
    have h2 : 2 ≤ ‖(ξ : ℂ) - γ k.succ‖ := by
      simpa [γ, Fin.castSucc_succ, ← Complex.ofReal_sub, Complex.norm_real, abs_sub_comm] using
        hfar2 (Fin.castSucc k)
    have htri := sub_sub_sub_cancel_right (ξ : ℂ) (γ k.succ) (α k.succ) ▸
      norm_sub_le ((ξ : ℂ) - α k.succ) (γ k.succ - α k.succ)
    linarith [hdist k.succ]
  have hαB (j : Fin (m + 1)) : ‖α j‖ ≤ |ξ| + m + 3 := by
    have htri := sub_sub_cancel (γ j) (α j) ▸ norm_sub_le (γ j) (γ j - α j)
    have hγj : ‖γ j‖ ≤ |ξ| + m + 2 := by simpa [γ, Complex.norm_real] using hbound j
    linarith [hdist j]
  have hdist0 : ‖(ξ : ℂ) - α 0‖ < 1 / 2 := by simpa [γ, wirsingPoints] using hdist 0
  obtain ⟨x, hxC, hxP⟩ := exists_real_eq_and_aeval_eq_zero henum hinj 0 (y := ξ) fun j hj ↦
    hdist0.trans_le ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans (hfar j hj))
  have hxne : x ≠ ξ := fun h ↦ aeval_ne_zero_of_not_natDegree_le hξ hP0 hPdeg (h ▸ hxP)
  have hest := henum.supNorm_mul_norm_sub_le_two_mul_pow_mul_norm_eval 0
    (B := |ξ| + m + 3) (by linarith [abs_nonneg ξ, Nat.cast_nonneg (α := ℝ) m]) hαB hfar
  rw [Fintype.card_fin, hpsup, ← hxC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    norm_eval_map_intCast_complex] at hest
  exact ⟨x, isAlgebraic_rat_of_aeval_eq_zero hP0 hxP,
    (natDegree_minpoly_rat_le_of_aeval_eq_zero hP0 hxP).trans hPdeg,
    abs_pos.2 (sub_ne_zero.2 hxne.symm),
    hest.trans (mul_le_mul_of_nonneg_left hPξ (by positivity)),
    (naiveHeight_le_two_pow_mul_supNorm_of_aeval_eq_zero hP0 hxP).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hPdeg) P.supNorm_nonneg)⟩

/-- Choosing `w'` slightly above `w₀ ≥ m + 1` preserves `u < w₀ / (w₀ - m)`. -/
private theorem exists_gt_and_lt_div_sub {m : ℕ} {w₀ u : ℝ} (hw₀ : (m : ℝ) + 1 ≤ w₀)
    (hu : u < w₀ / (w₀ - m)) :
    ∃ w' > w₀, u < w' / (w' - m) := by
  have hwm : 0 < w₀ - m := by linarith
  have hum : u * (w₀ - m) < w₀ := (lt_div_iff₀ hwm).1 hu
  rcases le_or_gt u 1 with hu1 | hu1
  · refine ⟨w₀ + 1, by linarith, (lt_div_iff₀ (by linarith)).2 ?_⟩
    linarith
  · have hbound : w₀ < u * m / (u - 1) := (lt_div_iff₀ (by linarith)).2 (by linarith)
    refine ⟨(w₀ + u * m / (u - 1)) / 2, by linarith, (lt_div_iff₀ (by linarith)).2 ?_⟩
    have hw' : (w₀ + u * m / (u - 1)) / 2 < u * m / (u - 1) := by linarith
    have := (lt_div_iff₀ (by linarith : 0 < u - 1)).1 hw'
    linarith

/-- Combine the root-separation estimate `S * |ξ - x| ≤ K₀ * H ^ (-w')`, Gelfond's height bound
`naiveHeight x ≤ 2 ^ (m + 1) * S`, and `S ≤ C₁ * H ^ (w' - m)` into
`|ξ - x| ≤ naiveHeight x ^ (-u - 1)` once `H ^ (-(w' - u * (w' - m)))` absorbs the leading
constants. -/
private theorem abs_sub_le_naiveHeight_rpow_of_wirsing_bounds {m : ℕ} {ξ x H w' u C₁ K₀ S : ℝ}
    (hH0 : 0 < H) (hu0 : 0 ≤ u) (hC₁ : 1 ≤ C₁) (hK₀ : 0 < K₀)
    (hxest : S * |ξ - x| ≤ K₀ * H ^ (-w'))
    (hxh : naiveHeight x ≤ 2 ^ (m + 1) * S)
    (hS : S ≤ C₁ * H ^ (w' - m))
    (hHK : H ^ (-(w' - u * (w' - m))) < (2 ^ (m + 1) * K₀ * (2 ^ (m + 1) * C₁) ^ u)⁻¹) :
    |ξ - x| ≤ naiveHeight x ^ (-u - 1) := by
  set Ktot : ℝ := 2 ^ (m + 1) * K₀ * (2 ^ (m + 1) * C₁) ^ u
  have hH_nx : naiveHeight x * |ξ - x| ≤ 2 ^ (m + 1) * (K₀ * H ^ (-w')) :=
    (mul_le_mul_of_nonneg_right hxh (abs_nonneg _)).trans
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hxest (by positivity))
  have hhu : naiveHeight x ^ u ≤ (2 ^ (m + 1) * C₁) ^ u * H ^ ((w' - m) * u) := by
    calc naiveHeight x ^ u ≤ (2 ^ (m + 1) * (C₁ * H ^ (w' - m))) ^ u :=
          Real.rpow_le_rpow (zero_le_one.trans (one_le_naiveHeight x))
            (hxh.trans (mul_le_mul_of_nonneg_left hS (by positivity))) hu0
      _ = (2 ^ (m + 1) * C₁) ^ u * H ^ ((w' - m) * u) := by
          rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hH0.le]
  have hnx0 : 0 < naiveHeight x := zero_lt_one.trans_le (one_le_naiveHeight x)
  have hprod_le : |ξ - x| * naiveHeight x ^ (u + 1) ≤ 1 := by
    calc |ξ - x| * naiveHeight x ^ (u + 1)
        = (naiveHeight x * |ξ - x|) * naiveHeight x ^ u := by
            rw [Real.rpow_add_one hnx0.ne']; ring
      _ ≤ (2 ^ (m + 1) * (K₀ * H ^ (-w'))) * ((2 ^ (m + 1) * C₁) ^ u * H ^ ((w' - m) * u)) :=
          mul_le_mul hH_nx hhu (by positivity) (by positivity)
      _ = Ktot * H ^ (-(w' - u * (w' - m))) := by
          have hexp : H ^ (-w') * H ^ ((w' - m) * u) = H ^ (-(w' - u * (w' - m))) := by
            rw [← Real.rpow_add hH0]; ring_nf
          calc (2 ^ (m + 1) * (K₀ * H ^ (-w'))) * ((2 ^ (m + 1) * C₁) ^ u * H ^ ((w' - m) * u))
              = Ktot * (H ^ (-w') * H ^ ((w' - m) * u)) := by simp only [Ktot]; ring
            _ = Ktot * H ^ (-(w' - u * (w' - m))) := by rw [hexp]
      _ ≤ 1 := by
          have := mul_lt_mul_of_pos_left hHK (by positivity : 0 < Ktot)
          rw [mul_inv_cancel₀ (by positivity : Ktot ≠ 0)] at this
          exact this.le
  rw [show -u - 1 = -(u + 1) by ring, Real.rpow_neg hnx0.le, ← one_div,
    le_div_iff₀ (by positivity)]
  exact hprod_le

/-- If `S ^ (-w'') < v ≤ H ^ (-w')` with `1 < S`, `0 < w''`, `0 < H`, `0 < cloc`, and
`cloc⁻¹ < H ^ (w' / w'' - 1)`, then `H < cloc * S`. -/
private theorem lt_mul_of_rpow_neg_lt {H w' w'' S v cloc : ℝ} (hH0 : 0 < H) (hw'' : 0 < w'')
    (hS1 : 1 < S) (hlow : S ^ (-w'') < v) (hup : v ≤ H ^ (-w')) (hcloc0 : 0 < cloc)
    (hHloc : cloc⁻¹ < H ^ (w' / w'' - 1)) : H < cloc * S := by
  have hS_gt : H ^ (w' / w'') < S := not_le.1 fun hle ↦ hlow.not_ge <| by
    have h : (H ^ (w' / w'')) ^ (-w'') ≤ S ^ (-w'') :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hS1) hle (neg_nonpos.2 hw''.le)
    have hexp : w' / w'' * -w'' = -w' := by have := hw''.ne'; field_simp
    rw [← Real.rpow_mul hH0.le, hexp] at h
    exact hup.trans h
  calc H = cloc * (cloc⁻¹ * H) := by rw [← mul_assoc, mul_inv_cancel₀ hcloc0.ne', one_mul]
    _ < cloc * (H ^ (w' / w'' - 1) * H) := by gcongr
    _ = cloc * H ^ (w' / w'') := by rw [← Real.rpow_add_one hH0.ne', sub_add_cancel]
    _ < cloc * S := mul_lt_mul_of_pos_left hS_gt hcloc0

/-- For fixed `m`, `ξ` not algebraic of degree at most `m + 1`, `0 ≤ u < w₀ / (w₀ - m)`, and any
threshold `ε > 0`, there exists a real algebraic number `x ∈ Complex.ofReal ⁻¹'
algebraicApproximations (m + 1) ξ u` with `|ξ - x| < ε`. -/
private theorem exists_real_approx_lt_eps {m : ℕ} {ξ u ε : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ m + 1))
    (htop : mahlerExponent (m + 1) ξ ≠ ⊤)
    (hw₀ : (m : ℝ) + 1 ≤ (mahlerExponent (m + 1) ξ).toReal) (hu0 : 0 ≤ u)
    (hu : u < (mahlerExponent (m + 1) ξ).toReal / ((mahlerExponent (m + 1) ξ).toReal - m))
    (hε : 0 < ε) :
    ∃ x ∈ Complex.ofReal ⁻¹' algebraicApproximations (m + 1) ξ u, |ξ - x| < ε := by
  set w₀ := (mahlerExponent (m + 1) ξ).toReal
  obtain ⟨w', hw₀w', huw'⟩ := exists_gt_and_lt_div_sub hw₀ hu
  let w'' := (w₀ + w') / 2
  have hw''_gt : w₀ < w'' := by dsimp [w'']; linarith
  have hw''_lt : w'' < w' := by dsimp [w'']; linarith
  have hw''_pos : 0 < w'' := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmah : mahlerExponent (m + 1) ξ < ENNReal.ofReal w'' :=
    ENNReal.ofReal_toReal htop ▸ (ENNReal.ofReal_lt_ofReal_iff hw''_pos).2 hw''_gt
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_forall_rpow_neg_lt_abs_aeval hξ hmah
  obtain ⟨C₁, hC₁, hpoly⟩ := exists_ge_one_forall_exists_poly_wirsing m ξ
  set cloc : ℝ := (1 / 2 / (4 * (|ξ| + m + 2 + 1))) ^ (m + 1)
  set K₀ : ℝ := (2 * (|ξ| + m + 3)) ^ (m + 1)
  set Ktot : ℝ := 2 ^ (m + 1) * K₀ * (2 ^ (m + 1) * C₁) ^ u
  -- Choose `H` large enough that all asymptotic bounds hold simultaneously.
  have hexp1 : 0 < w' / w'' - 1 := sub_pos.2 ((one_lt_div hw''_pos).2 hw''_lt)
  have hexp2 : 0 < w' - u * (w' - m) := sub_pos.2 ((lt_div_iff₀ (by linarith)).1 huw')
  obtain ⟨H, ⟨hH1, hHw'⟩, hHloc, hHK⟩ :=
    (((eventually_ge_atTop (1 : ℝ)).and
      ((tendsto_rpow_neg_atTop (hw''_pos.trans hw''_lt)).eventually
        (gt_mem_nhds (lt_min hδ (div_pos hε (by positivity : 0 < K₀)))))).and
      (((tendsto_rpow_atTop hexp1).eventually_gt_atTop cloc⁻¹).and
        ((tendsto_rpow_neg_atTop hexp2).eventually
          (gt_mem_nhds (inv_pos.2 (by positivity : 0 < Ktot)))))).exists
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  obtain ⟨P, hP0, hPdeg, hPξ, hPk, hPsup'⟩ := hpoly H w' hH1 (by linarith)
  obtain ⟨hP1, hPlow⟩ := hgap P hP0 hPdeg (hPξ.trans_lt (hHw'.trans_le (min_le_left _ _)))
  have hPloc : H < cloc * P.supNorm :=
    lt_mul_of_rpow_neg_lt hH0 hw''_pos hP1 hPlow hPξ (by positivity) hHloc
  obtain ⟨x, halg, hxdeg, hxpos, hxest, hxh⟩ :=
    exists_real_root_of_poly_wirsing hξ hH1 (hw''_pos.trans hw''_lt).le hP0 hPdeg hPξ hPk hPloc
  have hxle := abs_sub_le_naiveHeight_rpow_of_wirsing_bounds hH0 hu0 hC₁ (by positivity)
    hxest hxh hPsup' hHK
  refine ⟨x, ?_, ((le_mul_of_one_le_left (abs_nonneg _) hP1.le).trans hxest).trans_lt
    ((lt_div_iff₀' (by positivity)).1 (hHw'.trans_le (min_le_right _ _)))⟩
  have hmin : minpoly ℚ (x : ℂ) = minpoly ℚ x :=
    minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective x
  simp only [Set.mem_preimage, mem_algebraicApproximations, hmin, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    show naiveHeight (x : ℂ) = naiveHeight x from naiveHeight_map Complex.ofRealHom x]
  exact ⟨halg.algebraMap, hxdeg, hxpos, hxle⟩

/-! ### Real algebraic approximants and the infinite-exponent regime -/

/-- Private core of Wirsing's real-approximant construction when `ξ` is not algebraic of degree at
most `m + 1`. -/
private theorem infinite_preimage_ofReal_of_not_natDegree_le {m : ℕ} {ξ w : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ m + 1))
    (hw : ENNReal.ofReal w <
      mahlerExponent (m + 1) ξ / (mahlerExponent (m + 1) ξ - (m + 1 : ℕ) + 1)) :
    (Complex.ofReal ⁻¹' algebraicApproximations (m + 1) ξ w).Infinite := by
  have htop : mahlerExponent (m + 1) ξ ≠ ⊤ := fun ht ↦ by simp [ht] at hw
  set w₀ := (mahlerExponent (m + 1) ξ).toReal
  have hw₀ : (m : ℝ) + 1 ≤ w₀ := by
    have h := ENNReal.toReal_mono htop (natCast_le_mahlerExponent hξ)
    rwa [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one] at h
  have hw₀_pos : 0 < w₀ := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hwm_pos : 0 < w₀ - m := by linarith
  have hquot : mahlerExponent (m + 1) ξ / (mahlerExponent (m + 1) ξ - (m + 1 : ℕ) + 1) =
      ENNReal.ofReal (w₀ / (w₀ - m)) := by
    have hm1 : ((m + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ) + 1) := by
      rw [← ENNReal.ofReal_natCast]; simp
    have hsub : mahlerExponent (m + 1) ξ - (m + 1 : ℕ) + 1 = ENNReal.ofReal (w₀ - m) := by
      rw [← ENNReal.ofReal_toReal htop, hm1,
        ← ENNReal.ofReal_sub w₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one]
      ring_nf
    rw [hsub, ← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_div_of_pos hwm_pos]
  rw [hquot] at hw
  have hq_pos : 0 < w₀ / (w₀ - m) := div_pos hw₀_pos hwm_pos
  have hu : max w 0 < w₀ / (w₀ - m) := max_lt ((ENNReal.ofReal_lt_ofReal_iff hq_pos).1 hw) hq_pos
  have hS : (Complex.ofReal ⁻¹' algebraicApproximations (m + 1) ξ (max w 0)).Infinite :=
    infinite_of_forall_pos_of_forall_exists_lt (f := (|ξ - ·|))
      (fun x hx ↦ by
        rw [Set.mem_preimage, mem_algebraicApproximations] at hx
        simpa [← Complex.ofReal_sub, Complex.norm_real] using hx.2.2.1)
      fun ε hε ↦ exists_real_approx_lt_eps hξ htop hw₀ (le_max_right w 0) hu hε
  exact hS.mono (Set.preimage_mono (algebraicApproximations_antitone _ _ (le_max_left w 0)))

/-- **Wirsing's theorem with real algebraic approximants** (Wirsing 1961; Bugeaud, Theorem 3.4).
For `1 ≤ n` and irrational `ξ`, every real exponent `w` strictly below
`max 1 (wₙ(ξ) / (wₙ(ξ) - n + 1))` is achieved by infinitely many **real** algebraic numbers of
degree at most `n`. When `wₙ(ξ) = ⊤`, `⊤ / ⊤ = 0` in `ℝ≥0∞`, so the `max 1 (...)` term supplies the
rational-approximant bound `w < 1`. -/
theorem infinite_preimage_ofReal_algebraicApproximations_of_lt_max {n : ℕ} (hn : 1 ≤ n)
    {ξ : ℝ} (hξ : Irrational ξ) {w : ℝ}
    (hw : ENNReal.ofReal w < max 1 (mahlerExponent n ξ / (mahlerExponent n ξ - n + 1))) :
    (Complex.ofReal ⁻¹' algebraicApproximations n ξ w).Infinite := by
  rcases lt_max_iff.1 hw with hw1 | hwdiv
  · -- Degree-one approximations are rational, hence already real.
    have hinf1 : (algebraicApproximations 1 ξ w).Infinite :=
      infinite_algebraicApproximations_of_lt
        (hw1.trans_le (one_le_algebraicApproximationExponent_iff.2 ⟨le_rfl, hξ⟩))
    refine fun hfin ↦ hinf1 ((hfin.image Complex.ofReal).subset fun α hα ↦ ?_)
    have hα' := mem_algebraicApproximations.1 hα
    have hnot2 : ¬2 ≤ (minpoly ℚ α).natDegree := not_le.2 (Nat.lt_succ_of_le hα'.2.1)
    obtain ⟨q, rfl⟩ := not_not.1 (mt (minpoly.two_le_natDegree_iff hα'.1.isIntegral).2 hnot2)
    exact ⟨q, algebraicApproximations_mono ξ w hn (by simpa using hα), by simp⟩
  · by_cases halg : IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n
    · -- For irrational algebraic `ξ` of degree `2 ≤ D ≤ n`, reduce to degree `D - 1`.
      obtain ⟨hξalg, hdeg⟩ := halg
      have h2 : 2 ≤ (minpoly ℚ ξ).natDegree :=
        (minpoly.two_le_natDegree_iff hξalg.isIntegral).2 fun ⟨q, hq⟩ ↦ hξ ⟨q, by simpa using hq⟩
      set m := (minpoly ℚ ξ).natDegree - 2
      have hm_le : m + 1 ≤ n := by omega
      have hmn : mahlerExponent n ξ = ((m + 1 : ℕ) : ℝ≥0∞) := by
        rw [hξalg.mahlerExponent_eq_of_natDegree_minpoly_le (n := n) (by omega)]
        congr 1
        omega
      have hmm : mahlerExponent (m + 1) ξ = ((m + 1 : ℕ) : ℝ≥0∞) := by
        rw [hξalg.mahlerExponent_eq_of_natDegree_minpoly_le (n := m + 1) (by omega)]
        congr 1
        omega
      have hsub_n : ((m + 1 : ℕ) : ℝ≥0∞) - n = 0 := tsub_eq_zero_of_le (by exact_mod_cast hm_le)
      have hw' : ENNReal.ofReal w <
          mahlerExponent (m + 1) ξ / (mahlerExponent (m + 1) ξ - (m + 1 : ℕ) + 1) := by
        rw [hmm, tsub_self, zero_add, div_one]
        rwa [hmn, hsub_n, zero_add, div_one] at hwdiv
      exact (infinite_preimage_ofReal_of_not_natDegree_le (fun ⟨_, _⟩ ↦ by omega) hw').mono
        (Set.preimage_mono (algebraicApproximations_mono ξ w hm_le))
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.1 hn)
      exact infinite_preimage_ofReal_of_not_natDegree_le halg hwdiv

/-- Single-polynomial complex root location: if `ξ` is transcendental and a polynomial `P ∈ ℤ[X]`
of degree at most `n ≥ 1` has sufficiently large `P.supNorm` and satisfies
`0 < |P(ξ)| ≤ P.supNorm ^ (-(n (u + 2)))`, then `P` has a root in `algebraicApproximations n ξ u`
within `8 (|ξ| + 1) / P.supNorm` of `ξ`. -/
private theorem exists_mem_algebraicApproximations_of_abs_aeval_le {n : ℕ} (hn1 : 1 ≤ n) {ξ u : ℝ}
    (htrans : ¬IsAlgebraic ℚ ξ) (hu0 : 0 < u) {P : ℤ[X]} (hPdeg : P.natDegree ≤ n)
    (hHP1 : 1 < P.supNorm) (hKP : 8 * (|ξ| + 1) < P.supNorm)
    (hK2 : 8 * (|ξ| + 1) * (2 ^ n : ℝ) ^ (u + 1) < P.supNorm)
    (hPpos : 0 < |aeval ξ P|) (hPle : |aeval ξ P| ≤ P.supNorm ^ (-(n * (u + 2)))) :
    ∃ α ∈ algebraicApproximations n ξ u, ‖(ξ : ℂ) - α‖ ≤ 8 * (|ξ| + 1) / P.supNorm := by
  have hHP0 : 0 < P.supNorm := zero_lt_one.trans hHP1
  set K : ℝ := 8 * (|ξ| + 1)
  set r : ℝ := K * P.supNorm ^ (-(u + 2))
  have hr_inv : r ≤ K / P.supNorm := div_eq_mul_inv K _ ▸ Real.rpow_neg_one P.supNorm ▸
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHP1.le (by linarith))
      (by positivity)
  set p : ℂ[X] := P.map (Int.castRingHom ℂ)
  have hpeval : ‖p.eval (ξ : ℂ)‖ < (r / (4 * (‖(ξ : ℂ)‖ + 1))) ^ n * p.supNorm := by
    have hquot_r : r / (4 * (‖(ξ : ℂ)‖ + 1)) = 2 * P.supNorm ^ (-(u + 2)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; simp only [r, K]; field_simp; ring
    have hpow_r : (2 * P.supNorm ^ (-(u + 2))) ^ n = 2 ^ n * P.supNorm ^ (-(n * (u + 2))) := by
      rw [mul_pow, ← Real.rpow_natCast (P.supNorm ^ (-(u + 2))) n, ← Real.rpow_mul hHP0.le]; ring_nf
    rw [norm_eval_map_intCast_complex, hquot_r, hpow_r, P.supNorm_map (Int.castRingHom ℂ)]
    have h2n : (1 : ℝ) < 2 ^ n * P.supNorm := by
      have : (2 : ℝ) ≤ 2 ^ n := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn1
      nlinarith
    exact (hPle.trans_lt (lt_mul_of_one_lt_right (by positivity) h2n)).trans_eq (by ring)
  obtain ⟨α, hαroot, hαr⟩ := p.exists_isRoot_norm_sub_lt_of_norm_eval_lt (ξ : ℂ)
    (Polynomial.natDegree_map_le.trans hPdeg) (by positivity)
    (hr_inv.trans ((div_le_one hHP0).2 hKP.le)) hpeval
  have hP0 : P ≠ 0 := fun h0 ↦ (abs_pos.1 hPpos) (by simp [h0])
  have hαP : aeval α P = 0 := by simpa [p, ← algebraMap_int_eq, aeval_map_algebraMap] using hαroot
  have halg : IsAlgebraic ℚ α := isAlgebraic_rat_of_aeval_eq_zero hP0 hαP
  have hαne : 0 < ‖(ξ : ℂ) - α‖ := norm_pos_iff.2 <| sub_ne_zero.2 fun h ↦ by
    have hξC : IsAlgebraic ℚ (ξ : ℂ) := h ▸ halg
    exact htrans ((isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 hξC)
  have hnh : naiveHeight α ≤ 2 ^ n * P.supNorm :=
    (naiveHeight_le_two_pow_mul_supNorm_of_aeval_eq_zero hP0 hαP).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hPdeg) P.supNorm_nonneg)
  have hna0 : 0 < naiveHeight α := zero_lt_one.trans_le (one_le_naiveHeight α)
  have hαle : ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-u - 1) := by
    rw [show -u - 1 = -(u + 1) by ring, Real.rpow_neg hna0.le, ← one_div,
      le_div_iff₀ (by positivity)]
    calc ‖(ξ : ℂ) - α‖ * naiveHeight α ^ (u + 1)
        ≤ r * (2 ^ n * P.supNorm) ^ (u + 1) :=
          mul_le_mul hαr.le (Real.rpow_le_rpow hna0.le hnh (by linarith))
            (Real.rpow_nonneg hna0.le _) (by positivity)
      _ = K * (2 ^ n : ℝ) ^ (u + 1) * (P.supNorm ^ (-(u + 2)) * P.supNorm ^ (u + 1)) := by
          rw [Real.mul_rpow (by positivity) hHP0.le]; simp only [r]; ring
      _ = K * (2 ^ n : ℝ) ^ (u + 1) / P.supNorm := by
          rw [← Real.rpow_add hHP0, show -(u + 2) + (u + 1) = -1 by ring, Real.rpow_neg_one,
            div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hHP0).2 hK2.le
  exact ⟨α, mem_algebraicApproximations.2 ⟨halg,
    (natDegree_minpoly_rat_le_of_aeval_eq_zero hP0 hαP).trans hPdeg, hαne, hαle⟩,
    hαr.le.trans hr_inv⟩

/-- When `wₙ(ξ) = ⊤`, `0 < u`, and `0 < ε`, some complex algebraic approximation in
`algebraicApproximations n ξ u` lies within `ε` of `ξ`. -/
private theorem exists_algebraicApprox_lt_eps_of_mahlerExponent_eq_top {n : ℕ} {ξ u ε : ℝ}
    (htop : mahlerExponent n ξ = ⊤) (hu0 : 0 < u) (hε_pos : 0 < ε) :
    ∃ α ∈ algebraicApproximations n ξ u, ‖(ξ : ℂ) - α‖ < ε := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at htop
  have htrans : ¬IsAlgebraic ℚ ξ := fun halg ↦ by
    have := halg.mahlerExponent_le n
    simp [htop] at this
  set w : ℝ := n * (u + 2)
  have hS : (linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w).Infinite :=
    infinite_linearFormApproximations_of_lt (by simp [← mahlerExponent_def, htop])
  set K : ℝ := 8 * (|ξ| + 1)
  set M : ℝ := max 1 (max K (max (K / ε) (K * (2 ^ n : ℝ) ^ (u + 1))))
  obtain ⟨x, hxS, hxM⟩ :
      ∃ x ∈ linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w, M < ‖x‖ := by
    by_contra! hle
    exact hS ((isCompact_closedBall (0 : ℤ × (Fin n → ℤ)) M).finite_of_discrete.subset
      fun x hx ↦ mem_closedBall_zero_iff.2 (hle x hx))
  rw [mem_linearFormApproximations, ← aeval_linearFormPoly, ← supNorm_linearFormPoly] at hxS
  rw [← supNorm_linearFormPoly] at hxM
  simp only [M, max_lt_iff] at hxM
  obtain ⟨hHP1, hKP, hKε, hK2⟩ := hxM
  obtain ⟨α, hαmem, hαle⟩ := exists_mem_algebraicApproximations_of_abs_aeval_le hn1 htrans hu0
    (natDegree_linearFormPoly_le x) hHP1 hKP hK2 hxS.1 hxS.2
  refine ⟨α, hαmem, hαle.trans_lt ?_⟩
  rw [div_lt_iff₀ (zero_lt_one.trans hHP1)]
  linarith [(div_lt_iff₀ hε_pos).1 hKε]

/-- When `wₙ(ξ) = ⊤` and `0 < u`, there are infinitely many algebraic approximations to `ξ` of
degree at most `n` and exponent `u`. -/
private theorem infinite_algebraicApproximations_of_mahlerExponent_eq_top {n : ℕ} {ξ u : ℝ}
    (htop : mahlerExponent n ξ = ⊤) (hu0 : 0 < u) :
    (algebraicApproximations n ξ u).Infinite :=
  infinite_of_forall_pos_of_forall_exists_lt (f := fun α ↦ ‖(ξ : ℂ) - α‖)
    (fun _ hα ↦ (mem_algebraicApproximations.1 hα).2.2.1)
    fun _ hε ↦ exists_algebraicApprox_lt_eps_of_mahlerExponent_eq_top htop hu0 hε

/-- **Infinite Koksma and Mahler exponents coincide.** For every `n : ℕ` and `ξ : ℝ`,
`w*ₙ(ξ) = ⊤ ↔ wₙ(ξ) = ⊤`: Mahler's `U`-numbers and Koksma's `U*`-numbers agree in every degree. -/
theorem algebraicApproximationExponent_eq_top_iff (n : ℕ) (ξ : ℝ) :
    algebraicApproximationExponent n ξ = ⊤ ↔ mahlerExponent n ξ = ⊤ := by
  refine ⟨fun h ↦ top_unique (h ▸ algebraicApproximationExponent_le_mahlerExponent n ξ),
    fun htop ↦ by_contra fun hne ↦ ?_⟩
  set u : ℝ := (algebraicApproximationExponent n ξ).toReal + 1
  have hu0 : 0 < u := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  have hle := ENNReal.toReal_mono hne (le_algebraicApproximationExponent_of_infinite
    (infinite_algebraicApproximations_of_mahlerExponent_eq_top htop hu0))
  rw [ENNReal.toReal_ofReal hu0.le] at hle
  linarith

/-! ### Wirsing's third inequality and exact values for algebraic numbers -/

/-- **Wirsing's third inequality** (Wirsing 1961; Bugeaud, Theorem 3.4). For every `n : ℕ` and
every `ξ : ℝ`, `wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)` in `ℝ≥0∞`. At `wₙ(ξ) = n` this reads
`n ≤ w*ₙ(ξ)`; at `wₙ(ξ) = ⊤` the left-hand side is `⊤ / ⊤ = 0`, while
`algebraicApproximationExponent_eq_top_iff` gives `w*ₙ(ξ) = ⊤`; and when `ξ` is algebraic of
degree `D ≤ n`, truncated subtraction sets `wₙ(ξ) - n = 0` so both sides equal `D - 1`. -/
theorem div_le_algebraicApproximationExponent (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ / (mahlerExponent n ξ - n + 1) ≤ algebraicApproximationExponent n ξ := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hm0 : mahlerExponent n ξ ≠ 0 := fun h0 ↦ by simp [h0] at hr
  have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h0 ↦ hm0 (by simp [h0])
  have hξ : Irrational ξ := fun ⟨q, hq⟩ ↦ hm0 (hq ▸ mahlerExponent_ratCast n q)
  have hr' : ENNReal.ofReal (r : ℝ) <
      max 1 (mahlerExponent n ξ / (mahlerExponent n ξ - n + 1)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hr.trans_le (le_max_right 1 _)
  have hinf := infinite_preimage_ofReal_algebraicApproximations_of_lt_max hn hξ hr'
  simpa [ENNReal.ofReal_coe_nnreal] using le_algebraicApproximationExponent_of_infinite
    ((hinf.image Complex.ofReal_injective.injOn).mono (Set.image_preimage_subset _ _))

/-- For a real algebraic number `ξ` of degree `n + 1` over `ℚ`, Koksma's exponent in degree `n` is
`n`, matching Mahler's exponent `mahlerExponent_eq_of_natDegree_minpoly_eq`. -/
theorem algebraicApproximationExponent_eq_of_natDegree_minpoly_eq {ξ : ℝ} {n : ℕ}
    (hn : (minpoly ℚ ξ).natDegree = n + 1) :
    algebraicApproximationExponent n ξ = n := by
  have hξ : IsAlgebraic ℚ ξ :=
    (by_contra fun h ↦ by simp [minpoly.eq_zero h] at hn : IsIntegral ℚ ξ).isAlgebraic
  refine le_antisymm (by simpa [hn] using hξ.algebraicApproximationExponent_le n) ?_
  simpa [mahlerExponent_eq_of_natDegree_minpoly_eq hn] using
    div_le_algebraicApproximationExponent n ξ

end TauCeti

/-- If `ξ` is a real algebraic number of degree `D ≤ n + 1` over `ℚ`, then `w*ₙ(ξ) = D - 1`. -/
theorem IsAlgebraic.algebraicApproximationExponent_eq_of_natDegree_minpoly_le {ξ : ℝ}
    (hξ : IsAlgebraic ℚ ξ) {n : ℕ} (hn : (minpoly ℚ ξ).natDegree ≤ n + 1) :
    TauCeti.algebraicApproximationExponent n ξ = ((minpoly ℚ ξ).natDegree - 1 : ℕ) := by
  have hpos : 1 ≤ (minpoly ℚ ξ).natDegree := minpoly.natDegree_pos hξ.isIntegral
  refine le_antisymm (hξ.algebraicApproximationExponent_le n) ?_
  calc (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞)
      = TauCeti.algebraicApproximationExponent ((minpoly ℚ ξ).natDegree - 1) ξ :=
        (TauCeti.algebraicApproximationExponent_eq_of_natDegree_minpoly_eq (by omega)).symm
    _ ≤ TauCeti.algebraicApproximationExponent n ξ :=
        TauCeti.algebraicApproximationExponent_mono ξ (by omega)

namespace TauCeti

/-! ### Boundary examples -/

/-- At any Liouville number `ξ` and any `n ≥ 1`, both `wₙ(ξ)` and `w*ₙ(ξ)` are `⊤`, while the
left-hand side of `div_le_algebraicApproximationExponent` evaluates to `0` under `⊤ / ⊤ = 0`. -/
example {ξ : ℝ} (hξ : Liouville ξ) {n : ℕ} (hn : 1 ≤ n) :
    mahlerExponent n ξ = ⊤ ∧ algebraicApproximationExponent n ξ = ⊤ ∧
      mahlerExponent n ξ / (mahlerExponent n ξ - n + 1) = 0 := by
  have hw1 : mahlerExponent 1 ξ = ⊤ := by
    have h := mahlerExponent_one_add_one ξ
    rw [(irrationalityExponent_eq_top_iff ξ).2 hξ] at h
    simpa [ENNReal.add_eq_top] using h
  have hwn : mahlerExponent n ξ = ⊤ := top_unique (hw1 ▸ mahlerExponent_mono ξ hn)
  exact ⟨hwn, (algebraicApproximationExponent_eq_top_iff n ξ).2 hwn, by simp [hwn]⟩

/-- For `√2` (algebraic of degree `2`), both `wₙ(√2)` and `w*ₙ(√2)` equal `1` for every `n ≥ 1`. -/
example {n : ℕ} (hn : 1 ≤ n) :
    mahlerExponent n (Real.sqrt 2) = 1 ∧ algebraicApproximationExponent n (Real.sqrt 2) = 1 := by
  have hp0 : (X ^ 2 - C (2 : ℚ)) ≠ 0 := (monic_X_pow_sub_C (2 : ℚ) (by norm_num)).ne_zero
  have hp2 : aeval (Real.sqrt 2) (X ^ 2 - C (2 : ℚ)) = 0 := by
    simp [aeval_def, Real.sq_sqrt zero_le_two]
  have halg : IsAlgebraic ℚ (Real.sqrt 2) := ⟨X ^ 2 - C 2, hp0, hp2⟩
  have hdeg_le : (minpoly ℚ (Real.sqrt 2)).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ _ hp2) hp0).trans (by compute_degree!)
  have hdeg_ge : 2 ≤ (minpoly ℚ (Real.sqrt 2)).natDegree :=
    (minpoly.two_le_natDegree_iff halg.isIntegral).2 fun ⟨q, hq⟩ ↦
      irrational_sqrt_two ⟨q, by simpa using hq⟩
  have hdeg : (minpoly ℚ (Real.sqrt 2)).natDegree = 2 := le_antisymm hdeg_le hdeg_ge
  exact ⟨by simpa [hdeg] using halg.mahlerExponent_eq_of_natDegree_minpoly_le (n := n) (by omega),
    by simpa [hdeg] using
      halg.algebraicApproximationExponent_eq_of_natDegree_minpoly_le (n := n) (by omega)⟩

end TauCeti
