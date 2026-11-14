/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.AlgebraicExponent
public import TauCeti.NumberTheory.DiophantineApproximation.MahlerExponent
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.CountableDenseLinearOrder
import TauCeti.Analysis.Polynomial.SupNorm.Location
import TauCeti.Analysis.Polynomial.SupNorm.Northcott
import TauCeti.NumberTheory.GeometryOfNumbers.LinearForms
import TauCeti.NumberTheory.Height.Comparison

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
parameter `H`, Minkowski's linear forms theorem applied to the Vandermonde matrix at the `m + 2`
points `ξ, ξ + 2, …, ξ + m + 2` produces a nonzero `P ∈ ℤ[X]` of degree at most `m + 1` with
`|P(ξ)| ≤ H ^ (-w')`, `|P(ξ + 2 + k)| ≤ H` at the first `m` auxiliary points, and
`P.supNorm ≤ C₁ H ^ (w' - m)`. Because `w'' > w₀`, only finitely many integer polynomials violate
`|P(ξ)| > P.supNorm ^ (-w'')`; for large `H` this forces `P.supNorm > H ^ (w' / w'')`. Since
`w' / w'' > 1`, `P` is small relative to `P.supNorm` at all `m + 1` separated real points
`ξ, ξ + 2, …, ξ + m + 1`. Root location (`SupNorm.Location`) then places a unique simple root of
`P` within `1 / 2` of each of these `m + 1` points; the root `x` near `ξ` is real by conjugation
symmetry, satisfies `P.supNorm * |ξ - x| ≤ K₀ |P(ξ)|` because the remaining `m` roots stay at
distance at least `1` from `ξ`, and inherits `naiveHeight x ≤ 2 ^ (m + 1) P.supNorm` from Gelfond's
divisor bound (`Height.Comparison`). Letting `H → ∞` and `w' ↓ w₀` yields infinitely many real
algebraic approximants for every exponent below `w₀ / (w₀ - n + 1)`.

At `wₙ(ξ) = ⊤`, the `ℝ≥0∞` quotient `⊤ / ⊤` evaluates to `0`, while single-point root location
shows directly that `w*ₙ(ξ) = ⊤ ↔ wₙ(ξ) = ⊤` (`TauCeti.algebraicApproximationExponent_eq_top_iff`),
so `1 ≤ w*ₙ(ξ)` holds whenever `1 ≤ n` and `ξ` is not algebraic of degree at most `n`
(`TauCeti.one_le_algebraicApproximationExponent`). For algebraic `ξ` of degree `D ≤ n + 1`,
combining Wirsing's third inequality at `D - 1`, monotonicity in `n`, and Liouville's upper bound
determines both exponents unconditionally: `wₙ(ξ) = w*ₙ(ξ) = D - 1`.

## Main results

* `TauCeti.div_le_algebraicApproximationExponent`: Wirsing's third inequality
  `wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)`, with no hypothesis on `n` or `ξ`.
* `TauCeti.infinite_real_algebraicApproximations_of_lt`: for `ξ` not algebraic of degree at most
  `n`, every real exponent strictly below `wₙ(ξ) / (wₙ(ξ) - n + 1)` is achieved by infinitely many
  real algebraic numbers of degree at most `n`.
* `TauCeti.algebraicApproximationExponent_eq_top_iff`: `w*ₙ(ξ) = ⊤ ↔ wₙ(ξ) = ⊤`.
* `TauCeti.one_le_algebraicApproximationExponent`: `1 ≤ w*ₙ(ξ)` when `1 ≤ n` and `ξ` is not
  algebraic of degree at most `n`.
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

/-! ### Liouville's upper bound for Koksma's exponent -/

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

/-! ### Non-vanishing and Vandermonde–Minkowski polynomial construction -/

/-- For `P ∈ ℤ[X]` of degree at most `n`, the sup norm of `coeffVec n P` equals `P.supNorm`. -/
private theorem norm_coeffVec_eq_supNorm {n : ℕ} {P : ℤ[X]} (hP : P.natDegree ≤ n) :
    ‖coeffVec n P‖ = P.supNorm :=
  le_antisymm (norm_coeffVec_le n P) <| by
    simpa only [linearFormPoly_coeffVec hP] using supNorm_linearFormPoly_le (coeffVec n P)

/-- Any root `x` in a characteristic-zero field of a nonzero `P ∈ ℤ[X]` of degree at most `n` is
algebraic over `ℚ` of degree at most `n`. -/
private theorem isAlgebraic_and_natDegree_le_of_aeval_eq_zero {F : Type*} [Field F] [CharZero F]
    {n : ℕ} {x : F} {P : ℤ[X]} (hP0 : P ≠ 0) (hP : P.natDegree ≤ n) (hx : aeval x P = 0) :
    IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ n := by
  have hQ0 : P.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP0
  have hQx : aeval x (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [← algebraMap_int_eq, aeval_map_algebraMap, hx]
  exact ⟨⟨_, hQ0, hQx⟩,
    (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ x hQx) hQ0).trans
      (Polynomial.natDegree_map_le.trans hP)⟩

/-- If `ξ` is not algebraic of degree at most `n`, no nonzero integer polynomial of degree at most
`n` vanishes at `ξ`. -/
private theorem aeval_ne_zero_of_not_natDegree_le {n : ℕ} {ξ : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n)) {P : ℤ[X]} (hP0 : P ≠ 0)
    (hP : P.natDegree ≤ n) : aeval ξ P ≠ 0 := fun h0 ↦
  hξ (isAlgebraic_and_natDegree_le_of_aeval_eq_zero hP0 hP h0)

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

/-- Given `n + 1` distinct real points `β : Fin (n + 1) → ℝ`, Minkowski's linear forms theorem
applied to `Matrix.vandermonde β` yields a constant `C ≥ 1` such that any bounds `0 ≤ a i ≤ B` with
`|(Matrix.vandermonde β).det| ≤ ∏ i, a i` admit a nonzero `P ∈ ℤ[X]` of degree at most `n` with
`|P(β i)| ≤ a i` and `P.supNorm ≤ C * B`. -/
private theorem exists_ge_one_forall_exists_poly_abs_aeval_le {n : ℕ} {β : Fin (n + 1) → ℝ}
    (hinj : Function.Injective β) :
    ∃ C ≥ 1, ∀ (a : Fin (n + 1) → ℝ) (B : ℝ), 0 ≤ a →
      |(Matrix.vandermonde β).det| ≤ ∏ i, a i → (∀ i, a i ≤ B) →
      ∃ P : ℤ[X], P ≠ 0 ∧ P.natDegree ≤ n ∧ (∀ i, |aeval (β i) P| ≤ a i) ∧
        P.supNorm ≤ C * B := by
  set V := Matrix.vandermonde β
  have hdet : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hinj
  let e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    ((Matrix.toLin' V).equivOfDetNeZero (by rwa [LinearMap.det_toLin'])).toContinuousLinearEquiv
  set C := max 1 ‖(e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))‖
  refine ⟨C, le_max_left _ _, fun a B ha hprod hB ↦ ?_⟩
  have hB0 : 0 ≤ B := (ha 0).trans (hB 0)
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_ne_zero_int_abs_sum_mul_le V hdet ha hprod
  set x : ℤ × (Fin n → ℤ) := (z 0, fun j ↦ z j.succ)
  set P : ℤ[X] := linearFormPoly x
  have hP0 : P ≠ 0 := fun h0 ↦ by
    have hx0 : x = 0 := norm_eq_zero.1 <| by
      rw [← coeffVec_linearFormPoly x, norm_coeffVec_eq_supNorm (natDegree_linearFormPoly_le x),
        show linearFormPoly x = 0 from h0, supNorm_zero]
    exact hz0 <| funext <| Fin.cases (congrArg Prod.fst hx0)
      fun j ↦ congrFun (congrArg Prod.snd hx0) j
  have heval (i : Fin (n + 1)) : aeval (β i) P = ∑ k, V i k * (z k : ℝ) := by
    rw [aeval_linearFormPoly, Fin.sum_univ_succ]
    simp [V, x, mul_comm]
  -- Invert `V` continuously to bound the integer coefficient vector `z` by `C * B`.
  set zR : Fin (n + 1) → ℝ := fun k ↦ z k
  have hez : ‖e zR‖ ≤ B := (pi_norm_le_iff_of_nonneg hB0).2 fun i ↦ by
    have hi : (e zR) i = ∑ k, V i k * zR k := by
      simp [e, Matrix.mulVec_apply_eq_sum]
    rw [Real.norm_eq_abs, hi]
    exact (hz i).trans (hB i)
  have hzR : ‖zR‖ ≤ C * B := by
    calc ‖zR‖ = ‖e.symm (e zR)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖(e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))‖ * ‖e zR‖ :=
          (e.symm : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).le_opNorm (e zR)
      _ ≤ C * B := mul_le_mul (le_max_right _ _) hez (norm_nonneg _) (by positivity)
  have hx : ‖x‖ ≤ ‖zR‖ := max_le
    (by simpa [x, zR, Int.norm_eq_abs] using norm_le_pi_norm zR 0)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg zR)).2 fun j ↦ by
      simpa [x, zR, Int.norm_eq_abs] using norm_le_pi_norm zR j.succ)
  exact ⟨P, hP0, natDegree_linearFormPoly_le x, fun i ↦ heval i ▸ hz i,
    (supNorm_linearFormPoly_le x).trans (hx.trans hzR)⟩

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
  obtain ⟨CV, hCV, hmink⟩ := exists_ge_one_forall_exists_poly_abs_aeval_le hinj
  set Ddet := |(Matrix.vandermonde β).det|
  refine ⟨CV * max 1 Ddet, one_le_mul_of_one_le_of_one_le hCV (le_max_left _ _),
    fun H w' hH1 hw' ↦ ?_⟩
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  let a : Fin (m + 2) → ℝ :=
    Fin.cases (H ^ (-w')) (Fin.lastCases (Ddet * H ^ (w' - m)) fun _ : Fin m ↦ H)
  have ha0 : 0 ≤ a := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · dsimp only [a]; rw [Fin.cases_zero]; positivity
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl <;>
        · dsimp only [a]; simp only [Fin.cases_succ, Fin.lastCases_castSucc, Fin.lastCases_last]
          positivity
  have haprod : Ddet ≤ ∏ i, a i := by
    rw [Fin.prod_univ_succ]
    dsimp only [a]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [Fin.prod_univ_castSucc, Fin.lastCases_last]
    simp only [Fin.lastCases_castSucc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hpow : H ^ (-w') * (H ^ m * (Ddet * H ^ (w' - m))) = Ddet := by
      rw [← Real.rpow_natCast H m]
      calc H ^ (-w') * (H ^ (m : ℝ) * (Ddet * H ^ (w' - m)))
          = Ddet * (H ^ (-w') * H ^ (m : ℝ) * H ^ (w' - m)) := by ring
        _ = Ddet * H ^ (-w' + m + (w' - m)) := by rw [← Real.rpow_add hH0, ← Real.rpow_add hH0]
        _ = Ddet := by norm_num
    exact hpow.symm.le
  have haB (i : Fin (m + 2)) : a i ≤ max 1 Ddet * H ^ (w' - m) := by
    have h1wm : 1 ≤ H ^ (w' - m) := Real.one_le_rpow hH1 (by linarith)
    have hHwm : H ≤ H ^ (w' - m) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hH1 (by linarith : (1 : ℝ) ≤ w' - m)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · dsimp only [a]; rw [Fin.cases_zero]
      exact ((Real.rpow_le_one_of_one_le_of_nonpos hH1
        (by linarith [Nat.cast_nonneg (α := ℝ) m])).trans h1wm).trans
        (le_mul_of_one_le_left (by positivity) (le_max_left 1 Ddet))
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · dsimp only [a]; rw [Fin.cases_succ, Fin.lastCases_castSucc]
        exact hHwm.trans (le_mul_of_one_le_left (by positivity) (le_max_left 1 Ddet))
      · dsimp only [a]; rw [Fin.cases_succ, Fin.lastCases_last]
        exact mul_le_mul_of_nonneg_right (le_max_right 1 Ddet) (by positivity)
  obtain ⟨P, hP0, hPdeg, hPeval, hPsup⟩ := hmink a (max 1 Ddet * H ^ (w' - m)) ha0 haprod haB
  exact ⟨P, hP0, hPdeg, by simpa [β, wirsingPoints, a] using hPeval 0,
    fun k ↦ by simpa [β, a] using hPeval (Fin.castSucc k).succ,
    by simpa [mul_assoc] using hPsup⟩

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
  have hp0 : p ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hP0
  have hpdeg : p.natDegree ≤ m + 1 := Polynomial.natDegree_map_le.trans hPdeg
  have hpsup : p.supNorm = P.supNorm := P.supNorm_map (Int.castRingHom ℂ)
  have hγsep : Pairwise fun i j ↦ 2 * (1 / 2 : ℝ) ≤ ‖γ i - γ j‖ := fun i j hij ↦ by
    simpa [γ, ← Complex.ofReal_sub, Complex.norm_real] using
      hsep (Fin.castSucc_injective _ |>.ne hij)
  have hγeval (j : Fin (m + 1)) :
      ‖p.eval (γ j)‖ < (1 / 2 / (4 * (‖γ j‖ + 1))) ^ (m + 1) * p.supNorm := by
    have hjH : ‖p.eval (γ j)‖ ≤ H := by
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · have h0 : ‖p.eval (γ 0)‖ = |aeval ξ P| := by
          simpa [p, γ, wirsingPoints, ← algebraMap_int_eq, aeval_map_algebraMap] using
            congrArg norm (aeval_algebraMap_apply ℂ ξ P)
        exact h0.trans_le (hPξ.trans ((Real.rpow_le_one_of_one_le_of_nonpos hH
          (neg_nonpos.2 hw')).trans hH))
      · have hk : ‖p.eval (γ k.succ)‖ = |aeval (wirsingPoints m ξ (Fin.castSucc k).succ) P| := by
          simpa [p, γ, Fin.castSucc_succ, ← algebraMap_int_eq, aeval_map_algebraMap] using
            congrArg norm (aeval_algebraMap_apply ℂ (wirsingPoints m ξ (Fin.castSucc k).succ) P)
        exact hk.trans_le (hPk k)
    have hγnorm : ‖γ j‖ ≤ |ξ| + m + 2 := by simpa [γ, Complex.norm_real] using hbound j
    rw [hpsup]
    exact hjH.trans_lt (hPloc.trans_le (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by gcongr) _) P.supNorm_nonneg))
  obtain ⟨α, _, henum, _, hdist⟩ :=
    p.exists_isRootEnumeration_of_forall_norm_eval_lt hp0
      (by simpa [Fintype.card_fin] using hpdeg) (by norm_num) (by norm_num) hγsep
      (by simpa [Fintype.card_fin] using hγeval)
  -- Every root `α j` (`j ≠ 0`) stays at distance `≥ 1` from `ξ`, and all have norm `≤ |ξ| + m + 3`.
  have hfar (j : Fin (m + 1)) (hj : j ≠ 0) : 1 ≤ ‖(ξ : ℂ) - α j‖ := by
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hj
    have h2 : 2 ≤ ‖(ξ : ℂ) - γ k.succ‖ := by
      simpa [γ, Fin.castSucc_succ, ← Complex.ofReal_sub, Complex.norm_real, abs_sub_comm] using
        hfar2 (Fin.castSucc k)
    have htri := norm_sub_le ((ξ : ℂ) - α k.succ) (γ k.succ - α k.succ)
    rw [sub_sub_sub_cancel_right] at htri
    linarith [hdist k.succ]
  have hαB (j : Fin (m + 1)) : ‖α j‖ ≤ |ξ| + m + 3 := by
    have htri := norm_sub_le (γ j) (γ j - α j)
    rw [sub_sub_cancel] at htri
    have hγj : ‖γ j‖ ≤ |ξ| + m + 2 := by simpa [γ, Complex.norm_real] using hbound j
    linarith [hdist j]
  have him : (α 0).im = 0 := by
    have hrh : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    have henumR : (P.map (Int.castRingHom ℝ)).IsRootEnumeration α := by
      rw [isRootEnumeration_iff, Polynomial.map_map, hrh]
      simpa [isRootEnumeration_iff, p] using henum
    exact henumR.im_eq_zero_of_norm_sub_lt (by simpa [γ, wirsingPoints] using hdist 0)
      fun j hj ↦ (by norm_num : (1 / 2 : ℝ) ≤ 1).trans (hfar j hj)
  set x : ℝ := (α 0).re
  have hxC : (x : ℂ) = α 0 := Complex.ext rfl him.symm
  have hxP : aeval x P = 0 := by
    have hmem : α 0 ∈ p.rootSet ℂ := henum.range_eq_rootSet ▸ Set.mem_range_self 0
    have hev : aeval (x : ℂ) P = 0 := by
      simpa [p, ← hxC, ← algebraMap_int_eq, aeval_map_algebraMap] using (mem_rootSet.1 hmem).2
    have hcoe : (aeval x P : ℂ) = aeval (x : ℂ) P := (aeval_algebraMap_apply ℂ x P).symm
    exact Complex.ofReal_injective (by rw [hcoe, hev, Complex.ofReal_zero])
  obtain ⟨halg, hxdeg⟩ := isAlgebraic_and_natDegree_le_of_aeval_eq_zero hP0 hPdeg hxP
  have hxne : x ≠ ξ := fun h ↦ aeval_ne_zero_of_not_natDegree_le hξ hP0 hPdeg (h ▸ hxP)
  have hest := henum.supNorm_mul_norm_sub_le_two_mul_pow_mul_norm_eval 0
    (B := |ξ| + m + 3) (by linarith [abs_nonneg ξ, Nat.cast_nonneg (α := ℝ) m]) hαB hfar
  have hevalξ : ‖p.eval (ξ : ℂ)‖ = |aeval ξ P| := by
    simpa [p, ← algebraMap_int_eq, aeval_map_algebraMap] using
      congrArg norm (aeval_algebraMap_apply ℂ ξ P)
  rw [Fintype.card_fin, hpsup, ← hxC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    hevalξ] at hest
  exact ⟨x, halg, hxdeg, abs_pos.2 (sub_ne_zero.2 hxne.symm),
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

/-- For fixed `m`, `ξ` not algebraic of degree at most `m + 1`, `0 ≤ u < w₀ / (w₀ - m)`, and any
threshold `ε > 0`, there exists a real algebraic number `x` of degree at most `m + 1` with
`0 < |ξ - x| < ε` and `|ξ - x| ≤ naiveHeight x ^ (-u - 1)`. -/
private theorem exists_real_approx_lt_eps {m : ℕ} {ξ u ε : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ m + 1))
    (htop : mahlerExponent (m + 1) ξ ≠ ⊤) (hu0 : 0 ≤ u)
    (hu : u < (mahlerExponent (m + 1) ξ).toReal / ((mahlerExponent (m + 1) ξ).toReal - m))
    (hε : 0 < ε) :
    ∃ x : ℝ, IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ m + 1 ∧ 0 < |ξ - x| ∧ |ξ - x| < ε ∧
      |ξ - x| ≤ naiveHeight x ^ (-u - 1) := by
  set w₀ := (mahlerExponent (m + 1) ξ).toReal
  have hw₀ : (m : ℝ) + 1 ≤ w₀ := by
    have h := ENNReal.toReal_mono htop (natCast_le_mahlerExponent hξ)
    rw [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one] at h
    exact h
  obtain ⟨w', hw₀w', huw'⟩ := exists_gt_and_lt_div_sub hw₀ hu
  let w'' := (w₀ + w') / 2
  have hw''_gt : w₀ < w'' := by dsimp [w'']; linarith
  have hw''_lt : w'' < w' := by dsimp [w'']; linarith
  have hmah : mahlerExponent (m + 1) ξ < ENNReal.ofReal w'' := by
    rw [← ENNReal.ofReal_toReal htop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [Nat.cast_nonneg (α := ℝ) m])).2 hw''_gt
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_forall_rpow_neg_lt_abs_aeval hξ hmah
  obtain ⟨C₁, hC₁, hpoly⟩ := exists_ge_one_forall_exists_poly_wirsing m ξ
  set cloc : ℝ := (1 / 2 / (4 * (|ξ| + m + 2 + 1))) ^ (m + 1)
  set K₀ : ℝ := (2 * (|ξ| + m + 3)) ^ (m + 1)
  set Ktot : ℝ := 2 ^ (m + 1) * K₀ * (2 ^ (m + 1) * C₁) ^ u
  -- Choose `H` large enough that all four asymptotic inequalities hold simultaneously.
  have hexp1 : 0 < w' / w'' - 1 :=
    sub_pos.2 ((one_lt_div (by linarith [Nat.cast_nonneg (α := ℝ) m])).2 hw''_lt)
  have hexp2 : 0 < w' - u * (w' - m) := sub_pos.2 ((lt_div_iff₀ (by linarith)).1 huw')
  obtain ⟨H, ⟨⟨hH1, hHδ⟩, hHloc, hHε, hHK⟩⟩ :=
    (((eventually_ge_atTop (1 : ℝ)).and
      ((tendsto_rpow_neg_atTop (by linarith [Nat.cast_nonneg (α := ℝ) m] : 0 < w')).eventually
        (gt_mem_nhds hδ))).and
      (((tendsto_rpow_atTop hexp1).eventually_gt_atTop cloc⁻¹).and
        (((tendsto_rpow_neg_atTop (by linarith [Nat.cast_nonneg (α := ℝ) m] : 0 < w')).eventually
          (gt_mem_nhds (div_pos hε (by positivity : 0 < K₀)))).and
          ((tendsto_rpow_neg_atTop hexp2).eventually
            (gt_mem_nhds (inv_pos.2 (by positivity : 0 < Ktot))))))).exists
  have hH0 : 0 < H := zero_lt_one.trans_le hH1
  obtain ⟨P, hP0, hPdeg, hPξ, hPk, hPsup'⟩ := hpoly H w' hH1 (by linarith)
  obtain ⟨hP1, hPlow⟩ := hgap P hP0 hPdeg (hPξ.trans_lt hHδ)
  have hPsup_gt : H ^ (w' / w'') < P.supNorm := not_le.1 fun hle ↦ hPlow.not_ge <| by
    have h := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hP1) hle
      (by linarith [Nat.cast_nonneg (α := ℝ) m] : -w'' ≤ 0)
    have hexp : w' / w'' * -w'' = -w' := by
      have : w'' ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      field_simp
    rw [← Real.rpow_mul hH0.le, hexp] at h
    exact hPξ.trans h
  have hPloc : H < cloc * P.supNorm := by
    have hcloc0 : 0 < cloc := by positivity
    have h1 : H < cloc * H ^ (w' / w'') := by
      calc H = cloc * (cloc⁻¹ * H) := by rw [← mul_assoc, mul_inv_cancel₀ hcloc0.ne', one_mul]
        _ < cloc * (H ^ (w' / w'' - 1) * H) := by gcongr
        _ = cloc * H ^ (w' / w'') := by rw [← Real.rpow_add_one hH0.ne', sub_add_cancel]
    exact h1.trans (mul_lt_mul_of_pos_left hPsup_gt hcloc0)
  obtain ⟨x, halg, hxdeg, hxpos, hxest, hxh⟩ :=
    exists_real_root_of_poly_wirsing hξ hH1 (by linarith [Nat.cast_nonneg (α := ℝ) m]) hP0 hPdeg
      hPξ hPk hPloc
  exact ⟨x, halg, hxdeg, hxpos,
    ((le_mul_of_one_le_left (abs_nonneg _) hP1.le).trans hxest).trans_lt
      ((lt_div_iff₀' (by positivity)).1 hHε),
    abs_sub_le_naiveHeight_rpow_of_wirsing_bounds hH0 hu0 hC₁ (by positivity)
      hxest hxh hPsup' hHK⟩

/-! ### Real algebraic approximants and the infinite-exponent regime -/

/-- **Wirsing's theorem with real algebraic approximants.** If `ξ` is not algebraic of degree at
most `n`, every real exponent `w` strictly below `wₙ(ξ) / (wₙ(ξ) - n + 1)` is achieved by
infinitely many **real** algebraic numbers `x` of degree at most `n`. -/
theorem infinite_real_algebraicApproximations_of_lt {n : ℕ} {ξ w : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n))
    (hw : ENNReal.ofReal w < mahlerExponent n ξ / (mahlerExponent n ξ - n + 1)) :
    {x : ℝ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ n ∧ 0 < |ξ - x| ∧
      |ξ - x| ≤ naiveHeight x ^ (-w - 1)}.Infinite := by
  rcases n with _ | m
  · simp at hw
  have htop : mahlerExponent (m + 1) ξ ≠ ⊤ := fun ht ↦ by simp [ht] at hw
  set w₀ := (mahlerExponent (m + 1) ξ).toReal
  have hw₀ : (m : ℝ) + 1 ≤ w₀ := by
    have h := ENNReal.toReal_mono htop (natCast_le_mahlerExponent hξ)
    rw [ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_one] at h
    exact h
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
  have hw_lt : w < w₀ / (w₀ - m) := (ENNReal.ofReal_lt_ofReal_iff hq_pos).1 hw
  set u := max w 0
  have hu : u < w₀ / (w₀ - m) := max_lt hw_lt hq_pos
  set S := {x : ℝ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ m + 1 ∧ 0 < |ξ - x| ∧
    |ξ - x| ≤ naiveHeight x ^ (-u - 1)}
  have hS : S.Infinite := by
    intro hfin
    obtain ⟨ε, hε0, hε⟩ := Order.exists_between_finsets {0} (hfin.image (|ξ - ·|)).toFinset (by
      simp only [Finset.mem_singleton, forall_eq]
      rintro _ hy
      obtain ⟨x, hx, rfl⟩ := (hfin.image _).mem_toFinset.1 hy
      exact hx.2.2.1)
    obtain ⟨x, halg, hxdeg, hxpos, hxlt, hxle⟩ :=
      exists_real_approx_lt_eps hξ htop (le_max_right w 0) hu (hε0 0 (Finset.mem_singleton_self 0))
    have hxS : x ∈ S := ⟨halg, hxdeg, hxpos, hxle⟩
    exact (hε _ ((hfin.image _).mem_toFinset.2 ⟨x, hxS, rfl⟩)).not_gt hxlt
  refine hS.mono fun x (hx : x ∈ S) ↦ ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_naiveHeight x)
    (by linarith [le_max_left w 0])

/-- If `ξ` is not algebraic of degree at most `n`, then `wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)`. -/
private theorem div_le_algebraicApproximationExponent_of_not_natDegree_le {n : ℕ} {ξ : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n)) :
    mahlerExponent n ξ / (mahlerExponent n ξ - n + 1) ≤ algebraicApproximationExponent n ξ := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hr' : ENNReal.ofReal (r : ℝ) < mahlerExponent n ξ / (mahlerExponent n ξ - n + 1) := by
    simpa [ENNReal.ofReal_coe_nnreal] using hr
  have hinf := infinite_real_algebraicApproximations_of_lt hξ hr'
  have hinfC : (algebraicApproximations n ξ r).Infinite := by
    refine (hinf.image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨x, ⟨halg, hxdeg, hxpos, hxle⟩, rfl⟩
    rw [mem_algebraicApproximations]
    refine ⟨halg.algebraMap, ?_, ?_, ?_⟩
    · have hmin : minpoly ℚ (x : ℂ) = minpoly ℚ x :=
        minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective x
      rwa [hmin]
    · simpa [← Complex.ofReal_sub, Complex.norm_real] using hxpos
    · simpa [← Complex.ofReal_sub, Complex.norm_real,
        show naiveHeight (x : ℂ) = naiveHeight x from naiveHeight_map Complex.ofRealHom x] using
        hxle
  simpa [ENNReal.ofReal_coe_nnreal] using le_algebraicApproximationExponent_of_infinite hinfC

/-- Single-point root location at a polynomial `P` of degree at most `n` with
`|P(ξ)| ≤ P.supNorm ^ (-n (u + 2))` and sufficiently large `P.supNorm` produces an algebraic
approximation to `ξ` of exponent `u` within `ε`. -/
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
  rw [mem_linearFormApproximations] at hxS
  set P := linearFormPoly x
  have hPdeg : P.natDegree ≤ n := natDegree_linearFormPoly_le x
  have hPsup : P.supNorm = ‖x‖ := (norm_coeffVec_eq_supNorm hPdeg).symm.trans
    (by rw [coeffVec_linearFormPoly])
  have hHP1 : 1 < P.supNorm := (le_max_left 1 _).trans_lt (hPsup ▸ hxM)
  have hHP0 : 0 < P.supNorm := zero_lt_one.trans hHP1
  set r : ℝ := K * P.supNorm ^ (-(u + 2))
  have hr_inv : r ≤ K / P.supNorm := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hHP1.le (by linarith)) (by positivity)
  have hr1 : r ≤ 1 := hr_inv.trans <| (div_le_one hHP0).2 <|
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hPsup ▸ hxM.le)
  have hrε : r < ε := hr_inv.trans_lt <| (div_lt_iff₀ hHP0).2 <| by
    have hKM : K / ε < P.supNorm :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans_lt (hPsup ▸ hxM)
    have := (div_lt_iff₀ hε_pos).1 hKM
    linarith
  set p : ℂ[X] := P.map (Int.castRingHom ℂ)
  have hpeval : ‖p.eval (ξ : ℂ)‖ < (r / (4 * (‖(ξ : ℂ)‖ + 1))) ^ n * p.supNorm := by
    have hev : ‖p.eval (ξ : ℂ)‖ = |(x.1 : ℝ) + ∑ j, (x.2 j : ℝ) * ξ ^ (j.val + 1)| := by
      rw [← aeval_linearFormPoly]
      simpa [p, ← algebraMap_int_eq, aeval_map_algebraMap] using
        congrArg norm (aeval_algebraMap_apply ℂ ξ P)
    have hquot_r : r / (4 * (‖(ξ : ℂ)‖ + 1)) = 2 * P.supNorm ^ (-(u + 2)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]; simp only [r, K]; field_simp; ring
    have hpow_r : (2 * P.supNorm ^ (-(u + 2))) ^ n = 2 ^ n * P.supNorm ^ (-w) := by
      rw [mul_pow, ← Real.rpow_natCast (P.supNorm ^ (-(u + 2))) n, ← Real.rpow_mul hHP0.le]
      simp only [w]; ring_nf
    rw [hev, hquot_r, hpow_r, P.supNorm_map (Int.castRingHom ℂ)]
    have h2n : (1 : ℝ) < 2 ^ n * P.supNorm := by
      have : (2 : ℝ) ≤ 2 ^ n := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn1
      nlinarith
    calc |(x.1 : ℝ) + ∑ j, (x.2 j : ℝ) * ξ ^ (j.val + 1)| ≤ P.supNorm ^ (-w) := by
          simpa [hPsup] using hxS.2
      _ < P.supNorm ^ (-w) * (2 ^ n * P.supNorm) := lt_mul_of_one_lt_right (by positivity) h2n
      _ = 2 ^ n * P.supNorm ^ (-w) * P.supNorm := by ring
  obtain ⟨α, hαroot, hαr⟩ := p.exists_isRoot_norm_sub_lt_of_norm_eval_lt (ξ : ℂ)
    (Polynomial.natDegree_map_le.trans hPdeg) (by positivity) hr1 hpeval
  have hP0 : P ≠ 0 := fun h0 ↦
    (abs_pos.1 hxS.1) (by simpa [P, h0] using (aeval_linearFormPoly x ξ).symm)
  have hαP : aeval α P = 0 := by simpa [p, ← algebraMap_int_eq, aeval_map_algebraMap] using hαroot
  obtain ⟨halg, hαdeg⟩ := isAlgebraic_and_natDegree_le_of_aeval_eq_zero hP0 hPdeg hαP
  have hαne : 0 < ‖(ξ : ℂ) - α‖ := norm_pos_iff.2 <| sub_ne_zero.2 fun h ↦ by
    have hξC : IsAlgebraic ℚ (ξ : ℂ) := h ▸ halg
    exact htrans ((isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective).1 hξC)
  have hαle : ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-u - 1) := by
    have hnh : naiveHeight α ≤ 2 ^ n * P.supNorm :=
      (naiveHeight_le_two_pow_mul_supNorm_of_aeval_eq_zero hP0 hαP).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hPdeg) P.supNorm_nonneg)
    have hna0 : 0 < naiveHeight α := zero_lt_one.trans_le (one_le_naiveHeight α)
    have hprod : ‖(ξ : ℂ) - α‖ * naiveHeight α ^ (u + 1) ≤ 1 := by
      calc ‖(ξ : ℂ) - α‖ * naiveHeight α ^ (u + 1)
          ≤ r * (2 ^ n * P.supNorm) ^ (u + 1) :=
            mul_le_mul hαr.le
              (Real.rpow_le_rpow hna0.le hnh (by linarith))
              (Real.rpow_nonneg hna0.le _) (by positivity)
        _ = K * (2 ^ n : ℝ) ^ (u + 1) * (P.supNorm ^ (-(u + 2)) * P.supNorm ^ (u + 1)) := by
            rw [Real.mul_rpow (by positivity) hHP0.le]; simp only [r]; ring
        _ = K * (2 ^ n : ℝ) ^ (u + 1) / P.supNorm := by
            rw [← Real.rpow_add hHP0, show -(u + 2) + (u + 1) = -1 by ring, Real.rpow_neg_one,
              div_eq_mul_inv]
        _ ≤ 1 := (div_le_one hHP0).2 <|
            ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans
              (hPsup ▸ hxM.le)
    rw [show -u - 1 = -(u + 1) by ring, Real.rpow_neg hna0.le, ← one_div,
      le_div_iff₀ (by positivity)]
    exact hprod
  exact ⟨α, mem_algebraicApproximations.2 ⟨halg, hαdeg, hαne, hαle⟩, hαr.trans hrε⟩

/-- When `wₙ(ξ) = ⊤` and `0 < u`, there are infinitely many algebraic approximations to `ξ` of
degree at most `n` and exponent `u`. -/
private theorem infinite_algebraicApproximations_of_mahlerExponent_eq_top {n : ℕ} {ξ u : ℝ}
    (htop : mahlerExponent n ξ = ⊤) (hu0 : 0 < u) :
    (algebraicApproximations n ξ u).Infinite := by
  intro hfin
  obtain ⟨ε, hε0, hε⟩ := Order.exists_between_finsets {0}
    (hfin.image fun α ↦ ‖(ξ : ℂ) - α‖).toFinset (by
      simp only [Finset.mem_singleton, forall_eq]
      rintro _ hy
      obtain ⟨α, hα, rfl⟩ := (hfin.image _).mem_toFinset.1 hy
      rw [mem_algebraicApproximations] at hα
      exact hα.2.2.1)
  obtain ⟨α, hαmem, hαlt⟩ := exists_algebraicApprox_lt_eps_of_mahlerExponent_eq_top htop hu0
    (hε0 0 (Finset.mem_singleton_self 0))
  exact (hε _ ((hfin.image _).mem_toFinset.2 ⟨α, hαmem, rfl⟩)).not_gt hαlt

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

/-! ### Exact values for algebraic numbers of degree `D ≤ n + 1` and Wirsing's third inequality -/

/-- For a real algebraic number `ξ` of degree `n + 1` over `ℚ`, Koksma's exponent in degree `n` is
`n`, matching Mahler's exponent `mahlerExponent_eq_of_natDegree_minpoly_eq`. -/
theorem algebraicApproximationExponent_eq_of_natDegree_minpoly_eq {ξ : ℝ} {n : ℕ}
    (hn : (minpoly ℚ ξ).natDegree = n + 1) :
    algebraicApproximationExponent n ξ = n := by
  have hξ : IsAlgebraic ℚ ξ :=
    (by_contra fun h ↦ by simp [minpoly.eq_zero h] at hn : IsIntegral ℚ ξ).isAlgebraic
  refine le_antisymm (by simpa [hn] using hξ.algebraicApproximationExponent_le n) ?_
  have hw := div_le_algebraicApproximationExponent_of_not_natDegree_le (n := n) (ξ := ξ)
    fun h ↦ by omega
  simpa [mahlerExponent_eq_of_natDegree_minpoly_eq hn] using hw

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

/-- **Wirsing's third inequality** (Wirsing 1961; Bugeaud, Theorem 3.4). For every `n : ℕ` and
every `ξ : ℝ`, `wₙ(ξ) / (wₙ(ξ) - n + 1) ≤ w*ₙ(ξ)` in `ℝ≥0∞`. At `wₙ(ξ) = n` this reads
`n ≤ w*ₙ(ξ)`; at `wₙ(ξ) = ⊤` the left-hand side is `⊤ / ⊤ = 0`, while
`algebraicApproximationExponent_eq_top_iff` gives `w*ₙ(ξ) = ⊤`; and when `ξ` is algebraic of
degree `D ≤ n`, truncated subtraction sets `wₙ(ξ) - n = 0` so both sides equal `D - 1`. -/
theorem div_le_algebraicApproximationExponent (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ / (mahlerExponent n ξ - n + 1) ≤ algebraicApproximationExponent n ξ := by
  by_cases hξ : IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n
  · obtain ⟨halg, hdeg⟩ := hξ
    have hle : (((minpoly ℚ ξ).natDegree - 1 : ℕ) : ℝ≥0∞) ≤ n := by exact_mod_cast (by omega)
    rw [halg.mahlerExponent_eq_of_natDegree_minpoly_le (by omega),
      halg.algebraicApproximationExponent_eq_of_natDegree_minpoly_le (by omega),
      tsub_eq_zero_of_le hle, zero_add, div_one]
  · exact div_le_algebraicApproximationExponent_of_not_natDegree_le hξ

/-- If `1 ≤ n` and `ξ` is not algebraic of degree at most `n`, then `1 ≤ w*ₙ(ξ)`. -/
theorem one_le_algebraicApproximationExponent {n : ℕ} (hn : 1 ≤ n) {ξ : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n)) :
    1 ≤ algebraicApproximationExponent n ξ := by
  by_cases htop : mahlerExponent n ξ = ⊤
  · simp [(algebraicApproximationExponent_eq_top_iff n ξ).2 htop]
  · refine le_trans ?_ (div_le_algebraicApproximationExponent n ξ)
    have hge : (n : ℝ≥0∞) ≤ mahlerExponent n ξ := natCast_le_mahlerExponent hξ
    have h1 : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast hn
    have hden_ne_zero : mahlerExponent n ξ - n + 1 ≠ 0 := by simp
    have hden_ne_top : mahlerExponent n ξ - n + 1 ≠ ⊤ := by
      simp [ENNReal.add_eq_top, ENNReal.sub_eq_top_iff, htop]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hden_ne_zero) (Or.inl hden_ne_top), one_mul]
    calc mahlerExponent n ξ - n + 1 ≤ mahlerExponent n ξ - n + n := add_le_add_right h1 _
      _ = mahlerExponent n ξ := tsub_add_cancel_of_le hge

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
  have hdeg_gt : ¬(minpoly ℚ (Real.sqrt 2)).natDegree ≤ 1 := fun h1 ↦ by
    have hm0 : mahlerExponent 1 (Real.sqrt 2) ≤ 0 := by
      have := halg.mahlerExponent_le 1
      have h0 : ((minpoly ℚ (Real.sqrt 2)).natDegree - 1 : ℕ) = 0 := by omega
      simpa [h0] using this
    have hm1 : mahlerExponent 1 (Real.sqrt 2) + 1 ≤ 0 + 1 := by gcongr
    rw [mahlerExponent_one_add_one, zero_add] at hm1
    have h2 := (two_le_irrationalityExponent_iff (Real.sqrt 2)).2 irrational_sqrt_two
    exact absurd (h2.trans hm1) (by norm_num)
  have hdeg : (minpoly ℚ (Real.sqrt 2)).natDegree = 2 := by omega
  exact ⟨by simpa [hdeg] using halg.mahlerExponent_eq_of_natDegree_minpoly_le (n := n) (by omega),
    by simpa [hdeg] using
      halg.algebraicApproximationExponent_eq_of_natDegree_minpoly_le (n := n) (by omega)⟩

end TauCeti
