/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.HeightApproximation
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Auxiliary
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.IndexEstimate
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.KeyInequality
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Parameters
public import TauCeti.Algebra.Order.Ring.MulGrowth
public import TauCeti.Order.Northcott.Sequence
import TauCeti.Algebra.MvPolynomial.Degrees

/-!
# Roth's theorem

**Roth's theorem** (Roth, 1955): if `α` is a real algebraic number and `κ > 2`, then only
finitely many rational numbers `ξ` satisfy `|ξ - α| ≤ H(ξ) ^ (-κ)`, where `H` is the
multiplicative height `Height.mulHeight₁` on `ℚ`. Equivalently, there is a constant `c > 0`
with `|ξ - α| ≥ c H(ξ) ^ (-κ)` for every `ξ ∈ ℚ` with `ξ ≠ α`; for irrational `α` this holds for
every `ξ ∈ ℚ`. The proof is ineffective: it gives neither a bound for the heights of the
exceptional `ξ` nor a value of `c`. For rational `α` the statement also holds, and is elementary.
The lower bound extends to complex algebraic `α`, since a non-real `α` stays at distance at least
`|im α|` from `ℚ`.

As consequences, a real algebraic number is not a Liouville number with any exponent `p > 2`,
so its irrationality exponent is at most `2`, and exactly `2` if it is irrational.

The proof assembles the steps of the auxiliary polynomial method. Suppose that infinitely many
`ξ` satisfy the inequality. Fix a small `ε > 0` and a number `n` of variables with
`2 d ≤ exp (ε² n / 2)`, where `d` is the degree of `α`.

* Choose good approximations `β₀, β₁, …` of `α` whose logarithmic heights `h(βₖ)` start above a
  large bound `L` and grow by a factor `M` at each step (`Northcott.exists_seq_mem_lt`).
* For `D = h(β_{n-1}) / ε`, the degree bounds `rₖ = ⌊D / h(βₖ)⌋₊` satisfy `rₖ h(βₖ) ≈ D`, and
  Roth's auxiliary polynomial `P ∈ ℤ[X₀, …, X_{n-1}]` with these partial degrees has index at
  least `(n / 2) (1 - ε)` at the diagonal point `(α, …, α)`
  (`TauCeti.exists_roth_auxiliary_polynomial`).
* By Roth's lemma (`TauCeti.weightedIndex_le_of_logHeight_le`), the index of `P` at
  `β = (β₀, …, β_{n-1})` is at most `5 n ε / 2`; the parameters are chosen as in
  `TauCeti.inv_mul_add_le_floor_div_mul`.
* The key inequality (`TauCeti.roth_key_inequality`) then gives
  `κ (1 - ε) (1 / 2 - 3 ε) ≤ 1 + C₂ / (n L)`, which fails for small `ε` and large `L` because
  `κ > 2`.

## Main results

* `IsAlgebraic.finite_setOfPred_abs_sub_le_mulHeight₁_rpow_neg`: Roth's theorem, the finiteness
  of the set of very good rational approximations of a real algebraic number.
* `IsAlgebraic.exists_pos_mul_mulHeight₁_rpow_neg_le_abs_sub`: Roth's theorem as a lower bound
  for `|ξ - α|`, for `ξ ≠ α`.
* `IsAlgebraic.exists_pos_mul_mulHeight₁_rpow_neg_le_norm_sub`: the same lower bound for a
  complex algebraic number `α`.
* `IsAlgebraic.not_liouvilleWith`: a real algebraic number is not `LiouvilleWith p` for `p > 2`.
* `IsAlgebraic.irrationalityExponent_le_two`, `IsAlgebraic.irrationalityExponent_eq_two`: the
  irrationality exponent of a real algebraic number is at most `2`, and equal to `2` if the
  number is irrational.

## References

* K. F. Roth, *Rational approximations to algebraic numbers*, Mathematika 2 (1955), 1–20.
* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), Theorem 3.0.1 and §3.5.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Theorem 6.2.
-/

public section

open Finset Height MvPolynomial Real

namespace TauCeti

/-- The constant `12 b max(1, house α)` in the coefficient bound of Roth's auxiliary polynomial
is at least `2`. -/
private theorem two_le_twelve_mul_max_house (α : ℝ) {b : ℕ} (hb : 0 < b) :
    2 ≤ 12 * b * max 1 (house α) := by
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith [le_max_left 1 (house α)]

/-- The main step of the proof of Roth's theorem. Let `β₀, β₁, …` be rational approximations
of `α` with `|βₖ - α| ≤ H(βₖ) ^ (-κ)`, whose logarithmic heights satisfy `L ≤ h(β₀)` and
`M h(βₖ) ≤ h(βₖ₊₁)`, where `σ M ≥ 2` and `σ⁻¹ (5 C₁ / 2 + 5 n) ≤ L` for
`σ = (5 ε / 4) ^ 2 ^ (n - 1)` and `C₁ = log (12 b max(1, house α))`, where `house α` is the
largest absolute value of the conjugates of `α`. If `n ≥ 1` and
`2 d ≤ exp (ε² n / 2)`, then `κ (1 - ε) (1 / 2 - 3 ε) n ≤ n + C₂ / L`, where
`C₂ = 4 C₁ + 2 log (2 max(1, |α|)) + 4`. -/
private theorem roth_inequality {α : ℝ} {b : ℕ} (hb : 0 < b)
    (hbα : IsIntegral ℤ ((b : ℝ) * α)) {ε : ℝ} (hε₀ : 0 < ε) (hε : ε ≤ 1 / 12) {n : ℕ}
    (hn : 0 < n) (hd : 2 * ((minpoly ℚ α).natDegree : ℝ) ≤ exp (ε ^ 2 * n / 2))
    {κ L M : ℝ} (hκ : 0 ≤ κ) (hM : 2 ≤ (5 * ε / 4) ^ 2 ^ (n - 1) * M)
    (hL : ((5 * ε / 4) ^ 2 ^ (n - 1))⁻¹ *
      (5 * log (12 * b * max 1 (house α)) / 2 + 5 * n) ≤ L)
    {β : ℕ → ℚ} (hβ : ∀ k, |(β k : ℝ) - α| ≤ mulHeight₁ (β k) ^ (-κ))
    (h₀ : L ≤ logHeight₁ (β 0)) (hh : ∀ k, M * logHeight₁ (β k) ≤ logHeight₁ (β (k + 1))) :
    κ * (1 - ε) * ((1 / 2 - 3 * ε) * n) ≤
      n + (4 * log (12 * b * max 1 (house α)) + 2 * log (2 * max 1 |α|) + 4) / L := by
  set σ := (5 * ε / 4) ^ 2 ^ (n - 1) with hσ_def
  set C₁ := log (12 * b * max 1 (house α)) with hC₁_def
  set h : ℕ → ℝ := fun k ↦ logHeight₁ (β k) with h_def
  have hσ₀ : 0 < σ := by positivity
  have hσ : σ ≤ 5 * ε / 4 :=
    pow_le_of_le_one (by positivity) (by linarith) (pow_ne_zero _ two_ne_zero)
  have hM₂ : 2 ≤ M := by nlinarith
  have h12 := two_le_twelve_mul_max_house α hb
  have hC₁ : log 2 ≤ C₁ := log_le_log two_pos h12
  have hC₁₀ : 0 ≤ C₁ := log_nonneg (by linarith)
  have hL₀ : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨hpos, hmono⟩ := forall_pos_and_monotone_of_mul_le (by linarith) hL₀ h₀ hh
  -- The degree bounds `r i = ⌊D / h i⌋₊` for `D = h (n - 1) / ε`.
  set D := h (n - 1) / ε with hD_def
  have hεD : ε * D = h (n - 1) := by rw [hD_def]; field_simp
  have hD₀ : 0 < D := div_pos (hpos _) hε₀
  set r : Fin n → ℕ := fun i ↦ ⌊D / h i⌋₊ with hr_def
  have hfl := floor_div_bounds hε hpos hmono hD₀ hεD
  have h5D (i : Fin n) : 5 * h i ≤ D := (hfl i).1
  have hr (i : Fin n) : 0 < r i := (hfl i).2.1
  have hup (i : Fin n) : r i * h i ≤ D := (hfl i).2.2.1
  have hlow (i : Fin n) : (1 - ε) * D ≤ r i * h i := (hfl i).2.2.2
  have hsum : ∑ i, (r i : ℝ) = ∑ k ∈ range n, (⌊D / h k⌋₊ : ℝ) :=
    Fin.sum_univ_eq_sum_range (fun k ↦ (⌊D / h k⌋₊ : ℝ)) n
  -- Roth's auxiliary polynomial with these partial degrees.
  obtain ⟨P, hP0, hPdeg, hPind, hPcoeff⟩ := exists_roth_auxiliary_polynomial (ι := Fin n) hb hbα
    hε₀.le (by simpa using hd) fun i ↦ (hr i).ne'
  have hPcoeff' : ∀ μ, |(P.coeff μ : ℝ)| ≤ Real.exp (C₁ * ∑ i, (r i : ℝ)) := fun μ ↦ by
    rw [mul_comm, ← Nat.cast_sum, Real.exp_nat_mul, hC₁_def,
      Real.exp_log (by linarith : 0 < 12 * (b : ℝ) * max 1 (house α))]
    exact hPcoeff μ
  have hPlog := (MvPolynomial.logHeight_map_intCast_le_log hP0 hPcoeff').trans_eq
    (Real.log_exp _)
  -- Roth's lemma bounds the index of `P` at `β`.
  have : NeZero n := ⟨hn.ne'⟩
  set P' := P.map (Int.castRingHom ℚ) with hP'_def
  have hP'0 : P' ≠ 0 := fun h0 ↦ hP0 (map_injective _ (RingHom.injective_int _) (by simpa))
  have hP'deg (i : Fin n) : P'.degreeOf i ≤ r i := (degreeOf_map_le _ P i).trans (hPdeg i)
  have hP'height : P'.logHeight ≤ C₁ * ∑ k ∈ range n, (⌊D / h k⌋₊ : ℝ) := hsum ▸ hPlog
  have hindβ := weightedIndex_le_of_logHeight_le (K := ℚ) hP'0 hr hP'deg hσ₀
    (by linarith) (fun i j hij ↦ by
      simp only [hr_def, hij]
      exact floor_div_le_mul_floor_div hσ₀ hM (hpos i) (hh i) (by linarith [h5D i, hpos i]))
    (fun i ↦ β i) (fun i ↦ by
      rw [Module.finrank_self, Nat.cast_one, mul_one]
      exact inv_mul_add_le_floor_div_mul hσ₀ hL₀ hM₂ h₀ (fun j _ ↦ hh j) hC₁₀ hL (hpos i)
        (h5D i) hP'height)
  have hθ := two_mul_mul_rpow_inv_two_pow hε₀.le n
  rw [← hσ_def] at hθ
  rw [hθ] at hindβ
  -- The key inequality, divided by `D`.
  have key := roth_key_inequality hPdeg hε₀.le hC₁
    (hsum.trans_le (sum_range_floor_div_le_two_mul_div hD₀.le hL₀ hM₂ h₀ fun j _ ↦ hh j))
    hPcoeff' hPind hindβ hκ (by nlinarith) (fun i ↦ hβ i) hlow hup
  rw [Fintype.card_fin] at key
  refine le_of_mul_le_mul_right ?_ hD₀
  rw [add_mul, div_mul_eq_mul_div]
  linarith

/-- **Roth's theorem** (Roth, 1955). If `α` is a real algebraic number and `κ > 2`, then only
finitely many rational numbers `ξ` satisfy `|ξ - α| ≤ H(ξ) ^ (-κ)`, where `H` is the
multiplicative height on `ℚ`. -/
theorem _root_.IsAlgebraic.finite_setOfPred_abs_sub_le_mulHeight₁_rpow_neg {α : ℝ}
    (hα : IsAlgebraic ℚ α) {κ : ℝ} (hκ : 2 < κ) :
    {ξ : ℚ | |(ξ : ℝ) - α| ≤ mulHeight₁ ξ ^ (-κ)}.Finite := by
  by_contra hS
  -- A denominator `b` of `α`, and the parameters `ε`, `n`, `σ`, `L` of the proof.
  set b := Algebra.natDenominator α
  have hb : 0 < b := Nat.pos_of_ne_zero <|
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 hα)
  have hbα : IsIntegral ℤ ((b : ℝ) * α) := by
    simpa [nsmul_eq_mul] using Algebra.isIntegral_natDenominator_smul α
  set ε := (κ - 2) / (16 * κ) with hε_def
  have hκ₀ : 0 < κ := by linarith
  have hε₀ : 0 < ε := div_pos (by linarith) (by positivity)
  have hε : ε ≤ 1 / 12 := by
    rw [hε_def, div_le_iff₀ (by positivity)]
    linarith
  have hεκ : 16 * κ * ε = κ - 2 := by rw [hε_def]; field_simp
  have hκε : 1 + ε < κ * (1 - ε) * (1 / 2 - 3 * ε) := by nlinarith
  set d : ℝ := ((minpoly ℚ α).natDegree : ℝ)
  set n := ⌈4 * d / ε ^ 2⌉₊ + 1 with hn_def
  have hn : 0 < n := Nat.succ_pos _
  have hd : 2 * d ≤ exp (ε ^ 2 * n / 2) := by
    have h4 : 4 * d / ε ^ 2 ≤ n := by
      rw [hn_def]
      push_cast
      linarith [Nat.le_ceil (4 * d / ε ^ 2)]
    rw [div_le_iff₀ (by positivity)] at h4
    linarith [add_one_le_exp (ε ^ 2 * n / 2)]
  set σ := (5 * ε / 4) ^ 2 ^ (n - 1)
  have hσ₀ : 0 < σ := by positivity
  set C₂ := 4 * log (12 * b * max 1 (house α)) + 2 * log (2 * max 1 |α|) + 4
  set L := max (σ⁻¹ * (5 * log (12 * b * max 1 (house α)) / 2 + 5 * n)) (C₂ / ε)
  -- Good approximations of rapidly increasing heights.
  obtain ⟨β, hβ, h₀, hh⟩ := Northcott.exists_seq_mem_lt (logHeight₁ (K := ℚ))
    (fun x ↦ 2 / σ * x) hS L
  have key := roth_inequality hb hbα hε₀ hε hn hd hκ₀.le (M := 2 / σ)
    (by rw [mul_div_cancel₀ _ hσ₀.ne']) (le_max_left _ _) hβ h₀.le fun k ↦ (hh k).le
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC₁₀ : 0 ≤ log (12 * b * max 1 (house α)) :=
    log_nonneg (by linarith [two_le_twelve_mul_max_house α hb])
  have hL₀ : 0 < L := lt_of_lt_of_le (mul_pos (inv_pos.2 hσ₀) (by linarith)) (le_max_left _ _)
  have hC₂L : C₂ / L ≤ ε := by
    rw [div_le_iff₀ hL₀]
    have := (div_le_iff₀ hε₀).1 (le_max_right _ _ : C₂ / ε ≤ L)
    linarith
  -- Multiplying `1 + ε < κ (1 - ε) (1 / 2 - 3 ε)` by `n ≥ 1` contradicts `key`, as
  -- `C₂ / L ≤ ε ≤ ε n`.
  have key' : κ * (1 - ε) * ((1 / 2 - 3 * ε) * n) ≤ n + C₂ / L := key
  have hκεn : (1 + ε) * n < κ * (1 - ε) * ((1 / 2 - 3 * ε) * n) := by
    linarith [mul_lt_mul_of_pos_right hκε (by positivity : (0 : ℝ) < n)]
  linarith [mul_le_mul_of_nonneg_left hn₁ hε₀.le]

/-- **Roth's theorem** as a lower bound (Evertse, Theorem 6.2). If `α` is a real algebraic
number and `κ > 2`, then there is `c > 0` with `c H(ξ) ^ (-κ) ≤ |ξ - α|` for every `ξ ∈ ℚ` with
`ξ ≠ α`. For irrational `α` the condition `ξ ≠ α` always holds, by `Irrational.ne_rat`. -/
theorem _root_.IsAlgebraic.exists_pos_mul_mulHeight₁_rpow_neg_le_abs_sub {α : ℝ}
    (hα : IsAlgebraic ℚ α) {κ : ℝ} (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : ℚ, (ξ : ℝ) ≠ α → c * mulHeight₁ ξ ^ (-κ) ≤ |(ξ : ℝ) - α| := by
  set S := {ξ : ℚ | |(ξ : ℝ) - α| ≤ mulHeight₁ ξ ^ (-κ) ∧ (ξ : ℝ) ≠ α}
  have hS : S.Finite := (hα.finite_setOfPred_abs_sub_le_mulHeight₁_rpow_neg hκ).subset
    fun _ hξ ↦ hξ.1
  -- On the finite set `S`, the positive function `|ξ - α| H(ξ) ^ κ` is bounded below.
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ξ ∈ S, c ≤ |(ξ : ℝ) - α| * mulHeight₁ ξ ^ κ := by
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · exact ⟨1, one_pos, by simp [hS0]⟩
    obtain ⟨ξ₀, hξ₀, hmin⟩ := Set.exists_min_image S
      (fun ξ : ℚ ↦ |(ξ : ℝ) - α| * mulHeight₁ ξ ^ κ) hS hSne
    exact ⟨_, mul_pos (abs_pos.2 (sub_ne_zero.2 hξ₀.2))
      (rpow_pos_of_pos (mulHeight₁_pos ξ₀) κ), hmin⟩
  refine ⟨min c 1, lt_min hc₀ one_pos, fun ξ hξα ↦ ?_⟩
  have hH : 0 < mulHeight₁ ξ := mulHeight₁_pos ξ
  have hHκ : 0 < mulHeight₁ ξ ^ κ := rpow_pos_of_pos hH κ
  rw [rpow_neg hH.le, ← div_eq_mul_inv, div_le_iff₀ hHκ]
  by_cases hξ : ξ ∈ S
  · exact (min_le_left _ _).trans (hc ξ hξ)
  · have hlt : mulHeight₁ ξ ^ (-κ) < |(ξ : ℝ) - α| := lt_of_not_ge fun h ↦ hξ ⟨h, hξα⟩
    rw [rpow_neg hH.le, inv_lt_iff_one_lt_mul₀' hHκ] at hlt
    exact (min_le_right _ _).trans (by linarith)

/-- **Roth's theorem** for a complex algebraic number (Evertse, remarks after Theorem 6.2). If
`α ∈ ℂ` is algebraic and `κ > 2`, then there is `c > 0` with `c H(ξ) ^ (-κ) ≤ ‖ξ - α‖` for every
`ξ ∈ ℚ` with `ξ ≠ α`. For real `α` this is
`IsAlgebraic.exists_pos_mul_mulHeight₁_rpow_neg_le_abs_sub`; a non-real `α` is at distance at
least `|im α|` from every rational number. -/
theorem _root_.IsAlgebraic.exists_pos_mul_mulHeight₁_rpow_neg_le_norm_sub {α : ℂ}
    (hα : IsAlgebraic ℚ α) {κ : ℝ} (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : ℚ, (ξ : ℂ) ≠ α → c * mulHeight₁ ξ ^ (-κ) ≤ ‖(ξ : ℂ) - α‖ := by
  by_cases him : α.im = 0
  · have hαre : (α.re : ℂ) = α := Complex.ext rfl him.symm
    have hre : IsAlgebraic ℚ α.re := by
      rw [← isAlgebraic_algebraMap_iff (algebraMap ℝ ℂ).injective]
      exact hαre ▸ hα
    obtain ⟨c, hc, h⟩ := hre.exists_pos_mul_mulHeight₁_rpow_neg_le_abs_sub hκ
    refine ⟨c, hc, fun ξ hξ ↦ ?_⟩
    rw [← hαre, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact h ξ fun h' ↦ hξ (by rw [← hαre, ← h', Complex.ofReal_ratCast])
  · refine ⟨|α.im|, abs_pos.2 him, fun ξ _ ↦ ?_⟩
    calc |α.im| * mulHeight₁ ξ ^ (-κ) ≤ |α.im| * 1 := by
          gcongr
          exact rpow_le_one_of_one_le_of_nonpos (one_le_mulHeight₁ ξ) (by linarith)
      _ = |((ξ : ℂ) - α).im| := by simp
      _ ≤ ‖(ξ : ℂ) - α‖ := Complex.abs_im_le_norm _

/-- **Roth's theorem** in terms of Liouville exponents: a real algebraic number is not a
Liouville number with any exponent `p > 2`. -/
theorem _root_.IsAlgebraic.not_liouvilleWith {α : ℝ} (hα : IsAlgebraic ℚ α) {p : ℝ}
    (hp : 2 < p) : ¬LiouvilleWith p α := by
  intro hL
  obtain ⟨κ, hκ, hκp⟩ := exists_between hp
  exact hL.infinite_setOf_abs_sub_lt_mulHeight₁_rpow_neg hκp <|
    (hα.finite_setOfPred_abs_sub_le_mulHeight₁_rpow_neg hκ).subset fun r hr ↦
      (abs_sub_comm (r : ℝ) α).trans_le hr.le

/-- The irrationality exponent of a real algebraic number is at most two. -/
theorem _root_.IsAlgebraic.irrationalityExponent_le_two {α : ℝ} (hα : IsAlgebraic ℚ α) :
    irrationalityExponent α ≤ 2 :=
  (irrationalityExponent_le_two_iff α).2 fun _ hp ↦ hα.not_liouvilleWith hp

/-- The irrationality exponent of a real algebraic irrational number is two. -/
theorem _root_.IsAlgebraic.irrationalityExponent_eq_two {α : ℝ} (hα : IsAlgebraic ℚ α)
    (hirr : Irrational α) : irrationalityExponent α = 2 :=
  hα.irrationalityExponent_le_two.antisymm ((two_le_irrationalityExponent_iff α).2 hirr)

end TauCeti
