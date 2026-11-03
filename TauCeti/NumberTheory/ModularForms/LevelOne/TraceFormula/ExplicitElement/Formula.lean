/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HurwitzClassNumber
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Trace
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Finrank
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.NonElliptic
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.PeriodRelation

/-!
# The closed-form trace of Popa–Zagier's explicit element

Let `Tₙ` be Popa and Zagier's explicit element of `K[ℳₙ]`, defined by eq. (15) of their paper, for
a positive integer `n` and a field `K` of characteristic zero, and write
`TauCeti.PopaZagier.weight M` for twelve times the coefficient of `M` in `Tₙ`. For even degree `w`,
`TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_eq_sum_trace_fibres`
expresses the trace of `Tₙ` on the space `V_w` of binary forms of degree `w` (and, for `w ≠ 0`, on
the period-polynomial space `W_w`) as one twelfth of the finite sum over `t ∈ [-4 n, 4 n]` of the
weight sums on the trace-`t`, determinant-`n` matrix fibres multiplied by the Eichler–Selberg
Dickson weights `P_{w+2}(t, n) = (dickson 2 n w).eval t`.

Substituting the elliptic (`t² < 4 n`) and non-elliptic (`t² ≥ 4 n`) fibre sums from
`ExplicitElement/ClassNumber.lean` and `ExplicitElement/NonElliptic.lean` evaluates this trace in
closed form:

* on `t² ≤ 4 n`, each elliptic fibre (`t² < 4 n`) has weight sum `-12 H(4 n - t²)` and therefore
  contributes `((-12 H(4 n - t²)) / 12) P_{w+2}(t, n) = -H(4 n - t²) P_{w+2}(t, n)`. When `n = a²`
  is a square (`a > 0`), the parabolic fibre `t = 2 a` has weight sum `2` and the fibre `t = -2 a`
  has weight sum `0`; dividing these boundary weights by `12` and using
  `P_{w+2}(-2 a, n) = P_{w+2}(2 a, n)` (for even `w`) together with `H(0) = -1/12` in Zagier's
  normalisation gives
  `(2 / 12) P_{w+2}(2 a, n) + (0 / 12) P_{w+2}(-2 a, n) = (1 / 6) P_{w+2}(2 a, n)`,
  which equals `-H(0) P_{w+2}(2 a, n) - H(0) P_{w+2}(-2 a, n)` and is absorbed into the `t² ≤ 4 n`
  sum;
* on `t² > 4 n`, the fibres with `t < 0` or `t² - 4 n` non-square vanish, while the split
  hyperbolic fibres `t = a + d` (`a d = n`, `0 < a < d`) contribute
  `((12 (d - a)) / 12) P_{w+2}(a + d, a d) = d ^ (w + 1) - a ^ (w + 1)`, whose sum over `a < d`
  rewrites as `∑_{d ∣ n} d ^ (w + 1) - ∑_{a d = n} min(a, d) ^ (w + 1)`.

For positive even `w`, `Tₙ` acts on period polynomials of cusp forms as the Hecke operator `Tₙ`, so
this closed form on `W_w` is the algebraic half of the Eichler–Selberg trace formula: subtracting
the Eisenstein eigenvalue `σ_{w+1}(n) = ∑_{d ∣ n} d ^ (w + 1)` and dividing by `2` leaves the
cusp-form trace expression.

In degree `w = 0`, every matrix acts trivially on constant binary forms, so `tr(Tₙ | V_0)` is also
the sum of the coefficients of `Tₙ`, which equals `-σ₁(n)` because `ℳₙ` has `σ₁(n)` right cosets of
`PSL(2, ℤ)` and each right coset sum of `Tₙ` is `-1`. Comparing the two evaluations of
`tr(Tₙ | V_0)` gives the **Kronecker–Hurwitz class number relation**

`(∑_{|t| ≤ √(4 n)} H(4 n - t²)) + ∑_{a d = n} min(a, d) = 2 ∑_{d ∣ n} d`.

At `n = 1` and positive even `w`, the trace formula on `W_w` simplifies to `dim W_w`; at `n = 2`
and `w = 10` (weight `12`), it evaluates to `2001 = σ₁₁(2) + 2 · (-24)`.

## Main results

* `TauCeti.PopaZagier.sum_Icc_le_weight_traceDetFiber_mul_dickson`: one twelfth of the `t² ≤ 4 n`
  weighted trace-fibre sum equals `-∑_{|t| ≤ √(4 n)} H(4 n - t²) P_{w+2}(t, n)` for `n ≠ 0` and
  even `w`.
* `TauCeti.PopaZagier.sum_Icc_gt_weight_traceDetFiber_mul_dickson`: one twelfth of the `t² > 4 n`
  weighted trace-fibre sum equals `∑_{a d = n, a < d} (d ^ (w + 1) - a ^ (w + 1))` for `n ≠ 0`.
* `TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement` and
  `TauCeti.TraceFormulaMatrixModule.trace_periodActionRestrict_popaZagierElement`: the closed-form
  trace of Popa–Zagier's explicit element on `V_w` (for even `w`) and on `W_w` (for positive even
  `w`).
* `TauCeti.TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_zero`: in degree `0`,
  `tr(Tₙ | V_0) = -∑_{d ∣ n} d`.
* `TauCeti.sum_Icc_hurwitzClassNumber_add_sum_divisorsAntidiagonal_min`: the Kronecker–Hurwitz
  class number relation.
* `TauCeti.TraceFormulaMatrixModule.trace_periodActionRestrict_popaZagierElement_one` and
  `TauCeti.TraceFormulaMatrixModule.trace_periodActionRestrict_popaZagierElement_two_ten`: the
  specialisations `n = 1` (`tr(T₁ | W_w) = dim W_w`) and `n = 2, w = 10` (`tr(T₂ | W₁₀) = 2001`).

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §§1, 4, eqs. (2) and (15),
  Theorem 4.
* D. Zagier, *Nombres de classes et formes modulaires de poids 3/2*, C. R. Acad. Sci. Paris
  Sér. A-B **281** (1975), 883–886.
* D. Zagier, *The Eichler–Selberg trace formula on `SL₂(ℤ)`*, appendix to S. Lang,
  *Introduction to Modular Forms*, Springer, 1976.
-/

public section

open Matrix MvPolynomial

namespace TauCeti

namespace PopaZagier

/-- On an elliptic fibre (`t² < 4 n`), the integer weight sum cast to any characteristic-zero field
is `-12 H(4 n - t²)`. -/
private theorem cast_finsum_weight_traceDetFiber_of_sq_lt {K : Type*} [Field K] [CharZero K]
    {t n : ℤ} (h : t ^ 2 < 4 * n) :
    (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, weight A.1) : K) =
      -12 * (hurwitzClassNumber (4 * n - t ^ 2).toNat : K) := by
  set D := (4 * n - t ^ 2).toNat
  have : NeZero D := ⟨by omega⟩
  have hD : t ^ 2 - 4 * n = -D := by omega
  have hq := (Int.castAddHom ℚ).map_finsum (finite_support_weight_traceDetFiber t n)
  simp only [Int.coe_castAddHom] at hq
  rw [finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber hD] at hq
  rw [← Rat.cast_intCast (α := K), hq]
  push_cast
  rfl

/-- **The elliptic and parabolic range (`t² ≤ 4 n`) of the trace-fibre sum.** For `n ≠ 0` and even
`w`, the `t² ≤ 4 n` fibres contribute `-∑_{|t| ≤ √(4 n)} H(4 n - t²) P_{w+2}(t, n)` to a twelfth of
the Dickson-weighted sum: when `n = a²` is a square, the weights `2` at `t = 2 a` and `0` at
`t = -2 a` combine with `P_{w+2}(-2 a, n) = P_{w+2}(2 a, n)` to match `-2 H(0) = 1/6`. -/
theorem sum_Icc_le_weight_traceDetFiber_mul_dickson {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hw : Even w) :
    (12 : K)⁻¹ * ∑ t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * (n : ℤ)) with t ^ 2 ≤ 4 * (n : ℤ),
        (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, weight A.1) : K) *
          (Polynomial.dickson 2 (n : K) w).eval (t : K) =
      - ∑ t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K) *
            (Polynomial.dickson 2 (n : K) w).eval (t : K) := by
  set s := Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n))
  have hs (t : ℤ) : t ∈ s ↔ t ^ 2 ≤ 4 * (n : ℤ) := by
    rw [Finset.mem_Icc, ← abs_le, ← Int.sqrt_natCast,
      Int.abs_le_sqrt_iff_sq_le (Nat.cast_nonneg (4 * n)), Nat.cast_mul, Nat.cast_ofNat]
  have hIcc : {t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * (n : ℤ)) | t ^ 2 ≤ 4 * (n : ℤ)} = s := by
    have hle : (Nat.sqrt (4 * n) : ℤ) ≤ 4 * (n : ℤ) := by exact_mod_cast Nat.sqrt_le_self (4 * n)
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, hs]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨by have := Finset.mem_Icc.mp ((hs t).mpr h); omega, h⟩⟩
  rw [hIcc]
  set g : ℤ → K := fun t ↦
    ((↑(∑ᶠ A : traceDetFiber (Fin 2) t n, weight A.1) : K) +
        12 * (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K)) *
      (Polynomial.dickson 2 (n : K) w).eval (t : K)
  have hg_lt {t : ℤ} (ht : t ^ 2 < 4 * (n : ℤ)) : g t = 0 := by
    simp only [g, cast_finsum_weight_traceDetFiber_of_sq_lt ht]
    ring
  suffices hsum : ∑ t ∈ s, g t = 0 by
    simp only [g, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
    linear_combination (12 : K)⁻¹ * hsum
  by_cases hsq : ∃ t₀ : ℤ, t₀ ^ 2 = 4 * (n : ℤ)
  · obtain ⟨t₀, ht₀⟩ := hsq
    obtain ⟨b, rfl⟩ : Even t₀ := by
      rcases Int.even_or_odd t₀ with h | ⟨c, rfl⟩
      · exact h
      · exfalso
        have hmod : (2 * c + 1) ^ 2 % 4 = 4 * (n : ℤ) % 4 := congrArg (· % 4) ht₀
        have hodd : (2 * c + 1) ^ 2 = 4 * (c ^ 2 + c) + 1 := by ring
        rw [hodd] at hmod
        omega
    set a : ℤ := |b|
    have ha2 : (n : ℤ) = a ^ 2 := by
      rw [sq_abs]
      nlinarith
    have ha : 0 < a := by
      have : a ≠ 0 := fun h ↦ hn (by simpa [h] using ha2)
      positivity
    rw [Finset.sum_eq_add (2 * a) (-(2 * a))]
    · have h2a : (2 * a) ^ 2 = 4 * (n : ℤ) := by rw [ha2]; ring
      have hn2a : (-(2 * a)) ^ 2 = 4 * (n : ℤ) := by rw [ha2]; ring
      have hwpos : ∑ᶠ A : traceDetFiber (Fin 2) (2 * a) n, weight A.1 = 2 :=
        ha2 ▸ finsum_weight_traceDetFiber_two_mul_sq_eq_two ha
      have hwneg : ∑ᶠ A : traceDetFiber (Fin 2) (-(2 * a)) n, weight A.1 = 0 :=
        finsum_weight_traceDetFiber_eq_zero_of_neg (by omega) (by omega)
      simp only [g, hwpos, hwneg, h2a, hn2a, sub_self, Int.toNat_zero, hurwitzClassNumber_zero,
        Int.cast_neg, Polynomial.dickson_eval_neg_of_even _ _ _ hw]
      push_cast
      ring
    · omega
    · rintro t ht ⟨h1, h2⟩
      refine hg_lt ((hs t).mp ht |>.lt_of_ne fun heq ↦ ?_)
      have hfac : (t - 2 * a) * (t + 2 * a) = 0 := by
        rw [ha2] at heq
        linear_combination heq
      rcases Int.mul_eq_zero.mp hfac with h | h <;> omega
    · exact fun h ↦ absurd ((hs (2 * a)).mpr (by rw [ha2]; linarith)) h
    · exact fun h ↦ absurd ((hs (-(2 * a))).mpr (by rw [ha2]; linarith)) h
  · exact Finset.sum_eq_zero fun t ht ↦ hg_lt ((hs t).mp ht |>.lt_of_ne fun h ↦ hsq ⟨t, h⟩)

/-- **The hyperbolic range (`t² > 4 n`) of the trace-fibre sum.** For `n ≠ 0`, the `t² > 4 n`
fibres contribute `∑_{a d = n, a < d} (d ^ (w + 1) - a ^ (w + 1))` to a twelfth of the
Dickson-weighted sum: only the split hyperbolic fibres `t = a + d` (`a d = n`, `0 < a < d`) are
nonzero, and `(d - a) P_{w+2}(a + d, a d) = d ^ (w + 1) - a ^ (w + 1)`. -/
theorem sum_Icc_gt_weight_traceDetFiber_mul_dickson {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (hn : n ≠ 0) (w : ℕ) :
    (12 : K)⁻¹ * ∑ t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * (n : ℤ)) with 4 * (n : ℤ) < t ^ 2,
        (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, weight A.1) : K) *
          (Polynomial.dickson 2 (n : K) w).eval (t : K) =
      ∑ p ∈ n.divisorsAntidiagonal with p.1 < p.2,
        ((p.2 : K) ^ (w + 1) - (p.1 : K) ^ (w + 1)) := by
  set P := {p ∈ n.divisorsAntidiagonal | p.1 < p.2}
  set φ : ℕ × ℕ → ℤ := fun p ↦ (p.1 : ℤ) + p.2
  have hsub : P.image φ ⊆ {t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * (n : ℤ)) | 4 * (n : ℤ) < t ^ 2} := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hp_mem, hp_lt⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hlt, -⟩ :=
      (Int.exists_mem_divisorsAntidiagonal_lt_add_eq_iff hn (φ p)).mp ⟨p, hp_mem, hp_lt, rfl⟩
    have hle := Nat.add_le_add_one_of_mem_divisorsAntidiagonal hp_mem
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hφ : φ p = (p.1 : ℤ) + p.2 := rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hlt⟩
  have hzero (t : ℤ)
      (ht : t ∈ {t ∈ Finset.Icc (-4 * (n : ℤ)) (4 * (n : ℤ)) | 4 * (n : ℤ) < t ^ 2})
      (htP : t ∉ P.image φ) :
      (↑(∑ᶠ A : traceDetFiber (Fin 2) t n, weight A.1) : K) *
        (Polynomial.dickson 2 (n : K) w).eval (t : K) = 0 := by
    have hnot : ¬ (0 ≤ t ∧ 4 * (n : ℤ) < t ^ 2 ∧ IsSquare (t ^ 2 - 4 * (n : ℤ))) := by
      rw [← Int.exists_mem_divisorsAntidiagonal_lt_add_eq_iff hn t]
      rintro ⟨p, hp_mem, hp_lt, hpt⟩
      exact htP (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp_mem, hp_lt⟩, hpt⟩)
    have hlt := (Finset.mem_filter.mp ht).2
    rcases lt_or_ge t 0 with ht_neg | ht_nonneg
    · simp [finsum_weight_traceDetFiber_eq_zero_of_neg ht_neg hlt.le]
    · have hnsq : ¬ IsSquare (t ^ 2 - 4 * (n : ℤ)) := fun hsq ↦ hnot ⟨ht_nonneg, hlt, hsq⟩
      simp [finsum_weight_traceDetFiber_eq_zero_of_not_isSquare hlt.le hnsq]
  have hinj : Set.InjOn φ P := fun p hp q hq hpq ↦ by
    simp only [Finset.mem_coe, Finset.mem_filter, P] at hp hq
    have hpq' : p.1 + p.2 = q.1 + q.2 := by dsimp only [φ] at hpq; exact_mod_cast hpq
    exact Nat.add_injOn_divisorsAntidiagonal_le n ⟨hp.1, hp.2.le⟩ ⟨hq.1, hq.2.le⟩ hpq'
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hp_mem, hp_lt⟩ := Finset.mem_filter.mp hp
  have hp_mul : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp_mem).1
  obtain ⟨h1, h2⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hp_mem
  have hn_int : (n : ℤ) = (p.1 : ℤ) * p.2 := by exact_mod_cast hp_mul.symm
  have hw_eq : ∑ᶠ A : traceDetFiber (Fin 2) (φ p) n, weight A.1 = 12 * ((p.2 : ℤ) - p.1) := by
    rw [hn_int, finsum_weight_traceDetFiber_add_mul_eq_twelve_mul_abs_sub
      (by positivity) (by positivity) (by omega), abs_of_nonneg (by omega)]
  have hmul_K : (p.2 : K) * p.1 = n := by exact_mod_cast (mul_comm p.2 p.1).trans hp_mul
  rw [hw_eq]
  simp only [φ, Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  rw [mul_assoc (12 : K), inv_mul_cancel_left₀ (by norm_num), add_comm (p.1 : K), mul_comm,
    Polynomial.dickson_two_eval_add_mul_sub hmul_K w]

end PopaZagier

namespace TraceFormulaMatrixModule

/-- **The closed-form trace of Popa–Zagier's explicit element on binary forms.** Over a field `K`
of characteristic zero, for `n ≠ 0` and even `w`, the trace of `Tₙ` on the degree-`w` binary forms
`V_w` is `∑_{d ∣ n} d ^ (w + 1) - ∑_{|t| ≤ √(4 n)} H(4 n - t²) P_{w+2}(t, n)` minus
`∑_{a d = n} min(a, d) ^ (w + 1)`. This holds for `w = 0` as well as for `w > 0`. -/
theorem trace_periodAction_popaZagierElement {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hw : Even w) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
        (periodAction hw (popaZagierElement K n)) =
      (∑ d ∈ n.divisors, (d : K) ^ (w + 1)) -
        (∑ t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K) *
            (Polynomial.dickson 2 (n : K) w).eval (t : K)) -
        ∑ p ∈ n.divisorsAntidiagonal, (↑(min p.1 p.2) : K) ^ (w + 1) := by
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  rw [trace_periodAction_popaZagierElement_eq_sum_trace_fibres hn' w hw, Int.cast_natCast,
    ← Finset.sum_filter_add_sum_filter_not _ (fun t : ℤ ↦ t ^ 2 ≤ 4 * (n : ℤ)),
    Finset.filter_congr (fun _ _ ↦ not_le), mul_add,
    PopaZagier.sum_Icc_le_weight_traceDetFiber_mul_dickson hn hw,
    PopaZagier.sum_Icc_gt_weight_traceDetFiber_mul_dickson hn w,
    Nat.sum_divisorsAntidiagonal_filter_lt_sub n (fun d ↦ (d : K) ^ (w + 1))]
  ring

/-- **The closed-form trace of Popa–Zagier's explicit element on period polynomials.** Over a field
`K` of characteristic zero, for `n ≠ 0` and positive even `w`, the trace of `Tₙ` on the
period-polynomial space `W_w` equals
`∑_{d ∣ n} d ^ (w + 1) - ∑_{|t| ≤ √(4 n)} H(4 n - t²) P_{w+2}(t, n)` minus
`∑_{a d = n} min(a, d) ^ (w + 1)`. Subtracting the Eisenstein eigenvalue `∑_{d ∣ n} d ^ (w + 1)`
and dividing by `2` gives the Eichler–Selberg cusp-form trace expression in Zagier's `H(0) = -1/12`
normalisation. -/
theorem trace_periodActionRestrict_popaZagierElement {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (hn : n ≠ 0) {w : ℕ} (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
        ((exchangeRelations_popaZagierElement K n).periodActionRestrict hw) =
      (∑ d ∈ n.divisors, (d : K) ^ (w + 1)) -
        (∑ t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)),
          (hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : K) *
            (Polynomial.dickson 2 (n : K) w).eval (t : K)) -
        ∑ p ∈ n.divisorsAntidiagonal, (↑(min p.1 p.2) : K) ^ (w + 1) := by
  rw [(exchangeRelations_popaZagierElement K n).trace_periodActionRestrict_eq_trace hw hw₀,
    trace_periodAction_popaZagierElement hn hw]

/-- In degree `0`, every matrix acts trivially on `V_0`, so the trace of Popa–Zagier's explicit
element `Tₙ` on `V_0` is the sum of its coefficients, `-∑_{d ∣ n} d`. -/
theorem trace_periodAction_popaZagierElement_zero {K : Type*} [Field K] (h12 : (12 : K) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K 0)
        (periodAction .zero (popaZagierElement K n)) =
      - ∑ d ∈ n.divisors, (d : K) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [trace_periodAction_zero, sum_coeff_popaZagierElement h12 hn', Int.natAbs_natCast,
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

end TraceFormulaMatrixModule

/-- **The Kronecker–Hurwitz class number relation.** For every nonzero natural number `n`,

`(∑_{|t| ≤ √(4 n)} H(4 n - t²)) + ∑_{a d = n} min(a, d) = 2 ∑_{d ∣ n} d`,

where `H` is the Hurwitz class number (`H 0 = -1/12`). It follows from equating the closed-form
trace of Popa–Zagier's explicit element on constant binary forms (`w = 0`, where `P_2(t, n) = 1`)
with its coefficient sum `-σ₁(n)`. -/
theorem sum_Icc_hurwitzClassNumber_add_sum_divisorsAntidiagonal_min {n : ℕ} (hn : n ≠ 0) :
    (∑ t ∈ Finset.Icc (-(Nat.sqrt (4 * n) : ℤ)) (Nat.sqrt (4 * n)),
        hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat) +
      (∑ p ∈ n.divisorsAntidiagonal, (↑(min p.1 p.2) : ℚ)) =
    2 * ∑ d ∈ n.divisors, (d : ℚ) := by
  have h := TraceFormulaMatrixModule.trace_periodAction_popaZagierElement (K := ℚ) hn .zero
  rw [TraceFormulaMatrixModule.trace_periodAction_popaZagierElement_zero (by norm_num) hn] at h
  have hd0 (t : ℤ) : (Polynomial.dickson 2 (n : ℚ) 0).eval (t : ℚ) = 1 := by norm_num
  simp only [zero_add, pow_one, hd0, mul_one, Rat.cast_id] at h
  linear_combination h

namespace TraceFormulaMatrixModule

/-- **At `n = 1`, the trace of Popa–Zagier's explicit element on `W_w` equals `dim W_w`** for
positive even `w` over a field of characteristic zero: the `t = ±2`, `0`, `±1` terms evaluate via
`H 0 = -1/12`, `H 4 = 1/2`, `H 3 = 1/3` and the periodic values `P_{w+2}(0, 1)` and
`P_{w+2}(±1, 1)` to `2 ⌈w / 4⌉ + 2 ⌈w / 3⌉ - (w + 1)`. -/
theorem trace_periodActionRestrict_popaZagierElement_one {K : Type*} [Field K] [CharZero K]
    {w : ℕ} (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
        ((exchangeRelations_popaZagierElement K 1).periodActionRestrict hw) =
      (Module.finrank K (periodPolynomials K w) : K) := by
  have hsqrt : (4 * 1).sqrt = 2 := (Nat.eq_sqrt.mpr (by decide)).symm
  have hIcc : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  have hp2 : (Polynomial.dickson 2 (1 : K) w).eval 2 = w + 1 := by
    simpa using Polynomial.dickson_two_sq_eval_two_mul (1 : K) w
  rw [trace_periodActionRestrict_popaZagierElement one_ne_zero hw hw₀,
    hsqrt, Nat.cast_ofNat, hIcc, Nat.divisors_one, Nat.divisorsAntidiagonal_one]
  norm_num [hurwitzClassNumber_zero, hurwitzClassNumber_three, hurwitzClassNumber_four, hw, hp2]
  have hW := congrArg (Nat.cast : ℕ → K) (finrank_periodPolynomials_add_eq (K := K) hw hw₀)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r,
      (r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 8 ∨ r = 10) ∧ w = 12 * q + r :=
    ⟨w / 12, w % 12, by obtain ⟨m, rfl⟩ := hw; omega, (Nat.div_add_mod w 12).symm⟩
  have h12q : 12 * q + r = 6 * (2 * q) + r := by ring
  have h1 : (Polynomial.dickson 2 (1 : K) (12 * q + r)).eval 1 =
      (Polynomial.dickson 2 (1 : K) r).eval 1 := by
    rw [h12q, Polynomial.dickson_two_one_eval_one_six_mul_add]
  rw [h1]
  have h4 : (12 * q + r + 3) / 4 = 3 * q + (r + 3) / 4 := by omega
  have h3 : (12 * q + r + 2) / 3 = 4 * q + (r + 2) / 3 := by omega
  have hev : 12 * q + r = 2 * (6 * q + r / 2) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have h0 : (Polynomial.dickson 2 (1 : K) (12 * q + r)).eval 0 =
      (-1 : K) ^ (6 * q + r / 2) := by
    rw [hev, Polynomial.dickson_two_eval_zero_two_mul]
  rw [h4, h3] at hW
  rw [h0, pow_add, Even.neg_one_pow ⟨3 * q, by ring⟩, one_mul]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · norm_num [Polynomial.dickson_two, Polynomial.dickson_add_two]
    push_cast at hW ⊢
    linear_combination -hW

/-- **At `n = 2` and `w = 10` (weight `12`), the trace of Popa–Zagier's explicit element on `W₁₀`
equals `2001`** (`= σ₁₁(2) + 2 · (-24)`, matching Ramanujan's `τ(2) = -24` on `S₁₂ = ℂ Δ`). -/
theorem trace_periodActionRestrict_popaZagierElement_two_ten {K : Type*} [Field K] [CharZero K] :
    LinearMap.trace K (periodPolynomials K 10)
        ((exchangeRelations_popaZagierElement K 2).periodActionRestrict ⟨5, rfl⟩) = 2001 := by
  have hsqrt : (4 * 2).sqrt = 2 := (Nat.eq_sqrt.mpr (by decide)).symm
  have hIcc : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by decide
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  have hanti : (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} := by decide
  rw [trace_periodActionRestrict_popaZagierElement (by decide) ⟨5, rfl⟩ (by decide),
    hsqrt, Nat.cast_ofNat, hIcc, hdiv, hanti]
  norm_num [hurwitzClassNumber_four, hurwitzClassNumber_seven, hurwitzClassNumber_eight,
    Polynomial.dickson_add_two, Polynomial.dickson_two]

end TraceFormulaMatrixModule

end TauCeti
