/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Symbol.CutoffInverse
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency.Basic
import TauCeti.Analysis.Pseudodifferential.Symbol.HighFrequency
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Examples: classical expansions and asymptotic sums of symbols

Write `r(ξ) = ⟨ξ / 2π⟩ = (1 + ‖ξ / 2π‖²) ^ (1 / 2)` for the Bessel weight in the angular frequency,
so that `r ^ s` is the symbol `TauCeti.Symbol.besselPotential s` of order `s`. The examples below
pin the conventions of `TauCeti.ClassicalSymbol` and `TauCeti.Symbol.IsAsymptoticSum`.

* **A symbol without a classical expansion.** For `0 < s < 1` and `n ≥ 1`, the symbol `r ^ s + 1`
  of order `s` is not classical of order `s`. Its principal symbol would be the high-frequency
  limit `‖ξ / 2π‖ ^ s`, and the remainder after this term would have the negative order `s - 1`.
  But that remainder is `r ^ s - ‖ξ / 2π‖ ^ s + 1 ≥ 1` at large frequencies. The homogeneous
  terms of a classical symbol have the degrees `s, s - 1, s - 2, …`, and the constant `1`, of
  degree `0`, is not among them.
* **An asymptotic sum that is not a pointwise sum.** For the orders `-1, -2, -3, …`, the symbols
  `aⱼ = (-1) ^ j r ^ (-j - 1)` have the asymptotic sum `b = (r + 1)⁻¹`, with the remainders
  `b - ∑_{j < N} aⱼ = (-1) ^ N r ^ (-N) (r + 1)⁻¹` of order `-N - 1`. At `ξ = 0`, where `r = 1`,
  `b = 1 / 2` and the remainders alternate between `1 / 2` and `-1 / 2`, while the terms
  `aⱼ(x, 0) = (-1) ^ j` are not summable.
* **Finite expansions.** For the orders `0, -1, -2, …` and `a₀ = 1`, all other terms `0`, the
  symbol `b = 1` is an asymptotic sum, with remainder `1` after no terms and `0` after at least one
  term. Successive orders may be equal: for the orders `0, 0, -1, -2, …` and the terms
  `1, 2, 0, 0, …`, `b = 3` is an asymptotic sum with the remainders `3, 2, 0, 0, …`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Examples.AsymptoticSum

open Filter Finset Topology Symbol
open scoped Real

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The Bessel weight `r(ξ) = ⟨ξ / 2π⟩ = (1 + ‖ξ / 2π‖²) ^ (1 / 2)`. -/
private def bracket (ξ : CoordinateSpace n) : ℝ := (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (1 / 2 : ℝ)

private theorem bracket_pos (ξ : CoordinateSpace n) : 0 < bracket ξ := by
  unfold bracket
  positivity

private theorem bracket_zero : bracket (0 : CoordinateSpace n) = 1 := by
  simp [bracket]

/-- The symbol `besselPotential s` is the power `r ^ s` of the Bessel weight. -/
private theorem coefficient_besselPotential_eq (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    (besselPotential s : Symbol n V V s).coefficient p =
      ((bracket p.2 ^ s : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_besselPotential, bracket, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The coefficient of `r ^ s + 1`. -/
private theorem coefficient_besselPotential_add_one {s : ℝ} (hs : 0 ≤ s)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (besselPotential s + inclusion hs (const (ContinuousLinearMap.id ℂ V)) :
      Symbol n V V s).coefficient p =
      ((bracket p.2 ^ s + 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  simp only [coefficient_add, Pi.add_apply, coefficient_besselPotential_eq, coefficient_inclusion,
    coefficient_const, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]

private theorem norm_ofReal_smul_id_le (u : ℝ) :
    ‖((u : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V‖ ≤ |u| := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg u) ContinuousLinearMap.norm_id_le

private theorem norm_ofReal_smul_id [Nontrivial V] (u : ℝ) :
    ‖((u : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V‖ = |u| := by
  simp [norm_smul]

/-! ### A symbol of order `s` without a classical expansion of order `s` -/

private theorem bracket_smul {ξ : CoordinateSpace n} {t : ℝ} (ht : 0 ≤ t) :
    bracket (t • ξ) = (1 + (t * ‖(2 * π)⁻¹ • ξ‖) ^ 2) ^ (1 / 2 : ℝ) := by
  rw [bracket, smul_comm, norm_smul, Real.norm_of_nonneg ht]

/-- `t ^ (-s) (r(t ξ) ^ s + 1) → ‖ξ / 2π‖ ^ s` as `t → ∞`: the principal symbol of `r ^ s + 1`. -/
private theorem tendsto_rpow_neg_mul_bracket_rpow_add_one {s : ℝ} (hs : 0 < s)
    (ξ : CoordinateSpace n) :
    Tendsto (fun t : ℝ ↦ t ^ (-s) * (bracket (t • ξ) ^ s + 1)) atTop
      (𝓝 (‖(2 * π)⁻¹ • ξ‖ ^ s)) := by
  set c := ‖(2 * π)⁻¹ • ξ‖
  have h₁ : Tendsto (fun t : ℝ ↦ ((t ^ 2)⁻¹ + c ^ 2) ^ (s / 2) + t ^ (-s)) atTop
      (𝓝 ((0 + c ^ 2) ^ (s / 2) + 0)) :=
    (((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).add_const _).rpow_const
      (Or.inr (by positivity))).add (tendsto_rpow_neg_atTop hs)
  rw [zero_add, add_zero, Real.sq_rpow_div_two (norm_nonneg _)] at h₁
  refine h₁.congr' ((eventually_gt_atTop 0).mono fun t ht ↦ ?_)
  dsimp only
  have hts : t ^ (-s) = ((t ^ 2)⁻¹) ^ (s / 2) := by
    rw [Real.inv_rpow (by positivity), Real.sq_rpow_div_two ht.le, Real.rpow_neg ht.le]
  rw [bracket_smul ht.le, ← Real.rpow_mul (by positivity), mul_add, mul_one, hts,
    show 1 / 2 * s = s / 2 by ring, ← Real.mul_rpow (by positivity) (by positivity)]
  congr 2
  rw [mul_add, mul_one, mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- `r(t ξ) ^ s + 1 - (t ‖ξ / 2π‖) ^ s ≥ 1`: the full symbol `r ^ s + 1` minus its principal
symbol is at least `1`. -/
private theorem one_le_bracket_rpow_add_one_sub {s : ℝ} (hs : 0 ≤ s) (ξ : CoordinateSpace n)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ bracket (t • ξ) ^ s + 1 - (t * ‖(2 * π)⁻¹ • ξ‖) ^ s := by
  set u := t * ‖(2 * π)⁻¹ • ξ‖
  have hu : 0 ≤ u := by positivity
  have hmono : u ^ s ≤ bracket (t • ξ) ^ s := by
    rw [bracket_smul ht, ← Real.rpow_mul (by positivity), one_div_mul_eq_div,
      ← Real.sq_rpow_div_two hu s]
    gcongr
    linarith
  linarith

/-- For `0 < s < 1` and `n ≥ 1`, the symbol `r ^ s + 1` of order `s` has no classical expansion of
order `s`: its principal symbol is `‖ξ / 2π‖ ^ s`, and after this term the constant `1` remains,
which is not of the negative order `s - 1`. -/
example [Nontrivial V] (hn : 0 < n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ¬∃ a : ClassicalSymbol n V V s,
      a.toSymbol = besselPotential s + inclusion hs0.le (const (ContinuousLinearMap.id ℂ V)) := by
  rintro ⟨a, ha⟩
  have hcoeff (ξ : CoordinateSpace n) : a.toSymbol.coefficient (0, ξ) =
      ((bracket ξ ^ s + 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
    rw [ha, coefficient_besselPotential_add_one]
  -- A nonzero frequency `ξ₀` and the norm `c = ‖ξ₀ / 2π‖ > 0`.
  set ξ₀ : CoordinateSpace n := EuclideanSpace.single ⟨0, hn⟩ 1
  have hξ₀ : ξ₀ ≠ 0 := by simp [ξ₀]
  set c := ‖(2 * π)⁻¹ • ξ₀‖
  have hc : 0 < c := norm_pos_iff.2 (smul_ne_zero (by positivity) hξ₀)
  -- The principal symbol at `ξ₀` is the high-frequency limit `c ^ s`.
  have hprincipal : a.principal.coefficient (0, ξ₀) =
      ((c ^ s : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
    refine tendsto_nhds_unique ((a.tendsto_rpow_neg_smul_coefficient_smul hξ₀).comp
      (tendsto_id.prodMk tendsto_const_nhds)) ?_
    refine ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_rpow_neg_mul_bracket_rpow_add_one hs0 ξ₀) |>.smul_const _).congr fun t ↦ ?_
    simp only [Function.comp_apply, id_eq, hcoeff, ← Complex.coe_smul, smul_smul,
      Complex.ofReal_mul]
  -- After the principal term, the remainder `e` has the negative order `s - 1`, so it vanishes
  -- along `t ξ₀` as `t → ∞`; but there it is `r(t ξ₀) ^ s + 1 - (t c) ^ s ≥ 1` at large `t`.
  obtain ⟨e, he⟩ := a.exists_sub_cutoffSymbol_principal default
  have hlim : Tendsto (fun t : ℝ ↦ e.coefficient (0, t • ξ₀)) atTop (𝓝 0) := by
    refine ((e.tendsto_rpow_neg_smul_coefficient_smul_zero (m := 0) (x := 0) (by linarith)
      hξ₀).comp (tendsto_id.prodMk tendsto_const_nhds)).congr fun t ↦ ?_
    simp
  have hge : ∀ᶠ t : ℝ in atTop, 1 ≤ ‖e.coefficient (0, t • ξ₀)‖ := by
    filter_upwards [eventually_ge_atTop (2 / ‖ξ₀‖)] with t ht
    have ht0 : 0 < t := (by positivity : 0 < 2 / ‖ξ₀‖).trans_le ht
    have h2 : 2 ≤ ‖t • ξ₀‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      rwa [div_le_iff₀ (norm_pos_iff.2 hξ₀)] at ht
    have h := one_le_bracket_rpow_add_one_sub hs0.le ξ₀ ht0.le
    rw [Real.mul_rpow ht0.le hc.le] at h
    rw [he, coefficient_sub, Pi.sub_apply,
      HomogeneousSymbol.coefficient_cutoffSymbol_of_two_le_norm _ _ h2,
      a.principal.homogeneous _ _ _ ht0, hprincipal, hcoeff]
    refine (h.trans (le_abs_self _)).trans_eq ?_
    rw [← norm_ofReal_smul_id (V := V)]
    congr 1
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, sub_smul, ← Complex.coe_smul, smul_smul]
  obtain ⟨t, ht₁, ht₂⟩ := (hge.and (hlim.norm.eventually
    (gt_mem_nhds (by simp : ‖(0 : V →L[ℂ] V)‖ < 1)))).exists
  linarith

/-! ### An asymptotic sum which is not a pointwise sum -/

/-- The orders `-1, -2, -3, …`. -/
def order (j : ℕ) : ℝ := -((j : ℝ) + 1)

/-- The terms `aⱼ = (-1) ^ j r ^ (-j - 1)` of order `-j - 1`. -/
def term (j : ℕ) : Symbol n V V (order j) := ((-1 : ℂ) ^ j) • besselPotential (order j)

private theorem coefficient_term (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (term j : Symbol n V V (order j)).coefficient p =
      (((-1) ^ j * (bracket p.2 ^ (j + 1))⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [term, coefficient_smul, Pi.smul_apply, coefficient_besselPotential_eq, order,
    Real.rpow_neg (bracket_pos p.2).le, smul_smul]
  norm_cast

/-- `(r + 1)⁻¹ - ∑_{j < N} (-1) ^ j r ^ (-j - 1) = (-1) ^ N r ^ (-N) (r + 1)⁻¹`. -/
private theorem inv_add_one_sub_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) :
    (ρ + 1)⁻¹ - ∑ j ∈ range N, (-1) ^ j * (ρ ^ (j + 1))⁻¹ = (-1) ^ N * (ρ ^ N)⁻¹ * (ρ + 1)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

/-- At `ξ = 0` the terms `(-1) ^ j` of the asymptotic sum below are not summable: an asymptotic
sum is not a pointwise sum. -/
example [Nontrivial V] (x : CoordinateSpace n) :
    ¬Summable fun j ↦ (term j : Symbol n V V (order j)).coefficient (x, 0) := by
  intro h
  have h₀ := h.tendsto_atTop_zero.norm
  simp only [coefficient_term, bracket_zero, one_pow, inv_one, mul_one, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, ContinuousLinearMap.norm_id,
    norm_zero] at h₀
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h₀)

private theorem isInvertible_coefficient_bracketAddOne (p : CoordinateSpace n × CoordinateSpace n) :
    ((besselPotential 1 + inclusion zero_le_one (const (ContinuousLinearMap.id ℂ V)) :
      Symbol n V V 1).coefficient p).IsInvertible := by
  rw [coefficient_besselPotential_add_one, ContinuousLinearMap.isInvertible_smul_iff
    (Complex.ofReal_ne_zero.2 (by linarith [Real.rpow_pos_of_pos (bracket_pos p.2) 1]))]
  exact ContinuousLinearEquiv.coe_refl (R₁ := ℂ) (M₁ := V) ▸ ContinuousLinearMap.isInvertible_equiv

private theorem inverse_coefficient_bracketAddOne (p : CoordinateSpace n × CoordinateSpace n) :
    ((besselPotential 1 + inclusion zero_le_one (const (ContinuousLinearMap.id ℂ V)) :
      Symbol n V V 1).coefficient p).inverse =
      (((bracket p.2 + 1)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_besselPotential_add_one, Real.rpow_one, ContinuousLinearMap.inverse_smul,
    ContinuousLinearMap.inverse_id, Complex.ofReal_inv]

section InverseBracket

variable [CompleteSpace V]

/-- `(r + 1)⁻¹ ≤ 2π ⟨ξ⟩ ^ (-1)`, the inverse bound of order `-1`. -/
private theorem inv_bracket_add_one_le (ξ : CoordinateSpace n) :
    (bracket ξ + 1)⁻¹ ≤ 2 * π * (1 + ‖ξ‖ ^ 2) ^ (-1 / 2 : ℝ) := by
  -- `⟨ξ⟩ ≤ 2π r(ξ)`, the comparison of the brackets of `ξ` and `ξ / 2π`.
  have hle : (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) ≤ 2 * π * bracket ξ := by
    have h := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) 1
      ((2 * π)⁻¹ • ξ)
    rwa [smul_inv_smul₀ (by positivity), abs_one, Real.rpow_one] at h
  have hq : 0 < (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by positivity
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ hq, inv_mul_le_iff₀ (by linarith [bracket_pos ξ])]
  nlinarith [bracket_pos ξ, Real.pi_pos]

/-- The symbol `b = (r + 1)⁻¹` of order `-1`. -/
private def inverseBracketAddOne : Symbol n V V (-1) :=
  (besselPotential 1 + inclusion zero_le_one (const (ContinuousLinearMap.id ℂ V))).inverse
    isInvertible_coefficient_bracketAddOne 0 fun _ _ ↦ ⟨2 * π, fun x _ ξ _ ↦ by
      rw [inverse_coefficient_bracketAddOne]
      refine (norm_ofReal_smul_id_le _).trans ?_
      rw [abs_of_pos (inv_pos.2 (by linarith [bracket_pos ξ]))]
      exact inv_bracket_add_one_le ξ⟩

private theorem coefficient_inverseBracketAddOne (p : CoordinateSpace n × CoordinateSpace n) :
    (inverseBracketAddOne : Symbol n V V (-1)).coefficient p =
      (((bracket p.2 + 1)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [inverseBracketAddOne, coefficient_inverse, inverse_coefficient_bracketAddOne]

/-- The asymptotic sum `b = (r + 1)⁻¹`, as a symbol of the order `-1` of the first term. -/
def asymptoticSum : Symbol n V V (order 0) :=
  inclusion (by simp [order]) inverseBracketAddOne

private theorem coefficient_asymptoticSum (p : CoordinateSpace n × CoordinateSpace n) :
    (asymptoticSum : Symbol n V V (order 0)).coefficient p =
      (((bracket p.2 + 1)⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [asymptoticSum, coefficient_inclusion, coefficient_inverseBracketAddOne]

/-- The remainder after `N` terms is `(-1) ^ N r ^ (-N) (r + 1)⁻¹`. -/
private theorem coefficient_asymptoticSum_sub_sum (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ((asymptoticSum : Symbol n V V (order 0)).coefficient -
        ∑ j ∈ range N, (term j : Symbol n V V (order j)).coefficient) p =
      (((-1) ^ N * (bracket p.2 ^ N)⁻¹ * (bracket p.2 + 1)⁻¹ : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ V := by
  rw [← inv_add_one_sub_sum _ (bracket_pos p.2) N, Complex.ofReal_sub, Complex.ofReal_sum,
    sub_smul, sum_smul]
  simp only [Pi.sub_apply, Finset.sum_apply, coefficient_asymptoticSum, coefficient_term]

/-- `b = (r + 1)⁻¹` is an asymptotic sum of the terms `(-1) ^ j r ^ (-j - 1)`: the remainder
after `N` terms is the symbol `(-1) ^ N r ^ (-N) (r + 1)⁻¹` of order `-N - 1`. -/
example : (asymptoticSum : Symbol n V V (order 0)).IsAsymptoticSum term := by
  refine isAsymptoticSum_iff.2 fun N ↦ ⟨((-1 : ℂ) ^ N) •
    inclusion (m' := order N) (le_of_eq (by simp only [order]; ring))
      ((besselPotential (-(N : ℝ))).comp inverseBracketAddOne), funext fun p ↦ ?_⟩
  simp only [coefficient_asymptoticSum_sub_sum, coefficient_smul, Pi.smul_apply,
    coefficient_inclusion, coefficient_comp, coefficient_besselPotential_eq,
    coefficient_inverseBracketAddOne, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
    smul_smul, Real.rpow_neg (bracket_pos p.2).le, Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- At `ξ = 0`, where `r = 1`, the asymptotic sum is `b = 1 / 2`, and the remainders after `N`
terms alternate between `1 / 2` and `-1 / 2`. -/
example (x : CoordinateSpace n) (N : ℕ) :
    (asymptoticSum : Symbol n V V (order 0)).coefficient (x, 0) =
        ((1 / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V ∧
      ((asymptoticSum : Symbol n V V (order 0)).coefficient -
        ∑ j ∈ range N, (term j : Symbol n V V (order j)).coefficient) (x, 0) =
        (((-1) ^ N / 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_asymptoticSum, coefficient_asymptoticSum_sub_sum, bracket_zero]
  constructor <;> congr 2 <;> ring

end InverseBracket

/-! ### Finite expansions -/

/-- The orders `0, -1, -2, …`. -/
def natOrder (j : ℕ) : ℝ := -(j : ℝ)

/-- The terms `1, 0, 0, …` of the orders `0, -1, -2, …`. -/
def unitTerm : (j : ℕ) → Symbol n V V (natOrder j)
  | 0 => inclusion (by simp [natOrder]) (const (ContinuousLinearMap.id ℂ V))
  | _ + 1 => 0

/-- `1` is an asymptotic sum of the terms `1, 0, 0, …`, with remainder `1` after no terms and `0`
after at least one term. -/
example : (inclusion (by simp [natOrder]) (const (ContinuousLinearMap.id ℂ V)) :
    Symbol n V V (natOrder 0)).IsAsymptoticSum unitTerm := by
  refine isAsymptoticSum_iff.2 fun N ↦ ?_
  rcases N with _ | N
  · exact ⟨inclusion (by simp [natOrder]) (const (ContinuousLinearMap.id ℂ V)), by simp⟩
  · refine ⟨0, ?_⟩
    rw [sum_range_succ']
    simp [unitTerm]

/-- The orders `0, 0, -1, -2, …`, in which the first two coincide. -/
def repeatedOrder : ℕ → ℝ
  | 0 => 0
  | j + 1 => -(j : ℝ)

/-- The terms `1, 2, 0, 0, …` of the orders `0, 0, -1, -2, …`. -/
def twoTerms : (j : ℕ) → Symbol n V V (repeatedOrder j)
  | 0 => const (ContinuousLinearMap.id ℂ V)
  | 1 => (2 : ℂ) • inclusion (by simp [repeatedOrder]) (const (ContinuousLinearMap.id ℂ V))
  | _ + 2 => 0

/-- `3` is an asymptotic sum of the terms `1, 2, 0, 0, …` of the orders `0, 0, -1, -2, …`, with
the remainders `3`, `2` and then `0`. -/
example : ((3 : ℂ) • const (ContinuousLinearMap.id ℂ V) :
    Symbol n V V (repeatedOrder 0)).IsAsymptoticSum twoTerms := by
  refine isAsymptoticSum_iff.2 fun N ↦ ?_
  rcases N with _ | _ | N
  · exact ⟨(3 : ℂ) • const (ContinuousLinearMap.id ℂ V), by simp⟩
  · refine ⟨twoTerms 1, funext fun p ↦ ?_⟩
    simp only [twoTerms, zero_add, range_one, sum_singleton, Pi.sub_apply, coefficient_smul,
      Pi.smul_apply, coefficient_inclusion, coefficient_const]
    module
  · refine ⟨0, funext fun p ↦ ?_⟩
    rw [sum_range_succ', sum_range_succ']
    simp only [twoTerms, coefficient_zero, sum_const_zero, zero_add, Pi.sub_apply, Pi.add_apply,
      Pi.zero_apply, coefficient_smul, Pi.smul_apply, coefficient_inclusion, coefficient_const]
    module

end TauCeti.Examples.AsymptoticSum
