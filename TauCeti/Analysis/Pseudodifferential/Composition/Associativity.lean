/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Associativity of the formal composition of symbols

The composition of quantizations has the asymptotic expansion `a # b ∼ ∑ₖ sharpTerm a b k`, whose
`k`-th term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` has order `m' + m - k`
(`TauCeti.Symbol.sharpTerm`). This file shows that this formal composition is associative: for
three symbols `a`, `b`, `c` and every `l`, the terms of total index `l` of `(a # b) # c` and of
`a # (b # c)` agree,

`∑_{i + j = l} sharpTerm (sharpTerm a b i) c j = ∑_{i + j = l} sharpTerm a (sharpTerm b c j) i`.

Both sides equal `((-i)^l / l!) (L₁₂ + L₁₃ + L₂₃)^l (a, b, c)`, where `L_{pq}` differentiates the
`p`-th factor in the frequency and the `q`-th in the position, contracted over the coordinates.

The main consequence is that **parametrix symbols are unique modulo smoothing symbols**. If
`1 ∼ ∑ₖ sharpTerm a b k` (`b` is the symbol of a right parametrix of `Op(a)`) and
`1 ∼ ∑ₖ sharpTerm b' a k` (`b'` is the symbol of a left parametrix), then `b - b'` is smoothing,
by the formal version of `b' = b' (a b) = (b' a) b = b`. So a left and a right parametrix
symbol of an elliptic symbol, which are constructed separately, are both two-sided parametrix
symbols.

## Main results

* `TauCeti.Symbol.sum_antidiagonal_coefficient_sharpTerm_assoc`: **associativity of the formal
  composition**.
* `TauCeti.Symbol.isSmoothing_sub_of_isAsymptoticSum_sharpTerm`: **uniqueness of parametrix
  symbols**: a right and a left parametrix symbol of the same symbol differ by a smoothing symbol.

## Proof outline

Write `F_l(a, b, c)` for either side of the associativity identity. Both satisfy `F_0 = (a ∘ b) ∘ c`
and the same recursion

`(l + 1) F_{l+1}(a, b, c) = -i ∑ⱼ (F_l(∂_{ξⱼ} a, ∂_{xⱼ} b, c) + F_l(∂_{ξⱼ} a, b, ∂_{xⱼ} c) +
  F_l(a, ∂_{ξⱼ} b, ∂_{xⱼ} c))`,

so they agree by induction on `l`. The recursion follows by splitting `l + 1 = i + j` on the
antidiagonal: the defining recursion of `sharpTerm` handles the index that is lowered, and the
Leibniz rules for `sharpTerm` (`TauCeti.Symbol.coefficient_frequencyDeriv_sharpTerm` and
`TauCeti.Symbol.spatialDeriv_sharpTerm`) distribute the derivative that falls on the inner
formal composition.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.5)–(2.7)
  and (4.1)–(4.6).
-/

public section

noncomputable section

open Finset Finset.Nat

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' m'' : ℝ} {V W U X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Associativity -/

section Assoc

/-- The bookkeeping on the antidiagonal behind both recursions: if
`(i + 1) F(i + 1, k) = c ∑ⱼ A j (i, k)` and `(k + 1) F(i, k + 1) = c ∑ⱼ B j (i, k)`, then
`(l + 1) ∑_{i + k = l + 1} F(i, k) = c ∑ⱼ (∑_{i + k = l} A j (i, k) + ∑_{i + k = l} B j (i, k))`. -/
private theorem succ_smul_sum_antidiagonal {M ι : Type*} [AddCommGroup M] [Module ℂ M]
    [Fintype ι] (c : ℂ) (F : ℕ × ℕ → M) (A B : ι → ℕ × ℕ → M)
    (hA : ∀ i k : ℕ, ((i : ℂ) + 1) • F (i + 1, k) = c • ∑ j, A j (i, k))
    (hB : ∀ i k : ℕ, ((k : ℂ) + 1) • F (i, k + 1) = c • ∑ j, B j (i, k)) (l : ℕ) :
    ((l : ℂ) + 1) • ∑ p ∈ antidiagonal (l + 1), F p =
      c • ∑ j, (∑ p ∈ antidiagonal l, A j p + ∑ p ∈ antidiagonal l, B j p) := by
  calc ((l : ℂ) + 1) • ∑ p ∈ antidiagonal (l + 1), F p
      = ∑ p ∈ antidiagonal (l + 1), (p.1 : ℂ) • F p +
          ∑ p ∈ antidiagonal (l + 1), (p.2 : ℂ) • F p := by
        rw [smul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [← add_smul]
        congr 1
        exact_mod_cast (mem_antidiagonal.1 hp).symm
    _ = ∑ p ∈ antidiagonal l, c • ∑ j, A j p + ∑ p ∈ antidiagonal l, c • ∑ j, B j p := by
        rw [sum_antidiagonal_succ, sum_antidiagonal_succ']
        simp only [Nat.cast_zero, zero_smul, zero_add, Nat.cast_add, Nat.cast_one]
        exact congrArg₂ (· + ·) (sum_congr rfl fun p _ ↦ hA p.1 p.2)
          (sum_congr rfl fun p _ ↦ hB p.1 p.2)
    _ = _ := by
        simp only [← smul_sum, ← smul_add]
        rw [sum_comm (s := antidiagonal l), sum_comm (s := antidiagonal l), ← sum_add_distrib]

/-- The terms of `(a # b) # c` of total index `l`. -/
private def assocLeft (a : Symbol n U X m'') (b : Symbol n W U m') (c : Symbol n V W m) (l : ℕ) :
    CoordinateSpace n × CoordinateSpace n → V →L[ℂ] X :=
  ∑ p ∈ antidiagonal l, ((a.sharpTerm b p.1).sharpTerm c p.2).coefficient

/-- The terms of `a # (b # c)` of total index `l`. -/
private def assocRight (a : Symbol n U X m'') (b : Symbol n W U m') (c : Symbol n V W m) (l : ℕ) :
    CoordinateSpace n × CoordinateSpace n → V →L[ℂ] X :=
  ∑ p ∈ antidiagonal l, (a.sharpTerm (b.sharpTerm c p.2) p.1).coefficient

/-- The coefficient of `sharpTerm a b (k + 1)` as the linear combination of the coefficients of the
terms `sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k` given by the defining recursion. -/
private theorem coefficient_sharpTerm_succ_eq_sum (a : Symbol n W U m') (b : Symbol n V W m)
    (k : ℕ) : (a.sharpTerm b (k + 1)).coefficient = ∑ j, (-Complex.I / (k + 1)) •
      ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient := by
  funext p
  simp [coefficient_sharpTerm_succ, smul_sum]

/-- Multiplying the recursion of `coefficient_sharpTerm_succ_eq_sum` by `k + 1`. -/
private theorem succ_smul_sum_smul {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Fintype ι]
    (k : ℕ) (f : ι → M) :
    ((k : ℂ) + 1) • ∑ j, (-Complex.I / (k + 1)) • f j = -Complex.I • ∑ j, f j := by
  rw [← smul_sum, smul_smul, mul_div_cancel₀ _ (by exact_mod_cast k.succ_ne_zero)]

/-- The recursion satisfied by the terms of `(a # b) # c`. -/
private theorem recursion_assocLeft (a : Symbol n U X m'') (b : Symbol n W U m')
    (c : Symbol n V W m) (l : ℕ) :
    ((l : ℂ) + 1) • assocLeft a b c (l + 1) = -Complex.I • ∑ j,
      (assocLeft (frequencyDeriv j a) (spatialDeriv j b) c l +
        (assocLeft (frequencyDeriv j a) b (spatialDeriv j c) l +
          assocLeft a (frequencyDeriv j b) (spatialDeriv j c) l)) := by
  have hA (i k : ℕ) : ((i : ℂ) + 1) • ((a.sharpTerm b (i + 1)).sharpTerm c k).coefficient =
      -Complex.I • ∑ j, (((frequencyDeriv j a).sharpTerm (spatialDeriv j b) i).sharpTerm c
        k).coefficient := by
    -- The inner index is lowered by the recursion of `sharpTerm a b`.
    rw [coefficient_sharpTerm_eq_sum_left univ _ _ (coefficient_sharpTerm_succ_eq_sum a b i),
      succ_smul_sum_smul]
  have hB (i k : ℕ) : ((k : ℂ) + 1) • ((a.sharpTerm b i).sharpTerm c (k + 1)).coefficient =
      -Complex.I • ∑ j, ((((frequencyDeriv j a).sharpTerm b i).sharpTerm (spatialDeriv j c)
        k).coefficient + ((a.sharpTerm (frequencyDeriv j b) i).sharpTerm (spatialDeriv j c)
          k).coefficient) := by
    -- The outer index is lowered, and the frequency derivative of `sharpTerm a b i` is distributed.
    rw [coefficient_sharpTerm_succ_eq_sum, succ_smul_sum_smul]
    congr 1
    refine sum_congr rfl fun j _ ↦ coefficient_sharpTerm_add_left ?_ _ _
    funext p
    exact coefficient_frequencyDeriv_sharpTerm j a b i p
  rw [assocLeft, succ_smul_sum_antidiagonal _
    (fun p ↦ ((a.sharpTerm b p.1).sharpTerm c p.2).coefficient)
    (fun j p ↦ (((frequencyDeriv j a).sharpTerm (spatialDeriv j b) p.1).sharpTerm c
      p.2).coefficient)
    (fun j p ↦ (((frequencyDeriv j a).sharpTerm b p.1).sharpTerm (spatialDeriv j c)
      p.2).coefficient + ((a.sharpTerm (frequencyDeriv j b) p.1).sharpTerm (spatialDeriv j c)
        p.2).coefficient)
    hA hB l]
  simp only [assocLeft, sum_add_distrib]

/-- The recursion satisfied by the terms of `a # (b # c)`, the same as for `(a # b) # c`. -/
private theorem recursion_assocRight (a : Symbol n U X m'') (b : Symbol n W U m')
    (c : Symbol n V W m) (l : ℕ) :
    ((l : ℂ) + 1) • assocRight a b c (l + 1) = -Complex.I • ∑ j,
      ((assocRight (frequencyDeriv j a) (spatialDeriv j b) c l +
        assocRight (frequencyDeriv j a) b (spatialDeriv j c) l) +
          assocRight a (frequencyDeriv j b) (spatialDeriv j c) l) := by
  have hA (i k : ℕ) : ((i : ℂ) + 1) • (a.sharpTerm (b.sharpTerm c k) (i + 1)).coefficient =
      -Complex.I • ∑ j, (((frequencyDeriv j a).sharpTerm ((spatialDeriv j b).sharpTerm c k)
        i).coefficient + ((frequencyDeriv j a).sharpTerm (b.sharpTerm (spatialDeriv j c) k)
          i).coefficient) := by
    -- The outer index is lowered, and the position derivative of `sharpTerm b c k` is distributed.
    rw [coefficient_sharpTerm_succ_eq_sum, succ_smul_sum_smul]
    congr 1
    refine sum_congr rfl fun j _ ↦ coefficient_sharpTerm_add_right ?_ _ _
    rw [spatialDeriv_sharpTerm, coefficient_add]
  have hB (i k : ℕ) : ((k : ℂ) + 1) • (a.sharpTerm (b.sharpTerm c (k + 1)) i).coefficient =
      -Complex.I • ∑ j, (a.sharpTerm ((frequencyDeriv j b).sharpTerm (spatialDeriv j c) k)
        i).coefficient := by
    -- The inner index is lowered by the recursion of `sharpTerm b c`.
    rw [coefficient_sharpTerm_eq_sum_right univ _ _ (coefficient_sharpTerm_succ_eq_sum b c k),
      succ_smul_sum_smul]
  rw [assocRight, succ_smul_sum_antidiagonal _
    (fun p ↦ (a.sharpTerm (b.sharpTerm c p.2) p.1).coefficient)
    (fun j p ↦ ((frequencyDeriv j a).sharpTerm ((spatialDeriv j b).sharpTerm c p.2)
      p.1).coefficient + ((frequencyDeriv j a).sharpTerm (b.sharpTerm (spatialDeriv j c) p.2)
        p.1).coefficient)
    (fun j p ↦ (a.sharpTerm ((frequencyDeriv j b).sharpTerm (spatialDeriv j c) p.2)
      p.1).coefficient)
    hA hB l]
  simp only [assocRight, sum_add_distrib]

/-- Both groupings satisfy the same recursion, hence agree. -/
private theorem assocLeft_eq_assocRight (a : Symbol n U X m'') (b : Symbol n W U m')
    (c : Symbol n V W m) (l : ℕ) : assocLeft a b c l = assocRight a b c l := by
  induction l generalizing m m' m'' with
  | zero =>
    funext p
    simp [assocLeft, assocRight, ContinuousLinearMap.comp_assoc]
  | succ l ih =>
    refine smul_right_injective _ (by exact_mod_cast l.succ_ne_zero : (l : ℂ) + 1 ≠ 0) ?_
    simp only [recursion_assocLeft, recursion_assocRight, ih, add_assoc]

/-- **Associativity of the formal composition.** For symbols `a`, `b`, `c` and every `l`, the terms
of total index `l` of the formal compositions `(a # b) # c` and `a # (b # c)` agree:

`∑_{i + j = l} sharpTerm (sharpTerm a b i) c j = ∑_{i + j = l} sharpTerm a (sharpTerm b c j) i`.

Both sides are symbols of order `m'' + m' + m - l`; the identity is stated for their coefficients,
since the two orders are not syntactically equal. -/
theorem sum_antidiagonal_coefficient_sharpTerm_assoc (a : Symbol n U X m'') (b : Symbol n W U m')
    (c : Symbol n V W m) (l : ℕ) :
    ∑ p ∈ antidiagonal l, ((a.sharpTerm b p.1).sharpTerm c p.2).coefficient =
      ∑ p ∈ antidiagonal l, (a.sharpTerm (b.sharpTerm c p.2) p.1).coefficient := by
  simpa only [assocLeft, assocRight] using assocLeft_eq_assocRight a b c l

end Assoc

/-! ### Uniqueness of parametrix symbols -/

section Parametrix

/-- If `e - ∑_{i < N} tᵢ = r` on the level of coefficients, then the same holds for the terms of
index `k` of the formal compositions with `b` on the right. -/
private theorem sum_coefficient_sharpTerm_left {μ₀ μr : ℝ} {μ : ℕ → ℝ} (e : Symbol n W U μ₀)
    (t : ∀ i, Symbol n W U (μ i)) (r : Symbol n W U μr) (hμ : μr ≤ μ₀) (N : ℕ)
    (h : e.coefficient - ∑ i ∈ range N, (t i).coefficient = r.coefficient) (b : Symbol n V W m)
    (k : ℕ) : ∑ i ∈ range N, ((t i).sharpTerm b k).coefficient =
      (e.sharpTerm b k).coefficient - (r.sharpTerm b k).coefficient := by
  have hS : (e - inclusion hμ r).coefficient = ∑ i ∈ range N, (1 : ℂ) • (t i).coefficient := by
    rw [coefficient_sub, coefficient_inclusion, ← h]
    simp
  have he : e.coefficient = (e - inclusion hμ r).coefficient + r.coefficient := by
    rw [coefficient_sub, coefficient_inclusion, sub_add_cancel]
  rw [coefficient_sharpTerm_add_left he, coefficient_sharpTerm_eq_sum_left _ _ t hS]
  simp

/-- If `e - ∑_{i < N} tᵢ = r` on the level of coefficients, then the same holds for the terms of
index `k` of the formal compositions with `a` on the left. -/
private theorem sum_coefficient_sharpTerm_right {μ₀ μr : ℝ} {μ : ℕ → ℝ} (e : Symbol n V W μ₀)
    (t : ∀ i, Symbol n V W (μ i)) (r : Symbol n V W μr) (hμ : μr ≤ μ₀) (N : ℕ)
    (h : e.coefficient - ∑ i ∈ range N, (t i).coefficient = r.coefficient) (a : Symbol n W U m')
    (k : ℕ) : ∑ i ∈ range N, (a.sharpTerm (t i) k).coefficient =
      (a.sharpTerm e k).coefficient - (a.sharpTerm r k).coefficient := by
  have hS : (e - inclusion hμ r).coefficient = ∑ i ∈ range N, (1 : ℂ) • (t i).coefficient := by
    rw [coefficient_sub, coefficient_inclusion, ← h]
    simp
  have he : e.coefficient = (e - inclusion hμ r).coefficient + r.coefficient := by
    rw [coefficient_sub, coefficient_inclusion, sub_add_cancel]
  rw [coefficient_sharpTerm_add_right he, coefficient_sharpTerm_eq_sum_right _ _ t hS]
  simp

/-- The terms of the formal composition `1 # b`: only the term of index `0` survives. -/
private theorem sum_range_coefficient_const_sharpTerm (b : Symbol n V W m) (K : ℕ) :
    ∑ j ∈ range (K + 1), ((const (.id ℂ W)).sharpTerm b j).coefficient = b.coefficient := by
  rw [sum_range_succ']
  simp only [const_sharpTerm_succ, coefficient_zero, sum_const_zero, zero_add]
  funext p
  simp

/-- The terms of the formal composition `a # 1`: only the term of index `0` survives. -/
private theorem sum_range_coefficient_sharpTerm_const (a : Symbol n W U m') (K : ℕ) :
    ∑ i ∈ range (K + 1), (a.sharpTerm (const (.id ℂ W)) i).coefficient = a.coefficient := by
  rw [sum_range_succ']
  simp only [sharpTerm_const_succ, coefficient_zero, sum_const_zero, zero_add]
  funext p
  simp

/-- The order of the remainder terms in the left grouping. -/
private theorem order_sharpTerm_le (m : ℝ) {K j : ℕ} (hj : j ≤ K) :
    -m + m - ((K - j : ℕ) : ℝ) + -m - j ≤ -m - K := by
  rw [Nat.cast_sub hj]
  linarith

/-- The order of the remainder terms in the right grouping. -/
private theorem sharpTerm_order_le (m : ℝ) {K i : ℕ} (hi : i ≤ K) :
    -m + (m + -m - ((K - i : ℕ) : ℝ)) - i ≤ -m - K := by
  rw [Nat.cast_sub hi]
  linarith

/-- The left grouping `(b' # a) # b` up to total index `N + 1`: if `1 - ∑_{i < N} sharpTerm b' a i`
is the symbol `r' N` of order `-N`, it is `b` up to terms of order `-m - (N + 1)`. -/
private theorem sum_range_sum_antidiagonal_left {a : Symbol n V W m} {b' : Symbol n W V (-m)}
    {r' : ∀ N : ℕ, Symbol n V V (-m + m - N)}
    (hr' : ∀ N, (const (.id ℂ V)).coefficient - ∑ i ∈ range N, (b'.sharpTerm a i).coefficient =
      (r' N).coefficient) (b : Symbol n W V (-m)) (N : ℕ) :
    ∑ l ∈ range (N + 1), ∑ p ∈ antidiagonal l,
      ((b'.sharpTerm a p.1).sharpTerm b p.2).coefficient = b.coefficient -
        ∑ j : Fin (N + 1), ((r' (N + 1 - j)).sharpTerm b j).coefficient := by
  have hswap (l : ℕ) : ∑ p ∈ antidiagonal l, ((b'.sharpTerm a p.1).sharpTerm b p.2).coefficient =
      ∑ p ∈ antidiagonal l, ((b'.sharpTerm a p.2).sharpTerm b p.1).coefficient := by
    simpa only [Prod.fst_swap, Prod.snd_swap] using sum_antidiagonal_swap (n := l)
      (f := fun p ↦ ((b'.sharpTerm a p.2).sharpTerm b p.1).coefficient)
  -- Group the terms by the index `j` of the outer composition with `b`.
  rw [sum_congr rfl fun l _ ↦ hswap l, sum_congr rfl fun l _ ↦ sum_antidiagonal_eq_sum_range_succ
    (fun j i ↦ ((b'.sharpTerm a i).sharpTerm b j).coefficient) l]
  refine (sum_range_diag_flip (N + 1)
    fun j i ↦ ((b'.sharpTerm a i).sharpTerm b j).coefficient).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ ((r' (N + 1 - j)).sharpTerm b j).coefficient),
    ← sum_range_coefficient_const_sharpTerm b N, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ ↦ sum_coefficient_sharpTerm_left _ _ _ ?_ _ (hr' _) b j
  have := (N + 1 - j : ℕ).cast_nonneg (α := ℝ)
  linarith

/-- The right grouping `b' # (a # b)` up to total index `N + 1`: if `1 - ∑_{j < N} sharpTerm a b j`
is the symbol `r N` of order `-N`, it is `b'` up to terms of order `-m - (N + 1)`. -/
private theorem sum_range_sum_antidiagonal_right {a : Symbol n V W m} {b : Symbol n W V (-m)}
    {r : ∀ N : ℕ, Symbol n W W (m + -m - N)}
    (hr : ∀ N, (const (.id ℂ W)).coefficient - ∑ j ∈ range N, (a.sharpTerm b j).coefficient =
      (r N).coefficient) (b' : Symbol n W V (-m)) (N : ℕ) :
    ∑ l ∈ range (N + 1), ∑ p ∈ antidiagonal l,
      (b'.sharpTerm (a.sharpTerm b p.2) p.1).coefficient = b'.coefficient -
        ∑ i : Fin (N + 1), (b'.sharpTerm (r (N + 1 - i)) i).coefficient := by
  -- Group the terms by the index `i` of the outer composition with `b'`.
  rw [sum_congr rfl fun l _ ↦ sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ (b'.sharpTerm (a.sharpTerm b j) i).coefficient) l]
  refine (sum_range_diag_flip (N + 1)
    fun i j ↦ (b'.sharpTerm (a.sharpTerm b j) i).coefficient).trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (b'.sharpTerm (r (N + 1 - i)) i).coefficient),
    ← sum_range_coefficient_sharpTerm_const b' N, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ sum_coefficient_sharpTerm_right _ _ _ ?_ _ (hr _) b' i
  have := (N + 1 - i : ℕ).cast_nonneg (α := ℝ)
  linarith

/-- **Uniqueness of parametrix symbols.** Let `a` be a symbol of order `m`. If `b` is the symbol of
a right parametrix, `1 ∼ ∑ₖ sharpTerm a b k`, and `b'` is the symbol of a left parametrix,
`1 ∼ ∑ₖ sharpTerm b' a k`, then `b - b'` is a smoothing symbol.

This is the formal version of `b' = b' (a b) = (b' a) b = b`, for the associative formal
composition (`sum_antidiagonal_coefficient_sharpTerm_assoc`). -/
theorem isSmoothing_sub_of_isAsymptoticSum_sharpTerm {a : Symbol n V W m}
    {b b' : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b))
    (hb' : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b'.sharpTerm a)) :
    (b - b').IsSmoothing := by
  choose r hr using isAsymptoticSum_iff.1 hb
  choose r' hr' using isAsymptoticSum_iff.1 hb'
  refine isSmoothing_iff.2 fun μ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (-m - μ)
  -- Both groupings of `b' # a # b` up to total index `N + 1` agree; the first is `b` and the
  -- second is `b'`, up to terms of order `-m - (N + 1)`.
  have hassoc := sum_congr rfl fun l (_ : l ∈ range (N + 1)) ↦
    sum_antidiagonal_coefficient_sharpTerm_assoc b' a b l
  rw [sum_range_sum_antidiagonal_left (fun N ↦ by rw [← hr' N, coefficient_inclusion]) b N,
    sum_range_sum_antidiagonal_right (fun N ↦ by rw [← hr N, coefficient_inclusion]) b' N]
    at hassoc
  refine ⟨inclusion (show -m - ((N + 1 : ℕ) : ℝ) ≤ μ by push_cast; linarith)
    (∑ j : Fin (N + 1), inclusion (order_sharpTerm_le m j.isLt.le)
        ((r' (N + 1 - j)).sharpTerm b j) -
      ∑ i : Fin (N + 1), inclusion (sharpTerm_order_le m i.isLt.le)
        (b'.sharpTerm (r (N + 1 - i)) i)), ?_⟩
  simp only [coefficient_inclusion, coefficient_sub, coefficient_sum]
  rw [sub_eq_sub_iff_sub_eq_sub, ← neg_sub, hassoc, neg_sub]

end Parametrix

end Symbol

end TauCeti
