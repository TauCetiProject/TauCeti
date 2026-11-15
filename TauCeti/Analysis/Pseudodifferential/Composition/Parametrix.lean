/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Associativity
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic

/-!
# Parametrix symbols of elliptic symbols

Let `a` be a symbol of order `m` with values in `V →L[ℂ] W`. A *left parametrix symbol* of `a` is
a symbol `b` of order `-m` whose formal composition with `a` is the identity,

`1 ∼ ∑ₖ sharpTerm b a k`,

and a *right parametrix symbol* is one with `1 ∼ ∑ₖ sharpTerm a b k`, both in the sense of
asymptotic sums (`TauCeti.Symbol.IsAsymptoticSum`). These are the symbols from which parametrices
of `Op(a)` are built: the composition expansion
(`TauCeti.Symbol.sharp_eq_sum_sharpTerm_add_sharpRemainder`) identifies `sharpTerm` with the terms
of the symbol of a composition of quantizations.

This file constructs them. If `b₀` is a pointwise left inverse of `a` modulo a smoothing symbol,
for instance the cut-off inverse `χ(ξ / R) a(x, ξ)⁻¹` of an elliptic symbol
(`TauCeti.Symbol.cutoffInverse`), then `a` has a left parametrix symbol, and it agrees with `b₀`
up to a symbol of order `-m - 1` as soon as `b₀` is also a pointwise right inverse. In particular
every symbol elliptic above some radius has a **two-sided parametrix symbol**, unique modulo
smoothing symbols. Unlike `TauCeti.ClassicalSymbol.exists_sharpTerms_eq_left`, which solves the
same equations for the homogeneous terms of a classical symbol, nothing here assumes `a` classical.

## Main results

* `TauCeti.Symbol.exists_isAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.exists_isAsymptoticSum_sharpTerm_right`: a pointwise left (right) inverse modulo
  smoothing symbols gives a left (right) parametrix symbol.
* `TauCeti.Symbol.exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_right`: a left (right)
  parametrix symbol agrees with a pointwise right (left) inverse up to order `-m - 1`.
* `TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`: **an elliptic symbol has a
  two-sided parametrix symbol**.
* `TauCeti.Symbol.isAsymptoticSum_sharpTerm_left_iff`,
  `TauCeti.Symbol.isAsymptoticSum_sharpTerm_right_iff`: the left and the right parametrix symbols
  are exactly the symbols differing from a two-sided one by a smoothing symbol.
* `TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`: **the local parametrix modulo smoothing
  symbols.** For a smooth function `ψ` of the position, `q(x, ξ) = ψ(x) b(x, ξ)` with `b` a left
  parametrix symbol of `a`, and a symbol `p` with compact spatial support which agrees with `a`
  near the support of `ψ`, the composition symbol `q # p` is `ψ(x)` up to a smoothing symbol.

## Proof outline

Suppose `1 - ∑_{k < N} sharpTerm b a k` has order `-N`, which holds for `b = b₀` and `N = 0`. Then
`R = 1 - ∑_{k ≤ N} sharpTerm b a k` has order `-N` as well, and the correction `d = R b₀` of order
`-m - N` satisfies `d a = R` modulo smoothing symbols. Since the later terms `sharpTerm d a k`,
`k ≥ 1`, have order at most `-N - 1`, the symbol `b + d` inverts `a` up to order `-N - 1`. Iterating
gives corrections `d_N` of orders `-m - N`, and an asymptotic sum `b ∼ b₀ + ∑_N d_N` inverts `a` up
to every order, because changing `b` by a symbol of order `-m - N` does not affect the first `N`
terms modulo order `-N`. This is the construction of Taylor, Lecture I, (4.1)–(4.6). A left and a
right parametrix symbol differ by a smoothing symbol
(`TauCeti.Symbol.isSmoothing_sub_of_isAsymptoticSum_sharpTerm`), so each of them is two-sided.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Finset
open scoped Topology ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### Left parametrix symbols -/

section Left

/-- Changing the left factor `b` by a symbol of order `-m - N` keeps `1 - ∑_{k < N} sharpTerm b a k`
of order `-N`. -/
private theorem exists_sub_sum_sharpTerm_left_congr {a : Symbol n V W m} {N : ℕ}
    {b b' : Symbol n W V (-m)} (d : Symbol n W V (-m - N))
    (hb : ∃ r : Symbol n V V (-m + m - N), (const (.id ℂ V) : Symbol n V V 0).coefficient -
      ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    (h : b'.coefficient = b.coefficient + d.coefficient) :
    ∃ r : Symbol n V V (-m + m - N), (const (.id ℂ V) : Symbol n V V 0).coefficient -
      ∑ k ∈ range N, (b'.sharpTerm a k).coefficient = r.coefficient := by
  obtain ⟨r, hr⟩ := hb
  refine ⟨r - ∑ k : Fin N, inclusion (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (d.sharpTerm a k), ?_⟩
  rw [coefficient_sub, coefficient_sum, ← hr]
  simp only [coefficient_inclusion, coefficient_sharpTerm_eq_add_left h, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range fun k ↦ (d.sharpTerm a k).coefficient]
  abel

/-- The correction step for left parametrix symbols: if `b₀ a - 1` is smoothing and
`1 - ∑_{k < N} sharpTerm b a k` has order `-N`, then changing `b` by a symbol of order `-m - N`
makes the sum over `k ≤ N` have order `-N - 1`. -/
private theorem exists_sub_sum_sharpTerm_left_succ {a : Symbol n V W m}
    {b₀ : Symbol n W V (-m)}
    (hb₀ : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing) {N : ℕ}
    {b : Symbol n W V (-m)}
    (hb : ∃ r : Symbol n V V (-m + m - N), (const (.id ℂ V) : Symbol n V V 0).coefficient -
      ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient) :
    ∃ d : Symbol n W V (-m - N), ∃ r : Symbol n V V (-m + m - (N + 1 : ℕ)),
      (const (.id ℂ V) : Symbol n V V 0).coefficient -
        ∑ k ∈ range (N + 1), ((b + inclusion (by simp) d).sharpTerm a k).coefficient =
          r.coefficient := by
  obtain ⟨r, hr⟩ := hb
  -- The remainder `R = 1 - ∑_{k ≤ N} sharpTerm b a k`, of order `-N`, and the correction `R b₀`.
  set R := r - b.sharpTerm a N with hR
  have hRc : R.coefficient = (const (.id ℂ V) : Symbol n V V 0).coefficient -
      ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient := by
    rw [hR, coefficient_sub, ← hr, sum_range_succ]
    abel
  let d : Symbol n W V (-m - N) := inclusion (by linarith) (R.comp b₀)
  have hd₀ : (d.sharpTerm a 0).coefficient = R.coefficient +
      (R.comp (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V)))).coefficient := by
    funext p
    simp [d, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc]
  obtain ⟨t, ht⟩ := isSmoothing_iff.1 (hb₀.comp_left R) (-m + m - (N + 1 : ℕ))
  refine ⟨d, -t - ∑ k : Fin N,
    inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (d.sharpTerm a (k + 1)), ?_⟩
  rw [coefficient_sub, coefficient_neg, coefficient_sum, ht]
  simp only [coefficient_inclusion]
  simp only [coefficient_sharpTerm_eq_add_left (a₀ := b + inclusion (by simp) d) (a₁ := b)
    (a₂ := d) (by rw [coefficient_add, coefficient_inclusion]), sum_add_distrib]
  rw [sum_range_succ' fun k ↦ (d.sharpTerm a k).coefficient, hd₀,
    Fin.sum_univ_eq_sum_range fun k ↦ (d.sharpTerm a (k + 1)).coefficient]
  rw [show ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient =
    (const (.id ℂ V) : Symbol n V V 0).coefficient - R.coefficient by rw [hRc]; abel]
  abel

/-- **Left parametrix symbols.** If a symbol `b₀` of order `-m` is a pointwise left inverse of the
symbol `a` of order `m` modulo smoothing symbols, that is `b₀(x, ξ) a(x, ξ) - 1` is smoothing,
then `a` has a left parametrix symbol: a symbol `b` of order `-m` whose formal composition with `a`
is the identity, `1 ∼ ∑ₖ sharpTerm b a k`. -/
theorem exists_isAsymptoticSum_sharpTerm_left {a : Symbol n V W m} {b₀ : Symbol n W V (-m)}
    (hb₀ : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing) :
    ∃ b : Symbol n W V (-m), IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n V V (-m + m - N),
      (const (.id ℂ V) : Symbol n V V 0).coefficient -
        ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    (b₀ := b₀) ⟨inclusion (by simp) (const (.id ℂ V)), by simp⟩
    (fun _ _ _ d hb h ↦ exists_sub_sum_sharpTerm_left_congr d hb h)
    (fun _ _ hb ↦ exists_sub_sum_sharpTerm_left_succ hb₀ hb)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **The leading term of a left parametrix symbol.** A left parametrix symbol `b` of `a` agrees
with every pointwise right inverse `b₀` of `a` modulo smoothing symbols up to a symbol of order
`-m - 1`. -/
theorem exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_left {a : Symbol n V W m}
    {b b₀ : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    (hb₀ : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing) :
    ∃ r : Symbol n W V (-m - 1), b.coefficient - b₀.coefficient = r.coefficient := by
  -- `b - b₀ = -(1 - b a) b₀ - b (a b₀ - 1)`, where `1 - b a` has order `-1`.
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb 1
  obtain ⟨t, ht⟩ := isSmoothing_iff.1 (hb₀.comp_left b) (-m - 1)
  refine ⟨-inclusion (by push_cast; linarith) (r.comp b₀) - t, ?_⟩
  funext p
  have hp := congrFun hr p
  simp only [range_one, sum_singleton, Pi.sub_apply, coefficient_inclusion,
    coefficient_sharpTerm_zero, coefficient_const] at hp
  simp only [Pi.sub_apply, coefficient_sub, coefficient_neg, coefficient_inclusion,
    coefficient_comp, ht, Pi.neg_apply, coefficient_const, ← hp]
  ext v
  simp

end Left

/-! ### Right parametrix symbols -/

section Right

/-- Changing the right factor `b` by a symbol of order `-m - N` keeps
`1 - ∑_{k < N} sharpTerm a b k` of order `-N`. -/
private theorem exists_sub_sum_sharpTerm_right_congr {a : Symbol n V W m} {N : ℕ}
    {b b' : Symbol n W V (-m)} (d : Symbol n W V (-m - N))
    (hb : ∃ r : Symbol n W W (m + -m - N), (const (.id ℂ W) : Symbol n W W 0).coefficient -
      ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    (h : b'.coefficient = b.coefficient + d.coefficient) :
    ∃ r : Symbol n W W (m + -m - N), (const (.id ℂ W) : Symbol n W W 0).coefficient -
      ∑ k ∈ range N, (a.sharpTerm b' k).coefficient = r.coefficient := by
  obtain ⟨r, hr⟩ := hb
  refine ⟨r - ∑ k : Fin N, inclusion (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (a.sharpTerm d k), ?_⟩
  rw [coefficient_sub, coefficient_sum, ← hr]
  simp only [coefficient_inclusion, coefficient_sharpTerm_eq_add_right h, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range fun k ↦ (a.sharpTerm d k).coefficient]
  abel

/-- The correction step for right parametrix symbols: if `a b₀ - 1` is smoothing and
`1 - ∑_{k < N} sharpTerm a b k` has order `-N`, then changing `b` by a symbol of order `-m - N`
makes the sum over `k ≤ N` have order `-N - 1`. -/
private theorem exists_sub_sum_sharpTerm_right_succ {a : Symbol n V W m}
    {b₀ : Symbol n W V (-m)}
    (hb₀ : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing) {N : ℕ}
    {b : Symbol n W V (-m)}
    (hb : ∃ r : Symbol n W W (m + -m - N), (const (.id ℂ W) : Symbol n W W 0).coefficient -
      ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient) :
    ∃ d : Symbol n W V (-m - N), ∃ r : Symbol n W W (m + -m - (N + 1 : ℕ)),
      (const (.id ℂ W) : Symbol n W W 0).coefficient -
        ∑ k ∈ range (N + 1), (a.sharpTerm (b + inclusion (by simp) d) k).coefficient =
          r.coefficient := by
  obtain ⟨r, hr⟩ := hb
  -- The remainder `R = 1 - ∑_{k ≤ N} sharpTerm a b k`, of order `-N`, and the correction `b₀ R`.
  set R := r - a.sharpTerm b N with hR
  have hRc : R.coefficient = (const (.id ℂ W) : Symbol n W W 0).coefficient -
      ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient := by
    rw [hR, coefficient_sub, ← hr, sum_range_succ]
    abel
  let d : Symbol n W V (-m - N) := inclusion (by linarith) (b₀.comp R)
  have hd₀ : (a.sharpTerm d 0).coefficient = R.coefficient +
      ((a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).comp R).coefficient := by
    funext p
    simp [d, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
  obtain ⟨t, ht⟩ := isSmoothing_iff.1 (hb₀.comp_right R) (m + -m - (N + 1 : ℕ))
  refine ⟨d, -t - ∑ k : Fin N,
    inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
    (a.sharpTerm d (k + 1)), ?_⟩
  rw [coefficient_sub, coefficient_neg, coefficient_sum, ht]
  simp only [coefficient_inclusion]
  simp only [coefficient_sharpTerm_eq_add_right (b₀ := b + inclusion (by simp) d) (b₁ := b)
    (b₂ := d) (by rw [coefficient_add, coefficient_inclusion]), sum_add_distrib]
  rw [sum_range_succ' fun k ↦ (a.sharpTerm d k).coefficient, hd₀,
    Fin.sum_univ_eq_sum_range fun k ↦ (a.sharpTerm d (k + 1)).coefficient]
  rw [show ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient =
    (const (.id ℂ W) : Symbol n W W 0).coefficient - R.coefficient by rw [hRc]; abel]
  abel

/-- **Right parametrix symbols.** If a symbol `b₀` of order `-m` is a pointwise right inverse of
the symbol `a` of order `m` modulo smoothing symbols, that is `a(x, ξ) b₀(x, ξ) - 1` is smoothing,
then `a` has a right parametrix symbol: a symbol `b` of order `-m` such that the formal composition
of `a` with `b` is the identity, `1 ∼ ∑ₖ sharpTerm a b k`. -/
theorem exists_isAsymptoticSum_sharpTerm_right {a : Symbol n V W m} {b₀ : Symbol n W V (-m)}
    (hb₀ : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing) :
    ∃ b : Symbol n W V (-m), IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k)
      (inclusion (by simp) (const (.id ℂ W))) (a.sharpTerm b) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n W W (m + -m - N),
      (const (.id ℂ W) : Symbol n W W 0).coefficient -
        ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    (b₀ := b₀) ⟨inclusion (by simp) (const (.id ℂ W)), by simp⟩
    (fun _ _ _ d hb h ↦ exists_sub_sum_sharpTerm_right_congr d hb h)
    (fun _ _ hb ↦ exists_sub_sum_sharpTerm_right_succ hb₀ hb)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **The leading term of a right parametrix symbol.** A right parametrix symbol `b` of `a` agrees
with every pointwise left inverse `b₀` of `a` modulo smoothing symbols up to a symbol of order
`-m - 1`. -/
theorem exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_right {a : Symbol n V W m}
    {b b₀ : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b))
    (hb₀ : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing) :
    ∃ r : Symbol n W V (-m - 1), b.coefficient - b₀.coefficient = r.coefficient := by
  -- `b - b₀ = -b₀ (1 - a b) - (b₀ a - 1) b`, where `1 - a b` has order `-1`.
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hb 1
  obtain ⟨t, ht⟩ := isSmoothing_iff.1 (hb₀.comp_right b) (-m - 1)
  refine ⟨-inclusion (by push_cast; linarith) (b₀.comp r) - t, ?_⟩
  funext p
  have hp := congrFun hr p
  simp only [range_one, sum_singleton, Pi.sub_apply, coefficient_inclusion,
    coefficient_sharpTerm_zero, coefficient_const] at hp
  simp only [Pi.sub_apply, coefficient_sub, coefficient_neg, coefficient_inclusion,
    coefficient_comp, ht, Pi.neg_apply, coefficient_const, ← hp]
  ext v
  simp

end Right

/-! ### Two-sided parametrix symbols -/

/-- **An elliptic symbol has a two-sided parametrix symbol.** A symbol `a` of order `m` that is
elliptic above some radius has a parametrix symbol `b` of order `-m`: the formal compositions of
`b` with `a` in both orders are the identity, `1 ∼ ∑ₖ sharpTerm b a k` and
`1 ∼ ∑ₖ sharpTerm a b k`. It is unique modulo smoothing symbols
(`TauCeti.Symbol.isAsymptoticSum_sharpTerm_left_iff`), and agrees with the cut-off inverse
`χ(ξ / t) a(x, ξ)⁻¹` (`TauCeti.Symbol.cutoffInverse`) up to a symbol of order `-m - 1`
(`TauCeti.Symbol.exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_left`). -/
theorem IsEllipticAbove.exists_isAsymptoticSum_sharpTerm [CompleteSpace V] {a : Symbol n V W m}
    {R : ℝ} (ha : a.IsEllipticAbove R) :
    ∃ b : Symbol n W V (-m),
      IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
        (b.sharpTerm a) ∧
      IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
        (a.sharpTerm b) := by
  obtain ⟨b₀, R', hb₀⟩ := exists_isEllipticAbove_iff.1 ⟨R, ha⟩
  have hL : (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing :=
    isSmoothing_of_coefficient_eq_zero R' fun x ξ hξ ↦ by simp [(hb₀ x ξ hξ).1]
  have hR : (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing :=
    isSmoothing_of_coefficient_eq_zero R' fun x ξ hξ ↦ by simp [(hb₀ x ξ hξ).2]
  obtain ⟨bL, hbL⟩ := exists_isAsymptoticSum_sharpTerm_left hL
  obtain ⟨bR, hbR⟩ := exists_isAsymptoticSum_sharpTerm_right hR
  exact ⟨bL, hbL, isAsymptoticSum_sharpTerm_of_isSmoothing_sub_right hbR
    (isSmoothing_sub_of_isAsymptoticSum_sharpTerm hbL hbR)⟩

/-- **Uniqueness of left parametrix symbols.** If `b` is a two-sided parametrix symbol of `a`, then
the left parametrix symbols of `a` are exactly the symbols `b'` with `b' - b` smoothing. -/
theorem isAsymptoticSum_sharpTerm_left_iff {a : Symbol n V W m} {b b' : Symbol n W V (-m)}
    (hL : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    (hR : IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b)) :
    IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b'.sharpTerm a) ↔ (b' - b).IsSmoothing :=
  ⟨fun h ↦ isSmoothing_sub_of_isAsymptoticSum_sharpTerm h hR,
    isAsymptoticSum_sharpTerm_of_isSmoothing_sub_left hL⟩

/-- **Uniqueness of right parametrix symbols.** If `b` is a two-sided parametrix symbol of `a`,
then the right parametrix symbols of `a` are exactly the symbols `b'` with `b' - b` smoothing. -/
theorem isAsymptoticSum_sharpTerm_right_iff {a : Symbol n V W m} {b b' : Symbol n W V (-m)}
    (hL : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a))
    (hR : IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b)) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b') ↔ (b' - b).IsSmoothing := by
  refine ⟨fun h ↦ ?_, isAsymptoticSum_sharpTerm_of_isSmoothing_sub_right hR⟩
  simpa using (isSmoothing_sub_of_isAsymptoticSum_sharpTerm hL h).neg

/-! ### The local parametrix modulo smoothing symbols -/

section Parametrix

variable [CompleteSpace V] [CompleteSpace W]

/-- **The local parametrix modulo smoothing symbols.** Let `b` be a left parametrix symbol of the
symbol `a` of order `m`, `1 ∼ ∑ₖ sharpTerm b a k`. Let `ψ` be a smooth function of the position,
`q(x, ξ) = ψ(x) b(x, ξ)`, and `p` a symbol with compact spatial support which agrees with `a` at
all positions near the support of `ψ`. Then the composition symbol `q # p` is `ψ(x)` up to a
smoothing symbol. -/
theorem isSmoothing_sharp_sub_ofSpatial {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) {q : Symbol n W V (-m)}
    (hq : ∀ x ξ, q.coefficient (x, ξ) = ψ x • b.coefficient (x, ξ)) {p : Symbol n V W m}
    (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ)) :
    (q.sharp p hp - inclusion (neg_add_cancel m).ge
      (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
        (hψ.smul contDiff_const))).IsSmoothing := by
  refine isSmoothing_iff.2 fun μ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (-μ)
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hab N
  -- `q # p - ψ = (q # p - ∑_{k < N} sharpTerm q p k) - ψ (1 - ∑_{k < N} sharpTerm b a k)`.
  refine ⟨inclusion (m := -m + m - N) (by linarith) (q.sharpRemainder p hp N) -
    inclusion (m := 0 + (-m + m - N)) (by linarith)
      ((ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ.smul contDiff_const)).comp r),
    ?_⟩
  funext ⟨x, ξ⟩
  have hr' := congrFun hr (x, ξ)
  simp only [Pi.sub_apply, Finset.sum_apply, coefficient_inclusion, coefficient_const] at hr'
  simp only [coefficient_sub, coefficient_inclusion, coefficient_sharpRemainder, coefficient_comp,
    coefficient_ofSpatial, Pi.sub_apply, Finset.sum_apply,
    coefficient_sharpTerm_of_eq_smul_of_eventuallyEq hq hpa, ← hr',
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, smul_sub, Finset.smul_sum]
  abel

end Parametrix

end Symbol

end TauCeti
