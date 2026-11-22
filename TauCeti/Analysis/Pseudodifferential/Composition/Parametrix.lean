/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Associativity
public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
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

This file constructs them. If `b₀` is a pointwise left inverse of `a` modulo a symbol of order `-1`,
for instance the cut-off inverse `χ(ξ / R) a(x, ξ)⁻¹` of an elliptic symbol
(`TauCeti.Symbol.cutoffInverse`), then `a` has a left parametrix symbol, and it agrees with `b₀`
up to a symbol of order `-m - 1` as soon as `b₀` is also a pointwise right inverse. In particular
every symbol elliptic above some radius has a **two-sided parametrix symbol**, unique modulo
smoothing symbols. Unlike `TauCeti.ClassicalSymbol.exists_sharpTerms_eq_left`, which solves the
same equations for the homogeneous terms of a classical symbol, nothing here assumes `a` classical.

For a symbol `a` whose estimates are uniform in the position (`TauCeti.Symbol.IsUniform`) and that
is uniformly elliptic, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)` for `‖ξ‖ ≥ R` and `C`, `R` independent of
`x` (`TauCeti.Symbol.IsUniformlyEllipticAbove`), the parametrix symbols can be chosen uniform as
well, and the remainders `1 - ∑_{k < N} sharpTerm b a k` then have order `-N` uniformly in the
position. These are the parametrix symbols of the calculus of symbols with estimates uniform on all
of `ℝⁿ`, where no compact localization in the position is available.

A symbol which is only elliptic on a set `S` of points `(x, ξ)` (`TauCeti.Symbol.IsEllipticOn`)
has **microlocal parametrix symbols**: for every symbol `c` of order `0` vanishing outside `S`,
there are symbols `b` of order `-m` with `c ∼ ∑ₖ sharpTerm b a k`, and others with
`c ∼ ∑ₖ sharpTerm a b k`. For a conic cutoff `c` near a covector, these invert `Op(a)`
microlocally there.

## Main results

* `TauCeti.Symbol.exists_isAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.exists_isAsymptoticSum_sharpTerm_right`: a pointwise left (right) inverse modulo
  symbols of order `-1` gives a left (right) parametrix symbol.
* `TauCeti.Symbol.exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.exists_coefficient_sub_eq_of_isAsymptoticSum_sharpTerm_right`: a left (right)
  parametrix symbol agrees with a pointwise right (left) inverse up to order `-m - 1`.
* `TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`: **an elliptic symbol has a
  two-sided parametrix symbol**.
* `TauCeti.Symbol.isAsymptoticSum_sharpTerm_left_iff`,
  `TauCeti.Symbol.isAsymptoticSum_sharpTerm_right_iff`: the left and the right parametrix symbols
  are exactly the symbols differing from a two-sided one by a smoothing symbol.
* `TauCeti.Symbol.exists_isUniformAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.exists_isUniformAsymptoticSum_sharpTerm_right`: for symbols whose estimates are
  uniform in the position, the same construction stays in the uniform class, with remainders
  `1 - ∑_{k < N} sharpTerm b a k` uniform in the position
  (`TauCeti.Symbol.IsUniformAsymptoticSum`).
* `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm_right`:
  **a uniformly elliptic uniform symbol has uniform left and right parametrix symbols**.
* `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm`: **a uniformly
  elliptic uniform symbol has a two-sided uniform parametrix symbol**.
* `TauCeti.Symbol.isUniformAsymptoticSum_sharpTerm_left_iff`,
  `TauCeti.Symbol.isUniformAsymptoticSum_sharpTerm_right_iff`: the uniform left and right
  parametrix symbols are exactly the uniform symbols differing from a two-sided one by a uniformly
  smoothing symbol.
* `TauCeti.Symbol.IsUniformlyEllipticAbove.exists_quantizeUniformCLM_comp_eq_id_add`: **the
  uniform parametrix as an operator.** For a uniformly elliptic uniform symbol `a` there is a
  uniform symbol `b` of order `-m` with `Op(b) ∘ Op(a) = 1 + Op(r)` and `Op(a) ∘ Op(b) = 1 + Op(r')`
  on Schwartz space, `r` and `r'` uniformly smoothing, with no compact spatial support assumed.
* `TauCeti.ClassicalSymbol.IsElliptic.exists_isAsymptoticSum_sharpTerm_left`: **an elliptic
  classical symbol has a left parametrix symbol**, with no radius of invertibility uniform in the
  position.
* `TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`: **the local parametrix modulo smoothing
  symbols.** For a smooth function `ψ` of the position, `q(x, ξ) = ψ(x) b(x, ξ)` with `b` a left
  parametrix symbol of `a`, and a symbol `p` with compact spatial support which agrees with `a`
  near the support of `ψ`, the composition symbol `q # p` is `ψ(x)` up to a smoothing symbol.
  `TauCeti.Symbol.isSmoothing_sharp_sub_of_isAsymptoticSum` is the same for a symbol `b` whose
  formal composition with `a` is a symbol `c` of order `0`: then `q # p` is `ψ(x) c(x, ξ)` up to a
  smoothing symbol.
* `TauCeti.Symbol.IsEllipticOn.exists_isAsymptoticSum_sharpTerm_left`,
  `TauCeti.Symbol.IsEllipticOn.exists_isAsymptoticSum_sharpTerm_right`: **microlocal left and
  right parametrix symbols** of a symbol elliptic on a set `S`, for a target symbol of order `0`
  vanishing outside `S`.

## Proof outline

Suppose `1 - ∑_{k < N} sharpTerm b a k` has order `-N`, which holds for `b = b₀` and `N = 0`. Then
`R = 1 - ∑_{k ≤ N} sharpTerm b a k` has order `-N` as well, and the correction `d = R b₀` of order
`-m - N` satisfies `d a = R` up to the term `R (b₀ a - 1)` of order `-N - 1`. Since the later
terms `sharpTerm d a k`, `k ≥ 1`, have order at most `-N - 1`, the symbol `b + d` inverts `a` up to
order `-N - 1`. Iterating gives corrections `d_N` of orders `-m - N`, and an asymptotic sum
`b ∼ b₀ + ∑_N d_N` inverts `a` up to every order, because changing `b` by a symbol of order
`-m - N` does not affect the first `N` terms modulo order `-N`. This is the construction of Taylor,
Lecture I, (4.1)–(4.6). A left and a right parametrix symbol differ by a smoothing symbol
(`TauCeti.Symbol.isSmoothing_sub_of_isAsymptoticSum_sharpTerm`), so each of them is two-sided. In
the uniform class they differ by a uniformly smoothing symbol
(`TauCeti.Symbol.isUniformlySmoothing_sub_of_isUniformAsymptoticSum_sharpTerm`).

If `a` and `b₀` are uniform and `b₀ a - 1` is uniform of order `-1`, every correction `d_N` and
every remainder is uniform, and the corrections have an asymptotic sum with uniform remainders
(`TauCeti.Symbol.exists_isUniform_forall_of_exists_add`); for a uniformly elliptic `a` the uniform
cut-off inverse provides `b₀`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.11), and §7 for microlocal parametrices.
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

/-- The correction step for left parametrix symbols with target `e`: if
`r = e - ∑_{k < N} sharpTerm b a k` has order `-N` and the correction `d` of order `-m - N`
satisfies `d a = (r - sharpTerm b a N) + t` pointwise, then the new remainder
`e - ∑_{k ≤ N} sharpTerm (b + d) a k` is `-t - ∑_{k < N} sharpTerm d a (k + 1)`, which has order
`-N - 1` when `t` has. -/
private theorem coefficient_sub_sum_sharpTerm_left_succ {μ : ℝ} {e : Symbol n V V μ}
    {a : Symbol n V W m} {N : ℕ} {b : Symbol n W V (-m)} {r : Symbol n V V (-m + m - N)}
    (hr : e.coefficient - ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    {d : Symbol n W V (-m - N)} {t : Symbol n V V (-m + m - (N + 1 : ℕ))}
    (hd : (d.comp a).coefficient = (r - b.sharpTerm a N).coefficient + t.coefficient) :
    e.coefficient -
      ∑ k ∈ range (N + 1), ((b + inclusion (by simp) d).sharpTerm a k).coefficient =
        (-t - ∑ k : Fin N,
          inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
            (d.sharpTerm a (k + 1))).coefficient := by
  -- The remainder `R = e - ∑_{k ≤ N} sharpTerm b a k`, of order `-N`.
  set R := r - b.sharpTerm a N with hR
  have hRc : R.coefficient = e.coefficient -
      ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient := by
    rw [hR, coefficient_sub, ← hr, sum_range_succ]
    abel
  have hd₀ : (d.sharpTerm a 0).coefficient = R.coefficient + t.coefficient := by
    rw [← hd]
    funext p
    simp
  rw [coefficient_sub, coefficient_neg, coefficient_sum]
  simp only [coefficient_inclusion]
  simp only [coefficient_sharpTerm_eq_add_left (a₀ := b + inclusion (by simp) d) (a₁ := b)
    (a₂ := d) (by rw [coefficient_add, coefficient_inclusion]), sum_add_distrib]
  rw [sum_range_succ' fun k ↦ (d.sharpTerm a k).coefficient, hd₀,
    Fin.sum_univ_eq_sum_range fun k ↦ (d.sharpTerm a (k + 1)).coefficient]
  rw [show ∑ k ∈ range (N + 1), (b.sharpTerm a k).coefficient =
    e.coefficient - R.coefficient by rw [hRc]; abel]
  abel

/-- The correction step for left parametrix symbols: if `r = 1 - ∑_{k < N} sharpTerm b a k` has
order `-N` and `t` is `(r - sharpTerm b a N) (b₀ a - 1)` at order `-N - 1`, then changing `b` by
the symbol `d = (r - sharpTerm b a N) b₀` of order `-m - N` makes the new remainder
`1 - ∑_{k ≤ N} sharpTerm (b + d) a k` equal to `-t - ∑_{k < N} sharpTerm d a (k + 1)`, which has
order `-N - 1`. -/
private theorem exists_coefficient_sub_sum_sharpTerm_left_succ {a : Symbol n V W m}
    {b₀ : Symbol n W V (-m)} {N : ℕ} {b : Symbol n W V (-m)} {r : Symbol n V V (-m + m - N)}
    (hr : (const (.id ℂ V) : Symbol n V V 0).coefficient -
      ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    {t : Symbol n V V (-m + m - (N + 1 : ℕ))}
    (ht : t.coefficient = ((r - b.sharpTerm a N).comp
      (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V)))).coefficient) :
    ∃ d : Symbol n W V (-m - N), d = inclusion (by linarith) ((r - b.sharpTerm a N).comp b₀) ∧
      (const (.id ℂ V) : Symbol n V V 0).coefficient -
        ∑ k ∈ range (N + 1), ((b + inclusion (by simp) d).sharpTerm a k).coefficient =
          (-t - ∑ k : Fin N,
            inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
              (d.sharpTerm a (k + 1))).coefficient := by
  -- `(R b₀) a = R + R (b₀ a - 1)` for `R = r - sharpTerm b a N`.
  refine ⟨_, rfl, coefficient_sub_sum_sharpTerm_left_succ hr ?_⟩
  rw [ht]
  funext p
  simp [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_assoc]

/-- **Left parametrix symbols.** If a symbol `b₀` of order `-m` is a pointwise left inverse of the
symbol `a` of order `m` modulo symbols of order `-1`, that is `b₀(x, ξ) a(x, ξ) - 1` is a symbol of
order `-1`, then `a` has a left parametrix symbol: a symbol `b` of order `-m` whose formal
composition with `a` is the identity, `1 ∼ ∑ₖ sharpTerm b a k`. -/
theorem exists_isAsymptoticSum_sharpTerm_left {a : Symbol n V W m} {b₀ : Symbol n W V (-m)}
    (hb₀a : ∃ s : Symbol n V V (-1),
      s.coefficient = (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).coefficient) :
    ∃ b : Symbol n W V (-m), IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n V V (-m + m - N),
      (const (.id ℂ V) : Symbol n V V 0).coefficient -
        ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    (b₀ := b₀) ⟨inclusion (by simp) (const (.id ℂ V)), by simp⟩
    (fun _ _ _ d ⟨_, hr⟩ h ↦ ⟨_, coefficient_sub_sum_sharpTerm_left_congr d hr h⟩)
    (fun N b ⟨r, hr⟩ ↦ by
      -- The term `(r - sharpTerm b a N) (b₀ a - 1)` has order `-N - 1`.
      obtain ⟨s, hs⟩ := hb₀a
      obtain ⟨d, -, hd⟩ := exists_coefficient_sub_sum_sharpTerm_left_succ (b₀ := b₀) hr
        (t := inclusion (by push_cast; linarith) ((r - b.sharpTerm a N).comp s))
        (funext fun p ↦ by simp only [coefficient_inclusion, coefficient_comp, hs])
      exact ⟨d, _, hd⟩)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **Uniform left parametrix symbols.** If a uniform symbol `b₀` of order `-m` is a pointwise left
inverse of the uniform symbol `a` of order `m` modulo a uniform symbol of order `-1`, then `a`
has a uniform left parametrix symbol `b`: `1 ∼ ∑ₖ sharpTerm b a k` with remainders of order `-N`
whose estimates are uniform in the position. -/
theorem exists_isUniformAsymptoticSum_sharpTerm_left {a : Symbol n V W m} (ha : a.IsUniform)
    {b₀ : Symbol n W V (-m)} (hb₀ : b₀.IsUniform)
    (hb₀a : ∃ s : Symbol n V V (-1), s.IsUniform ∧
      s.coefficient = (b₀.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).coefficient) :
    ∃ b : Symbol n W V (-m), b.IsUniform ∧ IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a) := by
  obtain ⟨b, hbu, hb⟩ := exists_isUniform_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n V V (-m + m - N), r.IsUniform ∧
      (const (.id ℂ V) : Symbol n V V 0).coefficient -
        ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    hb₀ ⟨inclusion (by simp) (const (.id ℂ V)), (isUniform_const _).inclusion _, by simp⟩
    (fun _ _ _ d _ hd ⟨_, hru, hr⟩ h ↦ by
      refine ⟨_, ?_, coefficient_sub_sum_sharpTerm_left_congr d hr h⟩
      exact hru.sub (IsUniform.sum fun k _ ↦ (hd.sharpTerm ha k).inclusion _))
    (fun N b hbu ⟨r, hru, hr⟩ ↦ by
      have hR := hru.sub (hbu.sharpTerm ha N)
      -- The term `(r - sharpTerm b a N) (b₀ a - 1)` is uniform of order `-N - 1`.
      obtain ⟨s, hsu, hs⟩ := hb₀a
      obtain ⟨d, rfl, hd⟩ := exists_coefficient_sub_sum_sharpTerm_left_succ (b₀ := b₀) hr
        (t := inclusion (by push_cast; linarith) ((r - b.sharpTerm a N).comp s))
        (funext fun p ↦ by simp only [coefficient_inclusion, coefficient_comp, hs])
      refine ⟨_, (hR.comp hb₀).inclusion _, _, ?_, hd⟩
      exact ((hR.comp hsu).inclusion _).neg.sub (IsUniform.sum
        fun k _ ↦ (((hR.comp hb₀).inclusion _).sharpTerm ha (k + 1)).inclusion _))
  exact ⟨b, hbu, isUniformAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **A uniformly elliptic symbol has a uniform left parametrix symbol.** A symbol `a` of order `m`
with estimates uniform in the position that is uniformly elliptic above some radius has a uniform
left parametrix symbol `b` of order `-m`: `1 ∼ ∑ₖ sharpTerm b a k` with remainders whose estimates
are uniform in the position. -/
theorem IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm_left [CompleteSpace V]
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) :
    ∃ b : Symbol n W V (-m), b.IsUniform ∧
      IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
        (b.sharpTerm a) := by
  obtain ⟨b₀, hb₀, R', hb₀R⟩ := (exists_isUniformlyEllipticAbove_iff hau).1 ⟨R, ha⟩
  refine Symbol.exists_isUniformAsymptoticSum_sharpTerm_left hau hb₀ ?_
  exact isUniformlySmoothing_iff.1 (IsUniform.isUniformlySmoothing_of_coefficient_eq_zero
    ((hb₀.comp hau).sub ((isUniform_const _).inclusion _)) R'
    fun x ξ hξ ↦ by simp [(hb₀R x ξ hξ).1]) (-1)

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

/-- The correction step for right parametrix symbols with target `e`: if
`r = e - ∑_{k < N} sharpTerm a b k` has order `-N` and the correction `d` of order `-m - N`
satisfies `a d = (r - sharpTerm a b N) + t` pointwise, then the new remainder
`e - ∑_{k ≤ N} sharpTerm a (b + d) k` is `-t - ∑_{k < N} sharpTerm a d (k + 1)`, which has order
`-N - 1` when `t` has. -/
private theorem coefficient_sub_sum_sharpTerm_right_succ {μ : ℝ} {e : Symbol n W W μ}
    {a : Symbol n V W m} {N : ℕ} {b : Symbol n W V (-m)} {r : Symbol n W W (m + -m - N)}
    (hr : e.coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    {d : Symbol n W V (-m - N)} {t : Symbol n W W (m + -m - (N + 1 : ℕ))}
    (hd : (a.comp d).coefficient = (r - a.sharpTerm b N).coefficient + t.coefficient) :
    e.coefficient -
      ∑ k ∈ range (N + 1), (a.sharpTerm (b + inclusion (by simp) d) k).coefficient =
        (-t - ∑ k : Fin N,
          inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
            (a.sharpTerm d (k + 1))).coefficient := by
  -- The remainder `R = e - ∑_{k ≤ N} sharpTerm a b k`, of order `-N`.
  set R := r - a.sharpTerm b N with hR
  have hRc : R.coefficient = e.coefficient -
      ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient := by
    rw [hR, coefficient_sub, ← hr, sum_range_succ]
    abel
  have hd₀ : (a.sharpTerm d 0).coefficient = R.coefficient + t.coefficient := by
    rw [← hd]
    funext p
    simp
  rw [coefficient_sub, coefficient_neg, coefficient_sum]
  simp only [coefficient_inclusion]
  simp only [coefficient_sharpTerm_eq_add_right (b₀ := b + inclusion (by simp) d) (b₁ := b)
    (b₂ := d) (by rw [coefficient_add, coefficient_inclusion]), sum_add_distrib]
  rw [sum_range_succ' fun k ↦ (a.sharpTerm d k).coefficient, hd₀,
    Fin.sum_univ_eq_sum_range fun k ↦ (a.sharpTerm d (k + 1)).coefficient]
  rw [show ∑ k ∈ range (N + 1), (a.sharpTerm b k).coefficient =
    e.coefficient - R.coefficient by rw [hRc]; abel]
  abel

/-- The correction step for right parametrix symbols: if `r = 1 - ∑_{k < N} sharpTerm a b k` has
order `-N` and `t` is `(a b₀ - 1) (r - sharpTerm a b N)` at order `-N - 1`, then changing `b` by
the symbol `d = b₀ (r - sharpTerm a b N)` of order `-m - N` makes the new remainder
`1 - ∑_{k ≤ N} sharpTerm a (b + d) k` equal to `-t - ∑_{k < N} sharpTerm a d (k + 1)`, which has
order `-N - 1`. -/
private theorem exists_coefficient_sub_sum_sharpTerm_right_succ {a : Symbol n V W m}
    {b₀ : Symbol n W V (-m)} {N : ℕ} {b : Symbol n W V (-m)} {r : Symbol n W W (m + -m - N)}
    (hr : (const (.id ℂ W) : Symbol n W W 0).coefficient -
      ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    {t : Symbol n W W (m + -m - (N + 1 : ℕ))}
    (ht : t.coefficient = ((a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).comp
      (r - a.sharpTerm b N)).coefficient) :
    ∃ d : Symbol n W V (-m - N), d = inclusion (by linarith) (b₀.comp (r - a.sharpTerm b N)) ∧
      (const (.id ℂ W) : Symbol n W W 0).coefficient -
        ∑ k ∈ range (N + 1), (a.sharpTerm (b + inclusion (by simp) d) k).coefficient =
          (-t - ∑ k : Fin N,
            inclusion (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))])
              (a.sharpTerm d (k + 1))).coefficient := by
  -- `a (b₀ R) = R + (a b₀ - 1) R` for `R = r - sharpTerm a b N`.
  refine ⟨_, rfl, coefficient_sub_sum_sharpTerm_right_succ hr ?_⟩
  rw [ht]
  funext p
  simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
  abel

/-- **Right parametrix symbols.** If a symbol `b₀` of order `-m` is a pointwise right inverse of
the symbol `a` of order `m` modulo symbols of order `-1`, that is `a(x, ξ) b₀(x, ξ) - 1` is a symbol
of order `-1`, then `a` has a right parametrix symbol: a symbol `b` of order `-m` such that the
formal composition of `a` with `b` is the identity, `1 ∼ ∑ₖ sharpTerm a b k`. -/
theorem exists_isAsymptoticSum_sharpTerm_right {a : Symbol n V W m} {b₀ : Symbol n W V (-m)}
    (hab₀ : ∃ s : Symbol n W W (-1),
      s.coefficient = (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).coefficient) :
    ∃ b : Symbol n W V (-m), IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k)
      (inclusion (by simp) (const (.id ℂ W))) (a.sharpTerm b) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n W W (m + -m - N),
      (const (.id ℂ W) : Symbol n W W 0).coefficient -
        ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    (b₀ := b₀) ⟨inclusion (by simp) (const (.id ℂ W)), by simp⟩
    (fun _ _ _ d ⟨_, hr⟩ h ↦ ⟨_, coefficient_sub_sum_sharpTerm_right_congr d hr h⟩)
    (fun N b ⟨r, hr⟩ ↦ by
      -- The term `(a b₀ - 1) (r - sharpTerm a b N)` has order `-N - 1`.
      obtain ⟨s, hs⟩ := hab₀
      obtain ⟨d, -, hd⟩ := exists_coefficient_sub_sum_sharpTerm_right_succ (b₀ := b₀) hr
        (t := inclusion (by push_cast; linarith) (s.comp (r - a.sharpTerm b N)))
        (funext fun p ↦ by simp only [coefficient_inclusion, coefficient_comp, hs])
      exact ⟨d, _, hd⟩)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **Uniform right parametrix symbols.** If a uniform symbol `b₀` of order `-m` is a pointwise
right inverse of the uniform symbol `a` of order `m` modulo a uniform symbol of order `-1`, then
`a` has a uniform right parametrix symbol `b`: `1 ∼ ∑ₖ sharpTerm a b k` with remainders of order
`-N` whose estimates are uniform in the position. -/
theorem exists_isUniformAsymptoticSum_sharpTerm_right {a : Symbol n V W m} (ha : a.IsUniform)
    {b₀ : Symbol n W V (-m)} (hb₀ : b₀.IsUniform)
    (hab₀ : ∃ s : Symbol n W W (-1), s.IsUniform ∧
      s.coefficient = (a.comp b₀ - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).coefficient) :
    ∃ b : Symbol n W V (-m), b.IsUniform ∧ IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k)
      (inclusion (by simp) (const (.id ℂ W))) (a.sharpTerm b) := by
  obtain ⟨b, hbu, hb⟩ := exists_isUniform_forall_of_exists_add
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n W W (m + -m - N), r.IsUniform ∧
      (const (.id ℂ W) : Symbol n W W 0).coefficient -
        ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    hb₀ ⟨inclusion (by simp) (const (.id ℂ W)), (isUniform_const _).inclusion _, by simp⟩
    (fun _ _ _ d _ hd ⟨_, hru, hr⟩ h ↦ by
      refine ⟨_, ?_, coefficient_sub_sum_sharpTerm_right_congr d hr h⟩
      exact hru.sub (IsUniform.sum fun k _ ↦ (ha.sharpTerm hd k).inclusion _))
    (fun N b hbu ⟨r, hru, hr⟩ ↦ by
      have hR := hru.sub (ha.sharpTerm hbu N)
      -- The term `(a b₀ - 1) (r - sharpTerm a b N)` is uniform of order `-N - 1`.
      obtain ⟨s, hsu, hs⟩ := hab₀
      obtain ⟨d, rfl, hd⟩ := exists_coefficient_sub_sum_sharpTerm_right_succ (b₀ := b₀) hr
        (t := inclusion (by push_cast; linarith) (s.comp (r - a.sharpTerm b N)))
        (funext fun p ↦ by simp only [coefficient_inclusion, coefficient_comp, hs])
      refine ⟨_, (hb₀.comp hR).inclusion _, _, ?_, hd⟩
      exact ((hsu.comp hR).inclusion _).neg.sub (IsUniform.sum
        fun k _ ↦ (ha.sharpTerm ((hb₀.comp hR).inclusion _) (k + 1)).inclusion _))
  exact ⟨b, hbu, isUniformAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **A uniformly elliptic symbol has a uniform right parametrix symbol.** A symbol `a` of order
`m` with estimates uniform in the position that is uniformly elliptic above some radius has a
uniform right parametrix symbol `b` of order `-m`: `1 ∼ ∑ₖ sharpTerm a b k` with remainders whose
estimates are uniform in the position. -/
theorem IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm_right [CompleteSpace V]
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) :
    ∃ b : Symbol n W V (-m), b.IsUniform ∧
      IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
        (a.sharpTerm b) := by
  obtain ⟨b₀, hb₀, R', hb₀R⟩ := (exists_isUniformlyEllipticAbove_iff hau).1 ⟨R, ha⟩
  refine Symbol.exists_isUniformAsymptoticSum_sharpTerm_right hau hb₀ ?_
  exact isUniformlySmoothing_iff.1 (IsUniform.isUniformlySmoothing_of_coefficient_eq_zero
    ((hau.comp hb₀).sub ((isUniform_const _).inclusion _)) R'
    fun x ξ hξ ↦ by simp [(hb₀R x ξ hξ).2]) (-1)

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
  obtain ⟨bL, hbL⟩ := exists_isAsymptoticSum_sharpTerm_left (isSmoothing_iff.1 hL (-1))
  obtain ⟨bR, hbR⟩ := exists_isAsymptoticSum_sharpTerm_right (isSmoothing_iff.1 hR (-1))
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

/-- **A uniformly elliptic uniform symbol has a two-sided uniform parametrix symbol.** A symbol `a`
of order `m` whose estimates are uniform in the position and which is uniformly elliptic above some
radius has a uniform parametrix symbol `b` of order `-m`: the formal compositions of `b` with `a`
in both orders are the identity with uniform remainders, so `1 - ∑_{k < N} sharpTerm b a k` and
`1 - ∑_{k < N} sharpTerm a b k` are uniform symbols of order `-N` for every `N`. It is unique
modulo uniformly smoothing symbols (`TauCeti.Symbol.isUniformAsymptoticSum_sharpTerm_left_iff`). -/
theorem IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm [CompleteSpace V]
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) :
    ∃ b : Symbol n W V (-m), b.IsUniform ∧
      IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
        (b.sharpTerm a) ∧
      IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
        (a.sharpTerm b) := by
  obtain ⟨bL, hbLu, hbL⟩ := ha.exists_isUniformAsymptoticSum_sharpTerm_left hau
  obtain ⟨bR, hbRu, hbR⟩ := ha.exists_isUniformAsymptoticSum_sharpTerm_right hau
  exact ⟨bL, hbLu, hbL, isUniformAsymptoticSum_sharpTerm_of_isUniformlySmoothing_sub_right hau hbR
    (isUniformlySmoothing_sub_of_isUniformAsymptoticSum_sharpTerm hbLu hbRu hbL hbR)⟩

/-- **Uniqueness of uniform left parametrix symbols.** If the uniform symbol `b` is a two-sided
uniform parametrix symbol of the uniform symbol `a`, then the uniform left parametrix symbols of
`a` are exactly the uniform symbols `b'` with `b' - b` uniformly smoothing. -/
theorem isUniformAsymptoticSum_sharpTerm_left_iff {a : Symbol n V W m} (ha : a.IsUniform)
    {b b' : Symbol n W V (-m)} (hb : b.IsUniform) (hb' : b'.IsUniform)
    (hL : IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hR : IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k)
      (inclusion (by simp) (const (.id ℂ W))) (a.sharpTerm b)) :
    IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b'.sharpTerm a) ↔ (b' - b).IsUniformlySmoothing :=
  ⟨fun h ↦ isUniformlySmoothing_sub_of_isUniformAsymptoticSum_sharpTerm hb' hb h hR,
    isUniformAsymptoticSum_sharpTerm_of_isUniformlySmoothing_sub_left ha hL⟩

/-- **Uniqueness of uniform right parametrix symbols.** If the uniform symbol `b` is a two-sided
uniform parametrix symbol of the uniform symbol `a`, then the uniform right parametrix symbols of
`a` are exactly the uniform symbols `b'` with `b' - b` uniformly smoothing. -/
theorem isUniformAsymptoticSum_sharpTerm_right_iff {a : Symbol n V W m} (ha : a.IsUniform)
    {b b' : Symbol n W V (-m)} (hb : b.IsUniform) (hb' : b'.IsUniform)
    (hL : IsUniformAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (hR : IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k)
      (inclusion (by simp) (const (.id ℂ W))) (a.sharpTerm b)) :
    IsUniformAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
      (a.sharpTerm b') ↔ (b' - b).IsUniformlySmoothing := by
  refine ⟨fun h ↦ ?_, isUniformAsymptoticSum_sharpTerm_of_isUniformlySmoothing_sub_right ha hR⟩
  simpa using (isUniformlySmoothing_sub_of_isUniformAsymptoticSum_sharpTerm hb hb' hL h).neg

/-! ### The local parametrix modulo smoothing symbols -/

section Parametrix

variable [CompleteSpace V] [CompleteSpace W]

/-- **The local parametrix modulo smoothing symbols, for a target symbol.** Let `b` be a symbol of
order `-m` whose formal composition with the symbol `a` of order `m` is a symbol `c` of order `0`,
`c ∼ ∑ₖ sharpTerm b a k`. Let `ψ` be a smooth function of the position, `q(x, ξ) = ψ(x) b(x, ξ)`,
`e(x, ξ) = ψ(x) c(x, ξ)`, and `p` a symbol with compact spatial support which agrees with `a` at
all positions near the support of `ψ`. Then the composition symbol `q # p` is `e` up to a
smoothing symbol. -/
theorem isSmoothing_sharp_sub_of_isAsymptoticSum {a : Symbol n V W m} {b : Symbol n W V (-m)}
    {c : Symbol n V V 0}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) c) (b.sharpTerm a))
    {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ) {q : Symbol n W V (-m)}
    (hq : ∀ x ξ, q.coefficient (x, ξ) = ψ x • b.coefficient (x, ξ)) {p : Symbol n V W m}
    (hp : p.HasCompactSpatialSupport)
    (hpa : ∀ᶠ x in 𝓝ˢ (tsupport ψ), ∀ ξ, p.coefficient (x, ξ) = a.coefficient (x, ξ))
    {e : Symbol n V V 0} (he : ∀ x ξ, e.coefficient (x, ξ) = ψ x • c.coefficient (x, ξ)) :
    (q.sharp p hp - inclusion (neg_add_cancel m).ge e).IsSmoothing := by
  refine isSmoothing_iff.2 fun μ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (-μ)
  obtain ⟨r, hr⟩ := isAsymptoticSum_iff.1 hab N
  -- `q # p - e = (q # p - ∑_{k < N} sharpTerm q p k) - ψ (c - ∑_{k < N} sharpTerm b a k)`.
  refine ⟨inclusion (m := -m + m - N) (by linarith) (q.sharpRemainder p hp N) -
    inclusion (m := 0 + (-m + m - N)) (by linarith)
      ((ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ.smul contDiff_const)).comp r),
    ?_⟩
  funext ⟨x, ξ⟩
  have hr' := congrFun hr (x, ξ)
  simp only [Pi.sub_apply, Finset.sum_apply, coefficient_inclusion] at hr'
  simp only [coefficient_sub, coefficient_inclusion, coefficient_sharpRemainder, coefficient_comp,
    coefficient_ofSpatial, Pi.sub_apply, Finset.sum_apply, he,
    coefficient_sharpTerm_of_eq_smul_of_eventuallyEq hq hpa, ← hr',
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp, smul_sub, Finset.smul_sum]
  abel

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
        (hψ.smul contDiff_const))).IsSmoothing :=
  isSmoothing_sharp_sub_of_isAsymptoticSum hab hψ hq hp hpa fun x ξ ↦ by simp

end Parametrix

/-! ### The uniform parametrix as an operator -/

section UniformOperator

variable [CompleteSpace V] [CompleteSpace W]

/-- If the terms `sharpTerm p q k` of a composition of uniform symbols are a uniform asymptotic sum
for `1`, then `Op(p) ∘ Op(q)` is the identity plus the quantization of a uniformly smoothing
symbol. -/
private theorem exists_quantizeUniformCLM_comp_eq_id_add_of_isUniformAsymptoticSum {μ μ' : ℝ}
    (hμ : μ' + μ = 0)
    {p : Symbol n W V μ'} (hp : p.IsUniform) {q : Symbol n V W μ} (hq : q.IsUniform)
    (hpq : IsUniformAsymptoticSum (m := fun k : ℕ ↦ μ' + μ - k)
      (inclusion (by simp [hμ]) (const (.id ℂ V))) (p.sharpTerm q)) :
    ∃ (r : Symbol n V V 0) (hr : r.IsUniformlySmoothing),
      quantizeUniformCLM p hp ∘L quantizeUniformCLM q hq =
        ContinuousLinearMap.id ℂ _ + quantizeUniformCLM r hr.isUniform := by
  obtain ⟨c, hc, hcomp⟩ := hp.exists_quantizeUniformCLM_comp hq
  have hm' : Tendsto (fun k : ℕ ↦ μ' + μ - k) atTop atBot :=
    tendsto_atBot_add_const_left atTop _ <|
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  -- The symbol `c` of the composition and `1` are both asymptotic sums of the same terms.
  have hs := (hpq.isUniformAsymptoticSum_iff_isUniformlySmoothing_sub hm').1
    (hp.isUniformAsymptoticSum_sharpTerm_of_comp_eq hq hc hcomp)
  obtain ⟨r, hr, hrc⟩ := isUniformlySmoothing_iff.1 hs 0
  refine ⟨r, isUniformlySmoothing_iff.2 fun m'' ↦ (isUniformlySmoothing_iff.1 hs m'').imp
    fun _ h ↦ ⟨h.1, h.2.trans hrc.symm⟩, ?_⟩
  have hcr : c.coefficient = (const (.id ℂ V) + r).coefficient := by
    rw [coefficient_add, hrc, coefficient_sub, coefficient_inclusion, coefficient_inclusion]
    abel
  rw [hcomp, quantizeUniformCLM_congr hc ((isUniform_const _).add hr) hcr,
    quantizeUniformCLM_add (isUniform_const _) hr, quantizeUniformCLM_const]
  ext u x
  simp

/-- **The uniform parametrix as an operator.** Let `a` be a symbol of order `m` whose estimates hold
uniformly in the position and which is uniformly elliptic above some radius. Then there is a symbol
`b` of order `-m` whose estimates hold uniformly in the position with

`Op(b) ∘ Op(a) = 1 + Op(r)` and `Op(a) ∘ Op(b) = 1 + Op(r')`

on Schwartz space, for uniformly smoothing symbols `r` and `r'`. No compact spatial support is
assumed: the composition is that of the uniform calculus
(`TauCeti.Symbol.IsUniform.exists_quantizeUniformCLM_comp`), whose symbol has the expansion
`TauCeti.Symbol.IsUniform.isUniformAsymptoticSum_sharpTerm_of_comp_eq`, and `b` is the two-sided
uniform parametrix symbol
`TauCeti.Symbol.IsUniformlyEllipticAbove.exists_isUniformAsymptoticSum_sharpTerm`. -/
theorem IsUniformlyEllipticAbove.exists_quantizeUniformCLM_comp_eq_id_add {a : Symbol n V W m}
    {R : ℝ} (ha : a.IsUniformlyEllipticAbove R) (hau : a.IsUniform) :
    ∃ (b : Symbol n W V (-m)) (hb : b.IsUniform),
      (∃ (r : Symbol n V V 0) (hr : r.IsUniformlySmoothing),
        quantizeUniformCLM b hb ∘L quantizeUniformCLM a hau =
          ContinuousLinearMap.id ℂ _ + quantizeUniformCLM r hr.isUniform) ∧
      ∃ (r : Symbol n W W 0) (hr : r.IsUniformlySmoothing),
        quantizeUniformCLM a hau ∘L quantizeUniformCLM b hb =
          ContinuousLinearMap.id ℂ _ + quantizeUniformCLM r hr.isUniform := by
  obtain ⟨b, hb, hL, hR⟩ := ha.exists_isUniformAsymptoticSum_sharpTerm hau
  exact ⟨b, hb,
    exists_quantizeUniformCLM_comp_eq_id_add_of_isUniformAsymptoticSum (neg_add_cancel m) hb hau hL,
    exists_quantizeUniformCLM_comp_eq_id_add_of_isUniformAsymptoticSum (add_neg_cancel m) hau hb
      hR⟩

end UniformOperator

/-! ### Microlocal parametrix symbols

A symbol `a` that is only elliptic on a set `S` of points `(x, ξ)`, typically a conic set of large
frequencies over a compact set of positions, still has parametrix symbols there: for every symbol
`c` of order `0` vanishing outside `S`, the formal composition can be made equal to `c`. When `c` is
a conic cutoff equal to `1` near a covector `(x₀, ξ₀)`, this inverts `Op(a)` microlocally near
`(x₀, ξ₀)` modulo smoothing operators, which is how a microlocal parametrix detects elliptic
regular covectors.

The construction is the one for elliptic symbols, with the pointwise inverse of `a` used only on the
closure of `S`, where `a` is still elliptic (`TauCeti.Symbol.IsEllipticOn.closure`). Every
successive approximation `b` vanishes outside the closure, hence so do the terms `sharpTerm b a k`
and the remainder `R = c - ∑_{k ≤ N} sharpTerm b a k`, and the correction `d = R a⁻¹`
(`TauCeti.Symbol.compInverse`) is a symbol with `d a = R` exactly. The asymptotic sum of the
corrections need not vanish outside `S`, but the remainders only depend on it modulo symbols of the
order of the remainder. -/

section Microlocal

variable [CompleteSpace V] {S : Set (CoordinateSpace n × CoordinateSpace n)}

/-- **Microlocal left parametrix symbols.** Let the symbol `a` of order `m` be elliptic on a set
`S` of points `(x, ξ)`, and let `c` be a symbol of order `0` vanishing outside `S`. Then there
is a symbol `b` of order `-m` whose formal composition with `a` is `c`:
`c ∼ ∑ₖ sharpTerm b a k`. -/
theorem IsEllipticOn.exists_isAsymptoticSum_sharpTerm_left {a : Symbol n V W m}
    (ha : a.IsEllipticOn S) {c : Symbol n V V 0} (hc : ∀ p ∉ S, c.coefficient p = 0) :
    ∃ b : Symbol n W V (-m),
      IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) c) (b.sharpTerm a) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add_of_imp
    (fun N (b : Symbol n W V (-m)) ↦ (∃ r : Symbol n V V (-m + m - N),
      c.coefficient - ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient) ∧
        ∀ p ∉ _root_.closure S, b.coefficient p = 0)
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n V V (-m + m - N),
      c.coefficient - ∑ k ∈ range N, (b.sharpTerm a k).coefficient = r.coefficient)
    (b₀ := 0) ⟨⟨inclusion (by simp) c, by simp⟩, fun _ _ ↦ rfl⟩ (fun _ _ h ↦ h.1)
    (fun _ _ _ d ⟨_, hr⟩ h ↦ ⟨_, coefficient_sub_sum_sharpTerm_left_congr d hr h⟩)
    (fun N b ⟨⟨r, hr⟩, hb⟩ ↦ by
      -- The remainder `R = c - ∑_{k ≤ N} sharpTerm b a k` vanishes outside `S`, as `b` does.
      have hbS (k : ℕ) (p) (hp : p ∉ _root_.closure S) : (b.sharpTerm a k).coefficient p = 0 :=
        coefficient_sharpTerm_eq_zero_of_eventuallyEq_zero_left
          (eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hp) fun q hq ↦ hb q hq) a k
      have hR (p) (hp : p ∉ _root_.closure S) : (r - b.sharpTerm a N).coefficient p = 0 := by
        rw [coefficient_sub, Pi.sub_apply, ← hr]
        simp [hc p fun h ↦ hp (subset_closure h), hbS _ p hp]
      -- The correction `d = R a⁻¹` satisfies `d a = R` exactly.
      let d : Symbol n W V (-m - N) :=
        inclusion (by linarith) ((r - b.sharpTerm a N).compInverse a hR ha.closure)
      have hd : (d.comp a).coefficient =
          (r - b.sharpTerm a N).coefficient + (0 : Symbol n V V (-m + m - (N + 1 : ℕ))).coefficient
          := by
        funext p
        simp only [d, coefficient_comp, coefficient_inclusion,
          coefficient_compInverse_comp_coefficient, coefficient_zero, add_zero]
      refine ⟨d, ⟨_, coefficient_sub_sum_sharpTerm_left_succ hr hd⟩, fun p hp ↦ ?_⟩
      simp only [d, coefficient_add, coefficient_inclusion, Pi.add_apply, hb p hp, zero_add]
      exact coefficient_compInverse_of_notMem _ _ _ _ hp)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

/-- **Microlocal right parametrix symbols.** Let the symbol `a` of order `m` be elliptic on a set
`S` of points `(x, ξ)`, and let `c` be a symbol of order `0` vanishing outside `S`. Then there
is a symbol `b` of order `-m` such that the formal composition of `a` with `b` is `c`:
`c ∼ ∑ₖ sharpTerm a b k`. -/
theorem IsEllipticOn.exists_isAsymptoticSum_sharpTerm_right {a : Symbol n V W m}
    (ha : a.IsEllipticOn S) {c : Symbol n W W 0}
    (hc : ∀ p ∉ S, c.coefficient p = 0) :
    ∃ b : Symbol n W V (-m),
      IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) c) (a.sharpTerm b) := by
  obtain ⟨b, hb⟩ := exists_forall_of_exists_add_of_imp
    (fun N (b : Symbol n W V (-m)) ↦ (∃ r : Symbol n W W (m + -m - N),
      c.coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient) ∧
        ∀ p ∉ _root_.closure S, b.coefficient p = 0)
    (fun N (b : Symbol n W V (-m)) ↦ ∃ r : Symbol n W W (m + -m - N),
      c.coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient = r.coefficient)
    (b₀ := 0) ⟨⟨inclusion (by simp) c, by simp⟩, fun _ _ ↦ rfl⟩ (fun _ _ h ↦ h.1)
    (fun _ _ _ d ⟨_, hr⟩ h ↦ ⟨_, coefficient_sub_sum_sharpTerm_right_congr d hr h⟩)
    (fun N b ⟨⟨r, hr⟩, hb⟩ ↦ by
      -- The remainder `R = c - ∑_{k ≤ N} sharpTerm a b k` vanishes outside `S`, as `b` does.
      have hbS (k : ℕ) (p) (hp : p ∉ _root_.closure S) : (a.sharpTerm b k).coefficient p = 0 :=
        coefficient_sharpTerm_eq_zero_of_eventuallyEq_zero_right
          (eventuallyEq_of_mem (isClosed_closure.isOpen_compl.mem_nhds hp) fun q hq ↦ hb q hq) a k
      have hR (p) (hp : p ∉ _root_.closure S) : (r - a.sharpTerm b N).coefficient p = 0 := by
        rw [coefficient_sub, Pi.sub_apply, ← hr]
        simp [hc p fun h ↦ hp (subset_closure h), hbS _ p hp]
      -- The correction `d = a⁻¹ R` satisfies `a d = R` exactly.
      let d : Symbol n W V (-m - N) :=
        inclusion (by linarith) (a.inverseComp (r - a.sharpTerm b N) hR ha.closure)
      have hd : (a.comp d).coefficient =
          (r - a.sharpTerm b N).coefficient + (0 : Symbol n W W (m + -m - (N + 1 : ℕ))).coefficient
          := by
        funext p
        simp only [d, coefficient_comp, coefficient_inclusion,
          coefficient_comp_coefficient_inverseComp, coefficient_zero, add_zero]
      refine ⟨d, ⟨_, coefficient_sub_sum_sharpTerm_right_succ hr hd⟩, fun p hp ↦ ?_⟩
      simp only [d, coefficient_add, coefficient_inclusion, Pi.add_apply, hb p hp, zero_add]
      exact coefficient_inverseComp_of_notMem _ _ _ _ hp)
  exact ⟨b, isAsymptoticSum_iff.2 fun N ↦ by simpa using hb N⟩

end Microlocal

end Symbol

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- **An elliptic classical symbol has a left parametrix symbol.** If the principal symbol of a
classical symbol `a` of order `m` is invertible at every nonzero frequency, its full symbol has a
left parametrix symbol `b` of order `-m`, `1 ∼ ∑ₖ sharpTerm b a k`. Unlike
`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`, this asks for no radius beyond
which `a(x, ξ)` is invertible at all positions; such a radius need not exist when the base is
noncompact. -/
theorem IsElliptic.exists_isAsymptoticSum_sharpTerm_left {a : ClassicalSymbol n V W m}
    (ha : a.IsElliptic) :
    ∃ b : Symbol n W V (-m), Symbol.IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (Symbol.inclusion (by simp) (Symbol.const (.id ℂ V))) (b.sharpTerm a.toSymbol) := by
  have ha' := isElliptic_def.1 ha
  set χ : FrequencyCutoff (CoordinateSpace n) := default
  -- The cut-off inverse `χ(ξ) a_m(x, ξ)⁻¹` of the principal symbol is a left inverse of `a` up to
  -- the symbol `χ a_m⁻¹ r` of order `-1`, with `r = a - χ a_m`, and the symbol
  -- `χ² - 1`, which vanishes at large frequencies.
  set b₀ := cutoffSymbol χ (a.principal.inverse ha')
  refine Symbol.exists_isAsymptoticSum_sharpTerm_left (b₀ := b₀) ?_
  obtain ⟨t, ht⟩ := Symbol.isSmoothing_iff.1 (Symbol.isSmoothing_of_coefficient_eq_zero (a :=
    b₀.comp (cutoffSymbol χ a.principal) - Symbol.inclusion (by simp) (Symbol.const (.id ℂ V))) 2
    fun x ξ hξ ↦ by
      have h := (HomogeneousSymbol.isElliptic_iff.1 ha' x ξ
        (norm_pos_iff.1 (by linarith))).inverse_comp_self
      simp only [coefficient_principal] at h
      simp [b₀, coefficient_cutoffSymbol, χ.apply_eq_one_of_two_le_norm hξ, h]) (-1)
  refine ⟨t + Symbol.inclusion (by simp) (b₀.comp (a.remainder χ 1)), funext fun p ↦ ?_⟩
  simp [ht, b₀, coefficient_principal]

end ClassicalSymbol

end TauCeti
