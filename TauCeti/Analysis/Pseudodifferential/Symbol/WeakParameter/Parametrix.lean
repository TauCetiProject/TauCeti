/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.FormalComposition
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Resolvent
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.AsymptoticSum
import TauCeti.Algebra.BigOperators.NatAntidiagonal

/-!
# The parametrix of `1 - r p` in the weakly parametric calculus

Let `p` be a symbol of order `d` with values in the endomorphisms of a Banach space `V`, the
symbol of an operator `A` whose resolvent `(A - λ)⁻¹` is to be approximated, and suppose that `p`
is parameter-elliptic on an open set `R` of reciprocal spectral parameters `r = 1 / λ`
(`TauCeti.Symbol.IsParameterElliptic`). In the weakly parametric calculus of Grubb and Seeley, the
normalized resolvent `-λ (A - λ)⁻¹ = (1 - r A)⁻¹` is approximated by pseudodifferential operators
whose symbols are weakly parameter-dependent (`TauCeti.WeakParameterSymbol`). This file constructs
the terms of the formal parametrix of the family of symbols `1 - r p(x, ξ)`: weakly
parameter-dependent symbols `qⱼ` of frequency order `-j` and anisotropy `d`, the first of which is
the normalized resolvent `q₀ = (1 - r p)⁻¹` (`TauCeti.WeakParameterSymbol.normalizedResolvent`),
which solve the formal composition equations

`∑_{j + k = N} sharpTerm qⱼ (1 - r p) k = δ_{N,0}`

at every parameter `r ∈ R`, and symmetrically on the right.

The symbol `1 - r p` is not itself weakly parameter-dependent: it grows like `‖r‖` as `r` tends to
infinity. But the constant `1` has no derivatives, so for `k ≥ 1` the term of the composition
expansion of `qⱼ` with `1 - r p` is `-r sharpTerm qⱼ p k`. The recursion therefore reads

`q_{N+1} (1 - r p) = r ∑_{j ≤ N} sharpTerm qⱼ p (N + 1 - j)`,

and it is solved by composing on the right with the resolvent `r (1 - r p)⁻¹ = (λ - p)⁻¹`
(`TauCeti.WeakParameterSymbol.resolvent`), a weakly parameter-dependent symbol of frequency order
`-d`, which absorbs the factor `r`. Each correction term `sharpTerm qⱼ p (N + 1 - j)` has frequency
order `-j + d - (N + 1 - j) = d - (N + 1)`, so `q_{N+1}` has frequency order `-(N + 1)`, uniformly
in the parameter.

## Main definitions and results

* `TauCeti.WeakParameterSymbol.leftNormalizedResolventTerms p hp`: the terms `q₀, q₁, …` of the
  formal left parametrix of `1 - r p`, with `q₀ = (1 - r p)⁻¹` and
  `q_{N+1} = (∑_{j ≤ N} sharpTerm qⱼ p (N + 1 - j)) ∘ r (1 - r p)⁻¹`
  (`TauCeti.WeakParameterSymbol.coefficient_leftNormalizedResolventTerms_succ`).
* `TauCeti.WeakParameterSymbol.sum_coefficient_sharpTerm_leftNormalizedResolventTerms`: they solve
  the formal composition equations `∑_{j + k = N} sharpTerm qⱼ a k = δ_{N,0}` at every `r ∈ R`, for
  every symbol `a` whose coefficient is `1 - r p`.
* `TauCeti.WeakParameterSymbol.rightNormalizedResolventTerms p hp` and
  `TauCeti.WeakParameterSymbol.sum_coefficient_sharpTerm_rightNormalizedResolventTerms`: the formal
  right parametrix, with `q_{N+1} = r (1 - r p)⁻¹ ∘ ∑_{j ≤ N} sharpTerm p qⱼ (N + 1 - j)`, solving
  `∑_{j + k = N} sharpTerm a qⱼ k = δ_{N,0}`.

The recursions adapt `TauCeti.ParameterSymbol.leftInverseTerms` and
`TauCeti.ParameterSymbol.rightInverseTerms` of the strongly parametric calculus to the weakly
parametric one.

The formal equations turn into parametrix identities with remainders. For `N, K ≥ 1` the first `K`
composition terms of the truncation `Bₙ = ∑_{j < N} qⱼ` with `1 - r p` add up to `1 + r σ(r)`,
where `σ` is weakly parameter-dependent of frequency order `d - min N K`: the terms with
`j + k < min N K` add up to the identity, and every other term is `r` times a symbol of frequency
order `d - (j + k)`, from the recursion when `k = 0`. Since the frequency orders `-j` decrease to
`-∞`, the terms can also be summed asymptotically
(`TauCeti.WeakParameterSymbol.exists_asymptoticSum`) to a weakly parameter-dependent symbol `b` of
frequency order `0`; then the first `K` composition terms of `b` with `1 - r p` add up to
`1 + ρ(r) + r σ(r)` with `ρ` of frequency order `-K` and `σ` of frequency order `d - K`. In both
identities the remainder is stated with the factor `r` in front, as in the recursion: the symbol
`1 - r p` itself grows like `‖r‖`.

* `TauCeti.WeakParameterSymbol.leftNormalizedResolventParametrix p hp N`,
  `TauCeti.WeakParameterSymbol.rightNormalizedResolventParametrix p hp N`: the truncations
  `Bₙ = ∑_{j < N} qⱼ` of the formal left and right parametrices.
* `exists_sum_coefficient_sharpTerm_leftNormalizedResolventParametrix_eq_add` and
  `exists_sum_coefficient_sharpTerm_rightNormalizedResolventParametrix_eq_add`, in the namespace
  `TauCeti.WeakParameterSymbol`: `∑_{k < K} sharpTerm Bₙ(r) (1 - r p) k = 1 + r σ(r)` and
  `∑_{k < K} sharpTerm (1 - r p) Bₙ(r) k = 1 + r σ'(r)`, with `σ, σ'` of frequency order
  `d - min N K`.
* `exists_sum_coefficient_sharpTerm_eq_add_of_isAsymptoticSum_leftNormalizedResolventTerms` and
  `exists_sum_coefficient_sharpTerm_eq_add_of_isAsymptoticSum_rightNormalizedResolventTerms`, in
  the namespace `TauCeti.WeakParameterSymbol`: the same for asymptotic sums `b` of all the left,
  respectively right, terms, with remainders `ρ(r) + r σ(r)`.

The truncated parametrices follow `TauCeti.ParameterSymbol.leftParametrix` and
`TauCeti.ParameterSymbol.rightParametrix`.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1 (the parametrix of a
  parameter-elliptic family).
* G. Grubb and L. Hansen, *Complex powers of resolvents of pseudodifferential operators*,
  Comm. Partial Differential Equations 27 (2002), §2.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9 (the recursion
  for the parametrix of the resolvent).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace WeakParameterSymbol

variable {n : ℕ} {R : TopologicalSpace.Opens ℂ} {V : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [CompleteSpace V] {d : ℝ}

/-! ### Composition with `1 - r p` -/

section OneSubSmul

omit [CompleteSpace V]

variable {p : Symbol n V V d} {r : ℂ} {μ μ' : ℝ}

/-- Splitting a symbol `a` with coefficient `1 - r p` as `const 1 + (-r) p`. -/
private theorem coefficient_eq_const_add_smul {a : Symbol n V V μ}
    (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) :
    a.coefficient = (Symbol.const (1 : V →L[ℂ] V)).coefficient + ((-r) • p).coefficient := by
  funext q
  simp [ha, Symbol.coefficient_const, sub_eq_add_neg]

/-- For `k ≥ 1`, the term of the composition expansion of `b` with a symbol `a` with coefficient
`1 - r p` is `-r` times that of `b` with `p`: the constant `1` has no position derivatives. -/
private theorem coefficient_sharpTerm_of_coefficient_eq_one_sub_smul {b : Symbol n V V μ'}
    {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) {k : ℕ}
    (hk : k ≠ 0) : (b.sharpTerm a k).coefficient = (-r) • (b.sharpTerm p k).coefficient := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Symbol.coefficient_sharpTerm_eq_add_right (coefficient_eq_const_add_smul ha),
    Symbol.sharpTerm_const_succ, Symbol.coefficient_zero, zero_add,
    Symbol.coefficient_sharpTerm_eq_sum_right (univ : Finset Unit) (fun _ ↦ -r) (fun _ ↦ p)
      (by simp)]
  simp

/-- For `k ≥ 1`, the term of the composition expansion of a symbol `a` with coefficient `1 - r p`
with `b` is `-r` times that of `p` with `b`: the constant `1` has no frequency derivatives. -/
private theorem coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left {b : Symbol n V V μ'}
    {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) {k : ℕ}
    (hk : k ≠ 0) : (a.sharpTerm b k).coefficient = (-r) • (p.sharpTerm b k).coefficient := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Symbol.coefficient_sharpTerm_eq_add_left (coefficient_eq_const_add_smul ha),
    Symbol.const_sharpTerm_succ, Symbol.coefficient_zero, zero_add,
    Symbol.coefficient_sharpTerm_eq_sum_left (univ : Finset Unit) (fun _ ↦ -r) (fun _ ↦ p)
      (by simp)]
  simp

end OneSubSmul

/-! ### The formal left parametrix -/

section Left

/-- The orders of the summands in the recursion for the left parametrix. -/
private theorem leftNormalizedResolventTerms_order_le (N : ℕ) (j : Fin (N + 1)) :
    -(((j : ℕ) : ℝ)) + d - ((N + 1 - j : ℕ) : ℝ) ≤ d - ((N + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

/-- The terms `q₀, q₁, …` of the formal left parametrix of `1 - r p` for a parameter-elliptic
symbol `p` of order `d`, with `qⱼ` weakly parameter-dependent of frequency order `-j` and
anisotropy `d`: `q₀ = (1 - r p)⁻¹` is the normalized resolvent and
`q_{N+1} = (∑_{j ≤ N} sharpTerm qⱼ p (N + 1 - j)) ∘ r (1 - r p)⁻¹`, the last factor being the
resolvent of frequency order `-d`. They solve the formal composition equations
`∑_{j + k = N} sharpTerm qⱼ (1 - r p) k = δ_{N,0}`
(`TauCeti.WeakParameterSymbol.sum_coefficient_sharpTerm_leftNormalizedResolventTerms`). -/
def leftNormalizedResolventTerms (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    (N : ℕ) → WeakParameterSymbol n R V V d (-(N : ℝ))
  | 0 => inclusion (by simp) le_rfl (normalizedResolvent p hp)
  | N + 1 => inclusion (le_of_eq (by ring)) le_rfl
      ((∑ j : Fin (N + 1), inclusion (leftNormalizedResolventTerms_order_le N j) le_rfl
        ((leftNormalizedResolventTerms p hp j).sharpTerm
          (ofSymbol p : WeakParameterSymbol n R V V d d) (N + 1 - j))).comp (resolvent p hp))
decreasing_by exact j.isLt

variable {p : Symbol n V V d} {hp : p.IsParameterElliptic R}

/-- The leading term of the left parametrix is the normalized resolvent. -/
@[simp]
theorem coefficient_leftNormalizedResolventTerms_zero (q : CoordinateSpace n × CoordinateSpace n)
    (r : ℂ) :
    (leftNormalizedResolventTerms p hp 0).coefficient q r =
      (normalizedResolvent p hp).coefficient q r := by
  simp [leftNormalizedResolventTerms]

/-- The recursion for the left parametrix:
`q_{N+1} = (∑_{j ≤ N} sharpTerm qⱼ p (N + 1 - j)) ∘ r (1 - r p)⁻¹`. -/
theorem coefficient_leftNormalizedResolventTerms_succ (N : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (leftNormalizedResolventTerms p hp (N + 1)).coefficient q r =
      (∑ j ∈ range (N + 1), ((leftNormalizedResolventTerms p hp j).sharpTerm
          (ofSymbol p : WeakParameterSymbol n R V V d d) (N + 1 - j)).coefficient q r) ∘L
        (resolvent p hp).coefficient q r := by
  rw [leftNormalizedResolventTerms]
  simp [Fin.sum_univ_eq_sum_range (fun j => ((leftNormalizedResolventTerms p hp j).sharpTerm
    (ofSymbol p : WeakParameterSymbol n R V V d d) (N + 1 - j)).coefficient q r)]

/-- **The formal left parametrix of `1 - r p`.** For a parameter-elliptic symbol `p` and a
parameter `r ∈ R`, the values `qⱼ(r)` of the terms `qⱼ = leftNormalizedResolventTerms p hp j` solve
the formal composition equations with `1 - r p`: for every symbol `a`, of any order, with
coefficient `1 - r p`, `∑_{j + k = N} sharpTerm qⱼ(r) a k` is the identity for `N = 0` and vanishes
for `N ≥ 1`. -/
theorem sum_coefficient_sharpTerm_leftNormalizedResolventTerms {μ : ℝ} {r : ℂ} (hr : r ∈ R)
    {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) (N : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    ∑ j ∈ range (N + 1),
        (((leftNormalizedResolventTerms p hp j).toSymbol hr).sharpTerm a (N - j)).coefficient q =
      if N = 0 then ContinuousLinearMap.id ℂ V else 0 := by
  rcases N with _ | N
  · simp [ha, coefficient_normalizedResolvent_comp q hr]
  rw [sum_range_succ, Nat.sub_self, Symbol.coefficient_sharpTerm_zero, ha,
    coefficient_toSymbol, coefficient_leftNormalizedResolventTerms_succ,
    ContinuousLinearMap.comp_assoc, coefficient_resolvent_comp q hr,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  have hterm : ∀ j ∈ range (N + 1),
      (((leftNormalizedResolventTerms p hp j).toSymbol hr).sharpTerm a (N + 1 - j)).coefficient q =
        (-r) • ((leftNormalizedResolventTerms p hp j).sharpTerm
          (ofSymbol p : WeakParameterSymbol n R V V d d) (N + 1 - j)).coefficient q r := by
    intro j hj
    rw [coefficient_sharpTerm_of_coefficient_eq_one_sub_smul ha (by grind),
      Pi.smul_apply, ← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol]
  rw [sum_congr rfl hterm, ← smul_sum, neg_smul, neg_add_cancel]
  simp

end Left

/-! ### The formal right parametrix -/

section Right

/-- The orders of the summands in the recursion for the right parametrix. -/
private theorem rightNormalizedResolventTerms_order_le (N : ℕ) (j : Fin (N + 1)) :
    d + -(((j : ℕ) : ℝ)) - ((N + 1 - j : ℕ) : ℝ) ≤ d - ((N + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

/-- The terms `q₀, q₁, …` of the formal right parametrix of `1 - r p` for a parameter-elliptic
symbol `p` of order `d`, with `qⱼ` weakly parameter-dependent of frequency order `-j` and
anisotropy `d`: `q₀ = (1 - r p)⁻¹` is the normalized resolvent and
`q_{N+1} = r (1 - r p)⁻¹ ∘ ∑_{j ≤ N} sharpTerm p qⱼ (N + 1 - j)`, the first factor being the
resolvent of frequency order `-d`. They solve the formal composition equations
`∑_{j + k = N} sharpTerm (1 - r p) qⱼ k = δ_{N,0}`
(`TauCeti.WeakParameterSymbol.sum_coefficient_sharpTerm_rightNormalizedResolventTerms`). -/
def rightNormalizedResolventTerms (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    (N : ℕ) → WeakParameterSymbol n R V V d (-(N : ℝ))
  | 0 => inclusion (by simp) le_rfl (normalizedResolvent p hp)
  | N + 1 => inclusion (le_of_eq (by ring)) le_rfl
      ((resolvent p hp).comp (∑ j : Fin (N + 1),
        inclusion (rightNormalizedResolventTerms_order_le N j) le_rfl
          ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
            (rightNormalizedResolventTerms p hp j) (N + 1 - j))))
decreasing_by exact j.isLt

variable {p : Symbol n V V d} {hp : p.IsParameterElliptic R}

/-- The leading term of the right parametrix is the normalized resolvent. -/
@[simp]
theorem coefficient_rightNormalizedResolventTerms_zero (q : CoordinateSpace n × CoordinateSpace n)
    (r : ℂ) :
    (rightNormalizedResolventTerms p hp 0).coefficient q r =
      (normalizedResolvent p hp).coefficient q r := by
  simp [rightNormalizedResolventTerms]

/-- The recursion for the right parametrix:
`q_{N+1} = r (1 - r p)⁻¹ ∘ ∑_{j ≤ N} sharpTerm p qⱼ (N + 1 - j)`. -/
theorem coefficient_rightNormalizedResolventTerms_succ (N : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (rightNormalizedResolventTerms p hp (N + 1)).coefficient q r =
      (resolvent p hp).coefficient q r ∘L
        ∑ j ∈ range (N + 1), ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
          (rightNormalizedResolventTerms p hp j) (N + 1 - j)).coefficient q r := by
  rw [rightNormalizedResolventTerms]
  simp [Fin.sum_univ_eq_sum_range (fun j =>
    ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
      (rightNormalizedResolventTerms p hp j) (N + 1 - j)).coefficient q r)]

/-- **The formal right parametrix of `1 - r p`.** For a parameter-elliptic symbol `p` and a
parameter `r ∈ R`, the values `qⱼ(r)` of the terms `qⱼ = rightNormalizedResolventTerms p hp j`
solve the formal composition equations with `1 - r p`: for every symbol `a`, of any order, with
coefficient `1 - r p`, `∑_{j + k = N} sharpTerm a qⱼ(r) k` is the identity for `N = 0` and vanishes
for `N ≥ 1`. -/
theorem sum_coefficient_sharpTerm_rightNormalizedResolventTerms {μ : ℝ} {r : ℂ} (hr : r ∈ R)
    {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) (N : ℕ)
    (q : CoordinateSpace n × CoordinateSpace n) :
    ∑ j ∈ range (N + 1),
        (a.sharpTerm ((rightNormalizedResolventTerms p hp j).toSymbol hr) (N - j)).coefficient q =
      if N = 0 then ContinuousLinearMap.id ℂ V else 0 := by
  rcases N with _ | N
  · simp [ha, comp_coefficient_normalizedResolvent q hr]
  rw [sum_range_succ, Nat.sub_self, Symbol.coefficient_sharpTerm_zero, ha,
    coefficient_toSymbol, coefficient_rightNormalizedResolventTerms_succ,
    ← ContinuousLinearMap.comp_assoc, comp_coefficient_resolvent q hr,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]
  have hterm : ∀ j ∈ range (N + 1),
      (a.sharpTerm ((rightNormalizedResolventTerms p hp j).toSymbol hr) (N + 1 - j)).coefficient q =
        (-r) • ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
          (rightNormalizedResolventTerms p hp j) (N + 1 - j)).coefficient q r := by
    intro j hj
    rw [coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left ha (by grind),
      Pi.smul_apply, ← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol]
  rw [sum_congr rfl hterm, ← smul_sum, neg_smul, neg_add_cancel]
  simp

end Right

/-! ### Truncated parametrices -/

section Truncated

variable {p : Symbol n V V d} {hp : p.IsParameterElliptic R}

/-- The first `K ≥ 1` composition terms of the value `c(r)` of a weakly parameter-dependent symbol
with a symbol `a` with coefficient `1 - r p` add up to `c(r)` minus `r` times those of `c` with
`p`: the constant `1` only contributes to the term without derivatives. -/
private theorem sum_coefficient_sharpTerm_of_coefficient_eq_one_sub_smul {μ μ' : ℝ}
    (c : WeakParameterSymbol n R V V d μ') {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ}
    (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) {K : ℕ} (hK : K ≠ 0)
    (q : CoordinateSpace n × CoordinateSpace n) :
    ∑ k ∈ range K, ((c.toSymbol hr).sharpTerm a k).coefficient q =
      c.coefficient q r - r • ∑ k ∈ range K,
        (c.sharpTerm (ofSymbol p : WeakParameterSymbol n R V V d d) k).coefficient q r := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
  simp only [← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol]
  rw [sum_range_succ', sum_range_succ']
  simp [coefficient_sharpTerm_of_coefficient_eq_one_sub_smul ha (Nat.succ_ne_zero _), ha,
    smul_sum, sub_eq_add_neg, ContinuousLinearMap.one_def]
  abel

/-- The first `K ≥ 1` composition terms of a symbol `a` with coefficient `1 - r p` with the value
`c(r)` of a weakly parameter-dependent symbol add up to `c(r)` minus `r` times those of `p` with
`c`: the constant `1` only contributes to the term without derivatives. -/
private theorem sum_coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left {μ μ' : ℝ}
    (c : WeakParameterSymbol n R V V d μ') {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ}
    (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q) {K : ℕ} (hK : K ≠ 0)
    (q : CoordinateSpace n × CoordinateSpace n) :
    ∑ k ∈ range K, (a.sharpTerm (c.toSymbol hr) k).coefficient q =
      c.coefficient q r - r • ∑ k ∈ range K,
        ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm c k).coefficient q r := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
  simp only [← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol]
  rw [sum_range_succ', sum_range_succ']
  simp [coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left ha (Nat.succ_ne_zero _), ha,
    smul_sum, sub_eq_add_neg, ContinuousLinearMap.one_def]
  abel

/-- The orders of the remainder terms of the truncated parametrices: for `k = L - j + l`, so that
`j + k ≥ L`, the frequency order `d - (j + k)` is at most `d - L`. -/
private theorem remainderTerms_order_le (L j l : ℕ) :
    d - ((j + (L - j + l) : ℕ) : ℝ) ≤ d - (L : ℝ) := by
  have : (L : ℝ) ≤ ((j + (L - j + l) : ℕ) : ℝ) := by exact_mod_cast (by omega : L ≤ j + (L - j + l))
  linarith

omit [CompleteSpace V] in
/-- The bookkeeping shared by the truncated left and right parametrices. Let `σⱼₖ` be weakly
parameter-dependent symbols of frequency order `d - (j + k)`. There is a weakly
parameter-dependent symbol `σ` of frequency order `d - min N K` such that for any values `gⱼₖ`
solving the formal composition equations `∑_{j + k = L} gⱼₖ = δ_{L,0}`, with `gⱼₖ = r σⱼₖ(r)` for
`j + k ≥ 1`, the sum of the `gⱼₖ` over `j < N`, `k < K` is `1 + r σ(r)`. -/
private theorem exists_sum_range_sum_range_eq_id_add_smul {N K : ℕ} (hN : N ≠ 0) (hK : K ≠ 0)
    (σ : (j k : ℕ) → WeakParameterSymbol n R V V d (d - ((j + k : ℕ) : ℝ))) :
    ∃ σ' : WeakParameterSymbol n R V V d (d - ((min N K : ℕ) : ℝ)),
      ∀ {r : ℂ} (q : CoordinateSpace n × CoordinateSpace n) {g : ℕ → ℕ → V →L[ℂ] V},
        (∀ L, ∑ j ∈ range (L + 1), g j (L - j) =
          if L = 0 then ContinuousLinearMap.id ℂ V else 0) →
        (∀ j k, j + k ≠ 0 → g j k = r • (σ j k).coefficient q r) →
        ∑ k ∈ range K, ∑ j ∈ range N, g j k =
          ContinuousLinearMap.id ℂ V + r • σ'.coefficient q r := by
  -- The terms with `j + k ≥ min N K`, each `r` times a symbol of frequency order
  -- `d - (j + k) ≤ d - min N K`.
  refine ⟨∑ j ∈ range N, ∑ l ∈ range (K - (min N K - j)),
    inclusion (remainderTerms_order_le (min N K) j l) le_rfl (σ j (min N K - j + l)),
    fun q g hg hσ ↦ ?_⟩
  rw [sum_comm, Nat.sum_range_sum_range_eq_add _ (min_le_left N K) (min_le_right N K),
    Nat.sum_range_sum_range_sub_eq hg (by omega),
    sum_congr rfl fun j _ ↦ sum_congr rfl fun l _ ↦ hσ j _ (by omega)]
  simp [coefficient_sum, smul_sum]

omit [CompleteSpace V] in
/-- The bookkeeping shared by the parametrices obtained from asymptotic sums `b = Bₖ + c`. If the
first `K` composition terms with `Bₖ` add up to `1 + r σ(r)`, and those with `c` to
`c(r) - r ∑_{k < K} τₖ(r)`, then the first `K` composition terms with `b` add up to
`1 + c(r) + r σ'(r)` for a weakly parameter-dependent symbol `σ'` of frequency order `d - K`. -/
private theorem exists_sum_add_eq_id_add_add_smul {K : ℕ} {μ : ℝ}
    (c : WeakParameterSymbol n R V V d μ)
    (σ : WeakParameterSymbol n R V V d (d - ((min K K : ℕ) : ℝ)))
    (τ : ℕ → WeakParameterSymbol n R V V d (d - (K : ℝ))) :
    ∃ σ' : WeakParameterSymbol n R V V d (d - (K : ℝ)),
      ∀ {r : ℂ} (q : CoordinateSpace n × CoordinateSpace n) {x y : ℕ → V →L[ℂ] V},
        ∑ k ∈ range K, x k = ContinuousLinearMap.id ℂ V + r • σ.coefficient q r →
        ∑ k ∈ range K, y k = c.coefficient q r - r • ∑ k ∈ range K, (τ k).coefficient q r →
        ∑ k ∈ range K, (x k + y k) =
          ContinuousLinearMap.id ℂ V + c.coefficient q r + r • σ'.coefficient q r := by
  refine ⟨inclusion (by simp) le_rfl σ - ∑ k ∈ range K, τ k, fun q x y hx hy ↦ ?_⟩
  rw [sum_add_distrib, hx, hy]
  simp [coefficient_sum, smul_sub]
  abel

/-- The weakly parameter-dependent symbols `σⱼₖ` of frequency order `d - (j + k)` with
`sharpTerm qⱼ(r) (1 - r p) k = r σⱼₖ(r)` for `j + k ≥ 1`, where `qⱼ` are the terms of the formal
left parametrix: `-sharpTerm qⱼ p k` for `k ≥ 1`, and for `k = 0` the sum
`∑_{i < j} sharpTerm qᵢ p (j - i)` that the recursion composes with the resolvent to obtain `qⱼ`. -/
private def leftRemainderTerms (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    (j k : ℕ) → WeakParameterSymbol n R V V d (d - ((j + k : ℕ) : ℝ))
  | j, k + 1 => inclusion (le_of_eq (by push_cast; ring)) le_rfl
      (-(leftNormalizedResolventTerms p hp j).sharpTerm
        (ofSymbol p : WeakParameterSymbol n R V V d d) (k + 1))
  | j + 1, 0 => inclusion (le_of_eq (by simp)) le_rfl
      (∑ i : Fin (j + 1), inclusion (leftNormalizedResolventTerms_order_le j i) le_rfl
        ((leftNormalizedResolventTerms p hp i).sharpTerm
          (ofSymbol p : WeakParameterSymbol n R V V d d) (j + 1 - i)))
  | 0, 0 => 0

/-- For `j + k ≥ 1`, the composition term of the value `qⱼ(r)` of a term of the formal left
parametrix with a symbol with coefficient `1 - r p` is `r σⱼₖ(r)`. -/
private theorem coefficient_sharpTerm_leftNormalizedResolventTerms_eq_smul {μ : ℝ} {r : ℂ}
    (hr : r ∈ R) {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q)
    {j k : ℕ} (hjk : j + k ≠ 0) (q : CoordinateSpace n × CoordinateSpace n) :
    (((leftNormalizedResolventTerms p hp j).toSymbol hr).sharpTerm a k).coefficient q =
      r • (leftRemainderTerms p hp j k).coefficient q r := by
  rcases k with _ | k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hjk)
    simp only [Symbol.coefficient_sharpTerm_zero, ha, coefficient_toSymbol,
      coefficient_leftNormalizedResolventTerms_succ, ContinuousLinearMap.comp_assoc,
      coefficient_resolvent_comp q hr, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
    simp [leftRemainderTerms, coefficient_sum, Fin.sum_univ_eq_sum_range (fun i ↦
      ((leftNormalizedResolventTerms p hp i).sharpTerm
        (ofSymbol p : WeakParameterSymbol n R V V d d) (j + 1 - i)).coefficient q r)]
  · have hσ : (leftRemainderTerms p hp j (k + 1)).coefficient q r =
        -((leftNormalizedResolventTerms p hp j).sharpTerm
          (ofSymbol p : WeakParameterSymbol n R V V d d) (k + 1)).coefficient q r := by
      simp [leftRemainderTerms]
    rw [hσ, coefficient_sharpTerm_of_coefficient_eq_one_sub_smul ha k.succ_ne_zero, Pi.smul_apply,
      ← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol, smul_neg, neg_smul]

variable (p hp) in
/-- The sum `Bₙ = ∑_{j < N} qⱼ` of the first `N` terms of the formal left parametrix of `1 - r p`,
a weakly parameter-dependent symbol of frequency order `0`. -/
def leftNormalizedResolventParametrix (N : ℕ) : WeakParameterSymbol n R V V d 0 :=
  ∑ j ∈ range N,
    inclusion (neg_nonpos.2 (Nat.cast_nonneg j)) le_rfl (leftNormalizedResolventTerms p hp j)

@[simp]
theorem leftNormalizedResolventParametrix_zero : leftNormalizedResolventParametrix p hp 0 = 0 := by
  simp [leftNormalizedResolventParametrix]

theorem leftNormalizedResolventParametrix_succ (N : ℕ) :
    leftNormalizedResolventParametrix p hp (N + 1) = leftNormalizedResolventParametrix p hp N +
      inclusion (neg_nonpos.2 (Nat.cast_nonneg N)) le_rfl
        (leftNormalizedResolventTerms p hp N) := by
  simp [leftNormalizedResolventParametrix, sum_range_succ]

@[simp]
theorem coefficient_leftNormalizedResolventParametrix (N : ℕ) :
    (leftNormalizedResolventParametrix p hp N).coefficient =
      ∑ j ∈ range N, (leftNormalizedResolventTerms p hp j).coefficient := by
  simp [leftNormalizedResolventParametrix, coefficient_sum]

/-- The truncated left parametrix with at least one term is the normalized resolvent
`(1 - r p)⁻¹` up to a weakly parameter-dependent symbol of frequency order `-1`. -/
theorem exists_coefficient_leftNormalizedResolventParametrix_eq_normalizedResolvent_add (N : ℕ) :
    ∃ e : WeakParameterSymbol n R V V d (-1),
      (leftNormalizedResolventParametrix p hp (N + 1)).coefficient =
        (normalizedResolvent p hp).coefficient + e.coefficient := by
  refine ⟨∑ j ∈ range N, inclusion (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) le_rfl
    (leftNormalizedResolventTerms p hp (j + 1)), ?_⟩
  funext q r
  simp [sum_range_succ', add_comm, coefficient_sum]

/-- At a parameter `r ∈ R`, the composition terms of the value of the truncated left parametrix
with a symbol `a` are the sums of those of the values of its terms. -/
theorem coefficient_sharpTerm_leftNormalizedResolventParametrix {μ : ℝ} {r : ℂ} (hr : r ∈ R)
    (a : Symbol n V V μ) (N k : ℕ) (q : CoordinateSpace n × CoordinateSpace n) :
    (((leftNormalizedResolventParametrix p hp N).toSymbol hr).sharpTerm a k).coefficient q =
      ∑ j ∈ range N,
        (((leftNormalizedResolventTerms p hp j).toSymbol hr).sharpTerm a k).coefficient q := by
  rw [Symbol.coefficient_sharpTerm_eq_sum_left (range N) (fun _ ↦ 1)
    (fun j ↦ (leftNormalizedResolventTerms p hp j).toSymbol hr)
    (funext fun q ↦ by simp) a k]
  simp

/-- **The truncated left parametrix of `1 - r p`.** Let `p` be parameter-elliptic on `R`, and
`N, K ≥ 1`. There is a weakly parameter-dependent symbol `σ` of frequency order `d - min N K`
such that at every parameter `r ∈ R` the first `K` composition terms of the value `Bₙ(r)` of the
sum `Bₙ = ∑_{j < N} qⱼ` of the first `N` terms of the formal left parametrix with any symbol `a`
with coefficient `1 - r p` add up to the identity plus `r σ(r)`:

`∑_{k < K} sharpTerm Bₙ(r) a k = 1 + r σ(r)`.

The remainder is stated with the factor `r` in front, since `1 - r p` itself grows like
`‖r‖`. -/
theorem exists_sum_coefficient_sharpTerm_leftNormalizedResolventParametrix_eq_add {N K : ℕ}
    (hN : N ≠ 0) (hK : K ≠ 0) :
    ∃ σ : WeakParameterSymbol n R V V d (d - ((min N K : ℕ) : ℝ)),
      ∀ {μ : ℝ} {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ},
        a.coefficient = (fun q ↦ 1 - r • p.coefficient q) →
        ∀ q : CoordinateSpace n × CoordinateSpace n,
          ∑ k ∈ range K,
            (((leftNormalizedResolventParametrix p hp N).toSymbol hr).sharpTerm a k).coefficient q =
            ContinuousLinearMap.id ℂ V + r • σ.coefficient q r := by
  obtain ⟨σ, hσ⟩ := exists_sum_range_sum_range_eq_id_add_smul hN hK (leftRemainderTerms p hp)
  refine ⟨σ, fun {μ} {r} hr {a} ha q ↦ ?_⟩
  simp_rw [coefficient_sharpTerm_leftNormalizedResolventParametrix hr]
  exact hσ q (fun L ↦ sum_coefficient_sharpTerm_leftNormalizedResolventTerms hr ha L q)
    fun j k hjk ↦ coefficient_sharpTerm_leftNormalizedResolventTerms_eq_smul hr ha hjk q

/-- **A left parametrix of `1 - r p` in the weakly parametric calculus.** Let `p` be
parameter-elliptic on `R`, and let `b` be an asymptotic sum of the terms `qⱼ` of the formal left
parametrix of `1 - r p` (which exists by `TauCeti.WeakParameterSymbol.exists_asymptoticSum`), a
weakly parameter-dependent symbol of frequency order `0` equal to the normalized resolvent
`(1 - r p)⁻¹` up to order `-1`. For every `K ≥ 1` there are weakly parameter-dependent symbols `ρ`
of frequency order `-K` and `σ` of frequency order `d - K` such that at every parameter `r ∈ R`
the first `K` composition terms of `b(r)` with any symbol `a` with coefficient `1 - r p` add up to

`∑_{k < K} sharpTerm b(r) a k = 1 + ρ(r) + r σ(r)`. -/
theorem exists_sum_coefficient_sharpTerm_eq_add_of_isAsymptoticSum_leftNormalizedResolventTerms
    {b : WeakParameterSymbol n R V V d (-((0 : ℕ) : ℝ))}
    (hb : b.IsAsymptoticSum (leftNormalizedResolventTerms p hp)) {K : ℕ} (hK : K ≠ 0) :
    ∃ (ρ : WeakParameterSymbol n R V V d (-(K : ℝ)))
      (σ : WeakParameterSymbol n R V V d (d - (K : ℝ))),
      ∀ {μ : ℝ} {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ},
        a.coefficient = (fun q ↦ 1 - r • p.coefficient q) →
        ∀ q : CoordinateSpace n × CoordinateSpace n,
          ∑ k ∈ range K, ((b.toSymbol hr).sharpTerm a k).coefficient q =
            ContinuousLinearMap.id ℂ V + ρ.coefficient q r + r • σ.coefficient q r := by
  obtain ⟨c, hc⟩ := isAsymptoticSum_iff.1 hb K
  obtain ⟨σ, hσ⟩ := exists_sum_coefficient_sharpTerm_leftNormalizedResolventParametrix_eq_add
    (hp := hp) hK hK
  obtain ⟨σ', hσ'⟩ := exists_sum_add_eq_id_add_add_smul c σ fun k ↦
    inclusion (by linarith [Nat.cast_nonneg (α := ℝ) k]) le_rfl
      (c.sharpTerm (ofSymbol p : WeakParameterSymbol n R V V d d) k)
  refine ⟨c, σ', fun {μ} {r} hr {a} ha q ↦ ?_⟩
  have hbc : (b.toSymbol hr).coefficient =
      ((leftNormalizedResolventParametrix p hp K).toSymbol hr).coefficient +
        (c.toSymbol hr).coefficient := by
    funext q
    simp [← hc]
  simp_rw [Symbol.coefficient_sharpTerm_eq_add_left hbc, Pi.add_apply]
  exact hσ' q (hσ hr ha q) (by
    simpa using sum_coefficient_sharpTerm_of_coefficient_eq_one_sub_smul c hr ha hK q)

/-! ### The truncated right parametrix -/

/-- The weakly parameter-dependent symbols `σⱼₖ` of frequency order `d - (j + k)` with
`sharpTerm (1 - r p) qⱼ(r) k = r σⱼₖ(r)` for `j + k ≥ 1`, where `qⱼ` are the terms of the formal
right parametrix: `-sharpTerm p qⱼ k` for `k ≥ 1`, and for `k = 0` the sum
`∑_{i < j} sharpTerm p qᵢ (j - i)` that the recursion composes with the resolvent to obtain `qⱼ`. -/
private def rightRemainderTerms (p : Symbol n V V d) (hp : p.IsParameterElliptic R) :
    (j k : ℕ) → WeakParameterSymbol n R V V d (d - ((j + k : ℕ) : ℝ))
  | j, k + 1 => inclusion (le_of_eq (by push_cast; ring)) le_rfl
      (-(ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
        (rightNormalizedResolventTerms p hp j) (k + 1))
  | j + 1, 0 => inclusion (le_of_eq (by simp)) le_rfl
      (∑ i : Fin (j + 1), inclusion (rightNormalizedResolventTerms_order_le j i) le_rfl
        ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
          (rightNormalizedResolventTerms p hp i) (j + 1 - i)))
  | 0, 0 => 0

/-- For `j + k ≥ 1`, the composition term of a symbol with coefficient `1 - r p` with the value
`qⱼ(r)` of a term of the formal right parametrix is `r σⱼₖ(r)`. -/
private theorem coefficient_sharpTerm_rightNormalizedResolventTerms_eq_smul {μ : ℝ} {r : ℂ}
    (hr : r ∈ R) {a : Symbol n V V μ} (ha : a.coefficient = fun q ↦ 1 - r • p.coefficient q)
    {j k : ℕ} (hjk : j + k ≠ 0) (q : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm ((rightNormalizedResolventTerms p hp j).toSymbol hr) k).coefficient q =
      r • (rightRemainderTerms p hp j k).coefficient q r := by
  rcases k with _ | k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hjk)
    simp only [Symbol.coefficient_sharpTerm_zero, ha, coefficient_toSymbol,
      coefficient_rightNormalizedResolventTerms_succ, ← ContinuousLinearMap.comp_assoc,
      comp_coefficient_resolvent q hr, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp]
    simp [rightRemainderTerms, coefficient_sum, Fin.sum_univ_eq_sum_range (fun i ↦
      ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
        (rightNormalizedResolventTerms p hp i) (j + 1 - i)).coefficient q r)]
  · have hσ : (rightRemainderTerms p hp j (k + 1)).coefficient q r =
        -((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm
          (rightNormalizedResolventTerms p hp j) (k + 1)).coefficient q r := by
      simp [rightRemainderTerms]
    rw [hσ, coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left ha k.succ_ne_zero,
      Pi.smul_apply, ← coefficient_toSymbol _ hr, toSymbol_sharpTerm, toSymbol_ofSymbol, smul_neg,
      neg_smul]

variable (p hp) in
/-- The sum `Bₙ = ∑_{j < N} qⱼ` of the first `N` terms of the formal right parametrix of
`1 - r p`, a weakly parameter-dependent symbol of frequency order `0`. -/
def rightNormalizedResolventParametrix (N : ℕ) : WeakParameterSymbol n R V V d 0 :=
  ∑ j ∈ range N,
    inclusion (neg_nonpos.2 (Nat.cast_nonneg j)) le_rfl (rightNormalizedResolventTerms p hp j)

@[simp]
theorem rightNormalizedResolventParametrix_zero :
    rightNormalizedResolventParametrix p hp 0 = 0 := by
  simp [rightNormalizedResolventParametrix]

theorem rightNormalizedResolventParametrix_succ (N : ℕ) :
    rightNormalizedResolventParametrix p hp (N + 1) = rightNormalizedResolventParametrix p hp N +
      inclusion (neg_nonpos.2 (Nat.cast_nonneg N)) le_rfl
        (rightNormalizedResolventTerms p hp N) := by
  simp [rightNormalizedResolventParametrix, sum_range_succ]

@[simp]
theorem coefficient_rightNormalizedResolventParametrix (N : ℕ) :
    (rightNormalizedResolventParametrix p hp N).coefficient =
      ∑ j ∈ range N, (rightNormalizedResolventTerms p hp j).coefficient := by
  simp [rightNormalizedResolventParametrix, coefficient_sum]

/-- The truncated right parametrix with at least one term is the normalized resolvent
`(1 - r p)⁻¹` up to a weakly parameter-dependent symbol of frequency order `-1`. -/
theorem exists_coefficient_rightNormalizedResolventParametrix_eq_normalizedResolvent_add (N : ℕ) :
    ∃ e : WeakParameterSymbol n R V V d (-1),
      (rightNormalizedResolventParametrix p hp (N + 1)).coefficient =
        (normalizedResolvent p hp).coefficient + e.coefficient := by
  refine ⟨∑ j ∈ range N, inclusion (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) le_rfl
    (rightNormalizedResolventTerms p hp (j + 1)), ?_⟩
  funext q r
  simp [sum_range_succ', add_comm, coefficient_sum]

/-- At a parameter `r ∈ R`, the composition terms of a symbol `a` with the value of the truncated
right parametrix are the sums of those with the values of its terms. -/
theorem coefficient_sharpTerm_rightNormalizedResolventParametrix {μ : ℝ} {r : ℂ} (hr : r ∈ R)
    (a : Symbol n V V μ) (N k : ℕ) (q : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm ((rightNormalizedResolventParametrix p hp N).toSymbol hr) k).coefficient q =
      ∑ j ∈ range N,
        (a.sharpTerm ((rightNormalizedResolventTerms p hp j).toSymbol hr) k).coefficient q := by
  rw [Symbol.coefficient_sharpTerm_eq_sum_right (range N) (fun _ ↦ 1)
    (fun j ↦ (rightNormalizedResolventTerms p hp j).toSymbol hr)
    (funext fun q ↦ by simp) a k]
  simp

/-- **The truncated right parametrix of `1 - r p`.** Let `p` be parameter-elliptic on `R`, and
`N, K ≥ 1`. There is a weakly parameter-dependent symbol `σ` of frequency order `d - min N K`
such that at every parameter `r ∈ R` the first `K` composition terms of any symbol `a` with
coefficient `1 - r p` with the value `Bₙ(r)` of the sum `Bₙ = ∑_{j < N} qⱼ` of the first `N` terms
of the formal right parametrix add up to the identity plus `r σ(r)`:

`∑_{k < K} sharpTerm a Bₙ(r) k = 1 + r σ(r)`. -/
theorem exists_sum_coefficient_sharpTerm_rightNormalizedResolventParametrix_eq_add {N K : ℕ}
    (hN : N ≠ 0) (hK : K ≠ 0) :
    ∃ σ : WeakParameterSymbol n R V V d (d - ((min N K : ℕ) : ℝ)),
      ∀ {μ : ℝ} {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ},
        a.coefficient = (fun q ↦ 1 - r • p.coefficient q) →
        ∀ q : CoordinateSpace n × CoordinateSpace n,
          ∑ k ∈ range K, (a.sharpTerm
              ((rightNormalizedResolventParametrix p hp N).toSymbol hr) k).coefficient q =
            ContinuousLinearMap.id ℂ V + r • σ.coefficient q r := by
  obtain ⟨σ, hσ⟩ := exists_sum_range_sum_range_eq_id_add_smul hN hK (rightRemainderTerms p hp)
  refine ⟨σ, fun {μ} {r} hr {a} ha q ↦ ?_⟩
  simp_rw [coefficient_sharpTerm_rightNormalizedResolventParametrix hr]
  exact hσ q (fun L ↦ sum_coefficient_sharpTerm_rightNormalizedResolventTerms hr ha L q)
    fun j k hjk ↦ coefficient_sharpTerm_rightNormalizedResolventTerms_eq_smul hr ha hjk q

/-- **A right parametrix of `1 - r p` in the weakly parametric calculus.** Let `p` be
parameter-elliptic on `R`, and let `b` be an asymptotic sum of the terms `qⱼ` of the formal right
parametrix of `1 - r p`, a weakly parameter-dependent symbol of frequency order `0` equal to the
normalized resolvent `(1 - r p)⁻¹` up to order `-1`. For every `K ≥ 1` there are weakly
parameter-dependent symbols `ρ` of frequency order `-K` and `σ` of frequency order `d - K` such
that at every parameter `r ∈ R` the first `K` composition terms of any symbol `a` with coefficient
`1 - r p` with `b(r)` add up to

`∑_{k < K} sharpTerm a b(r) k = 1 + ρ(r) + r σ(r)`. -/
theorem exists_sum_coefficient_sharpTerm_eq_add_of_isAsymptoticSum_rightNormalizedResolventTerms
    {b : WeakParameterSymbol n R V V d (-((0 : ℕ) : ℝ))}
    (hb : b.IsAsymptoticSum (rightNormalizedResolventTerms p hp)) {K : ℕ} (hK : K ≠ 0) :
    ∃ (ρ : WeakParameterSymbol n R V V d (-(K : ℝ)))
      (σ : WeakParameterSymbol n R V V d (d - (K : ℝ))),
      ∀ {μ : ℝ} {r : ℂ} (hr : r ∈ R) {a : Symbol n V V μ},
        a.coefficient = (fun q ↦ 1 - r • p.coefficient q) →
        ∀ q : CoordinateSpace n × CoordinateSpace n,
          ∑ k ∈ range K, (a.sharpTerm (b.toSymbol hr) k).coefficient q =
            ContinuousLinearMap.id ℂ V + ρ.coefficient q r + r • σ.coefficient q r := by
  obtain ⟨c, hc⟩ := isAsymptoticSum_iff.1 hb K
  obtain ⟨σ, hσ⟩ := exists_sum_coefficient_sharpTerm_rightNormalizedResolventParametrix_eq_add
    (hp := hp) hK hK
  obtain ⟨σ', hσ'⟩ := exists_sum_add_eq_id_add_add_smul c σ fun k ↦
    inclusion (by linarith [Nat.cast_nonneg (α := ℝ) k]) le_rfl
      ((ofSymbol p : WeakParameterSymbol n R V V d d).sharpTerm c k)
  refine ⟨c, σ', fun {μ} {r} hr {a} ha q ↦ ?_⟩
  have hbc : (b.toSymbol hr).coefficient =
      ((rightNormalizedResolventParametrix p hp K).toSymbol hr).coefficient +
        (c.toSymbol hr).coefficient := by
    funext q
    simp [← hc]
  simp_rw [Symbol.coefficient_sharpTerm_eq_add_right hbc, Pi.add_apply]
  exact hσ' q (hσ hr ha q) (by
    simpa using sum_coefficient_sharpTerm_of_coefficient_eq_one_sub_smul_left c hr ha hK q)

end Truncated

end WeakParameterSymbol

end TauCeti
