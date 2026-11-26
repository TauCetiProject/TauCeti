/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.FormalComposition
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Resolvent

/-!
# The formal parametrix of `1 - r p` in the weakly parametric calculus

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
parametric one. Since their frequency orders `-j` decrease to `-∞`, each sequence can be summed
asymptotically (`TauCeti.WeakParameterSymbol.exists_asymptoticSum`) to a weakly
parameter-dependent symbol of frequency order `0`.

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

end WeakParameterSymbol

end TauCeti
