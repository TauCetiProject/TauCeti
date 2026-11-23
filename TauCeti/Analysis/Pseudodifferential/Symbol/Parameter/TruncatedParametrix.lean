/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Evaluation
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Parametrix
import TauCeti.Algebra.BigOperators.NatAntidiagonal

/-!
# Truncated parametrices of symbols elliptic with parameter

Let `a((x, ξ), z)` be a strongly parameter-dependent symbol of order `m` (`TauCeti.ParameterSymbol`)
which is elliptic with parameter, with no polynomial condition in the frequency. Its formal left
and right parametrices `bⱼ` (`TauCeti.ParameterSymbol.leftInverseTerms`,
`TauCeti.ParameterSymbol.rightInverseTerms`), with `bⱼ` of order `-m - j` and `b₀ = a⁻¹`, solve the
formal composition equations order by order. This file shows that their truncations
`Bₙ = ∑_{j < N} bⱼ` (`TauCeti.ParameterSymbol.leftParametrix`,
`TauCeti.ParameterSymbol.rightParametrix`) invert `a` up to order `-min N K` in the first `K`
terms of the composition expansion:

`∑_{k < K} sharpTerm Bₙ a k = 1 + r` and `∑_{k < K} sharpTerm a Bₙ k = 1 + r'`

for parameter-dependent symbols `r`, `r'` of order `-min N K`
(`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_leftParametrix_eq_add`,
`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_rightParametrix_eq_add`). By the formal
composition equations, the terms `sharpTerm bⱼ a k` with `j + k < min N K` add up to the identity;
the remaining ones, with `j < N`, `k < K` and `j + k ≥ min N K`, have order `-(j + k) ≤ -min N K`
and make up the remainder. Since `z` counts as two frequency orders, the remainder decays like
`(1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-min N K)`, also as `z → ∞` at a fixed frequency.

At every spectral parameter `z ∈ Λ` the parameter-dependent composition terms are the composition
terms of the ordinary symbols (`TauCeti.ParameterSymbol.toSymbol_sharpTerm`), so these are
parametrix identities in the ordinary symbol calculus whose remainders `r(z)` have order
`-min N K` uniformly in `z`. For the symbol of `A - z`, with `A` an elliptic operator of order
`2`, the right parametrix is the symbol-level approximation of the resolvent `(A - z)⁻¹` that
enters the contour integrals defining the complex powers of `A`. If `a` has frequency degree less
than `d`, the composition expansion of `a` with the right parametrix terminates after the terms
`k < d`, and for `N ≥ 1` the identity `∑_{k < d} sharpTerm a Bₙ k = 1 + rₙ` with an explicit
remainder of order `-N` is `TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightParametrix`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9 and §11.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Finset TopologicalSpace

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : Opens ℂ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-- At every spectral parameter, the composition terms of parameter-dependent symbols are the
composition terms `TauCeti.Symbol.sharpTerm` of their symbols at that parameter. Outside `Λ`
both sides vanish. -/
@[simp]
theorem toSymbol_sharpTerm (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m)
    (k : ℕ) (z : ℂ) :
    (b.sharpTerm a k).toSymbol z = (b.toSymbol z).sharpTerm (a.toSymbol z) k := by
  ext1
  funext ⟨x, ξ⟩
  by_cases hz : z ∈ Λ
  · rw [coefficient_toSymbol, coefficient_sharpTerm b a k x ξ hz, Symbol.coefficient_sharpTerm]
    simp [mixedDeriv_def]
  · simp [Symbol.coefficient_sharpTerm, toSymbol_of_notMem _ hz, mixedDeriv_def, ← Pi.zero_def]

/-- The orders of the composition terms in the remainders of the truncated parametrices: for a
symbol `a` of order `m` and a parametrix term `bⱼ` of order `-m - j`, the terms `sharpTerm a bⱼ k`
and `sharpTerm bⱼ a k` have order `-(j + k)`, which is at most `-L` for `k = L - j + l`. -/
theorem sharpTerm_inverseTerms_order_le (L j l : ℕ) :
    m + (-m - j) - ((L - j + l : ℕ) : ℝ) ≤ -(L : ℝ) := by
  have : (L : ℝ) ≤ j + ((L - j + l : ℕ) : ℝ) := by
    exact_mod_cast (by omega : L ≤ j + (L - j + l))
  linarith

variable [CompleteSpace V] {a : ParameterSymbol n Λ V W m}

/-! ### The truncated left parametrix -/

variable (a) in
/-- The sum `∑_{j < N} bⱼ` of the first `N` terms of the formal left parametrix of a symbol `a`
of order `m` elliptic with parameter, a parameter-dependent symbol of order `-m`. -/
def leftParametrix (ha : a.IsElliptic) (N : ℕ) : ParameterSymbol n Λ W V (-m) :=
  ∑ j ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg j)) (a.leftInverseTerms ha j)

@[simp]
theorem leftParametrix_zero (ha : a.IsElliptic) : a.leftParametrix ha 0 = 0 := by
  simp [leftParametrix]

theorem leftParametrix_succ (ha : a.IsElliptic) (N : ℕ) :
    a.leftParametrix ha (N + 1) = a.leftParametrix ha N +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.leftInverseTerms ha N) := by
  simp [leftParametrix, sum_range_succ]

@[simp]
theorem coefficient_leftParametrix (ha : a.IsElliptic) (N : ℕ) :
    (a.leftParametrix ha N).coefficient = ∑ j ∈ range N, (a.leftInverseTerms ha j).coefficient := by
  simp [leftParametrix, coefficient_sum]

/-- The truncated left parametrix with at least one term is the inverse symbol up to a symbol of
order `-m - 1`. -/
theorem exists_coefficient_leftParametrix_eq_inverse_add (ha : a.IsElliptic) (N : ℕ) :
    ∃ d : ParameterSymbol n Λ W V (-m - 1),
      (a.leftParametrix ha (N + 1)).coefficient = (a.inverse ha).coefficient + d.coefficient := by
  refine ⟨∑ j ∈ range N, inclusion (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])
    (a.leftInverseTerms ha (j + 1)), ?_⟩
  funext p
  simp [Finset.sum_range_succ', add_comm]

/-- The composition terms of the truncated left parametrix with `a` are the sums of those of its
terms. -/
theorem coefficient_sharpTerm_leftParametrix (ha : a.IsElliptic) (N k : ℕ)
    (x ξ : CoordinateSpace n) (z : ℂ) :
    ((a.leftParametrix ha N).sharpTerm a k).coefficient ((x, ξ), z) =
      ∑ j ∈ range N, ((a.leftInverseTerms ha j).sharpTerm a k).coefficient ((x, ξ), z) := by
  have h := Symbol.coefficient_sharpTerm_eq_sum_left (range N) (fun _ => 1)
    (fun j => (a.leftInverseTerms ha j).toSymbol z) (a₀ := (a.leftParametrix ha N).toSymbol z)
    (funext fun q => by simp [coefficient_leftParametrix]) (a.toSymbol z) k
  calc ((a.leftParametrix ha N).sharpTerm a k).coefficient ((x, ξ), z)
      = (((a.leftParametrix ha N).toSymbol z).sharpTerm (a.toSymbol z) k).coefficient (x, ξ) := by
        rw [← toSymbol_sharpTerm _ _ _ z, coefficient_toSymbol]
    _ = _ := by
        rw [h, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, one_smul, ← toSymbol_sharpTerm _ _ _ z, coefficient_toSymbol]

/-- **The truncated left parametrix with parameter.** Let `a` be elliptic with parameter. The
first `K` composition terms of the sum `Bₙ = ∑_{j < N} bⱼ` of the first `N` terms of its formal
left parametrix with `a` add up to the identity plus a parameter-dependent symbol `r` of order
`-min N K`: `∑_{k < K} sharpTerm Bₙ a k = 1 + r`. At a spectral parameter `z ∈ Λ` this is an
identity of ordinary symbols by `TauCeti.ParameterSymbol.toSymbol_sharpTerm`. -/
theorem exists_sum_coefficient_sharpTerm_leftParametrix_eq_add (ha : a.IsElliptic) (N K : ℕ) :
    ∃ r : ParameterSymbol n Λ V V (-(min N K : ℕ)), ∀ (x ξ : CoordinateSpace n) {z : ℂ}, z ∈ Λ →
      ∑ k ∈ range K, ((a.leftParametrix ha N).sharpTerm a k).coefficient ((x, ξ), z) =
        ContinuousLinearMap.id ℂ V + r.coefficient ((x, ξ), z) := by
  rcases Nat.eq_zero_or_pos (min N K) with h | h
  · refine ⟨inclusion (by simp [h]) (-ofSpatial (fun _ => ContinuousLinearMap.id ℂ V)
      contDiff_const), fun x ξ z hz => ?_⟩
    simp_rw [coefficient_sharpTerm_leftParametrix ha N _ x ξ z]
    rcases Nat.min_eq_zero_iff.1 h with rfl | rfl <;> simp [hz]
  -- The terms `sharpTerm bⱼ a k` with `j + k ≥ min N K`, of order `-(j + k) ≤ -min N K`.
  refine ⟨∑ j ∈ range N, ∑ l ∈ range (K - (min N K - j)),
    inclusion (by linarith [sharpTerm_inverseTerms_order_le (m := m) (min N K) j l])
    ((a.leftInverseTerms ha j).sharpTerm a (min N K - j + l)), fun x ξ z hz => ?_⟩
  simp_rw [coefficient_sharpTerm_leftParametrix ha N _ x ξ z]
  rw [sum_comm, Nat.sum_range_sum_range_eq_add _ (min_le_left N K) (min_le_right N K),
    Nat.sum_range_sum_range_sub_eq (g := fun j k =>
      ((a.leftInverseTerms ha j).sharpTerm a k).coefficient ((x, ξ), z))
      (fun L => sum_coefficient_sharpTerm_leftInverseTerms ha L x ξ hz) h.ne']
  simp [coefficient_sum]

/-! ### The truncated right parametrix -/

variable (a) in
/-- The sum `∑_{j < N} bⱼ` of the first `N` terms of the formal right parametrix of a symbol `a`
of order `m` elliptic with parameter, a parameter-dependent symbol of order `-m`. -/
def rightParametrix (ha : a.IsElliptic) (N : ℕ) : ParameterSymbol n Λ W V (-m) :=
  ∑ j ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg j)) (a.rightInverseTerms ha j)

@[simp]
theorem rightParametrix_zero (ha : a.IsElliptic) : a.rightParametrix ha 0 = 0 := by
  simp [rightParametrix]

theorem rightParametrix_succ (ha : a.IsElliptic) (N : ℕ) :
    a.rightParametrix ha (N + 1) = a.rightParametrix ha N +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.rightInverseTerms ha N) := by
  simp [rightParametrix, sum_range_succ]

@[simp]
theorem coefficient_rightParametrix (ha : a.IsElliptic) (N : ℕ) :
    (a.rightParametrix ha N).coefficient =
      ∑ j ∈ range N, (a.rightInverseTerms ha j).coefficient := by
  simp [rightParametrix, coefficient_sum]

/-- The truncated right parametrix with at least one term is the inverse symbol up to a symbol of
order `-m - 1`. -/
theorem exists_coefficient_rightParametrix_eq_inverse_add (ha : a.IsElliptic) (N : ℕ) :
    ∃ d : ParameterSymbol n Λ W V (-m - 1),
      (a.rightParametrix ha (N + 1)).coefficient = (a.inverse ha).coefficient + d.coefficient := by
  refine ⟨∑ j ∈ range N, inclusion (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])
    (a.rightInverseTerms ha (j + 1)), ?_⟩
  funext p
  simp [Finset.sum_range_succ', add_comm]

/-- The composition terms of `a` with the truncated right parametrix are the sums of those with
its terms. -/
theorem coefficient_sharpTerm_rightParametrix (ha : a.IsElliptic) (N k : ℕ)
    (x ξ : CoordinateSpace n) (z : ℂ) :
    (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z) =
      ∑ j ∈ range N, (a.sharpTerm (a.rightInverseTerms ha j) k).coefficient ((x, ξ), z) := by
  have h := Symbol.coefficient_sharpTerm_eq_sum_right (range N) (fun _ => 1)
    (fun j => (a.rightInverseTerms ha j).toSymbol z) (b₀ := (a.rightParametrix ha N).toSymbol z)
    (funext fun q => by simp [coefficient_rightParametrix]) (a.toSymbol z) k
  calc (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z)
      = ((a.toSymbol z).sharpTerm ((a.rightParametrix ha N).toSymbol z) k).coefficient (x, ξ) := by
        rw [← toSymbol_sharpTerm _ _ _ z, coefficient_toSymbol]
    _ = _ := by
        rw [h, Finset.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, one_smul, ← toSymbol_sharpTerm _ _ _ z, coefficient_toSymbol]

/-- **The truncated right parametrix with parameter.** Let `a` be elliptic with parameter. The
first `K` composition terms of `a` with the sum `Bₙ = ∑_{j < N} bⱼ` of the first `N` terms of its
formal right parametrix add up to the identity plus a parameter-dependent symbol `r` of order
`-min N K`: `∑_{k < K} sharpTerm a Bₙ k = 1 + r`. At a spectral parameter `z ∈ Λ` this is an
identity of ordinary symbols by `TauCeti.ParameterSymbol.toSymbol_sharpTerm`. -/
theorem exists_sum_coefficient_sharpTerm_rightParametrix_eq_add (ha : a.IsElliptic) (N K : ℕ) :
    ∃ r : ParameterSymbol n Λ W W (-(min N K : ℕ)), ∀ (x ξ : CoordinateSpace n) {z : ℂ}, z ∈ Λ →
      ∑ k ∈ range K, (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z) =
        ContinuousLinearMap.id ℂ W + r.coefficient ((x, ξ), z) := by
  rcases Nat.eq_zero_or_pos (min N K) with h | h
  · refine ⟨inclusion (by simp [h]) (-ofSpatial (fun _ => ContinuousLinearMap.id ℂ W)
      contDiff_const), fun x ξ z hz => ?_⟩
    simp_rw [coefficient_sharpTerm_rightParametrix ha N _ x ξ z]
    rcases Nat.min_eq_zero_iff.1 h with rfl | rfl <;> simp [hz]
  -- The terms `sharpTerm a bⱼ k` with `j + k ≥ min N K`, of order `-(j + k) ≤ -min N K`.
  refine ⟨∑ j ∈ range N, ∑ l ∈ range (K - (min N K - j)),
    inclusion (sharpTerm_inverseTerms_order_le (min N K) j l)
    (a.sharpTerm (a.rightInverseTerms ha j) (min N K - j + l)), fun x ξ z hz => ?_⟩
  simp_rw [coefficient_sharpTerm_rightParametrix ha N _ x ξ z]
  rw [sum_comm, Nat.sum_range_sum_range_eq_add _ (min_le_left N K) (min_le_right N K),
    Nat.sum_range_sum_range_sub_eq (g := fun j k =>
      (a.sharpTerm (a.rightInverseTerms ha j) k).coefficient ((x, ξ), z))
      (fun L => sum_coefficient_sharpTerm_rightInverseTerms ha L x ξ hz) h.ne']
  simp [coefficient_sum]

end ParameterSymbol

end TauCeti
