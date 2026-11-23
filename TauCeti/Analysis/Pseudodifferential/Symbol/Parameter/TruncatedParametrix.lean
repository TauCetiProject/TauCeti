/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.OperatorParametrix

/-!
# Truncated parametrices of symbols elliptic with parameter

Let `a((x, ξ), z)` be a strongly parameter-dependent symbol of order `m` (`TauCeti.ParameterSymbol`)
which is elliptic with parameter, with no polynomial condition in the frequency. Its formal left
and right parametrices `bⱼ` (`TauCeti.ParameterSymbol.leftInverseTerms`,
`TauCeti.ParameterSymbol.rightInverseTerms`), with `bⱼ` of order `-m - j` and `b₀ = a⁻¹`, solve the
formal composition equations order by order. This file shows that their truncations
`Bₙ = ∑_{j < N} bⱼ` (`TauCeti.ParameterSymbol.leftParametrix`,
`TauCeti.ParameterSymbol.rightParametrix`) invert `a` up to order `-N` in the first `N` terms of the
composition expansion:

`∑_{k < N} sharpTerm Bₙ a k = 1 + r` and `∑_{k < N} sharpTerm a Bₙ k = 1 + r'`

for parameter-dependent symbols `r`, `r'` of order `-N`
(`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_leftParametrix_eq_add`,
`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_rightParametrix_eq_add`). By the formal
composition equations, the terms `sharpTerm bⱼ a k` with `j + k < N` add up to the identity; the
remaining ones, with `j, k < N ≤ j + k`, have order `-(j + k) ≤ -N` and make up the remainder. Since
`z` counts as two frequency orders, the remainder decays like
`(1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)) ^ (-N)`, also as `z → ∞` at a fixed frequency.

At every spectral parameter `z ∈ Λ` these are parametrix identities in the ordinary symbol calculus
whose remainders `r(z)` have order `-N` uniformly in `z`
(`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_toSymbol_leftParametrix_eq_add`,
`TauCeti.ParameterSymbol.exists_sum_coefficient_sharpTerm_toSymbol_rightParametrix_eq_add`). For
the symbol of `A - z`, with `A` an elliptic operator of order `2`, the right parametrix is the
symbol-level approximation of the resolvent `(A - z)⁻¹` that enters the contour integrals defining
the complex powers of `A`. When `a` is polynomial in the frequency, the composition expansion is
exact and `TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightParametrix` gives the full
identity instead.

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

variable {n : ℕ} {Λ : Opens ℂ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace V] {m : ℝ}
  {a : ParameterSymbol n Λ V W m}

/-- The composition terms of the truncations beyond order `N` have order at most `-N`: for
`k = N - j + i` the total number of derivatives `j + k` is at least `N`. -/
private theorem truncatedParametrix_order_le (N j i : ℕ) :
    -(j : ℝ) - ((N - j + i : ℕ) : ℝ) ≤ -(N : ℝ) := by
  rcases le_or_gt j N with h | h
  · rw [Nat.cast_add, Nat.cast_sub h]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  · rw [Nat.sub_eq_zero_of_le h.le, zero_add]
    have hj : (N : ℝ) < j := by exact_mod_cast h
    linarith [Nat.cast_nonneg (α := ℝ) i]

/-- The terms `T j k` with `j < N` and `k < N` split into those with `j + k < N`, which add up to
the identity by the formal composition equations, and those with `k = N - j + i` for `i < j`. -/
private theorem sum_sum_eq_add {E : Type*} [AddCommMonoid E] {N : ℕ} (hN : N ≠ 0) (e : E)
    (T : ℕ → ℕ → E) (hT : ∀ L, ∑ j ∈ range (L + 1), T j (L - j) = if L = 0 then e else 0) :
    ∑ k ∈ range N, ∑ j ∈ range N, T j k =
      e + ∑ j ∈ range N, ∑ i ∈ range j, T j (N - j + i) := by
  have hsplit : ∀ j ∈ range N, ∑ k ∈ range N, T j k =
      ∑ k ∈ range (N - j), T j k + ∑ i ∈ range j, T j (N - j + i) := fun j hj => by
    rw [← Finset.sum_range_add, Nat.sub_add_cancel (Finset.mem_range.1 hj).le]
  have hdiag : ∑ j ∈ range N, ∑ k ∈ range (N - j), T j k = e := by
    rw [← Finset.sum_range_diag_flip]
    simp_rw [hT]
    simp [Nat.pos_of_ne_zero hN]
  rw [Finset.sum_comm, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hdiag]

/-! ### The truncated left parametrix -/

variable (a) in
/-- The sum `∑_{j < N} bⱼ` of the first `N` terms of the formal left parametrix of a symbol `a`
of order `m` elliptic with parameter, a parameter-dependent symbol of order `-m`. -/
def leftParametrix (ha : a.IsElliptic) (N : ℕ) : ParameterSymbol n Λ W V (-m) :=
  ∑ j ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg j)) (a.leftInverseTerms ha j)

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
first `N` composition terms of the sum `Bₙ = ∑_{j < N} bⱼ` of the first `N` terms of its formal
left parametrix with `a` add up to the identity plus a parameter-dependent symbol `r` of order
`-N`: `∑_{k < N} sharpTerm Bₙ a k = 1 + r`. -/
theorem exists_sum_coefficient_sharpTerm_leftParametrix_eq_add (ha : a.IsElliptic) (N : ℕ) :
    ∃ r : ParameterSymbol n Λ V V (-N), ∀ (x ξ : CoordinateSpace n) {z : ℂ}, z ∈ Λ →
      ∑ k ∈ range N, ((a.leftParametrix ha N).sharpTerm a k).coefficient ((x, ξ), z) =
        ContinuousLinearMap.id ℂ V + r.coefficient ((x, ξ), z) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨inclusion (by simp) (-ofSpatial (fun _ => ContinuousLinearMap.id ℂ V) contDiff_const),
      fun x ξ z hz => by simp [hz]⟩
  refine ⟨∑ j ∈ range N, ∑ i ∈ range j, inclusion
    (by have := truncatedParametrix_order_le N j i; linarith)
    ((a.leftInverseTerms ha j).sharpTerm a (N - j + i)), fun x ξ z hz => ?_⟩
  simp_rw [coefficient_sharpTerm_leftParametrix ha N _ x ξ z]
  rw [sum_sum_eq_add hN.ne' _ _ fun L => sum_coefficient_sharpTerm_leftInverseTerms ha L x ξ hz]
  simp

/-- **The truncated left parametrix in the ordinary calculus.** For `a` elliptic with parameter
and every `N`, there is a parameter-dependent symbol `r` of order `-N` such that at every spectral
parameter `z ∈ Λ`, `∑_{k < N} sharpTerm Bₙ(z) a(z) k = 1 + r(z)` for the ordinary symbols at `z`.
The remainder `r(z)` has order `-N` uniformly in `z`. -/
theorem exists_sum_coefficient_sharpTerm_toSymbol_leftParametrix_eq_add (ha : a.IsElliptic)
    (N : ℕ) :
    ∃ r : ParameterSymbol n Λ V V (-N), ∀ z ∈ Λ, ∀ q : CoordinateSpace n × CoordinateSpace n,
      ∑ k ∈ range N,
          (((a.leftParametrix ha N).toSymbol z).sharpTerm (a.toSymbol z) k).coefficient q =
        ContinuousLinearMap.id ℂ V + (r.toSymbol z).coefficient q := by
  obtain ⟨r, hr⟩ := exists_sum_coefficient_sharpTerm_leftParametrix_eq_add ha N
  refine ⟨r, fun z hz ⟨x, ξ⟩ => ?_⟩
  simp_rw [← toSymbol_sharpTerm, coefficient_toSymbol]
  exact hr x ξ hz

/-! ### The truncated right parametrix -/

/-- The truncated right parametrix with at least one term is the inverse symbol up to a symbol of
order `-m - 1`. -/
theorem exists_coefficient_rightParametrix_eq_inverse_add (ha : a.IsElliptic) (N : ℕ) :
    ∃ d : ParameterSymbol n Λ W V (-m - 1),
      (a.rightParametrix ha (N + 1)).coefficient = (a.inverse ha).coefficient + d.coefficient := by
  refine ⟨∑ j ∈ range N, inclusion (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j])
    (a.rightInverseTerms ha (j + 1)), ?_⟩
  funext p
  simp [Finset.sum_range_succ', add_comm]

/-- **The truncated right parametrix with parameter.** Let `a` be elliptic with parameter. The
first `N` composition terms of `a` with the sum `Bₙ = ∑_{j < N} bⱼ` of the first `N` terms of its
formal right parametrix add up to the identity plus a parameter-dependent symbol `r` of order
`-N`: `∑_{k < N} sharpTerm a Bₙ k = 1 + r`. -/
theorem exists_sum_coefficient_sharpTerm_rightParametrix_eq_add (ha : a.IsElliptic) (N : ℕ) :
    ∃ r : ParameterSymbol n Λ W W (-N), ∀ (x ξ : CoordinateSpace n) {z : ℂ}, z ∈ Λ →
      ∑ k ∈ range N, (a.sharpTerm (a.rightParametrix ha N) k).coefficient ((x, ξ), z) =
        ContinuousLinearMap.id ℂ W + r.coefficient ((x, ξ), z) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨inclusion (by simp) (-ofSpatial (fun _ => ContinuousLinearMap.id ℂ W) contDiff_const),
      fun x ξ z hz => by simp [hz]⟩
  refine ⟨∑ j ∈ range N, ∑ i ∈ range j, inclusion
    (by have := truncatedParametrix_order_le N j i; linarith)
    (a.sharpTerm (a.rightInverseTerms ha j) (N - j + i)), fun x ξ z hz => ?_⟩
  simp_rw [coefficient_sharpTerm_rightParametrix ha N _ x ξ z]
  rw [sum_sum_eq_add hN.ne' _ _ fun L => sum_coefficient_sharpTerm_rightInverseTerms ha L x ξ hz]
  simp

/-- **The truncated right parametrix in the ordinary calculus.** For `a` elliptic with parameter
and every `N`, there is a parameter-dependent symbol `r` of order `-N` such that at every spectral
parameter `z ∈ Λ`, `∑_{k < N} sharpTerm a(z) Bₙ(z) k = 1 + r(z)` for the ordinary symbols at `z`.
The remainder `r(z)` has order `-N` uniformly in `z`. -/
theorem exists_sum_coefficient_sharpTerm_toSymbol_rightParametrix_eq_add (ha : a.IsElliptic)
    (N : ℕ) :
    ∃ r : ParameterSymbol n Λ W W (-N), ∀ z ∈ Λ, ∀ q : CoordinateSpace n × CoordinateSpace n,
      ∑ k ∈ range N,
          ((a.toSymbol z).sharpTerm ((a.rightParametrix ha N).toSymbol z) k).coefficient q =
        ContinuousLinearMap.id ℂ W + (r.toSymbol z).coefficient q := by
  obtain ⟨r, hr⟩ := exists_sum_coefficient_sharpTerm_rightParametrix_eq_add ha N
  refine ⟨r, fun z hz ⟨x, ξ⟩ => ?_⟩
  simp_rw [← toSymbol_sharpTerm, coefficient_toSymbol]
  exact hr x ξ hz

end ParameterSymbol

end TauCeti
