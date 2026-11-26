/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.ProperSupport
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Evaluation
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.TruncatedParametrix
import TauCeti.Algebra.BigOperators.NatAntidiagonal

/-!
# Composition of parameter-dependent symbols at a spectral parameter

A strongly parameter-dependent symbol `b((x, ξ), z)` (`TauCeti.ParameterSymbol`) is, at each
spectral parameter `z`, the ordinary symbol `b(z) = TauCeti.ParameterSymbol.toSymbol b z`. The
terms of the formal composition of two parameter-dependent symbols evaluate to the terms of the
composition expansion of the ordinary symbols (`TauCeti.ParameterSymbol.toSymbol_sharpTerm`):

`(sharpTerm b a k)(z) = sharpTerm b(z) a(z) k`.

When `b(z)` is a polynomial of degree less than `N` in the frequency, as for the symbol
`p(x, ξ) - z` of `P - z` with `P` a second-order differential operator and `N = 3` (such as
`s - Δ - z`), the composition expansion of `b(z) # a(z)` is exact after `N` terms
(`TauCeti.Symbol.sharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero`). So the composition symbol at
`z` is the value at `z` of the single parameter-dependent symbol `∑_{k < N} sharpTerm b a k` of
order `m' + m` (`TauCeti.ParameterSymbol.sharp_toSymbol_eq_toSymbol_sum_sharpTerm`, and
`TauCeti.ParameterSymbol.properSharp_toSymbol_eq_toSymbol_sum_sharpTerm` without compact support of
`a(z)` when `b(z)` has finite propagation). Its estimates are therefore uniform in the spectral
parameter, with `z` counting as two frequency orders, and no remainder of the expansion has to be
estimated.

For `a` elliptic with parameter and polynomial in the frequency, the sum of the first `J + 1`
terms `bⱼ = a.rightInverseTerms ha j` of its formal right parametrix
(`TauCeti.ParameterSymbol.rightParametrix`) therefore gives an exact right parametrix up to order
`-(J + 1)`: `a(z) ∘ (∑_{j ≤ J} bⱼ(z)) = 1 + R(z)` for one parameter-dependent symbol `R` of order
`-(J + 1)` (`TauCeti.ParameterSymbol.IsElliptic.exists_properSharp_rightParametrix_eq_id_add`). This
is the symbol identity behind the comparison of the resolvent `(P - z)⁻¹` of a second-order
elliptic differential operator `P` with the quantized parametrix, the first step of the contour
construction of the complex powers of `P`.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, second edition, Springer
  (2001), Chapter II, §9 (the parametrix of `A - λ` for a differential operator `A`).
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] {m m' : ℝ}

variable [CompleteSpace W] [CompleteSpace U] {b : ParameterSymbol n Λ W U m'}
  {a : ParameterSymbol n Λ V W m} {z : ℂ} {N : ℕ}

/-- **Exact composition at a spectral parameter.** If the symbol `b(z)` is a polynomial of degree
less than `N` in the frequency, then for `a(z)` with compact spatial support the composition symbol
`b(z) # a(z)` is the value at `z` of the parameter-dependent symbol `∑_{k < N} sharpTerm b a k` of
order `m' + m`. -/
theorem sharp_toSymbol_eq_toSymbol_sum_sharpTerm
    (hb : ∀ β : List (Fin n), β.length = N → ∀ x ξ,
      mixedDeriv [] β (b.toSymbol z).coefficient x ξ = 0)
    (ha : (a.toSymbol z).HasCompactSpatialSupport) :
    (b.toSymbol z).sharp (a.toSymbol z) ha =
      (∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (b.sharpTerm a k)).toSymbol
        z := by
  simp [Symbol.sharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero hb ha]

/-- **Exact composition at a spectral parameter, with a properly supported left factor.** If the
symbol `b(z)` is a polynomial of degree less than `N` in the frequency and has finite propagation,
then the composition symbol of `b(z)` and `a(z)` is the value at `z` of the parameter-dependent
symbol `∑_{k < N} sharpTerm b a k` of order `m' + m`, with no support condition on `a(z)`. -/
theorem properSharp_toSymbol_eq_toSymbol_sum_sharpTerm [CompleteSpace V] {ε : ℝ}
    (hb : ∀ β : List (Fin n), β.length = N → ∀ x ξ,
      mixedDeriv [] β (b.toSymbol z).coefficient x ξ = 0)
    (hprop : (b.toSymbol z).HasPropagationLE ε) :
    (b.toSymbol z).properSharp hprop (a.toSymbol z) =
      (∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (b.sharpTerm a k)).toSymbol
        z := by
  simp [Symbol.properSharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero hprop hb]

/-! ### The right parametrix of a differential operator with parameter -/

/-- The bookkeeping of the right parametrix: if the terms `T j k` with `j + k = M` sum to `e` for
`M = 0` and to `0` otherwise, and `T j k = 0` for `k ≥ N`, then summing `T j k` over `j ≤ J` and
`k < N` gives `e` plus the terms with `j + k > J`. -/
private theorem sum_sum_eq_add_sum_sum {X : Type*} [AddCommGroup X] (T : ℕ → ℕ → X) (e : X)
    {N : ℕ} (hA : ∀ M, ∑ j ∈ range (M + 1), T j (M - j) = if M = 0 then e else 0)
    (hB : ∀ j k, N ≤ k → T j k = 0) (J : ℕ) :
    ∑ j ∈ range (J + 1), ∑ k ∈ range N, T j k =
      e + ∑ j ∈ range (J + 1), ∑ k ∈ range N, if J < j + k then T j k else 0 := by
  -- For `j ≤ J`, the terms with `j + k ≤ J` are those with `k < J + 1 - j`, as `T j k = 0` for
  -- `k ≥ N`.
  have hlow (j : ℕ) (hj : j ∈ range (J + 1)) :
      ∑ k ∈ range N, (if j + k ≤ J then T j k else 0) = ∑ k ∈ range (J + 1 - j), T j k := by
    rw [mem_range] at hj
    calc ∑ k ∈ range N, (if j + k ≤ J then T j k else 0)
        = ∑ k ∈ range (N + (J + 1 - j)), (if j + k ≤ J then T j k else 0) := by
          rw [sum_range_add, left_eq_add]
          exact sum_eq_zero fun k _ ↦ by simp [hB j (N + k) (by omega)]
      _ = ∑ k ∈ range (J + 1 - j), T j k := by
          rw [add_comm N, sum_range_add, sum_eq_zero (s := range N) fun k _ ↦ by simp; omega,
            add_zero]
          exact sum_congr rfl fun k hk ↦ by rw [mem_range] at hk; simp; omega
  calc ∑ j ∈ range (J + 1), ∑ k ∈ range N, T j k
      = ∑ j ∈ range (J + 1), ∑ k ∈ range N, (if j + k ≤ J then T j k else 0) +
          ∑ j ∈ range (J + 1), ∑ k ∈ range N, (if J < j + k then T j k else 0) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun k _ ↦ ?_
        split_ifs <;> first | omega | simp
    _ = e + ∑ j ∈ range (J + 1), ∑ k ∈ range N, if J < j + k then T j k else 0 := by
        rw [sum_congr rfl hlow, Nat.sum_range_sum_range_sub_eq hA J.succ_ne_zero]

variable [CompleteSpace V] {a : ParameterSymbol n Λ V W m}

/-- **The exact right parametrix with parameter.** Let `a` be elliptic with parameter, with
`a(z)` a polynomial of degree less than `N` in the frequency at every spectral parameter `z ∈ Λ`,
as for the symbol of `P - z` with `P` a second-order differential operator and `N = 3`: since `z`
counts as two frequency orders, `P - z` is elliptic with parameter only for `P` of order `2`. Let
`Q_J = ∑_{j ≤ J} bⱼ = a.rightParametrix ha (J + 1)` be the sum of the first `J + 1` terms
`bⱼ = a.rightInverseTerms ha j` of its right parametrix. Then there is a parameter-dependent
symbol `R` of order `-(J + 1)` with

`a(z) ∘ Q_J(z) = 1 + R(z)`

exactly, as composition symbols at every `z ∈ Λ` at which `a(z)` has finite propagation. The
estimates of `R` are uniform in the spectral parameter: as a symbol of order `0`, `R(z)` has
seminorms `O((1 + ‖z‖ ^ (1 / 2)) ^ (-(J + 1)))` on `Λ`
(`TauCeti.ParameterSymbol.exists_seminorm_inclusion_toSymbol_le`). -/
theorem IsElliptic.exists_properSharp_rightParametrix_eq_id_add
    (ha : a.IsElliptic) (hpoly : ∀ z ∈ Λ, ∀ β : List (Fin n), β.length = N → ∀ x ξ,
      mixedDeriv [] β (a.toSymbol z).coefficient x ξ = 0) (J : ℕ) :
    ∃ R : ParameterSymbol n Λ W W (-(J + 1 : ℕ)), ∀ z ∈ Λ, ∀ {ε : ℝ}
      (hprop : (a.toSymbol z).HasPropagationLE ε) (x ξ : CoordinateSpace n),
      ((a.toSymbol z).properSharp hprop ((a.rightParametrix ha (J + 1)).toSymbol z)).coefficient
          (x, ξ) =
        ContinuousLinearMap.id ℂ W + R.coefficient ((x, ξ), z) := by
  -- `R` collects the terms `sharpTerm a bⱼ k`, of order `-(j + k)`, with `j + k > J`.
  have hord {j k : ℕ} (h : J < j + k) :
      m + (-m - j) - k ≤ -((J + 1 : ℕ) : ℝ) := by
    have : ((J + 1 : ℕ) : ℝ) ≤ j + k := by exact_mod_cast h
    push_cast at this ⊢
    linarith
  refine ⟨∑ j ∈ range (J + 1), ∑ k ∈ range N, if h : J < j + k then
    inclusion (by simpa using hord h) (a.sharpTerm (a.rightInverseTerms ha j) k) else 0,
    fun z hz ε hprop x ξ ↦ ?_⟩
  set T : ℕ → ℕ → W →L[ℂ] W := fun j k ↦
    (a.sharpTerm (a.rightInverseTerms ha j) k).coefficient ((x, ξ), z) with hT
  -- The composition symbol at `z` is the exact finite expansion, linear in the right factor.
  have hlin (k : ℕ) : ((a.toSymbol z).sharpTerm ((a.rightParametrix ha (J + 1)).toSymbol z)
      k).coefficient (x, ξ) = ∑ j ∈ range (J + 1), T j k := by
    rw [← toSymbol_sharpTerm, coefficient_toSymbol, coefficient_sharpTerm_rightParametrix]
  have hB (j k : ℕ) (hk : N ≤ k) : T j k = 0 := by
    simp [hT, ← coefficient_toSymbol, toSymbol_sharpTerm,
      Symbol.sharpTerm_eq_zero_of_mixedDeriv_nil_eq_zero (hpoly z hz) _ hk]
  rw [Symbol.properSharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero hprop (hpoly z hz)]
  simp only [Symbol.coefficient_sum, Finset.sum_apply, Symbol.coefficient_inclusion, hlin]
  rw [sum_comm, sum_sum_eq_add_sum_sum T _ (fun M ↦ sum_coefficient_sharpTerm_rightInverseTerms
    ha M x ξ hz) hB J]
  simp [coefficient_sum, apply_dite, ite_apply, hT]

end ParameterSymbol

end TauCeti
