/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential

/-!
# Composition with a differential operator

Let `P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` be a differential operator of order `m` on `ℝⁿ` with
smooth coefficients, with classical symbol `p = TauCeti.ClassicalSymbol.ofDifferentialSymbol`.
Its symbol is a polynomial of degree at most `m` in the frequency
(`TauCeti.ClassicalSymbol.mixedDeriv_nil_coefficient_toSymbol_ofDifferentialSymbol_eq_zero`), so the
composition expansion of `p # q` terminates: for every symbol `q` with compact spatial support,
`p # q = ∑_{j ≤ m} sharpTerm p q j` exactly
(`TauCeti.Symbol.sharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero`). This file states the
consequence for the operators: applying `P` to `Op(q) u` is quantizing the finite sum
`∑_{j ≤ m} sharpTerm p q j`, with no smoothing remainder
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_sum_sharpTerm_ofDifferentialSymbol`). In the
familiar notation, `P ∘ Op(q) = Op(∑_{|α| ≤ m} (1 / α!) ∂_ξ^α p · D_x^α q)`.

Exactness is what makes the composition with a differential operator uniform in auxiliary
parameters, such as the spectral parameter of the resolvent symbol of `P - z`: no remainder of
the asymptotic expansion has to be estimated.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8 (the
  composition formula, which is exact when one factor is a differential operator).
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, second edition, Springer
  (2001), Chapter II, §9 (the parametrix of `A - λ` for a differential operator `A`).
-/

public section

noncomputable section

open Finset
open scoped ContDiff SchwartzMap

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {ι : Type*} {k : ι → ℕ}
  (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
  (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
  (hk : ∀ i ∈ s, k i ≤ m)

/-- **Exact composition with a differential operator.** For a differential operator
`P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` of order `m` with symbol `p`, and a symbol `q` with compact
spatial support, `P (Op(q) u)` is the quantization of the finite sum
`∑_{j ≤ m} sharpTerm p q j` of the terms of the composition expansion, for every Schwartz
function `u`. -/
theorem quantizeSchwartzValue_sum_sharpTerm_ofDifferentialSymbol [CompleteSpace V]
    [CompleteSpace W] {μ : ℝ} {q : Symbol n U V μ}
    (hq : q.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, U)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (∑ j ∈ range (m + 1), Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg j))
        ((ofDifferentialSymbol m s v b hb hk).toSymbol.sharpTerm q j)).coefficient u x =
      ∑ i ∈ s, b i x (iteratedFDeriv ℝ (k i) (quantizeSchwartzValue q.coefficient u) x (v i)) := by
  have hw : ⇑((hq.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
      (q.contDiff_quantizeSchwartzValue u)) = quantizeSchwartzValue q.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [← Symbol.sharp_eq_sum_sharpTerm_of_mixedDeriv_nil_eq_zero (fun β hβ x ξ ↦
      mixedDeriv_nil_coefficient_toSymbol_ofDifferentialSymbol_eq_zero m s v b hb hk
        (by rw [hβ]; norm_num) x ξ) hq,
    Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    quantizeSchwartzValue_ofDifferentialSymbol]
  simp only [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hw]

end ClassicalSymbol

end TauCeti
