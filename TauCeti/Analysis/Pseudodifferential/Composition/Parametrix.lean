/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Elliptic

/-!
# Formal left parametrices in the symbol calculus

Let `a` be a symbol of order `m` on `ℝⁿ`. A *formal left parametrix* of `a` is a symbol `b` of
order `-m` whose formal composition with `a` is the identity,

`1 ∼ ∑ₖ sharpTerm b a k`,

meaning that `1 - ∑_{k < N} sharpTerm b a k` is a symbol of order `-N` for every `N`.

* `TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial`: **the local parametrix modulo smoothing
  symbols.** For a smooth function `ψ` of the position, `q(x, ξ) = ψ(x) b(x, ξ)` and a symbol `p`
  with compact spatial support which agrees with `a` near the support of `ψ`, the composition
  symbol `q # p` is `ψ(x)` up to a smoothing symbol.
* `TauCeti.Symbol.isAsymptoticSum_sharpTerm_of_spatialDeriv_eq_zero`: for a symbol that does not
  depend on the position, a pointwise left inverse modulo smoothing symbols is a formal left
  parametrix.
* `TauCeti.Symbol.exists_isAsymptoticSum_sharpTerm_of_spatialDeriv_eq_zero`: every symbol that does
  not depend on the position and is elliptic above some radius, such as the symbol of a
  differential operator with constant coefficients, has a formal left parametrix.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Finset Set
open scoped Topology ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The local parametrix modulo smoothing symbols -/

section Parametrix

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **The local parametrix modulo smoothing symbols.** Let `b` be a formal left parametrix of the
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

/-! ### Formal parametrices of symbols independent of the position -/

section Constant

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- For a symbol `a` that does not depend on the position, a symbol `b` of order `-m` is a formal
left parametrix of `a` as soon as it is a pointwise left inverse modulo smoothing symbols. -/
theorem isAsymptoticSum_sharpTerm_of_spatialDeriv_eq_zero {a : Symbol n V W m}
    (ha : ∀ j, spatialDeriv j a = 0) {b : Symbol n W V (-m)}
    (hb : (b.comp a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing) :
    IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a) := by
  refine isAsymptoticSum_iff.2 fun N ↦ ?_
  rcases N with _ | N
  · exact ⟨inclusion (by simp) (const (.id ℂ V)), by simp⟩
  obtain ⟨r, hr⟩ := isSmoothing_iff.1 hb (-m + m - (N + 1 : ℕ))
  refine ⟨-r, ?_⟩
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ ↦ by
    rw [sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero ha, coefficient_zero], zero_add,
    coefficient_neg, hr]
  funext p
  simp

/-- **Elliptic symbols independent of the position have formal left parametrices.** A symbol of
order `m` that does not depend on the position and is elliptic above some radius, between
complete spaces, has a formal left parametrix of order `-m`, `1 ∼ ∑ₖ sharpTerm b a k`. -/
theorem exists_isAsymptoticSum_sharpTerm_of_spatialDeriv_eq_zero [CompleteSpace V]
    {a : Symbol n V W m} (ha : ∀ j, spatialDeriv j a = 0) {R : ℝ} (hR : a.IsEllipticAbove R) :
    ∃ b : Symbol n W V (-m), IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a) := by
  obtain ⟨b, R', hb⟩ := exists_isEllipticAbove_iff.1 ⟨R, hR⟩
  refine ⟨b, isAsymptoticSum_sharpTerm_of_spatialDeriv_eq_zero ha
    (isSmoothing_of_coefficient_eq_zero R' fun x ξ hξ ↦ ?_)⟩
  simp [(hb x ξ hξ).1]

end Constant

end Symbol

end TauCeti
