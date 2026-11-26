/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic
import TauCeti.Data.Multiset.Filter
import TauCeti.RingTheory.Valuation.Basic

/-!
# Gauss valuation of split polynomials

For a split polynomial `p` over an integral domain `R` with valuation `v : Valuation R Γ₀`, the
Gauss valuation at radius `r` factors as `v p.leadingCoeff` times the product of `max r (v α)` over
all roots `α` of `p`. From this we derive:
- the comparison with radius `1` via integral roots (`r ≤ 1`),
- evaluation equality `v (p.eval x) = p.gaussValuation v (v x)` whenever no root of valuation `v x`
  causes cancellation, and
- the exact quotient formula over a value group quantifying the loss from roots of valuation `v x`.

## Main results

* `Polynomial.gaussValuation_eq_mul_prod_roots`: root-product formula for the Gauss valuation of a
  split polynomial.
* `Polynomial.gaussValuation_eq_gaussValuation_one_mul_prod_roots_le_one`: comparison with radius
  `1` via roots of valuation at most `1`.
* `Polynomial.valuation_eval_eq_gaussValuation_of_forall_roots_eq`: sphere-evaluation equality when
  roots of valuation `v x` do not cancel with `x`.
* `Polynomial.valuation_eval_eq_gaussValuation_mul_prod_roots_eq`: exact evaluation formula over a
  value group in terms of the tied roots `v α = v x`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.
* L. Alpöge, `New.Selmer.gaussVal_eq_mul_prod_roots` in
  `src/Lib/General/NumberTheory/GaussValuation.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

namespace Polynomial

section Monoid

variable {R Γ₀ : Type*} [CommRing R] [IsDomain R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- For a split polynomial `p`, the Gauss valuation at radius `r` is the valuation of the leading
coefficient times the product of `max r (v α)` over all roots `α` of `p`. -/
theorem gaussValuation_eq_mul_prod_roots (v : Valuation R Γ₀) (p : R[X])
    (hp : p.Splits) (r : Γ₀) :
    p.gaussValuation v r = v p.leadingCoeff * (p.roots.map fun α ↦ max r (v α)).prod := by
  have hfac : p.gaussValuation v r =
      v.gauss r (C p.leadingCoeff * (p.roots.map fun α ↦ X - C α).prod) := by
    rw [Valuation.gauss_apply]
    exact congrArg (fun q ↦ q.gaussValuation v r) hp.eq_prod_roots
  rw [hfac, map_mul, map_multiset_prod, Multiset.map_map]
  simp

/-- For a split polynomial `p` and radius `r ≤ 1`, the Gauss valuation at `r` equals the radius-`1`
Gauss valuation times the product of `max r (v α)` over all roots `α` with `v α ≤ 1`. -/
theorem gaussValuation_eq_gaussValuation_one_mul_prod_roots_le_one (v : Valuation R Γ₀) (p : R[X])
    (hp : p.Splits) {r : Γ₀} (hr : r ≤ 1) :
    p.gaussValuation v r = p.gaussValuation v 1 *
      ((p.roots.filter fun α ↦ v α ≤ 1).map fun α ↦ max r (v α)).prod := by
  classical
  rw [gaussValuation_eq_mul_prod_roots v p hp r, gaussValuation_eq_mul_prod_roots v p hp 1,
    Multiset.prod_map_filter, mul_assoc, ← Multiset.prod_map_mul]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ ↦ ?_)
  by_cases hα : v α ≤ 1
  · simp only [hα, ↓reduceIte, max_eq_left hα, one_mul]
  · have h1 : 1 < v α := lt_of_not_ge hα
    simp only [hα, ↓reduceIte, mul_one, max_eq_right (hr.trans h1.le), max_eq_right h1.le]

/-- If a split polynomial `p` satisfies `v (x - α) = v x` for every root `α` with `v α = v x`,
then `v (p.eval x)` equals the Gauss valuation `p.gaussValuation v (v x)`. -/
theorem valuation_eval_eq_gaussValuation_of_forall_roots_eq (v : Valuation R Γ₀)
    (p : R[X]) (hp : p.Splits) {x : R}
    (hroots : ∀ α ∈ p.roots, v α = v x → v (x - α) = v x) :
    v (p.eval x) = p.gaussValuation v (v x) := by
  have hmap : (p.roots.map fun α ↦ v (x - α)) = p.roots.map fun α ↦ max (v x) (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      rcases eq_or_ne (v α) (v x) with heq | hne
      · rw [hroots α hα heq, max_eq_left heq.le]
      · exact v.map_sub_of_distinct_val hne.symm
  rw [hp.eval_eq_prod_roots x, gaussValuation_eq_mul_prod_roots v p hp (v x)]
  simp only [map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def, hmap]

end Monoid

section Group

variable {R Γ₀ : Type*} [CommRing R] [IsDomain R] [LinearOrderedCommGroupWithZero Γ₀]

/-- For a split polynomial `p` and any `x`, `v (p.eval x)` equals `p.gaussValuation v (v x)` times
the product of `v (x - α) / v x` over all roots `α` with `v α = v x`. -/
theorem valuation_eval_eq_gaussValuation_mul_prod_roots_eq (v : Valuation R Γ₀) (p : R[X])
    (hp : p.Splits) (x : R) :
    v (p.eval x) = p.gaussValuation v (v x) *
      ((p.roots.filter fun α ↦ v α = v x).map fun α ↦ v (x - α) / v x).prod := by
  classical
  rw [hp.eval_eq_prod_roots x, map_mul, map_multiset_prod, Multiset.map_map,
    gaussValuation_eq_mul_prod_roots v p hp (v x), Multiset.prod_map_filter, mul_assoc,
    ← Multiset.prod_map_mul]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ ↦ ?_)
  simp only [Function.comp_def]
  by_cases hα : v α = v x
  · simp only [hα, ↓reduceIte]
    rcases eq_or_ne (v x) 0 with hx0 | hx0
    · rw [v.map_sub_of_left_eq_zero hx0, hα, hx0]
      simp
    · rw [max_self, mul_div_cancel₀ _ hx0]
  · simp only [hα, ↓reduceIte, mul_one, v.map_sub_of_distinct_val (Ne.symm hα)]

end Group

end Polynomial
