/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.RingTheory.Polynomial.Gauss.Valuation.Basic

/-!
# Gauss valuation of split polynomials

For a split polynomial `p` over an integral domain `R` with valuation `v : Valuation R Γ₀`, the
Gauss valuation at radius `r` factors as `v p.leadingCoeff` times the product of `max r (v α)` over
all roots `α` of `p`. Consequently, evaluating `p` at any `x` whose valuation differs from every
root valuation attains `p.gaussValuation v (v x)`.

## Main results

* `Polynomial.gaussValuation_eq_mul_prod_roots`: root-product formula for the Gauss valuation of a
  split polynomial.
* `Polynomial.valuation_eval_eq_gaussValuation_of_forall_roots_ne`: sphere-evaluation equality
  away from root valuations.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.
* L. Alpöge, `New.Selmer.gaussVal_eq_mul_prod_roots` in
  `src/Lib/General/NumberTheory/GaussValuation.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

namespace Polynomial

section CommRing

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

/-- If a split polynomial `p` has no root of valuation `v x`, then `v (p.eval x)` equals the Gauss
valuation `p.gaussValuation v (v x)`. -/
theorem valuation_eval_eq_gaussValuation_of_forall_roots_ne (v : Valuation R Γ₀)
    (p : R[X]) (hp : p.Splits) {x : R} (hroots : ∀ α ∈ p.roots, v α ≠ v x) :
    v (p.eval x) = p.gaussValuation v (v x) := by
  have hmap : (p.roots.map fun α ↦ v (x - α)) = p.roots.map fun α ↦ max (v x) (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      rcases lt_or_gt_of_ne (hroots α hα) with hlt | hgt
      · rw [v.map_sub_eq_of_lt_left hlt, max_eq_left hlt.le]
      · rw [v.map_sub_eq_of_lt_right hgt, max_eq_right hgt.le]
  rw [hp.eval_eq_prod_roots x, gaussValuation_eq_mul_prod_roots v p hp (v x)]
  simp only [map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def, hmap]

end CommRing

end Polynomial
