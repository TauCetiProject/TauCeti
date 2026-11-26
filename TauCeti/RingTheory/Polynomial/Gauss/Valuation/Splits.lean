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
  rw [gaussValuation_eq_mul_prod_roots v p hp r, gaussValuation_eq_mul_prod_roots v p hp 1]
  have hsplit (t : Γ₀) : (p.roots.map fun α ↦ max t (v α)).prod =
      ((p.roots.filter fun α ↦ v α ≤ 1).map fun α ↦ max t (v α)).prod *
      ((p.roots.filter fun α ↦ ¬ v α ≤ 1).map fun α ↦ max t (v α)).prod := by
    rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  have hle : ((p.roots.filter fun α ↦ v α ≤ 1).map fun α ↦ max 1 (v α)).prod = 1 :=
    Multiset.prod_eq_one fun b hb ↦ by
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hb
      exact max_eq_left (Multiset.mem_filter.mp hα).2
  have hgt : ((p.roots.filter fun α ↦ ¬ v α ≤ 1).map fun α ↦ max r (v α)) =
      (p.roots.filter fun α ↦ ¬ v α ≤ 1).map fun α ↦ max 1 (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      have h1 : 1 < v α := lt_of_not_ge (Multiset.mem_filter.mp hα).2
      rw [max_eq_right (hr.trans h1.le), max_eq_right h1.le]
  rw [hsplit r, hsplit 1, hle, one_mul, hgt]
  ac_rfl

/-- If a split polynomial `p` satisfies `v (x - α) = v x` for every root `α` with `v α = v x`,
then `v (p.eval x)` equals the Gauss valuation `p.gaussValuation v (v x)`. -/
theorem valuation_eval_eq_gaussValuation_of_forall_roots_eq (v : Valuation R Γ₀)
    (p : R[X]) (hp : p.Splits) {x : R}
    (hroots : ∀ α ∈ p.roots, v α = v x → v (x - α) = v x) :
    v (p.eval x) = p.gaussValuation v (v x) := by
  have hmap : (p.roots.map fun α ↦ v (x - α)) = p.roots.map fun α ↦ max (v x) (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      rcases lt_trichotomy (v α) (v x) with hlt | heq | hgt
      · rw [v.map_sub_eq_of_lt_left hlt, max_eq_left hlt.le]
      · rw [hroots α hα heq, max_eq_left heq.le]
      · rw [v.map_sub_eq_of_lt_right hgt, max_eq_right hgt.le]
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
    gaussValuation_eq_mul_prod_roots v p hp (v x)]
  have hsplit (f : R → Γ₀) : (p.roots.map f).prod =
      ((p.roots.filter fun α ↦ v α = v x).map f).prod *
      ((p.roots.filter fun α ↦ ¬ v α = v x).map f).prod := by
    rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  have hne : ((p.roots.filter fun α ↦ ¬ v α = v x).map fun α ↦ v (x - α)) =
      (p.roots.filter fun α ↦ ¬ v α = v x).map fun α ↦ max (v x) (v α) :=
    Multiset.map_congr rfl fun α hα ↦ by
      rcases lt_or_gt_of_ne (Multiset.mem_filter.mp hα).2 with hlt | hgt
      · rw [v.map_sub_eq_of_lt_left hlt, max_eq_left hlt.le]
      · rw [v.map_sub_eq_of_lt_right hgt, max_eq_right hgt.le]
  have heq : ((p.roots.filter fun α ↦ v α = v x).map fun α ↦ v (x - α)).prod =
      ((p.roots.filter fun α ↦ v α = v x).map fun α ↦ max (v x) (v α)).prod *
      ((p.roots.filter fun α ↦ v α = v x).map fun α ↦ v (x - α) / v x).prod := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun α hα ↦ ?_
    have hα' : v α = v x := (Multiset.mem_filter.mp hα).2
    rcases eq_or_ne (v x) 0 with hx0 | hx0
    · have hsub : v (x - α) = 0 := nonpos_iff_eq_zero.mp <|
        (v.map_sub x α).trans (by simp [hx0, hα'])
      simp [hx0, hα', hsub]
    · rw [max_eq_left hα'.le, mul_div_cancel₀ _ hx0]
  simp only [Function.comp_def]
  rw [hsplit (fun α ↦ v (x - α)), hsplit (fun α ↦ max (v x) (v α)), hne, heq]
  ac_rfl

end Group

end Polynomial
