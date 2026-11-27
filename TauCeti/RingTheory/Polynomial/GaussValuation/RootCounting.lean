/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.GaussValuation
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Counting roots of specified additive valuations

For a polynomial with integral coefficients, a weighted coefficient bounds the total
multiplicity of roots at any finite set of distinct real valuations bounded by the radius.
This is the counting input for selecting radii at which evaluation loses little against the
Gauss valuation.

## Provenance

`Polynomial.sum_card_roots_valuation_mul_le` adapts
`New.Selmer.sum_card_rootsOfValuation_mul_le` in
`src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC). The statement for arbitrary real additive valuations and
polynomials, using the existing multiplicative Gauss valuation, is new here.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1 (Gauss valuations).
-/

public section

open Finset

namespace Polynomial

variable {K : Type*} [CommRing K] [IsDomain K] {v : AddValuation K (WithTop ℝ)}

/-- For a polynomial with integral coefficients, the sum of the truncated positive
valuations of its roots is at most the cost of each weighted coefficient. Roots are counted
with multiplicity; roots of negative valuation contribute zero. -/
theorem sum_max_min_valuation_roots_le (g : K[X])
    (hcoeff : ∀ i, 0 ≤ v (g.coeff i)) {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℕ) :
    (g.roots.map fun a ↦ max 0 (min (ρ : WithTop ℝ) (v a))).sum ≤
      v (g.coeff d) + d • (ρ : WithTop ℝ) := by
  let w := v.toValuation
  let r : Multiplicative (WithTop ℝ)ᵒᵈ := .ofAdd (.toDual ρ)
  obtain ⟨q, hg, _, _⟩ := g.exists_prod_multiset_X_sub_C_mul
  have hformula (t : Multiplicative (WithTop ℝ)ᵒᵈ) :
      g.gaussValuation w t =
        (g.roots.map fun a ↦ max t (w a)).prod * q.gaussValuation w t := by
    conv_lhs => rw [← hg]
    rw [gaussValuation_mul, gaussValuation_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, gaussValuation_X_sub_C]
  have hzero : g.gaussValuation w 1 ≤ 1 :=
    (gaussValuation_le_iff w 1).2 fun i ↦ by rw [one_pow, mul_one]; exact hcoeff i
  have hmono : q.gaussValuation w r ≤ q.gaussValuation w 1 := by
    refine (gaussValuation_le_iff w r).2 fun i ↦ ?_
    have hr : r ≤ 1 := WithTop.coe_le_coe.2 hρ
    calc
      w (q.coeff i) * r ^ i ≤ w (q.coeff i) * 1 :=
        mul_le_mul' le_rfl (pow_le_one₀ zero_le hr)
      _ ≤ q.gaussValuation w 1 := by
        simpa only [one_pow, mul_one] using le_gaussValuation w 1 q i
  have hbase : 0 ≤ (g.roots.map fun a ↦ min 0 (v a)).sum +
      (q.gaussValuation w r).toAdd.ofDual := by
    rw [hformula 1] at hzero
    have H := (mul_le_mul' (le_refl ((g.roots.map fun a ↦ max 1 (w a)).prod)) hmono).trans hzero
    exact H
  have H : (g.roots.map fun a ↦ min (ρ : WithTop ℝ) (v a)).sum +
      (q.gaussValuation w r).toAdd.ofDual ≤ v (g.coeff d) + d • (ρ : WithTop ℝ) := by
    have H := le_gaussValuation w r g d
    rw [hformula r] at H
    exact H
  have hsplit : (g.roots.map fun a ↦ min (ρ : WithTop ℝ) (v a)).sum =
      (g.roots.map fun a ↦ min 0 (v a)).sum +
        (g.roots.map fun a ↦ max 0 (min (ρ : WithTop ℝ) (v a))).sum := by
    rw [← Multiset.sum_map_add]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    have H := min_add_max (0 : WithTop ℝ) (min (ρ : WithTop ℝ) (v a))
    rw [← min_assoc, min_eq_left (show (0 : WithTop ℝ) ≤ ρ by exact_mod_cast hρ),
      zero_add] at H
    exact H.symm
  rw [hsplit] at H
  have H' : ((g.roots.map fun a ↦ min 0 (v a)).sum +
      (q.gaussValuation w r).toAdd.ofDual) +
        (g.roots.map fun a ↦ max 0 (min (ρ : WithTop ℝ) (v a))).sum ≤
          v (g.coeff d) + d • (ρ : WithTop ℝ) := by
    simpa only [add_right_comm] using H
  exact (le_add_of_nonneg_left hbase).trans H'

/-- A weighted coefficient bounds the total multiplicity at distinct root
valuations at most `ρ`. No bound on the degree or the size of the set of radii is required. -/
theorem sum_card_roots_valuation_mul_le (g : K[X])
    (hcoeff : ∀ i, 0 ≤ v (g.coeff i)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (s : Finset ℝ) (hs : ∀ r ∈ s, r ≤ ρ) (d : ℕ) :
    (∑ r ∈ s, ((g.roots.filter fun a ↦ v a = r).card : ℝ) * r : ℝ) ≤
      v (g.coeff d) + d • (ρ : WithTop ℝ) := by
  classical
  have sum_radii_le_max_min (a : WithTop ℝ) :
      (∑ r ∈ s with a = ((r : ℝ) : WithTop ℝ), ((r : ℝ) : WithTop ℝ)) ≤
        max 0 (min (ρ : WithTop ℝ) a) := by
    classical
    obtain he | ⟨r, hr⟩ := (s.filter fun r ↦ a = ((r : ℝ) : WithTop ℝ)).eq_empty_or_nonempty
    · simp [he]
    obtain ⟨hrs, har⟩ := mem_filter.1 hr
    rw [sum_eq_single_of_mem r hr, har]
    · exact le_max_of_le_right (le_min (by exact_mod_cast hs r hrs) le_rfl)
    · intro r' hr' hne
      exact (hne (WithTop.coe_injective ((mem_filter.1 hr').2.symm.trans har))).elim
  have hcount (r : ℝ) :
      (g.roots.filter fun a ↦ v a = r).card • ((r : ℝ) : WithTop ℝ) =
        (g.roots.map fun a ↦ if v a = r then ((r : ℝ) : WithTop ℝ) else 0).sum := by
    induction g.roots using Multiset.induction_on with
    | empty => simp
    | cons a t ih => by_cases ha : v a = r <;> simp [ha, ← ih, add_nsmul, add_comm]
  calc
    ((∑ r ∈ s, ((g.roots.filter fun a ↦ v a = r).card : ℝ) * r : ℝ) : WithTop ℝ)
        = (g.roots.map fun a ↦
            ∑ r ∈ s with v a = ((r : ℝ) : WithTop ℝ), ((r : ℝ) : WithTop ℝ)).sum := by
          simp only [WithTop.coe_sum, ← nsmul_eq_mul, WithTop.coe_nsmul, hcount,
            sum_filter, Multiset.sum_map_sum]
    _ ≤ (g.roots.map fun a ↦ max 0 (min (ρ : WithTop ℝ) (v a))).sum :=
      Multiset.sum_map_le_sum_map _ _ fun a _ ↦ sum_radii_le_max_min (v a)
    _ ≤ v (g.coeff d) + d • (ρ : WithTop ℝ) :=
      g.sum_max_min_valuation_roots_le (v := v) hcoeff hρ d

end Polynomial
