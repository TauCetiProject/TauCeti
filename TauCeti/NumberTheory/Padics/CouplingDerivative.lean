/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import TauCeti.NumberTheory.Padics.CouplingNormalForm

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Monoid
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.RingTheory.MvPowerSeries.NormCoeff

/-!
# Derivatives of the coupling series modulo `p`

Let `Γ_e = ∑_{(τ, i)} z_(τ,i) ^ p ^ e * z_(pr_e τ, i)` be the couplings and
`Ξ_λ = ∑_{e ∈ S} ∑_{j ≥ 0} λ_{e j} Γ_e ^ p ^ j` the coupling series of
`TauCeti/NumberTheory/Padics/CouplingNormalForm.lean`. The derivative of `Γ_e` in `z_y` is
`p ^ e` times a polynomial plus the *partner power sum*
`P_{e,y} = ∑_{x : (pr_e x₁, x₂) = y} z_x ^ p ^ e` (`MvPowerSeries.pderiv_coupling`). The
derivative of `Γ_e ^ p ^ j` carries a factor `p ^ j`, so modulo `p` only the terms with `j = 0` and
their partner power sums survive once `e ≥ 1`.

Over an ultrametric normed field `K`, with `‖λ_{e j}‖ ≤ 1` and `0 ∉ S`:

* `MvPowerSeries.norm_coeff_pderiv_couplingSum_sub_le`: the coefficients of
  `∂Ξ_λ/∂z_y - ∑_{e ∈ S} λ_{e 0} P_{e,y}` have norm at most `‖p‖`;
* `MvPowerSeries.exists_eq_single_of_norm_lt_norm_coeff_pderiv`: a coefficient of `∂Ξ_λ/∂z_y` of
  norm above `‖p‖` is at a monomial `z_x ^ p ^ e` with `e ∈ S` and `y = (pr_e x₁, x₂)`;
* `MvPowerSeries.norm_coeff_pderiv_couplingSum_sub_le_of_mem`: for `e ∈ S`, the coefficient of
  `z_x ^ p ^ e` in `∂Ξ_λ/∂z_(pr_e x₁, x₂)` is `λ_{e 0}` up to norm `‖p‖`.

When `‖p‖ < 1`, as for `K` a normed `ℚ_[p]`-algebra, these are the statements modulo `p` and modulo
the maximal ideal of the valuation ring.

## Provenance

Adapted from `New.partnerPowerSum`, `New.dvd_pderiv_couplingSum_sub`,
`New.residue_coeff_pderiv_couplingSum` and `New.exists_eq_single_of_residue_coeff_pderiv_ne_zero`
in `src/New/Derivatives/Divisibility/NormalForm.lean` of the Lean proof of the Riemann hypothesis
by Levent Alpöge with Claude, as published under Apache 2.0 at
https://github.com/leanprover-community/riemann-hypothesis (commit `3ad0b4b58709`). There the
coefficients are in the valuation ring of `ℂ_[p]` and the statements are divisibility by `p` and
congruences in the residue field; here they are norm bounds over any ultrametric normed field.
-/

public section

open MvPowerSeries Finsupp WithPiTopology
open scoped MvPowerSeries.WithPiTopology

namespace MvPowerSeries

section CommRing

variable (R : Type*) [CommRing R] {Φ c : Type*} [Fintype Φ] [Fintype c] [DecidableEq Φ]
  [DecidableEq c]

/-- The partner power sum `P_{e,y} = ∑_{x : (pr_e x₁, x₂) = y} z_x ^ p ^ e`: the part of the
derivative of the coupling `Γ_e` in `z_y` that does not carry the factor `p ^ e`. -/
noncomputable def partnerPowerSum (p : ℕ) (pr : ℕ → Φ → Φ) (e : ℕ) (y : Φ × c) :
    MvPowerSeries (Φ × c) R :=
  ∑ x with (pr e x.1, x.2) = y, X x ^ p ^ e

variable {R} {p : ℕ} {pr : ℕ → Φ → Φ}

/-- The derivative of the coupling `Γ_e` in `z_y` is `p ^ e` times a polynomial plus the partner
power sum `P_{e,y}`. -/
theorem pderiv_coupling (e : ℕ) (y : Φ × c) :
    pderiv y (coupling p pr e : MvPowerSeries (Φ × c) R) = p ^ e • (∑ x : Φ × c,
      X x ^ (p ^ e - 1) * pderiv y (X x) * X (pr e x.1, x.2)) + partnerPowerSum R p pr e y := by
  rw [coupling_def p pr e, partnerPowerSum, map_sum, Finset.sum_filter, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Derivation.leibniz, Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  split_ifs <;> simp [smul_eq_mul, nsmul_eq_mul, mul_comm, mul_left_comm, add_comm]

/-- The partner power sum `P_{e,y}` has order at least `p ^ e`. -/
theorem le_order_partnerPowerSum (e : ℕ) (y : Φ × c) :
    ((p ^ e : ℕ) : ℕ∞) ≤ (partnerPowerSum R p pr e y).order := by
  refine le_order fun d hd ↦ ?_
  rw [partnerPowerSum, map_sum]
  exact Finset.sum_eq_zero fun x _ ↦ coeff_of_lt_order
    (hd.trans_le (le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_X x)))

/-- The coefficient of the partner power sum `P_{e,y}` at `d`: the number of `x` with
`(pr_e x₁, x₂) = y` and `d = single x (p ^ e)`. -/
theorem coeff_partnerPowerSum (e : ℕ) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    coeff d (partnerPowerSum R p pr e y) =
      ∑ x with (pr e x.1, x.2) = y, if d = single x (p ^ e) then 1 else 0 := by
  simp [partnerPowerSum, map_sum, coeff_X_pow]

variable [TopologicalSpace R] {S : Set ℕ}

/-- For `1 < p`, the series `∑_{e ∈ S} λ_e P_{e,y}` converges: its coefficient at `d` only sees the
terms with `e ≤ d.degree`, as `P_{e,y}` has order at least `p ^ e > e`. -/
theorem summable_smul_partnerPowerSum (hp : 1 < p) (l : ℕ → R) (y : Φ × c) :
    Summable fun e : S ↦ l e • partnerPowerSum R p pr e y := by
  classical
  refine summable_iff_summable_coeff.2 fun d ↦ summable_of_ne_finset_zero
    (s := (Finset.range (d.degree + 1)).subtype (· ∈ S)) fun e he ↦ ?_
  have h_lt : d.degree < p ^ (e : ℕ) := by
    have := Nat.lt_pow_self (n := (e : ℕ)) hp
    simp only [Finset.mem_subtype, Finset.mem_range, not_lt] at he
    omega
  rw [coeff_smul, coeff_of_lt_order ((Nat.cast_lt.2 h_lt).trans_le
    (le_order_partnerPowerSum (e : ℕ) y)), mul_zero]

end CommRing

section Normed

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {Φ c : Type*} [Fintype Φ] [Fintype c]
  {p : ℕ} {pr : ℕ → Φ → Φ} {S : Set ℕ} {l : ℕ → ℕ → K}

/-- The coefficients of the coupling `Γ_e` have norm at most `1`. -/
theorem norm_coeff_coupling_le_one (e : ℕ) (d : Φ × c →₀ ℕ) :
    ‖coeff d (coupling p pr e : MvPowerSeries (Φ × c) K)‖ ≤ 1 := by
  rw [coupling_def p pr e, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ ↦
    (norm_coeff_mul_le_mul (norm_coeff_pow_le_one (norm_coeff_X_le_one x) _)
      (norm_coeff_X_le_one _) d).trans_eq (one_mul 1)

variable [DecidableEq Φ] [DecidableEq c]

/-- For `e ≠ 0`, the coefficients of `∂Γ_e/∂z_y - P_{e,y}` have norm at most `‖p‖`. -/
theorem norm_coeff_pderiv_coupling_sub_le {e : ℕ} (he : e ≠ 0) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    ‖coeff d (pderiv y (coupling p pr e : MvPowerSeries (Φ × c) K) - partnerPowerSum K p pr e y)‖ ≤
      ‖(p : K)‖ := by
  have hQ (t : Φ × c →₀ ℕ) : ‖coeff t (∑ x : Φ × c,
      X x ^ (p ^ e - 1) * pderiv y (X x) * X (pr e x.1, x.2) : MvPowerSeries (Φ × c) K)‖ ≤ 1 := by
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ ↦ ?_
    refine (norm_coeff_mul_le_mul (fun t ↦ (norm_coeff_mul_le_mul
      (norm_coeff_pow_le_one (norm_coeff_X_le_one x) _)
      (norm_coeff_pderiv_le (norm_coeff_X_le_one x) y) t).trans_eq (one_mul 1))
      (norm_coeff_X_le_one _) t).trans_eq (one_mul 1)
  have hp₁ : ‖(p : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K p
  rw [pderiv_coupling, add_sub_cancel_right, map_nsmul, nsmul_eq_mul, norm_mul, Nat.cast_pow,
    norm_pow]
  exact (mul_le_mul (pow_le_of_le_one (norm_nonneg _) hp₁ he) (hQ d) (norm_nonneg _)
    (norm_nonneg _)).trans_eq (mul_one _)

/-- For `e ≠ 0` and `‖λ_j‖ ≤ 1`, the coefficients of the derivative in `z_y` of the term
`λ_j Γ_e ^ p ^ j`, minus `λ_0 P_{e,y}` when `j = 0`, have norm at most `‖p‖`. -/
theorem norm_coeff_pderiv_smul_coupling_pow_sub_le {e : ℕ} (he : e ≠ 0) {a : ℕ → K}
    (ha : ∀ j, ‖a j‖ ≤ 1) (j : ℕ) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    ‖coeff d (pderiv y (a j • (coupling p pr e : MvPowerSeries (Φ × c) K) ^ p ^ j) -
      if j = 0 then a 0 • partnerPowerSum K p pr e y else 0)‖ ≤ ‖(p : K)‖ := by
  have hp₁ : ‖(p : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K p
  have hΓ := norm_coeff_coupling_le_one (K := K) (c := c) (p := p) (pr := pr) e
  rw [Derivation.map_smul]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [ite_eq_left rfl, pow_zero, pow_one, ← smul_sub, coeff_smul, norm_mul]
    exact (mul_le_mul (ha 0) (norm_coeff_pderiv_coupling_sub_le he y d) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul _)
  · rw [ite_eq_right hj.ne', sub_zero, Derivation.leibniz_pow, coeff_smul, map_nsmul, nsmul_eq_mul,
      smul_eq_mul, norm_mul, norm_mul, Nat.cast_pow, norm_pow]
    have h_rest := norm_coeff_mul_le_mul (norm_coeff_pow_le_one hΓ (p ^ j - 1))
      (norm_coeff_pderiv_le hΓ y) d
    refine (mul_le_mul (ha j) (mul_le_mul (pow_le_of_le_one (norm_nonneg _) hp₁
      hj.ne') h_rest (norm_nonneg _) (norm_nonneg _)) (by positivity)
      zero_le_one).trans_eq (by ring)

/-- **The derivative of the coupling series modulo `p`.** If `0 ∉ S`, `1 < p` and `‖λ_{e j}‖ ≤ 1`,
the coefficients of `∂Ξ_λ/∂z_y - ∑_{e ∈ S} λ_{e 0} P_{e,y}` have norm at most `‖p‖`. -/
theorem norm_coeff_pderiv_couplingSum_sub_le (hp : 1 < p) (hS : 0 ∉ S)
    (hl : ∀ e j, ‖l e j‖ ≤ 1) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    ‖coeff d (pderiv y (couplingSum p S pr l) -
      ∑' e : S, l e 0 • partnerPowerSum K p pr e y)‖ ≤ ‖(p : K)‖ := by
  have h_deriv := (hasSum_couplingSum (c := c) (S := S) (pr := pr) (l := l) hp).map (pderiv y)
    (WithPiTopology.continuous_pderiv y)
  have h_inj : Function.Injective fun e : S ↦ (e, 0) := fun a b h ↦ (Prod.ext_iff.1 h).1
  have h_partner : HasSum (fun x : S × ℕ ↦ if x.2 = 0 then l x.1 0 • partnerPowerSum K p pr x.1 y
      else 0) (∑' e : S, l e 0 • partnerPowerSum K p pr e y) := by
    refine (h_inj.hasSum_iff fun x hx ↦ ?_).1 ?_
    · exact ite_eq_right fun h0 ↦ hx ⟨x.1, Prod.ext rfl h0.symm⟩
    · simpa [Function.comp_def] using
        (summable_smul_partnerPowerSum hp (fun e ↦ l e 0) y).hasSum
  rw [← (WithPiTopology.hasSum_iff_hasSum_coeff.1 (h_deriv.sub h_partner) d).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
  rintro ⟨⟨e, he⟩, j⟩
  simpa only [Function.comp_apply] using norm_coeff_pderiv_smul_coupling_pow_sub_le (p := p)
    (pr := pr) (fun h ↦ hS (h ▸ he)) (hl e) j y d

omit [IsUltrametricDist K] in
/-- The coefficient of `∑_{e ∈ S} λ_{e 0} P_{e,y}` at `d`. -/
theorem coeff_tsum_smul_partnerPowerSum (hp : 1 < p) (y : Φ × c) (d : Φ × c →₀ ℕ) :
    coeff d (∑' e : S, l e 0 • partnerPowerSum K p pr e y) =
      ∑' e : S, l e 0 * coeff d (partnerPowerSum K p pr e y) := by
  simpa [coeff_smul] using ((WithPiTopology.hasSum_iff_hasSum_coeff.1
    (summable_smul_partnerPowerSum hp (fun e ↦ l e 0) y).hasSum d).tsum_eq).symm

omit [DecidableEq Φ] [DecidableEq c] in
/-- **The monomials of the derivative modulo `p`.** If `0 ∉ S`, `1 < p` and `‖λ_{e j}‖ ≤ 1`, a
coefficient of `∂Ξ_λ/∂z_y` of norm above `‖p‖` is at a monomial `z_x ^ p ^ e` with `e ∈ S` and
`y = (pr_e x₁, x₂)`. -/
theorem exists_eq_single_of_norm_lt_norm_coeff_pderiv (hp : 1 < p) (hS : 0 ∉ S)
    (hl : ∀ e j, ‖l e j‖ ≤ 1) {y : Φ × c} {d : Φ × c →₀ ℕ}
    (hd : ‖(p : K)‖ < ‖coeff d (pderiv y (couplingSum p S pr l))‖) :
    ∃ e ∈ S, ∃ x : Φ × c, (pr e x.1, x.2) = y ∧ d = single x (p ^ e) := by
  classical
  by_contra h
  push Not at h
  have h_zero : coeff d (∑' e : S, l e 0 • partnerPowerSum K p pr e y) = 0 := by
    rw [coeff_tsum_smul_partnerPowerSum hp]
    refine (tsum_congr fun e ↦ ?_).trans tsum_zero
    rw [coeff_partnerPowerSum, Finset.sum_eq_zero fun x hx ↦
      ite_eq_right (h e e.property x (Finset.mem_filter.1 hx).2), mul_zero]
  have := norm_coeff_pderiv_couplingSum_sub_le (pr := pr) hp hS hl y d
  rw [map_sub, h_zero, sub_zero] at this
  exact this.not_gt hd

omit [DecidableEq Φ] [DecidableEq c] in
/-- **The leading coefficients of the derivative modulo `p`.** If `0 ∉ S`, `1 < p`,
`‖λ_{e j}‖ ≤ 1` and `e ∈ S`, the coefficient of `z_x ^ p ^ e` in `∂Ξ_λ/∂z_(pr_e x₁, x₂)` is
`λ_{e 0}` up to norm `‖p‖`. -/
theorem norm_coeff_pderiv_couplingSum_sub_le_of_mem (hp : 1 < p) (hS : 0 ∉ S)
    (hl : ∀ e j, ‖l e j‖ ≤ 1) {e : ℕ} (he : e ∈ S) (x : Φ × c) :
    ‖coeff (single x (p ^ e)) (pderiv (pr e x.1, x.2) (couplingSum p S pr l)) - l e 0‖ ≤
      ‖(p : K)‖ := by
  classical
  have h_single {e' : ℕ} {x' : Φ × c} :
      single x (p ^ e) = single x' (p ^ e') ↔ x = x' ∧ e = e' := by
    rw [single_eq_single_iff]
    have hp₀ : p ≠ 0 := by omega
    simp [hp₀, (Nat.pow_right_injective hp).eq_iff]
  have h_coeff : coeff (single x (p ^ e))
      (∑' e' : S, l e' 0 • partnerPowerSum K p pr e' (pr e x.1, x.2)) = l e 0 := by
    rw [coeff_tsum_smul_partnerPowerSum hp, tsum_eq_single ⟨e, he⟩ fun e' he' ↦ ?_]
    · rw [coeff_partnerPowerSum, Finset.sum_eq_single_of_mem x (by simp) fun x' _ hx' ↦
        ite_eq_right fun h ↦ hx' (h_single.1 h).1.symm, ite_eq_left rfl, mul_one]
    · rw [coeff_partnerPowerSum, Finset.sum_eq_zero fun x' _ ↦
        ite_eq_right fun h ↦ he' (Subtype.ext (h_single.1 h).2.symm), mul_zero]
  have := norm_coeff_pderiv_couplingSum_sub_le (pr := pr) hp hS hl (pr e x.1, x.2)
    (single x (p ^ e))
  rwa [map_sub, h_coeff] at this

end Normed

end MvPowerSeries
