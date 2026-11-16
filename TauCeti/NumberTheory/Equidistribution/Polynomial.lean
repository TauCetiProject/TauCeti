/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Equidistribution.VanDerCorput
import Mathlib.Data.Nat.Choose.Sum
import TauCeti.Analysis.Fourier.Monomial

/-!
# Linear and polynomial equidistribution on the unit torus

This file proves the classical equidistribution theorems for linear and polynomial orbits in the
unit torus `UnitAddTorus d = (ℝ / ℤ)^d`:

* Linear equidistribution on `ℕ` (`TauCeti.linear_equidistribution_tfae`) and on `ℤ`
  (`TauCeti.linear_equidistribution_int_tfae`): `n ↦ n • α + β` is equidistributed (equivalently
  totally equidistributed) for Haar probability if and only if `α` is irrational
  (`TauCeti.TorusIrrational α`).
* Weyl's polynomial equidistribution theorem (`TauCeti.weyl_polynomial`): if `s ≥ 1` and the
  leading coefficient `α s` is irrational, then `n ↦ ∑ j ≤ s, n^j • α j` is equidistributed for
  Haar probability, proved by induction on `s` via van der Corput's difference theorem.
* The full polynomial equidistribution criterion (`TauCeti.polynomial_equidistribution_tfae`,
  `TauCeti.polynomial_equidistribution_iff`, `TauCeti.polynomial_total_equidistribution_iff`):
  equidistribution and total equidistribution on `ℕ` and `ℤ` of `n ↦ ∑ j ≤ s, n^j • α j` are
  all equivalent to the absence of a nonzero integer frequency `k` annihilating all nonconstant
  coefficients `α 1, …, α s`.

## Main results

* `TauCeti.linear_equidistribution_tfae`: equivalence of equidistribution, total equidistribution,
  and irrationality for `n ↦ n • α + β` on `ℕ`.
* `TauCeti.linear_equidistribution_int_tfae`: two-sided integer-indexed counterpart on `ℤ`.
* `TauCeti.weyl_polynomial`: Weyl's theorem for polynomials with irrational leading coefficient.
* `TauCeti.polynomial_equidistribution_tfae`, `TauCeti.polynomial_equidistribution_iff`,
  `TauCeti.polynomial_total_equidistribution_iff`: full characterization of polynomial
  equidistribution on `UnitAddTorus d`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Corollary 1.1.9, Exercises 1.1.5 and 1.1.6).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Topology

namespace TauCeti

section Linear

variable {d : Type*} [Fintype d]

/-- A sequence along which a nonzero Fourier character `mFourier k` is constant cannot be
equidistributed for Haar probability on `UnitAddTorus d`. -/
private theorem not_asympEquidistributed_of_mFourier_const {x : ℕ → UnitAddTorus d}
    (hx : AsympEquidistributed x volume.toProbabilityMeasure) {k : d → ℤ} (hk : k ≠ 0)
    (y : UnitAddTorus d) (hconst : ∀ n, UnitAddTorus.mFourier k (x n) = UnitAddTorus.mFourier k y) :
    False := by
  have htend := (weyl_criterion x).1 hx k hk
  have havg : (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (n + 1), UnitAddTorus.mFourier k (x i)) =
      fun _ ↦ UnitAddTorus.mFourier k y := by
    funext n
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), one_mul]
  rw [havg] at htend
  have hzero : UnitAddTorus.mFourier k y = 0 := tendsto_nhds_unique tendsto_const_nhds htend
  have hnorm := UnitAddTorus.norm_mFourier_apply k y
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- If `α` is irrational on `UnitAddTorus d`, then the linear orbit `n ↦ n • α + β` is
equidistributed for Haar probability. -/
private theorem asympEquidistributed_linear_of_torusIrrational {α : UnitAddTorus d}
    (hα : TorusIrrational α) (β : UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure := by
  rw [weyl_criterion]
  intro k hk
  set ζ : ℂ := UnitAddTorus.mFourier k α
  have hζ_ne : ζ ≠ 1 := (torusIrrational_iff_mFourier α).1 hα k hk
  have hζ_norm : ‖ζ‖ = 1 := UnitAddTorus.norm_mFourier_apply k α
  have hterm (i : ℕ) : UnitAddTorus.mFourier k (i • α + β) = UnitAddTorus.mFourier k β * ζ ^ i := by
    rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, mul_comm]
  simp_rw [hterm, ← Finset.mul_sum]
  have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * (2 / ‖ζ - 1‖)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).mul_const
        (2 / ‖ζ - 1‖)
  refine squeeze_zero_norm (fun n ↦ ?_) hbound
  rw [geom_sum_eq hζ_ne, norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
    UnitAddTorus.norm_mFourier_apply, one_mul, norm_div]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖ζ ^ (n + 1) - 1‖ ≤ ‖ζ ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hζ_norm, one_pow, norm_one]; norm_num

/-- **Linear equidistribution on `UnitAddTorus d` (over `ℕ`).** Equidistribution, total
equidistribution, and irrationality of the step `α` are equivalent for `n ↦ n • α + β`. -/
theorem linear_equidistribution_tfae (α β : UnitAddTorus d) :
    List.TFAE [AsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := by
    intro hα
    rw [totallyAsympEquidistributed_def]
    intro q r hq
    have hrew : (fun n : ℕ ↦ (q * n + r) • α + β) = fun n : ℕ ↦ n • (q • α) + (r • α + β) := by
      funext n
      rw [add_smul, mul_comm q n, mul_smul, add_assoc]
    rw [hrew]
    exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') (r • α + β)
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 3 := by
    intro h
    rw [torusIrrational_iff_mFourier]
    intro k hk h1
    refine not_asympEquidistributed_of_mFourier_const h hk β fun i ↦ ?_
    rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, h1, one_pow, one_mul]
  tfae_finish

/-- **Linear equidistribution on `UnitAddTorus d` (over `ℤ`).** Bilateral equidistribution, total
bilateral equidistribution, and irrationality of the step `α` are equivalent for
`n ↦ n • α + β`. -/
theorem linear_equidistribution_int_tfae (α β : UnitAddTorus d) :
    List.TFAE [AsympEquidistributedInt (fun n : ℤ ↦ n • α + β) volume.toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ n • α + β) volume.toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := by
    intro hα
    rw [totallyAsympEquidistributedInt_def]
    intro q hq r
    rw [asympEquidistributedInt_def]
    constructor
    · have hpos : (fun n : ℕ ↦ ((q : ℤ) * ((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • (q • α) + (((q : ℤ) + r) • α + β) := by
        funext n
        rw [mul_add, mul_one, add_assoc, add_smul, add_assoc, mul_comm (q : ℤ) (n : ℤ),
          mul_zsmul, natCast_zsmul, natCast_zsmul]
      rw [hpos]
      exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') _
    · have hneg : (fun n : ℕ ↦ ((q : ℤ) * (-((n : ℤ) + 1)) + r) • α + β) =
          fun n : ℕ ↦ n • ((-(q : ℤ)) • α) + ((r - (q : ℤ)) • α + β) := by
        funext n
        have hlin : (q : ℤ) * (-((n : ℤ) + 1)) + r = (n : ℤ) * (-(q : ℤ)) + (r - (q : ℤ)) := by
          ring
        rw [hlin, add_smul, mul_zsmul, natCast_zsmul, add_assoc]
      rw [hneg]
      exact asympEquidistributed_linear_of_torusIrrational
        (hα.zsmul (neg_ne_zero.2 (Nat.cast_ne_zero.2 hq.ne'))) _
  tfae_have 2 → 1 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 1 → 3 := by
    intro h
    have hnat : AsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure := by
      simpa only [natCast_zsmul] using h.natCast
    exact ((linear_equidistribution_tfae α β).out 1 3).1 hnat
  tfae_finish

end Linear

section PolynomialAlgebra

/-- Forward difference of a polynomial map `n ↦ ∑ j ≤ m + 1, n^j • α j` into an abelian group is a
polynomial map of degree `m` with leading coefficient `((m + 1) * h) • α (m + 1)`. -/
private theorem poly_diff_eq {G : Type*} [AddCommGroup G] (m h : ℕ) (α : ℕ → G) :
    ∃ β : ℕ → G, β m = ((m + 1) * h) • α (m + 1) ∧
      ∀ n : ℕ, (∑ j ∈ Finset.range (m + 2), ((n + h) ^ j) • α j) -
        (∑ j ∈ Finset.range (m + 2), (n ^ j) • α j) =
        ∑ l ∈ Finset.range (m + 1), (n ^ l) • β l := by
  let β (l : ℕ) : G :=
    ∑ j ∈ Finset.Ico (l + 1) (m + 2), (h ^ (j - l) * j.choose l) • α j
  refine ⟨β, ?_, fun n ↦ ?_⟩
  · have hico : Finset.Ico (m + 1) (m + 2) = {m + 1} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp only [β, hico, Finset.sum_singleton, Nat.add_sub_cancel_left, pow_one,
      Nat.choose_succ_self_right, mul_comm h (m + 1)]
  · rw [← Finset.sum_sub_distrib]
    have hterm (j : ℕ) :
        ((n + h) ^ j) • α j - (n ^ j) • α j =
          ∑ l ∈ Finset.range j, (n ^ l) • ((h ^ (j - l) * j.choose l) • α j) := by
      rw [add_pow, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
        Nat.cast_one, mul_one, add_smul, add_sub_cancel_right, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Nat.cast_id, mul_assoc, mul_smul]
    simp_rw [hterm]
    have hpad (j : ℕ) (hj : j ∈ Finset.range (m + 2)) :
        ∑ l ∈ Finset.range j, (n ^ l) • ((h ^ (j - l) * j.choose l) • α j) =
          ∑ l ∈ Finset.range (m + 1),
            if l < j then (n ^ l) • ((h ^ (j - l) * j.choose l) • α j) else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext l
      simp only [Finset.mem_range, Finset.mem_filter]
      have hj' : j < m + 2 := Finset.mem_range.1 hj
      omega
    rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← Finset.sum_filter, Finset.smul_sum]
    congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- Composing a polynomial map `n ↦ ∑ j ≤ j₀, n^j • c j` with an affine progression
`m ↦ Q * m + r` yields a polynomial map of degree `j₀` with leading coefficient
`(Q ^ j₀) • c j₀`. -/
private theorem poly_comp_affine_eq {G : Type*} [AddCommGroup G] (j₀ Q r : ℕ) (c : ℕ → G) :
    ∃ β : ℕ → G, β j₀ = (Q ^ j₀) • c j₀ ∧
      ∀ m : ℕ, ∑ j ∈ Finset.range (j₀ + 1), ((Q * m + r) ^ j) • c j =
        ∑ l ∈ Finset.range (j₀ + 1), (m ^ l) • β l := by
  let β (l : ℕ) : G :=
    ∑ j ∈ Finset.Ico l (j₀ + 1), (Q ^ l * r ^ (j - l) * j.choose l) • c j
  refine ⟨β, ?_, fun m ↦ ?_⟩
  · have hico : Finset.Ico j₀ (j₀ + 1) = {j₀} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp only [β, hico, Finset.sum_singleton, Nat.sub_self, pow_zero, mul_one, Nat.choose_self]
  · have hterm (j : ℕ) :
        ((Q * m + r) ^ j) • c j =
          ∑ l ∈ Finset.range (j + 1), (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) := by
      rw [add_pow, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Nat.cast_id, mul_pow, mul_comm (Q ^ l) (m ^ l), mul_assoc, mul_assoc, ← mul_assoc (Q ^ l),
        mul_smul]
    simp_rw [hterm]
    have hpad (j : ℕ) (hj : j ∈ Finset.range (j₀ + 1)) :
        ∑ l ∈ Finset.range (j + 1), (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) =
          ∑ l ∈ Finset.range (j₀ + 1),
            if l ≤ j then (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext l
      simp only [Finset.mem_range, Finset.mem_filter]
      have hj' : j < j₀ + 1 := Finset.mem_range.1 hj
      omega
    rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← Finset.sum_filter, Finset.smul_sum]
    congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- Along a residue class modulo a common multiple `Q` of the additive orders of the higher-degree
coefficients `c j` (`j₀ < j ≤ s`), those higher-degree terms collapse to a constant. -/
private theorem poly_split_higher_torsion {G : Type*} [AddCommGroup G] {s j₀ q Q r : ℕ}
    (c : ℕ → G) (hj₀_s : j₀ ≤ s) (hQdvd : ∀ j ∈ Finset.Ioc j₀ s, addOrderOf (c j) ∣ Q)
    (t m : ℕ) :
    ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j =
      (∑ j ∈ Finset.range (j₀ + 1), (((q * Q) * m + (q * t + r)) ^ j) • c j) +
        ∑ j ∈ Finset.Ioc j₀ s, ((q * t + r) ^ j) • c j := by
  have hunion : Finset.range (s + 1) = Finset.range (j₀ + 1) ∪ Finset.Ioc j₀ s := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.range (j₀ + 1)) (Finset.Ioc j₀ s) := by
    rw [Finset.disjoint_left]; intro j hj₁ hj₂
    simp only [Finset.mem_range, Finset.mem_Ioc] at hj₁ hj₂; omega
  have harg : q * (Q * m + t) + r = (q * Q) * m + (q * t + r) := by ring
  rw [hunion, Finset.sum_union hdisj]
  simp_rw [harg]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hmod : (q * Q) * m + (q * t + r) ≡ q * t + r [MOD Q] := by
    rw [Nat.ModEq, Nat.add_mod, mul_right_comm, Nat.mul_mod_left, zero_add, Nat.mod_mod]
  rw [← mod_addOrderOf_nsmul (c j), (hmod.pow j).of_dvd (hQdvd j hj), mod_addOrderOf_nsmul]

end PolynomialAlgebra

section WeylPolynomial

variable {d : Type*} [Fintype d]

/-- **Weyl's polynomial equidistribution theorem on `UnitAddTorus d`.** If `s ≥ 1` and the leading
coefficient `α s` is irrational (`TorusIrrational (α s)`), then the polynomial sequence
`n ↦ ∑ j ≤ s, n^j • α j` is equidistributed for Haar probability. -/
theorem weyl_polynomial (s : ℕ) (hs : 1 ≤ s) (α : ℕ → UnitAddTorus d)
    (hα : TorusIrrational (α s)) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
      volume.toProbabilityMeasure := by
  induction s, hs using Nat.le_induction generalizing α with
  | base =>
    have hlin : (fun n : ℕ ↦ ∑ j ∈ Finset.range 2, (n ^ j) • α j) =
        fun n : ℕ ↦ n • α 1 + α 0 := by
      funext n
      rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_smul, pow_one, add_comm]
    rw [hlin]
    exact asympEquidistributed_linear_of_torusIrrational hα (α 0)
  | succ m _ ih =>
    refine vanDerCorput_difference _ fun h hh ↦ ?_
    obtain ⟨β, hβm, hdiff⟩ := poly_diff_eq m h α
    simp_rw [hdiff]
    refine ih β ?_
    rw [hβm]
    exact hα.nsmul (mul_ne_zero (Nat.succ_ne_zero m) (by omega))

end WeylPolynomial

section PolynomialCriterion

variable {d : Type*} [Fintype d]

/-- Equidistribution on `UnitAddTorus Unit` is equivalent to equidistribution on
`UnitAddCircle`. -/
private theorem asympEquidistributed_unit_iff (x : ℕ → UnitAddCircle) :
    AsympEquidistributed (fun n _ ↦ x n : ℕ → UnitAddTorus Unit) volume.toProbabilityMeasure ↔
      AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion, asympEquidistributed_haarAddCircle_iff]
  have hchar (k : Unit → ℤ) (y : UnitAddCircle) :
      UnitAddTorus.mFourier k (fun _ ↦ y) = fourier (k ()) y := by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, Fintype.sum_unique, fourier_one, fourier_apply]
  constructor
  · intro h k hk
    have hk' : (fun _ : Unit ↦ k) ≠ 0 := fun h0 ↦ hk (congrFun h0 ())
    simpa only [hchar] using h (fun _ ↦ k) hk'
  · intro h k hk
    have hk0 : k () ≠ 0 := fun h0 ↦ hk (funext fun _ ↦ h0)
    simpa only [hchar] using h (k ()) hk0

/-- If no nonzero integer frequency kills all of `α 1, …, α s`, then for every nonzero `k`, at
least one projection `∑ i, k i • α j i` (`1 ≤ j ≤ s`) has infinite additive order. -/
private theorem exists_addOrderOf_eq_zero_of_forall_ne_zero {s : ℕ} {α : ℕ → UnitAddTorus d}
    (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0)
    {k : d → ℤ} (hk : k ≠ 0) :
    ∃ j ∈ Finset.Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0 := by
  by_contra hfin
  push Not at hfin
  set m : ℕ := ∏ j ∈ Finset.Icc 1 s, addOrderOf (∑ i, k i • α j i)
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj ↦ hfin j hj
  have hmk : (m : ℤ) • k ≠ 0 := by
    intro h0
    refine hk (funext fun i ↦ ?_)
    have hi := congrFun h0 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at hi
    exact hi.resolve_left (Nat.cast_ne_zero.2 hm)
  obtain ⟨j, hj, hne⟩ := h ((m : ℤ) • k) hmk
  apply hne
  have hpull : ∑ i, ((m : ℤ) • k) i • α j i = m • ∑ i, k i • α j i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_zsmul, natCast_zsmul]
  rw [hpull]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hj)

/-- Equidistribution along a residue class modulo the common order `Q` of higher-degree torsion
terms in a 1D circle polynomial. -/
private theorem asympEquidistributed_poly_circle_subseq {s j₀ q Q r : ℕ} (c : ℕ → UnitAddCircle)
    (hj₀_1 : 1 ≤ j₀) (hj₀_s : j₀ ≤ s) (hj₀_ord : addOrderOf (c j₀) = 0)
    (hQ : 0 < Q) (hQdvd : ∀ j ∈ Finset.Ioc j₀ s, addOrderOf (c j) ∣ Q) (hq : 0 < q) (t : ℕ) :
    AsympEquidistributed
      (fun m : ℕ ↦ ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  obtain ⟨β, hβ_lead, hβ_eq⟩ := poly_comp_affine_eq j₀ (q * Q) (q * t + r) c
  let C : UnitAddCircle := ∑ j ∈ Finset.Ioc j₀ s, ((q * t + r) ^ j) • c j
  let β' (l : ℕ) : UnitAddCircle := if l = 0 then β 0 + C else β l
  have hpoly_eq (m : ℕ) :
      ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j =
        ∑ l ∈ Finset.range (j₀ + 1), (m ^ l) • β' l := by
    rw [poly_split_higher_torsion c hj₀_s hQdvd t m, hβ_eq m]
    have h0 : 0 ∈ Finset.range (j₀ + 1) := Finset.mem_range.2 (Nat.succ_pos j₀)
    rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h0]
    have herase : ∑ l ∈ (Finset.range (j₀ + 1)).erase 0, (m ^ l) • β l =
        ∑ l ∈ (Finset.range (j₀ + 1)).erase 0, (m ^ l) • β' l :=
      Finset.sum_congr rfl fun l hl ↦ by simp [β', (Finset.mem_erase.1 hl).1]
    simp only [β', ↓reduceIte, pow_zero, one_smul, herase]
    abel
  simp_rw [hpoly_eq]
  rw [← asympEquidistributed_unit_iff]
  have hweyl : AsympEquidistributed
      (fun m : ℕ ↦ ∑ l ∈ Finset.range (j₀ + 1), (m ^ l) • (fun _ : Unit ↦ β' l))
      volume.toProbabilityMeasure := by
    refine weyl_polynomial j₀ hj₀_1 (fun l _ ↦ β' l) ?_
    have hlead : (fun _ : Unit ↦ β' j₀) = ((q * Q) ^ j₀) • (fun _ : Unit ↦ c j₀) := by
      funext _
      simp only [β', show j₀ ≠ 0 by omega, ↓reduceIte, hβ_lead, Pi.smul_apply]
    rw [hlead]
    have hirr : TorusIrrational (fun _ : Unit ↦ c j₀) :=
      (torusIrrational_unique_iff (fun _ : Unit ↦ c j₀)).2 hj₀_ord
    exact hirr.nsmul (pow_ne_zero j₀ (mul_ne_zero hq.ne' hQ.ne'))
  convert hweyl using 1
  funext m _
  simp [Finset.sum_apply]

/-- One-dimensional polynomial sequences in `UnitAddCircle` with at least one nonconstant
coefficient of infinite additive order are totally equidistributed for Haar probability. -/
private theorem totallyAsympEquidistributed_poly_circle {s : ℕ} (c : ℕ → UnitAddCircle)
    (hc : ∃ j ∈ Finset.Icc 1 s, addOrderOf (c j) = 0) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 s).filter fun j ↦ addOrderOf (c j) = 0
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hord⟩ := hc
    exact ⟨j, Finset.mem_filter.2 ⟨hj, hord⟩⟩
  set j₀ : ℕ := S.max' hS
  have hj₀_mem : j₀ ∈ S := Finset.max'_mem S hS
  have hj₀_1 : 1 ≤ j₀ := (Finset.mem_Icc.1 (Finset.mem_filter.1 hj₀_mem).1).1
  have hj₀_s : j₀ ≤ s := (Finset.mem_Icc.1 (Finset.mem_filter.1 hj₀_mem).1).2
  have hj₀_ord : addOrderOf (c j₀) = 0 := (Finset.mem_filter.1 hj₀_mem).2
  set Q : ℕ := ∏ j ∈ Finset.Ioc j₀ s, addOrderOf (c j)
  have hQ : 0 < Q := Finset.prod_pos fun j hj ↦ by
    have hj' := Finset.mem_Ioc.1 hj
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    have hmem : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hj'.2⟩, h0⟩
    exact not_lt_of_ge (Finset.le_max' S j hmem) hj'.1
  have hQdvd : ∀ j ∈ Finset.Ioc j₀ s, addOrderOf (c j) ∣ Q :=
    fun j hj ↦ Finset.dvd_prod_of_mem (fun l ↦ addOrderOf (c l)) hj
  rw [totallyAsympEquidistributed_def]
  intro q r hq
  exact AsympEquidistributed.of_mod_classes hQ fun t ↦
    asympEquidistributed_poly_circle_subseq c hj₀_1 hj₀_s hj₀_ord hQ hQdvd hq t.val

/-- Positive-half equidistribution for a polynomial sequence on `ℤ` shifted into `ℕ`. -/
private theorem asympEquidistributed_poly_pos_half {s : ℕ} {γ : ℕ → UnitAddTorus d}
    (htot : TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • γ j)
      volume.toProbabilityMeasure)
    {q : ℕ} (hq : 0 < q) (r : ℤ) :
    AsympEquidistributed
      (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (((q : ℤ) * ((n : ℤ) + 1) + r) ^ j) • γ j)
      volume.toProbabilityMeasure := by
  set M : ℕ := r.natAbs
  have hr_pos : 0 ≤ (q : ℤ) * ((M : ℤ) + 1) + r := by
    have h1 : (M : ℤ) + 1 ≤ (q : ℤ) * ((M : ℤ) + 1) := by
      nlinarith [show (1 : ℤ) ≤ q by exact_mod_cast hq]
    have h2 : -(M : ℤ) ≤ r := neg_le_of_abs_le (by simp [M])
    omega
  set r' : ℕ := Int.toNat ((q : ℤ) * ((M : ℤ) + 1) + r)
  rw [← asympEquidistributed_comp_add_iff _ M]
  have hrew : (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
        (((q : ℤ) * (((n + M : ℕ) : ℤ) + 1) + r) ^ j) • γ j) =
      fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), ((q * n + r') ^ j) • γ j := by
    funext n
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hlin : (q : ℤ) * (((n + M : ℕ) : ℤ) + 1) + r = ((q * n + r' : ℕ) : ℤ) := by
      have hr' : (r' : ℤ) = (q : ℤ) * ((M : ℤ) + 1) + r := Int.toNat_of_nonneg hr_pos
      push_cast; rw [hr']; ring
    rw [hlin, ← Nat.cast_pow, natCast_zsmul]
  rw [hrew]
  exact totallyAsympEquidistributed_def.1 htot q r' hq

/-- Lift total equidistribution of a polynomial sequence from `ℕ` to `ℤ`. -/
private theorem totallyAsympEquidistributedInt_poly_of_criterion {s : ℕ} (α : ℕ → UnitAddTorus d)
    (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0)
    (htot : ∀ γ : ℕ → UnitAddTorus d,
      (∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • γ j i ≠ 0) →
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • γ j)
        volume.toProbabilityMeasure) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
      volume.toProbabilityMeasure := by
  rw [totallyAsympEquidistributedInt_def]
  intro q hq r
  rw [asympEquidistributedInt_def]
  refine ⟨asympEquidistributed_poly_pos_half (htot α h) hq r, ?_⟩
  let α' (j : ℕ) : UnitAddTorus d := ((-1 : ℤ) ^ j) • α j
  have hα' : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α' j i ≠ 0 := by
    intro k hk
    obtain ⟨j, hj, hne⟩ := h k hk
    refine ⟨j, hj, fun h0 ↦ hne ?_⟩
    have hpull : ∑ i, k i • α' j i = ((-1 : ℤ) ^ j) • ∑ i, k i • α j i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [α', Pi.smul_apply, zsmul_comm]
    rw [hpull] at h0
    have hsq : ((-1 : ℤ) ^ j) • (((-1 : ℤ) ^ j) • ∑ i, k i • α j i) = ∑ i, k i • α j i := by
      rw [← mul_zsmul, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [← hsq, h0, smul_zero]
  have hneg_eq : (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
        (((q : ℤ) * (-((n : ℤ) + 1)) + r) ^ j) • α j) =
      fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
        (((q : ℤ) * ((n : ℤ) + 1) + (-r)) ^ j) • α' j := by
    funext n
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hlin : (q : ℤ) * (-((n : ℤ) + 1)) + r = (-1 : ℤ) * ((q : ℤ) * ((n : ℤ) + 1) + -r) := by
      ring
    rw [hlin, mul_pow, mul_comm ((-1 : ℤ) ^ j), mul_zsmul]
  rw [hneg_eq]
  exact asympEquidistributed_poly_pos_half (htot α' hα') hq (-r)

/-- Equidistribution of a polynomial sequence on `UnitAddTorus d` implies that no nonzero
integer frequency kills all of `α 1, …, α s`. -/
private theorem exists_ne_zero_of_asympEquidistributed_poly {s : ℕ} {α : ℕ → UnitAddTorus d}
    (h : AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
      volume.toProbabilityMeasure)
    {k : d → ℤ} (hk : k ≠ 0) :
    ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0 := by
  by_contra hkill
  push Not at hkill
  refine not_asympEquidistributed_of_mFourier_const h hk (α 0) fun n ↦ ?_
  rw [UnitAddTorus.mFourier_eq_fourier_sum, UnitAddTorus.mFourier_eq_fourier_sum]
  congr 1
  have hpull : ∑ i, k i • (∑ j ∈ Finset.range (s + 1), (n ^ j) • α j) i =
      ∑ j ∈ Finset.range (s + 1), (n ^ j) • (∑ i, k i • α j i) := by
    simp only [Finset.sum_apply, Finset.smul_sum, Pi.smul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← natCast_zsmul, ← natCast_zsmul, zsmul_comm]
  rw [hpull, Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    have hj' : j ∈ Finset.Icc 1 s := Finset.mem_Icc.2 ⟨by omega, by
      have := Finset.mem_range.1 hj; omega⟩
    rw [hkill j hj', smul_zero]
  · intro h0; exact (h0 (Finset.mem_range.2 (Nat.succ_pos s))).elim

/-- **Polynomial equidistribution criterion on `UnitAddTorus d`.** For any degree `s : ℕ` and
coefficients `α : ℕ → UnitAddTorus d`, equidistribution on `ℕ`, total equidistribution on `ℕ`,
bilateral equidistribution on `ℤ`, total bilateral equidistribution on `ℤ`, and the absence of a
nonzero integer frequency annihilating all nonconstant coefficients `α 1, …, α s` are equivalent. -/
theorem polynomial_equidistribution_tfae (s : ℕ) (α : ℕ → UnitAddTorus d) :
    List.TFAE [AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure,
      AsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure,
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0] := by
  have h52 (γ : ℕ → UnitAddTorus d)
      (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • γ j i ≠ 0) :
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • γ j)
        volume.toProbabilityMeasure := by
    rw [totallyAsympEquidistributed_def]
    intro q r hq
    rw [asympEquidistributed_volume_iff_projections]
    intro k hk
    have hproj : (fun n : ℕ ↦ ∑ i, k i • (∑ j ∈ Finset.range (s + 1), ((q * n + r) ^ j) • γ j) i) =
        fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), ((q * n + r) ^ j) • (∑ i, k i • γ j i) := by
      funext n
      simp only [Finset.sum_apply, Finset.smul_sum, Pi.smul_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← natCast_zsmul, ← natCast_zsmul, zsmul_comm]
    rw [hproj]
    exact totallyAsympEquidistributed_def.1
      (totallyAsympEquidistributed_poly_circle (fun j ↦ ∑ i, k i • γ j i)
        (exists_addOrderOf_eq_zero_of_forall_ne_zero h hk)) q r hq
  tfae_have 5 → 4 := fun h ↦ totallyAsympEquidistributedInt_poly_of_criterion α h h52
  tfae_have 4 → 3 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 4 → 2 := fun h ↦ by
    simpa only [← Nat.cast_pow, natCast_zsmul] using h.totallyAsympEquidistributed_natCast
  tfae_have 3 → 1 := fun h ↦ by
    simpa only [← Nat.cast_pow, natCast_zsmul] using h.natCast
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 5 := fun h _ hk ↦ exists_ne_zero_of_asympEquidistributed_poly h hk
  tfae_finish

/-- **Equidistribution criterion for polynomial sequences on `UnitAddTorus d`.** -/
theorem polynomial_equidistribution_iff (s : ℕ) (α : ℕ → UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 1 5

/-- **Total equidistribution criterion for polynomial sequences on `UnitAddTorus d`.** -/
theorem polynomial_total_equidistribution_iff (s : ℕ) (α : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
        volume.toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 2 5

end PolynomialCriterion

end TauCeti
