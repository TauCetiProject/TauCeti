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

This file proves the classical equidistribution theorems for linear and polynomial orbits in
`UnitAddTorus d = (ℝ / ℤ)^d`:

* `TauCeti.linear_equidistribution_tfae` and `TauCeti.linear_equidistribution_int_tfae`:
  equidistribution, total equidistribution, and irrationality of the step for `n ↦ n • α + β`
  on `ℕ` and `ℤ`.
* `TauCeti.weyl_polynomial`: Weyl's polynomial equidistribution theorem when `s ≥ 1` and `α s` is
  irrational, proved by induction via `TauCeti.vanDerCorput_difference`.
* `TauCeti.polynomial_equidistribution_tfae`, `TauCeti.polynomial_equidistribution_iff`, and
  `TauCeti.polynomial_total_equidistribution_iff`: full characterization of polynomial
  equidistribution and total equidistribution on `ℕ` and `ℤ`.

## References

* T. Tao, *Higher Order Fourier Analysis*, AMS, 2012, §1.1.1 (Cor. 1.1.9, Exercises 1.1.5–1.1.6).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Topology

namespace TauCeti

section Linear

variable {d : Type*} [Fintype d]

private theorem not_asympEquidistributed_of_mFourier_const {x : ℕ → UnitAddTorus d}
    (hx : AsympEquidistributed x volume.toProbabilityMeasure) {k : d → ℤ} (hk : k ≠ 0)
    (y : UnitAddTorus d) (hconst : ∀ n, UnitAddTorus.mFourier k (x n) = UnitAddTorus.mFourier k y) :
    False := by
  have htend := (weyl_criterion x).1 hx k hk
  rw [show (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), UnitAddTorus.mFourier k (x i)) =
      fun _ ↦ UnitAddTorus.mFourier k y from funext fun n ↦ by
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), one_mul]] at htend
  have hzero : UnitAddTorus.mFourier k y = 0 := tendsto_nhds_unique tendsto_const_nhds htend
  have hnorm := UnitAddTorus.norm_mFourier_apply k y
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

private theorem asympEquidistributed_linear_of_torusIrrational {α : UnitAddTorus d}
    (hα : TorusIrrational α) (β : UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure := by
  rw [weyl_criterion]
  intro k hk
  set ζ : ℂ := UnitAddTorus.mFourier k α
  have hζ_ne : ζ ≠ 1 := (torusIrrational_iff_mFourier α).1 hα k hk
  simp_rw [show ∀ i : ℕ, UnitAddTorus.mFourier k (i • α + β) = UnitAddTorus.mFourier k β * ζ ^ i
    from fun i ↦ by
      rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, mul_comm],
    ← Finset.mul_sum]
  refine squeeze_zero_norm (fun n ↦ ?_) (by
    simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖ζ - 1‖))
  rw [geom_sum_eq hζ_ne, norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
    UnitAddTorus.norm_mFourier_apply, one_mul, norm_div, Nat.cast_add, Nat.cast_one]
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (norm_nonneg _)) (by positivity)
  calc ‖ζ ^ (n + 1) - 1‖ ≤ ‖ζ ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, UnitAddTorus.norm_mFourier_apply, one_pow, norm_one]; norm_num

/-- **Linear equidistribution on `UnitAddTorus d` (over `ℕ`).** Equidistribution, total
equidistribution, and irrationality of the step `α` are equivalent for `n ↦ n • α + β`. -/
theorem linear_equidistribution_tfae (α β : UnitAddTorus d) :
    List.TFAE [AsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ n • α + β) volume.toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := fun hα ↦ totallyAsympEquidistributed_def.2 fun q r hq ↦ by
    rw [show (fun n : ℕ ↦ (q * n + r) • α + β) = fun n : ℕ ↦ n • (q • α) + (r • α + β) from
      funext fun n ↦ by rw [add_smul, mul_comm q n, mul_smul, add_assoc]]
    exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') (r • α + β)
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 3 := fun h ↦ (torusIrrational_iff_mFourier α).2 fun k hk h1 ↦
    not_asympEquidistributed_of_mFourier_const h hk β fun i ↦ by
      rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, h1, one_pow, one_mul]
  tfae_finish

/-- **Linear equidistribution on `UnitAddTorus d` (over `ℤ`).** Bilateral equidistribution, total
bilateral equidistribution, and irrationality of the step `α` are equivalent for
`n ↦ n • α + β`. -/
theorem linear_equidistribution_int_tfae (α β : UnitAddTorus d) :
    List.TFAE [AsympEquidistributedInt (fun n : ℤ ↦ n • α + β) volume.toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ n • α + β) volume.toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := fun hα ↦ totallyAsympEquidistributedInt_def.2 fun q hq r ↦ by
    refine asympEquidistributedInt_def.2 ⟨?_, ?_⟩
    · rw [show (fun n : ℕ ↦ ((q : ℤ) * ((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • (q • α) + (((q : ℤ) + r) • α + β) from funext fun n ↦ by
        rw [mul_add, mul_one, add_assoc, add_smul, add_assoc, mul_comm (q : ℤ) (n : ℤ),
          mul_zsmul, natCast_zsmul, natCast_zsmul]]
      exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') _
    · rw [show (fun n : ℕ ↦ ((q : ℤ) * (-((n : ℤ) + 1)) + r) • α + β) =
          fun n : ℕ ↦ n • ((-(q : ℤ)) • α) + ((r - (q : ℤ)) • α + β) from funext fun n ↦ by
        rw [show (q : ℤ) * (-((n : ℤ) + 1)) + r = (n : ℤ) * (-(q : ℤ)) + (r - (q : ℤ)) by ring,
          add_smul, mul_zsmul, natCast_zsmul, add_assoc]]
      exact asympEquidistributed_linear_of_torusIrrational
        (hα.zsmul (neg_ne_zero.2 (Nat.cast_ne_zero.2 hq.ne'))) _
  tfae_have 2 → 1 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 1 → 3 := fun h ↦ ((linear_equidistribution_tfae α β).out 1 3).1
    (by simpa only [natCast_zsmul] using h.natCast)
  tfae_finish

end Linear

section PolynomialAlgebra

private theorem poly_comp_affine_eq {G : Type*} [AddCommGroup G] (s Q r : ℕ) (c : ℕ → G) (m : ℕ) :
    ∑ j ∈ Finset.range (s + 1), ((Q * m + r) ^ j) • c j =
      ∑ l ∈ Finset.range (s + 1), (m ^ l) •
        ∑ j ∈ Finset.Ico l (s + 1), (Q ^ l * r ^ (j - l) * j.choose l) • c j := by
  have hterm (j : ℕ) : ((Q * m + r) ^ j) • c j =
      ∑ l ∈ Finset.range (j + 1), (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) := by
    rw [add_pow, Finset.sum_smul]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [Nat.cast_id, mul_pow, mul_comm (Q ^ l) (m ^ l), mul_assoc, mul_assoc, ← mul_assoc (Q ^ l),
        mul_smul]
  simp_rw [hterm]
  have hpad (j : ℕ) (hj : j ∈ Finset.range (s + 1)) :
      ∑ l ∈ Finset.range (j + 1), (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) =
        ∑ l ∈ Finset.range (s + 1),
          if l ≤ j then (m ^ l) • ((Q ^ l * r ^ (j - l) * j.choose l) • c j) else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext l
    simp only [Finset.mem_range, Finset.mem_filter]; have := Finset.mem_range.1 hj; omega
  rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Finset.sum_filter, Finset.smul_sum]
  congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

private theorem poly_diff_eq {G : Type*} [AddCommGroup G] (m h : ℕ) (α : ℕ → G) :
    ∃ β : ℕ → G, β m = ((m + 1) * h) • α (m + 1) ∧
      ∀ n : ℕ, (∑ j ∈ Finset.range (m + 2), ((n + h) ^ j) • α j) -
        (∑ j ∈ Finset.range (m + 2), (n ^ j) • α j) =
        ∑ l ∈ Finset.range (m + 1), (n ^ l) • β l := by
  let β (l : ℕ) : G := (∑ j ∈ Finset.Ico l (m + 2), (h ^ (j - l) * j.choose l) • α j) - α l
  refine ⟨β, ?_, fun n ↦ ?_⟩
  · have hico : Finset.Ico m (m + 2) = {m, m + 1} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]; omega
    simp only [β, hico, Finset.sum_pair (Nat.ne_of_lt (Nat.lt_succ_self m)), Nat.succ_eq_add_one,
      Nat.sub_self, Nat.add_sub_cancel_left, pow_zero, pow_one, Nat.choose_self,
      Nat.choose_succ_self_right, mul_one, one_smul, add_sub_cancel_left, mul_comm h (m + 1)]
  · have hshift := poly_comp_affine_eq (m + 1) 1 h α n
    simp only [one_pow, one_mul] at hshift
    rw [hshift, ← Finset.sum_sub_distrib, Finset.sum_range_succ]
    have htop : Finset.Ico (m + 1) (m + 2) = {m + 1} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp only [htop, Finset.sum_singleton, Nat.sub_self, pow_zero, mul_one, Nat.choose_self,
      one_smul, sub_self, add_zero]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [← smul_sub]

private theorem poly_split_higher_torsion {G : Type*} [AddCommGroup G] {s j₀ q Q r : ℕ}
    (c : ℕ → G) (hj₀_s : j₀ ≤ s) (hQdvd : ∀ j ∈ Finset.Ioc j₀ s, addOrderOf (c j) ∣ Q)
    (t m : ℕ) :
    ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j =
      (∑ j ∈ Finset.range (j₀ + 1), (((q * Q) * m + (q * t + r)) ^ j) • c j) +
        ∑ j ∈ Finset.Ioc j₀ s, ((q * t + r) ^ j) • c j := by
  have hunion : Finset.range (s + 1) = Finset.range (j₀ + 1) ∪ Finset.Ioc j₀ s := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.range (j₀ + 1)) (Finset.Ioc j₀ s) :=
    Finset.disjoint_left.2 fun _ h₁ h₂ ↦ by
      simp only [Finset.mem_range, Finset.mem_Ioc] at h₁ h₂; omega
  rw [hunion, Finset.sum_union hdisj]
  simp_rw [show q * (Q * m + t) + r = (q * Q) * m + (q * t + r) by ring]
  refine congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
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
    rw [show (fun n : ℕ ↦ ∑ j ∈ Finset.range 2, (n ^ j) • α j) = fun n : ℕ ↦ n • α 1 + α 0 from
      funext fun n ↦ by
        rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_smul, pow_one, add_comm]]
    exact asympEquidistributed_linear_of_torusIrrational hα (α 0)
  | succ m _ ih =>
    refine vanDerCorput_difference _ fun h hh ↦ ?_
    obtain ⟨β, hβm, hdiff⟩ := poly_diff_eq m h α
    simp_rw [hdiff]
    exact ih β (hβm ▸ hα.nsmul (mul_ne_zero (Nat.succ_ne_zero m) (by omega)))

end WeylPolynomial

section PolynomialCriterion

variable {d : Type*} [Fintype d]

private theorem sum_zsmul_poly (s a : ℕ) (k : d → ℤ) (α : ℕ → UnitAddTorus d) :
    ∑ i, k i • (∑ j ∈ Finset.range (s + 1), (a ^ j) • α j) i =
      ∑ j ∈ Finset.range (s + 1), (a ^ j) • (∑ i, k i • α j i) := by
  simp only [Finset.sum_apply, Finset.smul_sum, Pi.smul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
    rw [← natCast_zsmul, ← natCast_zsmul, zsmul_comm]

private theorem asympEquidistributed_unit_iff (x : ℕ → UnitAddCircle) :
    AsympEquidistributed (fun n _ ↦ x n : ℕ → UnitAddTorus Unit) volume.toProbabilityMeasure ↔
      AsympEquidistributed x AddCircle.haarAddCircle.toProbabilityMeasure := by
  rw [weyl_criterion, asympEquidistributed_haarAddCircle_iff]
  have hchar (k : Unit → ℤ) (y : UnitAddCircle) :
      UnitAddTorus.mFourier k (fun _ ↦ y) = fourier (k ()) y := by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, Fintype.sum_unique, fourier_one, fourier_apply]
  exact ⟨fun h k hk ↦ by simpa only [hchar] using h (fun _ ↦ k) (fun h0 ↦ hk (congrFun h0 ())),
    fun h k hk ↦ by simpa only [hchar] using h (k ()) (fun h0 ↦ hk (funext fun _ ↦ h0))⟩

private theorem exists_addOrderOf_eq_zero_of_forall_ne_zero {s : ℕ} {α : ℕ → UnitAddTorus d}
    (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0)
    {k : d → ℤ} (hk : k ≠ 0) :
    ∃ j ∈ Finset.Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0 := by
  by_contra hfin
  push Not at hfin
  set m : ℕ := ∏ j ∈ Finset.Icc 1 s, addOrderOf (∑ i, k i • α j i)
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.2 hfin
  obtain ⟨j, hj, hne⟩ := h ((m : ℤ) • k) (smul_ne_zero (Nat.cast_ne_zero.2 hm) hk)
  refine hne ?_
  rw [show ∑ i, ((m : ℤ) • k) i • α j i = m • ∑ i, k i • α j i by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, mul_zsmul, natCast_zsmul]]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hj)

private theorem asympEquidistributed_poly_circle_subseq {s j₀ q Q r : ℕ} (c : ℕ → UnitAddCircle)
    (hj₀_1 : 1 ≤ j₀) (hj₀_s : j₀ ≤ s) (hj₀_ord : addOrderOf (c j₀) = 0)
    (hQ : 0 < Q) (hQdvd : ∀ j ∈ Finset.Ioc j₀ s, addOrderOf (c j) ∣ Q) (hq : 0 < q) (t : ℕ) :
    AsympEquidistributed
      (fun m : ℕ ↦ ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  let β (l : ℕ) : UnitAddCircle :=
    ∑ j ∈ Finset.Ico l (j₀ + 1), ((q * Q) ^ l * (q * t + r) ^ (j - l) * j.choose l) • c j
  let β' (l : ℕ) : UnitAddCircle :=
    if l = 0 then β 0 + ∑ j ∈ Finset.Ioc j₀ s, ((q * t + r) ^ j) • c j else β l
  have hpoly_eq (m : ℕ) :
      ∑ j ∈ Finset.range (s + 1), ((q * (Q * m + t) + r) ^ j) • c j =
        ∑ l ∈ Finset.range (j₀ + 1), (m ^ l) • β' l := by
    rw [poly_split_higher_torsion c hj₀_s hQdvd t m, poly_comp_affine_eq j₀ (q * Q) (q * t + r) c m]
    have h0 : 0 ∈ Finset.range (j₀ + 1) := Finset.mem_range.2 (Nat.succ_pos j₀)
    have herase : ∑ l ∈ (Finset.range (j₀ + 1)).erase 0, (m ^ l) • β' l =
        ∑ l ∈ (Finset.range (j₀ + 1)).erase 0, (m ^ l) • β l :=
      Finset.sum_congr rfl fun l hl ↦ by simp [β', (Finset.mem_erase.1 hl).1]
    rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h0, herase]
    simp only [β', β, ↓reduceIte, pow_zero, one_smul]; abel
  simp_rw [hpoly_eq]
  rw [← asympEquidistributed_unit_iff]
  have hweyl : AsympEquidistributed
      (fun m : ℕ ↦ ∑ l ∈ Finset.range (j₀ + 1), (m ^ l) • (fun _ : Unit ↦ β' l))
      volume.toProbabilityMeasure := by
    refine weyl_polynomial j₀ hj₀_1 (fun l _ ↦ β' l) ?_
    have hico : Finset.Ico j₀ (j₀ + 1) = {j₀} := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [show (fun _ : Unit ↦ β' j₀) = ((q * Q) ^ j₀) • (fun _ : Unit ↦ c j₀) from funext fun _ ↦ by
      simp only [β', β, hico, show j₀ ≠ 0 by omega, ↓reduceIte, Finset.sum_singleton,
        Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Pi.smul_apply]]
    exact ((torusIrrational_unique_iff (fun _ : Unit ↦ c j₀)).2 hj₀_ord).nsmul
      (pow_ne_zero j₀ (mul_ne_zero hq.ne' hQ.ne'))
  convert hweyl using 1; funext m _; simp [Finset.sum_apply]

private theorem totallyAsympEquidistributed_poly_circle {s : ℕ} (c : ℕ → UnitAddCircle)
    (hc : ∃ j ∈ Finset.Icc 1 s, addOrderOf (c j) = 0) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 s).filter fun j ↦ addOrderOf (c j) = 0
  have hS : S.Nonempty := let ⟨j, hj, hord⟩ := hc; ⟨j, Finset.mem_filter.2 ⟨hj, hord⟩⟩
  set j₀ : ℕ := S.max' hS
  have hj₀ := Finset.mem_filter.1 (Finset.max'_mem S hS)
  set Q : ℕ := ∏ j ∈ Finset.Ioc j₀ s, addOrderOf (c j)
  have hQ : 0 < Q := Finset.prod_pos fun j hj ↦ Nat.pos_of_ne_zero fun h0 ↦ by
    have hj' := Finset.mem_Ioc.1 hj
    exact not_lt_of_ge (Finset.le_max' S j
      (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj₀.1).1; omega, hj'.2⟩,
        h0⟩)) hj'.1
  exact totallyAsympEquidistributed_def.2 fun q r hq ↦ AsympEquidistributed.of_mod_classes hQ
    fun t ↦ asympEquidistributed_poly_circle_subseq c (Finset.mem_Icc.1 hj₀.1).1
      (Finset.mem_Icc.1 hj₀.1).2 hj₀.2 hQ
      (fun j hj ↦ Finset.dvd_prod_of_mem (fun l ↦ addOrderOf (c l)) hj) hq t.val

private theorem asympEquidistributed_poly_pos_half {s : ℕ} {γ : ℕ → UnitAddTorus d}
    (htot : TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • γ j)
      volume.toProbabilityMeasure)
    {q : ℕ} (hq : 0 < q) (r : ℤ) :
    AsympEquidistributed
      (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (((q : ℤ) * ((n : ℤ) + 1) + r) ^ j) • γ j)
      volume.toProbabilityMeasure := by
  set M : ℕ := r.natAbs
  have hr_pos : 0 ≤ (q : ℤ) * ((M : ℤ) + 1) + r := by
    have : (M : ℤ) + 1 ≤ (q : ℤ) * ((M : ℤ) + 1) := by
      nlinarith [show (1 : ℤ) ≤ q by exact_mod_cast hq]
    have : -(M : ℤ) ≤ r := neg_le_of_abs_le (by simp [M])
    omega
  set r' : ℕ := Int.toNat ((q : ℤ) * ((M : ℤ) + 1) + r)
  rw [← asympEquidistributed_comp_add_iff _ M,
    show (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
          (((q : ℤ) * (((n + M : ℕ) : ℤ) + 1) + r) ^ j) • γ j) =
        fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), ((q * n + r') ^ j) • γ j from funext fun n ↦
      Finset.sum_congr rfl fun j _ ↦ by
        rw [show (q : ℤ) * (((n + M : ℕ) : ℤ) + 1) + r = ((q * n + r' : ℕ) : ℤ) by
            push_cast; rw [Int.toNat_of_nonneg hr_pos]; ring,
          ← Nat.cast_pow, natCast_zsmul]]
  exact totallyAsympEquidistributed_def.1 htot q r' hq

private theorem totallyAsympEquidistributedInt_poly_of_criterion {s : ℕ} (α : ℕ → UnitAddTorus d)
    (h : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0)
    (htot : ∀ γ : ℕ → UnitAddTorus d,
      (∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • γ j i ≠ 0) →
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • γ j)
        volume.toProbabilityMeasure) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
      volume.toProbabilityMeasure := totallyAsympEquidistributedInt_def.2 fun q hq r ↦ by
  refine asympEquidistributedInt_def.2 ⟨asympEquidistributed_poly_pos_half (htot α h) hq r, ?_⟩
  let α' (j : ℕ) : UnitAddTorus d := ((-1 : ℤ) ^ j) • α j
  have hα' : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α' j i ≠ 0 := fun k hk ↦ by
    obtain ⟨j, hj, hne⟩ := h k hk
    refine ⟨j, hj, fun h0 ↦ hne ?_⟩
    rw [show ∑ i, k i • α' j i = ((-1 : ℤ) ^ j) • ∑ i, k i • α j i by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by
        simp only [α', Pi.smul_apply, zsmul_comm]] at h0
    have hsq : ((-1 : ℤ) ^ j) • (((-1 : ℤ) ^ j) • ∑ i, k i • α j i) = ∑ i, k i • α j i := by
      rw [← mul_zsmul, ← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← hsq, h0, smul_zero]
  rw [show (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
        (((q : ℤ) * (-((n : ℤ) + 1)) + r) ^ j) • α j) =
      fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1),
        (((q : ℤ) * ((n : ℤ) + 1) + (-r)) ^ j) • α' j from funext fun n ↦
    Finset.sum_congr rfl fun j _ ↦ by
      rw [show (q : ℤ) * (-((n : ℤ) + 1)) + r = (-1 : ℤ) * ((q : ℤ) * ((n : ℤ) + 1) + -r) by ring,
        mul_pow, mul_comm ((-1 : ℤ) ^ j), mul_zsmul]]
  exact asympEquidistributed_poly_pos_half (htot α' hα') hq (-r)

private theorem exists_ne_zero_of_asympEquidistributed_poly {s : ℕ} {α : ℕ → UnitAddTorus d}
    (h : AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ Finset.range (s + 1), (n ^ j) • α j)
      volume.toProbabilityMeasure)
    {k : d → ℤ} (hk : k ≠ 0) :
    ∃ j ∈ Finset.Icc 1 s, ∑ i, k i • α j i ≠ 0 := by
  by_contra hkill
  push Not at hkill
  refine not_asympEquidistributed_of_mFourier_const h hk (α 0) fun n ↦ ?_
  rw [UnitAddTorus.mFourier_eq_fourier_sum, UnitAddTorus.mFourier_eq_fourier_sum, sum_zsmul_poly]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    rw [hkill j (Finset.mem_Icc.2 ⟨by omega, by have := Finset.mem_range.1 hj; omega⟩), smul_zero]
  · exact fun h0 ↦ (h0 (Finset.mem_range.2 (Nat.succ_pos s))).elim

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
        volume.toProbabilityMeasure := totallyAsympEquidistributed_def.2 fun q r hq ↦
    (asympEquidistributed_volume_iff_projections _).2 fun k hk ↦ by
      simp_rw [sum_zsmul_poly]
      exact totallyAsympEquidistributed_def.1 (totallyAsympEquidistributed_poly_circle
        (fun j ↦ ∑ i, k i • γ j i) (exists_addOrderOf_eq_zero_of_forall_ne_zero h hk)) q r hq
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
