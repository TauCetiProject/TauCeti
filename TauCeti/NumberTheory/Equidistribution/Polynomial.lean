/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.NumberTheory.Equidistribution.Weyl
public import TauCeti.Topology.Instances.AddCircle.UnitAddTorus
import TauCeti.Algebra.Group.PolynomialSequence
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.SpecificLimits.Cesaro.Basic
import TauCeti.Analysis.SpecificLimits.VanDerCorput

/-!
# Linear equidistribution, van der Corput's difference theorem, and Weyl's polynomial theorem

* `TauCeti.linear_equidistribution_tfae`, `TauCeti.linear_equidistributionInt_tfae`: equivalence
  of equidistribution, total equidistribution, and `TorusIrrational α` for `n ↦ n • α + β`.
* `TauCeti.vanDerCorput_difference`: van der Corput's difference theorem for torus sequences.
* `TauCeti.weyl_polynomial`: Weyl's polynomial equidistribution theorem for `s ≥ 1` and
  `TorusIrrational (α s)`.
* `TauCeti.asympEquidistributed_poly_comp_affine_addCircle`: affine equidistribution of a 1D
  polynomial sequence with a non-constant infinite-order coefficient.
* `TauCeti.polynomial_equidistribution_tfae`, `TauCeti.polynomial_equidistribution_iff`,
  `TauCeti.polynomial_total_equidistribution_iff`,
  `TauCeti.polynomial_total_equidistributionInt_iff`: characterization of equidistribution and
  total equidistribution (on `ℕ` and `ℤ`) for polynomial sequences in `UnitAddTorus d`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Lemma 1.1.6, Corollary 1.1.7, Corollary 1.1.9, Exercises 1.1.5 and 1.1.6).
-/

public section

open Filter Finset MeasureTheory Topology
open scoped ENNReal

namespace TauCeti

section Linear

variable {d : Type*} [Fintype d]

/-- If `α` is irrational in `UnitAddTorus d`, then `n ↦ n • α + β` is Haar-equidistributed. -/
private theorem asympEquidistributed_linear_of_torusIrrational {α : UnitAddTorus d}
    (hα : TorusIrrational α) (β : UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ n • α + β)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  rw [weyl_criterion]; intro k hk; set ζ : ℂ := UnitAddTorus.mFourier k α
  have hζne : ζ ≠ 1 := torusIrrational_iff_mFourier.mp hα k hk
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖ζ - 1‖))
  have hterm (i : ℕ) : UnitAddTorus.mFourier k (i • α + β) = UnitAddTorus.mFourier k β * ζ ^ i :=
    by rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, mul_comm]
  simp_rw [hterm, ← mul_sum, geom_sum_eq hζne, norm_mul, norm_inv, Complex.norm_natCast,
    UnitAddTorus.norm_mFourier_apply, one_mul, norm_div]
  push_cast; gcongr; refine (norm_sub_le (ζ ^ (n + 1)) 1).trans_eq ?_
  rw [norm_pow, UnitAddTorus.norm_mFourier_apply, one_pow, norm_one]; norm_num

/-- **Equidistribution of linear orbits on `UnitAddTorus d`**: for `α, β : UnitAddTorus d`,
equidistribution of `n ↦ n • α + β`, total equidistribution of `n ↦ n • α + β`, and irrationality
of `α` are equivalent. -/
theorem linear_equidistribution_tfae (α β : UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributed (fun n : ℕ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := fun hα ↦ totallyAsympEquidistributed_def.mpr fun q r hq ↦ by
    rw [(funext fun n ↦ by rw [add_nsmul, mul_nsmul, add_assoc] :
      (fun n : ℕ ↦ (q * n + r) • α + β) = fun n : ℕ ↦ n • (q • α) + (r • α + β))]
    exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') _
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 3 := fun h ↦ torusIrrational_iff_mFourier.mpr fun k hk h1 ↦ by
    have hlim := ((weyl_criterion.mp h) k hk).congr fun n ↦ by
      simp_rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, h1, one_pow,
        one_mul]
      simpa only [Nat.succ_eq_add_one, smul_eq_mul] using
        inv_natCast_smul_sum_const (𝕜 := ℂ) (Nat.succ_ne_zero n) (UnitAddTorus.mFourier k β)
    simpa [tendsto_nhds_unique tendsto_const_nhds hlim] using UnitAddTorus.norm_mFourier_apply k β
  tfae_finish

/-- **Equidistribution of doubly infinite linear orbits on `UnitAddTorus d`**: for
`α, β : UnitAddTorus d`, two-sided equidistribution of `n ↦ n • α + β` (`n : ℤ`), total two-sided
equidistribution, and irrationality of `α` are equivalent. -/
theorem linear_equidistributionInt_tfae (α β : UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributedInt (fun n : ℤ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TorusIrrational α] := by
  tfae_have 3 → 2 := fun hα ↦ totallyAsympEquidistributedInt_def.mpr fun q hq r ↦
    asympEquidistributedInt_def.mpr ⟨by
      rw [(funext fun n ↦ by
        rw [← add_assoc, ← natCast_zsmul, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul]
        congr 2; ring :
        (fun n : ℕ ↦ ((q : ℤ) * ((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • (q • α) + (((q : ℤ) + r) • α + β))]
      exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') _, by
      rw [(funext fun n ↦ by
        rw [← add_assoc, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul]; congr 2; ring :
        (fun n : ℕ ↦ ((q : ℤ) * -((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • ((-(q : ℤ)) • α) + ((r - (q : ℤ)) • α + β))]
      exact asympEquidistributed_linear_of_torusIrrational
        (hα.zsmul (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hq.ne'))) _⟩
  tfae_have 2 → 1 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 1 → 3 := fun h ↦
    ((linear_equidistribution_tfae α β).out 1 3).mp (by simpa only [natCast_zsmul] using h.natCast)
  tfae_finish

end Linear

section VanDerCorput

/-- **Van der Corput's difference theorem on `UnitAddTorus d`**: if every positive-lag difference
sequence `n ↦ x (n + h) - x n` (`h > 0`) is equidistributed for Haar probability, then `x` is
equidistributed for Haar probability. -/
theorem vanDerCorput_difference {d : Type*} [Fintype d] {x : ℕ → UnitAddTorus d}
    (hx : ∀ h : ℕ, 0 < h → AsympEquidistributed (fun n ↦ x (n + h) - x n)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  rw [weyl_criterion]; intro k hk
  refine tendsto_cesaro_zero_of_forall_correlation ⟨1, fun n ↦ by simp⟩ fun h hh ↦ ?_
  simpa only [← UnitAddTorus.mFourier_apply_sub] using (weyl_criterion.mp (hx h hh)) k hk

end VanDerCorput

section Polynomial

/-- **Weyl's polynomial equidistribution theorem**: if `s ≥ 1` and the leading coefficient `α s`
is irrational in `UnitAddTorus d`, then the polynomial sequence
`n ↦ ∑ j ∈ range (s + 1), n ^ j • α j` is equidistributed for Haar probability. -/
theorem weyl_polynomial {d : Type*} [Fintype d] (s : ℕ) (hs : 1 ≤ s) (α : ℕ → UnitAddTorus d)
    (hα : TorusIrrational (α s)) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hs; clear hs
  induction m generalizing α with
  | zero =>
    rw [(funext fun n ↦ by simp [sum_range_succ, add_comm] :
      (fun n : ℕ ↦ ∑ j ∈ range 2, n ^ j • α j) = fun n : ℕ ↦ n • α 1 + α 0)]
    exact ((linear_equidistribution_tfae (α 1) (α 0)).out 3 1).mp hα
  | succ m ih =>
    refine vanDerCorput_difference fun h hh ↦ ?_
    let β : ℕ → UnitAddTorus d :=
      fun r ↦ ∑ j ∈ Ico (r + 1) (m + 3), (h ^ (j - r) * j.choose r) • α j
    rw [(funext (poly_sub_shift (m + 2) h α) :
      (fun n : ℕ ↦ (∑ j ∈ range (m + 3), (n + h) ^ j • α j) - ∑ j ∈ range (m + 3), n ^ j • α j)
        = _)]
    exact ih β ((by simp [β, Nat.choose_succ_self_right] : β (m + 1) = (h * (m + 2)) • α (m + 2))
      ▸ hα.nsmul (Nat.mul_ne_zero hh.ne' (Nat.succ_ne_zero _)))

/-- One-dimensional Weyl polynomial equidistribution on `UnitAddCircle`. -/
private theorem weyl_polynomial_addCircle (s : ℕ) (hs : 1 ≤ s) (c : ℕ → UnitAddCircle)
    (hc : addOrderOf (c s) = 0) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  simpa [Fintype.sum_unique] using
    (asympEquidistributed_unitAddTorus_iff_forall_linear_comb.mp
      (weyl_polynomial (d := Unit) s hs (fun j _ ↦ c j) (torusIrrational_unique_iff.mpr hc)))
      (fun _ ↦ 1) (fun h0 ↦ one_ne_zero (congrFun h0 ()))

/-- One-dimensional polynomial sequences with an infinite-order non-constant coefficient are
equidistributed on `UnitAddCircle` along every affine progression `Q * n + R` (`Q ≠ 0`). -/
theorem asympEquidistributed_poly_comp_affine_addCircle {s : ℕ} (c : ℕ → UnitAddCircle)
    (hex : ∃ j ∈ Icc 1 s, addOrderOf (c j) = 0) {Q : ℤ} (hQ : Q ≠ 0) (R : ℤ) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  let S : Finset ℕ := (Icc 1 s).filter (fun j ↦ addOrderOf (c j) = 0)
  have hSne : S.Nonempty := let ⟨j, hj, h0⟩ := hex; ⟨j, mem_filter.mpr ⟨hj, h0⟩⟩
  set j₀ : ℕ := S.max' hSne; have hj₀_mem := mem_filter.mp (max'_mem S hSne)
  have hj₀_ge : 1 ≤ j₀ := (mem_Icc.mp hj₀_mem.1).1
  let D : ℕ := ∏ j ∈ Ioc j₀ s, addOrderOf (c j)
  have hDpos : 0 < D := prod_pos fun j hj ↦ Nat.pos_of_ne_zero fun h0 ↦
    not_le_of_gt (mem_Ioc.mp hj).1 <| le_max' S j <| mem_filter.mpr
      ⟨mem_Icc.mpr ⟨by have := (mem_Ioc.mp hj).1; omega, (mem_Ioc.mp hj).2⟩, h0⟩
  refine asympEquidistributed_of_forall_mod hDpos fun r _ ↦ ?_
  obtain ⟨γ, hγ_lead, hγ_eq⟩ := poly_comp_affine_kill_high hj₀_ge (mem_Icc.mp hj₀_mem.1).2 c
    (q := Q * (D : ℤ)) (fun j hj ↦ by rw [mul_zsmul, natCast_zsmul,
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (dvd_prod_of_mem (fun j ↦ addOrderOf (c j)) hj),
      smul_zero]) (Q * (r : ℤ) + R)
  rw [(funext fun n ↦ by
    have heq : Q * ((D * n + r : ℕ) : ℤ) + R = (Q * (D : ℤ)) * (n : ℤ) + (Q * (r : ℤ) + R) := by
      push_cast; ring
    simp_rw [heq, hγ_eq (n : ℤ), ← Int.natCast_pow, natCast_zsmul] :
    (fun n : ℕ ↦ ∑ j ∈ range (s + 1), (Q * ((D * n + r : ℕ) : ℤ) + R) ^ j • c j) =
      fun n : ℕ ↦ ∑ t ∈ range (j₀ + 1), n ^ t • γ t)]
  exact weyl_polynomial_addCircle j₀ hj₀_ge γ <| by
    rw [hγ_lead, ← torusIrrational_unique_iff (d := Unit) (α := fun _ ↦ (Q * (D : ℤ)) ^ j₀ • c j₀)]
    exact ((torusIrrational_unique_iff (d := Unit) (α := fun _ ↦ c j₀)).mpr hj₀_mem.2).zsmul
      (pow_ne_zero j₀ (mul_ne_zero hQ (Int.natCast_ne_zero.mpr hDpos.ne')))

/-- Sufficient condition for total two-sided equidistribution of a polynomial sequence. -/
private theorem totallyAsympEquidistributedInt_poly_of_forall_addOrderOf {d : Type*} [Fintype d]
    (s : ℕ) (α : ℕ → UnitAddTorus d)
    (h6 : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  have haff (Q R : ℤ) (hQ : Q ≠ 0) :
      AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure :=
    asympEquidistributed_unitAddTorus_iff_forall_linear_comb.mpr fun k hk ↦ by
      simp_rw [(fun n : ℕ ↦
        (by change UnitAddTorus.pairing k _ = _; simp [map_sum, map_zsmul] :
          ∑ i, k i • (∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • α j) i =
            ∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • ∑ i, k i • α j i))]
      exact asympEquidistributed_poly_comp_affine_addCircle _ (h6 k hk) hQ R
  refine totallyAsympEquidistributedInt_def.mpr fun q hq r ↦
    asympEquidistributedInt_def.mpr ⟨?_, ?_⟩
  · rw [(funext fun _ ↦ sum_congr rfl fun _ _ ↦ by ring_nf :
        (fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * ((n : ℤ) + 1) + r) ^ j • α j) =
          fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * (n : ℤ) + ((q : ℤ) + r)) ^ j • α j)]
    exact haff (q : ℤ) ((q : ℤ) + r) (Int.natCast_ne_zero.mpr hq.ne')
  · rw [(funext fun _ ↦ sum_congr rfl fun _ _ ↦ by ring_nf :
        (fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * -((n : ℤ) + 1) + r) ^ j • α j) =
          fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((-(q : ℤ)) * (n : ℤ) + (r - (q : ℤ))) ^ j • α j)]
    exact haff (-(q : ℤ)) (r - (q : ℤ)) (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hq.ne'))

/-- Necessary non-annihilation condition for equidistribution of a polynomial sequence. -/
private theorem forall_pairing_ne_zero_of_asympEquidistributed_poly {d : Type*} [Fintype d]
    (s : ℕ) (α : ℕ → UnitAddTorus d)
    (h1 : AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) :
    ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 := by
  intro k hk; by_contra hnone; push Not at hnone
  have hconst_term (n : ℕ) :
      UnitAddTorus.mFourier k (∑ j ∈ range (s + 1), n ^ j • α j) =
        UnitAddTorus.mFourier k (α 0) := by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, UnitAddTorus.mFourier_eq_fourier_sum]; congr 1
    change UnitAddTorus.pairing k _ = UnitAddTorus.pairing k (α 0)
    rw [map_sum, sum_range_succ', pow_zero, one_nsmul, sum_eq_zero fun j hj ↦ by
      rw [map_nsmul, UnitAddTorus.pairing_apply,
        hnone (j + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩), smul_zero],
      zero_add]
  have hlim := ((weyl_criterion.mp h1) k hk).congr fun n ↦ by
    simp_rw [hconst_term]; simpa only [Nat.succ_eq_add_one, smul_eq_mul] using
      inv_natCast_smul_sum_const (𝕜 := ℂ) (Nat.succ_ne_zero n) (UnitAddTorus.mFourier k (α 0))
  simpa [tendsto_nhds_unique tendsto_const_nhds hlim] using UnitAddTorus.norm_mFourier_apply k (α 0)

/-- **Full equidistribution criterion for polynomial sequences on `UnitAddTorus d`**: for any
`s : ℕ` and `α : ℕ → UnitAddTorus d`, equidistribution on `ℕ`, total equidistribution on `ℕ`,
two-sided equidistribution on `ℤ`, total two-sided equidistribution on `ℤ`, non-annihilation of
`α 1, …, α s` by nonzero frequencies, and existence of an infinite-order pairing are equivalent. -/
theorem polynomial_equidistribution_tfae {d : Type*} [Fintype d] (s : ℕ) (α : ℕ → UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      AsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0,
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0] := by
  have hcast (n : ℕ) :
      ∑ j ∈ range (s + 1), ((n : ℤ) ^ j) • α j = ∑ j ∈ range (s + 1), n ^ j • α j :=
    sum_congr rfl fun j _ ↦ by rw [← Int.natCast_pow, natCast_zsmul]
  tfae_have 6 → 4 := totallyAsympEquidistributedInt_poly_of_forall_addOrderOf s α
  tfae_have 4 → 3 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 4 → 2 := fun h ↦ by simpa only [hcast] using h.totallyAsympEquidistributed_natCast
  tfae_have 3 → 1 := fun h ↦ by simpa only [hcast] using h.natCast
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 5 := forall_pairing_ne_zero_of_asympEquidistributed_poly s α
  tfae_have 5 → 6 := UnitAddTorus.exists_addOrderOf_eq_zero_of_forall_pairing (Icc 1 s) α
  tfae_finish

/-- A polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` in `UnitAddTorus d` is equidistributed for
Haar probability iff no nonzero integer frequency annihilates all of `α 1, …, α s`. -/
theorem polynomial_equidistribution_iff {d : Type*} [Fintype d] (s : ℕ) (α : ℕ → UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 1 5

/-- A polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` in `UnitAddTorus d` is totally equidistributed
for Haar probability iff no nonzero integer frequency annihilates all of `α 1, …, α s`. -/
theorem polynomial_total_equidistribution_iff {d : Type*} [Fintype d] (s : ℕ)
    (α : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 2 5

/-- A doubly infinite polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` (`n : ℤ`) in `UnitAddTorus d`
is totally two-sided equidistributed for Haar probability iff no nonzero integer frequency
annihilates all of `α 1, …, α s`. -/
theorem polynomial_total_equidistributionInt_iff {d : Type*} [Fintype d] (s : ℕ)
    (α : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 4 5

end Polynomial

end TauCeti
