/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.NumberTheory.Equidistribution.Weyl
public import TauCeti.Topology.Instances.AddCircle.UnitAddTorus
import TauCeti.Algebra.BigOperators.Finset.Average
import TauCeti.Analysis.Fourier.Monomial

/-!
# Equidistribution of linear orbits on `UnitAddTorus d`

Equidistribution and total equidistribution (over `ℕ` and `ℤ`) of `n ↦ n • α + β` on
`UnitAddTorus d`, characterized by `TorusIrrational α`: `TauCeti.linear_equidistribution_tfae`
and `TauCeti.linear_equidistributionInt_tfae`.

## References

* T. Tao, *Higher Order Fourier Analysis*, GSM 142, AMS, 2012, §1.1.1 (Cor. 1.1.3,
  Ex. 1.1.1, 1.1.4).
-/

public section

open Filter Finset MeasureTheory Topology

namespace TauCeti

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

/-- **Equidistribution of linear orbits on `UnitAddTorus d`**: equivalence of equidistribution,
total equidistribution, and `TorusIrrational α` for `n ↦ n • α + β` (`n : ℕ`). -/
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

/-- **Equidistribution of doubly infinite linear orbits on `UnitAddTorus d`**: equivalence of
two-sided equidistribution, total two-sided equidistribution, and `TorusIrrational α`. -/
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
        rw [← add_assoc, ← natCast_zsmul, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul]; congr 2; ring
        : (fun n : ℕ ↦ ((q : ℤ) * ((n : ℤ) + 1) + r) • α + β) =
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

end TauCeti
