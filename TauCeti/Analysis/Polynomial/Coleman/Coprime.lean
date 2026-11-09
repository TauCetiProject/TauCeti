/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Coleman.Entire
public import TauCeti.RingTheory.PowerSeries.Entire.Resultant

/-!
# Coleman's transform detects coprime polynomial factors of entire series

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`, let `Q` be a polynomial
whose leading coefficient has an inverse `c`, and let `Q* = Q.reverse` be its reversal. The
polynomial `B = 1 - c Q*` vanishes at `0` and sends every inverse root of `Q` to `1`. For an entire
series `F` with `F(0) = 1`, the value at `T = 1` of Coleman's transform `D(B, F)` is the entire
resultant of the monic polynomial `c Q` and `F`
(`Polynomial.evalAt_one_colemanDSeries_one_sub_C_mul_reverse`). If `c Q = ∏ (T - rᵢ)` and
`F = ∏ (1 - βⱼ T)`, both sides are `∏ᵢ ∏ⱼ (1 - rᵢ βⱼ)`. Consequently that value is a unit exactly
when `Q` and `F` are coprime in the ring of entire series
(`Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff`).

For a polynomial `F` this is `Polynomial.eval_one_colemanDBounded_one_sub_C_mul_reflect`. The
entire case follows by passing to the limit along the truncations of `F`. On the one side, the
finite transforms of the truncations converge to `D(B, F)` in the Gauss norm at radius one, which
controls evaluation at `1`. On the other, the remainders of the truncations modulo `c Q` converge
coefficientwise to that of `F` (`Polynomial.tendsto_entireResultant_trunc`).

Applied to the Fredholm determinant `F = det (1 - T u)` of a compact operator, `D(B, F)` is the
Fredholm determinant of `B(u)`. This turns coprimality of a polynomial factor of `F` into
invertibility of `Q*(u)`.

## Main results

* `Polynomial.evalAt_one_colemanDSeries_one_sub_C_mul_reverse`: `D(1 - c Q*, F)(1) = Res(c Q, F)`.
* `Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff`: that value is a unit
  exactly when `Q` and `F` are coprime entire series.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
-/

public section

open Filter Topology
open scoped PowerSeries

open PowerSeries (IsEntire)

namespace Polynomial

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [NormOneClass R] [IsUltrametricDist R]
  {Q : R[X]} {c : R} {F : R⟦X⟧}

/-- Let `c` invert the leading coefficient of `Q` and let `F` be an entire series with
`F(0) = 1`. Along `B = 1 - c Q*`, the value at `T = 1` of Coleman's transform of `F` is the entire
resultant of the monic polynomial `c Q` and `F`. -/
theorem evalAt_one_colemanDSeries_one_sub_C_mul_reverse (hc : c * Q.leadingCoeff = 1)
    (hF : F.IsEntire) (hF₀ : PowerSeries.constantCoeff F = 1) :
    ((1 - C c * Q.reverse).colemanDSeries F).evalAt (1 : R) = entireResultant (C c * Q) F := by
  set B := 1 - C c * Q.reverse
  set d := Q.natDegree
  have hB0 : B.coeff 0 = 0 := coeff_zero_one_sub_C_mul_reverse hc
  have hBd : B.natDegree ≤ d := natDegree_one_sub_C_mul_reverse_le c Q
  have hF₀' : PowerSeries.coeff 0 F = 1 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hq : (C c * Q).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hqd : (C c * Q).natDegree = d :=
    natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
  have htrunc₀ (N : ℕ) : (PowerSeries.trunc (N + 1) F).coeff 0 = 1 := by
    simp [PowerSeries.coeff_trunc, hF₀']
  -- the finite transforms of the truncations of `F` at rank `N`
  set D : ℕ → R[X] := fun N ↦ colemanDBounded B (PowerSeries.trunc (N + 1) F) N d
  -- at `T = 1` they are the resultants of `c Q` with the truncations
  have hD (N : ℕ) : (D N).eval 1 = entireResultant (C c * Q) (PowerSeries.trunc (N + 1) F) := by
    rw [entireResultant_coe hq _ (Nat.lt_succ_iff.1 (PowerSeries.natDegree_trunc_lt F N)), hqd]
    exact eval_one_colemanDBounded_one_sub_C_mul_reflect c _ Q N d
  -- and they converge to `D(B, F)` in the Gauss norm at radius one
  have hE := PowerSeries.colemanDEntire_coe (F := F) hB0 hF₀'
  have hEe : (B.colemanDSeries F).IsEntire :=
    hE ▸ PowerSeries.isEntire_colemanDEntire (PowerSeries.isEntire_coe B) hF
      (by rwa [Polynomial.coeff_coe]) hF₀'
  have hgauss : Tendsto (fun N ↦ ((D N : R⟦X⟧) - B.colemanDSeries F).gaussNorm norm 1) atTop
      (𝓝 0) := by
    refine ((hE ▸ PowerSeries.tendsto_gaussNorm_colemanDBounded_trunc_sub_colemanDEntire
      (PowerSeries.isEntire_coe B) hF (by rwa [Polynomial.coeff_coe]) hF₀' one_pos).comp
      tendsto_atTop_diagonal).congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    rw [Function.comp_apply, PowerSeries.trunc_coe_eq_self (Nat.lt_succ_of_le (hBd.trans hN)),
      colemanDBounded_of_natDegree_le (hBd.trans hN) (htrunc₀ N),
      ← colemanDBounded_of_natDegree_le hBd (htrunc₀ N)]
  have hL : Tendsto (fun N ↦ (D N).eval 1) atTop (𝓝 ((B.colemanDSeries F).evalAt (1 : R))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_) hgauss
    have hsub := ((PowerSeries.isEntire_coe (D N)).sub hEe).isRestricted 1
    rw [← coe_aeval_eq_eval, ← PowerSeries.evalAt_coe,
      ← (PowerSeries.isEntire_coe (D N)).evalAt_sub hEe]
    exact PowerSeries.norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      hsub) norm_one.le
  exact tendsto_nhds_unique hL (((tendsto_entireResultant_trunc hq hF).comp
    (tendsto_add_atTop_nat 1)).congr fun N ↦ (hD N).symm)

/-- **Coleman's transform detects coprime factors.** Let `c` invert the leading coefficient of `Q`
and let `F` be an entire series with `F(0) = 1`. Along `B = 1 - c Q*`, the value at `T = 1` of
Coleman's transform of `F` is a unit exactly when `Q` and `F` are coprime in the ring of entire
series. -/
theorem isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff (hc : c * Q.leadingCoeff = 1)
    (hF : F.IsEntire) (hF₀ : PowerSeries.constantCoeff F = 1) :
    IsUnit (((1 - C c * Q.reverse).colemanDSeries F).evalAt (1 : R)) ↔
      IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
        ⟨F, IsEntire.mem_subring.mpr hF⟩ := by
  rw [evalAt_one_colemanDSeries_one_sub_C_mul_reverse hc hF hF₀,
    isUnit_entireResultant_iff (monic_C_mul_of_mul_leadingCoeff_eq_one hc) hF]
  -- `c Q` is the unit `c` times `Q` in the ring of entire series
  have hunit : IsUnit (⟨C c, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩ :
      IsEntire.subring R) :=
    IsUnit.of_mul_eq_one ⟨C Q.leadingCoeff, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe _)⟩
      (Subtype.ext (by simpa using congrArg PowerSeries.C hc))
  convert isCoprime_mul_unit_left_left hunit _ _ using 2
  exact Subtype.ext (by simp)

end Polynomial
