/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.RootBound
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Root bounds for distinguished polynomials

A monic polynomial distinguished in its full degree at a positive radius has all its roots
in the corresponding closed disc. This uses only the Gauss-norm coefficient bounds, without
Weierstrass division or preparation, and applies over ultrametric normed commutative rings
with multiplicative norm, without completeness. It supplies the outer root bound for quotients
of preparation polynomials at nested radii.

The polynomial root estimate is
`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] {c : ℝ} {s : ℕ}

/-- Every root of a monic polynomial distinguished in its full degree lies in its closed
disc. The coefficient ring need not be complete or a field. -/
theorem IsDistinguished.norm_le_of_eval_eq_zero {P : Polynomial R}
    (hP : IsDistinguished c s (P : PowerSeries R)) (hc : 0 < c)
    (hm : P.IsMonicOfDegree s) {x : R} (hx : P.eval x = 0) : ‖x‖ ≤ c := by
  have : Nontrivial R := nontrivial_of_ne _ _ hP.coeff_ne_zero
  have : NormOneClass R := NormMulClass.toNormOneClass
  obtain ⟨i, hi, hxi⟩ := hm.monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero
    (f := normRingNorm R) (fun a n _ => norm_pow a n)
    IsUltrametricDist.isNonarchimedean_norm hx
  rw [hm.natDegree_eq] at hi hxi
  have hxi' : ‖x‖ ^ (s - i) ≤ ‖P.coeff i‖ := by
    simpa only [← RingNorm.toFun_eq_coe, normRingNorm_toFun] using hxi
  have hcoeff : ‖P.coeff i‖ * c ^ i ≤ c ^ s := by
    simpa [← hP.norm_coeff_mul_pow_eq, hm.coeff_coe_self] using
      _root_.PowerSeries.le_gaussNorm norm c (P : PowerSeries R) hP.hasGaussNorm i
  have hpow : ‖x‖ ^ (s - i) ≤ c ^ (s - i) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hc i)).mp
    calc ‖x‖ ^ (s - i) * c ^ i ≤ ‖P.coeff i‖ * c ^ i :=
           mul_le_mul_of_nonneg_right hxi' (pow_nonneg hc.le i)
      _ ≤ c ^ (s - i) * c ^ i := by
           simpa only [← pow_add, Nat.sub_add_cancel hi.le] using hcoeff
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc.le (Nat.sub_ne_zero_of_lt hi)).mp hpow

end TauCeti.PowerSeries
