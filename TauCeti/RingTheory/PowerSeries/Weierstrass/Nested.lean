/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.Analysis.Normed.Unbundled.RootBound
public import TauCeti.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Weierstrass polynomials at nested radii

The monic preparation polynomial on a smaller closed disc divides the preparation
polynomial on a larger closed disc. The quotient is monic, has degree the difference
of the two preparation degrees, and is a unit on the smaller disc. Its roots therefore
lie in the intervening half-open annulus, in any complete isometric field extension.
These comparisons concern given prepared factorizations and require no completeness
of the coefficient ring; completeness is only needed to construct the factorizations.

The polynomial divisibility follows from divisibility reflection for a distinguished
monic polynomial. In particular, the conclusion is polynomial divisibility, not merely
divisibility of formal series, which would lose the disc information.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué
  complet*, §3.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R]
  {r s : ℝ} {d e : ℕ} {f : PowerSeries R} {P Q : Polynomial R}

/-- The monic preparation polynomial at a smaller positive radius divides the one at a
larger radius. The quotient is monic of the difference degree and is a unit of the
smaller restricted-series ring. Neither factorization has to be chosen canonically,
and completeness is not required. -/
theorem IsDistinguished.exists_isMonicOfDegree_mul_eq_of_preparations
    (hf : IsDistinguished r d f) (hr : 0 < r) (hrs : r ≤ s)
    {u : PowerSeries.IsRestricted.subring (R := R) r}
    {v : PowerSeries.IsRestricted.subring (R := R) s}
    (hu : IsUnit u) (hv : IsUnit v) (hP : P.IsMonicOfDegree d)
    (hQ : Q.IsMonicOfDegree e)
    (huf : (u : PowerSeries R) * (P : PowerSeries R) = f)
    (hvf : (v : PowerSeries R) * (Q : PowerSeries R) = f) :
    ∃ A : Polynomial R, A.IsMonicOfDegree (e - d) ∧ Q = P * A ∧
      IsUnit (polynomialToRestricted r A) := by
  have : Nontrivial R := nontrivial_of_ne _ _ hf.coeff_ne_zero
  let v' := restrictedRadiusHom hr.le hrs v
  have hv' : IsUnit v' := hv.map (restrictedRadiusHom hr.le hrs)
  have hvcoe : (v' : PowerSeries R) = v := coe_restrictedRadiusHom hr.le hrs v
  have hPQ : u * polynomialToRestricted r P = v' * polynomialToRestricted r Q := by
    apply Subtype.ext
    simpa only [Subring.coe_mul, coe_polynomialToRestricted, hvcoe]
      using huf.trans hvf.symm
  have hPd : IsDistinguished r d (P : PowerSeries R) :=
    IsDistinguished.of_isUnit_mul (huf ▸ hf) hr hu
  have hdiv : polynomialToRestricted r P ∣ polynomialToRestricted r Q := by
    obtain ⟨w, hw⟩ := hv'.exists_right_inv
    refine ⟨w * u, ?_⟩
    calc polynomialToRestricted r Q = w * (v' * polynomialToRestricted r Q) := by
           rw [← mul_assoc, mul_comm w v', hw, one_mul]
      _ = polynomialToRestricted r P * (w * u) := by rw [← hPQ]; ring
  obtain ⟨A, hA⟩ := (hPd.polynomialToRestricted_dvd_iff hr hP Q).mp hdiv
  have hPA : (P * A).IsMonicOfDegree e := hA ▸ hQ
  have hle : d ≤ e := by
    simpa only [hP.natDegree_eq, hQ.natDegree_eq] using
      Polynomial.natDegree_le_of_dvd ⟨A, hA⟩ hQ.ne_zero
  have hAm : A.IsMonicOfDegree (e - d) :=
    hP.of_mul_left (by simpa only [Nat.add_sub_of_le hle] using hPA)
  have hrel : u = v' * polynomialToRestricted r A := by
    have hP0 : polynomialToRestricted r P ≠ 0 := by
      intro h
      exact hP.ne_zero (Polynomial.coe_injective R (by
        simpa only [coe_polynomialToRestricted, Subring.coe_zero, Polynomial.coe_zero] using
          congrArg (fun x : PowerSeries.IsRestricted.subring (R := R) r =>
            (x : PowerSeries R)) h))
    apply mul_left_cancel₀ hP0
    calc polynomialToRestricted r P * u = v' * polynomialToRestricted r Q := by
           rw [mul_comm]; exact hPQ
      _ = polynomialToRestricted r P * (v' * polynomialToRestricted r A) := by
           rw [hA, map_mul]; ring
  exact ⟨A, hAm, hA, isUnit_of_mul_isUnit_right (hrel ▸ hu)⟩

/-- Every root of a monic polynomial distinguished in its full degree lies in its closed
disc. The coefficient ring need not be complete or a field. -/
theorem IsDistinguished.norm_le_of_eval_eq_zero
    (hP : IsDistinguished r d (P : PowerSeries R)) (hr : 0 < r)
    (hm : P.IsMonicOfDegree d) {x : R} (hx : P.eval x = 0) : ‖x‖ ≤ r := by
  have : Nontrivial R := nontrivial_of_ne _ _ hP.coeff_ne_zero
  have : NormOneClass R := NormMulClass.toNormOneClass
  obtain ⟨i, hi, hxi⟩ := hm.monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero
    (f := normRingNorm R) (fun a n _ => norm_pow a n)
    IsUltrametricDist.isNonarchimedean_norm hx
  rw [hm.natDegree_eq] at hi hxi
  -- The bundled seminorm here is the original norm.
  have hxi' : ‖x‖ ^ (d - i) ≤ ‖P.coeff i‖ := hxi
  have hcoeff : ‖P.coeff i‖ * r ^ i ≤ r ^ d := by
    have h := _root_.PowerSeries.le_gaussNorm norm r (P : PowerSeries R) hP.hasGaussNorm i
    rw [← hP.norm_coeff_mul_pow_eq, hm.coeff_coe_self, norm_one, one_mul,
      Polynomial.coeff_coe] at h
    exact h
  have hpow : ‖x‖ ^ (d - i) ≤ r ^ (d - i) := by
    apply (mul_le_mul_iff_left₀ (pow_pos hr i)).mp
    calc ‖x‖ ^ (d - i) * r ^ i ≤ ‖P.coeff i‖ * r ^ i :=
           mul_le_mul_of_nonneg_right hxi' (pow_nonneg hr.le i)
      _ ≤ r ^ (d - i) * r ^ i := by
           simpa only [← pow_add, Nat.sub_add_cancel hi.le] using hcoeff
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le (Nat.sub_ne_zero_of_lt hi)).mp hpow

section Field

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  {P A : Polynomial K}

/-- A polynomial divisor of a full-degree distinguished polynomial which is a restricted
unit on the smaller disc has all its roots in the half-open annulus `(r,s]`. In particular,
this applies to the quotient of two nested preparation polynomials. No splitting
hypothesis is needed to locate the roots which lie in the given extension. -/
theorem IsDistinguished.norm_mem_Ioc_of_aeval_eq_zero
    (hP : IsDistinguished s d (P : PowerSeries K)) (hr : 0 < r) (hrs : r ≤ s)
    (hm : P.IsMonicOfDegree d) (hA : A ∣ P)
    (hu : IsUnit (polynomialToRestricted r A)) {x : L}
    (hx : Polynomial.aeval x A = 0) : ‖x‖ ∈ Set.Ioc r s := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hlarge : ‖x‖ ≤ s := by
    have hroot : (P.map (algebraMap K L)).eval x = 0 := by
      rw [Polynomial.eval_map_algebraMap]
      exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hA hx
    have hd : IsDistinguished s d (P.map (algebraMap K L) : PowerSeries L) := by
      apply isDistinguished_of_isMonicOfDegree (hr.trans_le hrs) (hm.map _)
      intro i hi
      simp only [Polynomial.coeff_map, norm_algebraMap']
      calc ‖P.coeff i‖ * s ^ i ≤ (P : PowerSeries K).gaussNorm norm s := by
             simpa only [Polynomial.coeff_coe] using
               _root_.PowerSeries.le_gaussNorm norm s (P : PowerSeries K) hP.hasGaussNorm i
        _ = s ^ d := by
             rw [← hP.norm_coeff_mul_pow_eq, hm.coeff_coe_self, norm_one, one_mul]
    exact hd.norm_le_of_eval_eq_zero (hr.trans_le hrs) (hm.map _) hroot
  refine ⟨lt_of_not_ge (fun hsmall => ?_), hlarge⟩
  have hunit := hu.map (_root_.PowerSeries.IsRestricted.evalAtHom K hsmall)
  have hzero : _root_.PowerSeries.IsRestricted.evalAtHom K hsmall
      (polynomialToRestricted r A) = 0 := by
    simpa only [_root_.PowerSeries.IsRestricted.evalAtHom_apply, coe_polynomialToRestricted,
      _root_.PowerSeries.evalAt_coe] using hx
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

end Field

end TauCeti.PowerSeries
