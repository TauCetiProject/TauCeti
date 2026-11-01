/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Eval
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Taylor coefficients determine an entire series

Evaluating an entire series at `X + a` in a Gauss-normed restricted-series ring gives
its Taylor expansion at `a`: the coefficients are the evaluated Hasse derivatives.
Translation is injective, so these values cannot all vanish for a nonzero series.
This supplies the finite-order argument for zeros over a field without any factorial
or characteristic-zero assumption.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127
  (1997), Appendix A3–A4.
-/

public section

namespace PowerSeries

open Filter Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {f : R⟦X⟧}

/-- The Taylor coefficients of an entire series, computed in any positive-radius
Gauss-normed restricted-series ring, are its evaluated Hasse derivatives. -/
theorem IsEntire.coeff_evalAt_X_add_C (hf : f.IsEntire) (a : R) (c : ℝ)
    [Fact (0 < c)] (k : ℕ) :
    coeff k ((f.evalAt
      ((⟨X, isEntire_X.isRestricted c⟩ : IsRestricted.subring (R := R) c) +
        algebraMap R (IsRestricted.subring c) a :
        IsRestricted.subring c) : IsRestricted.subring c) : R⟦X⟧) =
      (PowerSeries.hasseDeriv k f).evalAt a := by
  let S := IsRestricted.subring (R := R) c
  have hnorm (r : R) : ‖algebraMap R S r‖ = ‖r‖ :=
    MvPowerSeries.norm_algebraMap_isRestrictedSubring (c := fun _ : Unit ↦ c) r
  have hmap (r : R) : (algebraMap R S r : R⟦X⟧) = C r :=
    MvPowerSeries.coe_algebraMap_isRestrictedSubring r
  let : IsBoundedSMul R S := .of_norm_smul_le fun r g ↦ by
    simpa only [Algebra.smul_def, hnorm]
      using norm_mul_le (algebraMap R S r) g
  let b : S := ⟨X, isEntire_X.isRestricted c⟩ + algebraMap R S a
  have hp (n : ℕ) : coeff k ((b ^ n : S) : R⟦X⟧) = a ^ (n - k) * (n.choose k : R) := by
    have hb : (b : R⟦X⟧) = ((Polynomial.X + Polynomial.C a : Polynomial R) : R⟦X⟧) := by
      simp [b, Polynomial.coe_add, hmap]
    rw [Subring.coe_pow, hb, ← Polynomial.coe_pow, Polynomial.coeff_coe,
      Polynomial.coeff_X_add_C_pow]
  have h : HasSum (fun n ↦ coeff k ((coeff n f • b ^ n : S) : R⟦X⟧))
      (coeff k ((f.evalAt b : S) : R⟦X⟧)) := (hf.hasSum_evalAt b).map
    ((coeff k).toAddMonoidHom.comp (IsRestricted.subring c).subtype.toAddMonoidHom)
    (TauCeti.PowerSeries.uniformContinuous_coeff k).continuous
  have hterm (n : ℕ) : coeff k ((coeff n f • b ^ n : S) : R⟦X⟧) =
      coeff n f * (a ^ (n - k) * (n.choose k : R)) := by
    rw [Algebra.smul_def, Subring.coe_mul, hmap, coeff_C_mul, hp]
  simp only [hterm] at h
  have hhead : ∑ n ∈ Finset.range k,
      coeff n f * (a ^ (n - k) * (n.choose k : R)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
  rw [← add_zero (coeff k ((f.evalAt b : S) : R⟦X⟧)), ← hhead,
    ← hasSum_nat_add_iff k] at h
  have hder := (hf.hasseDeriv k).hasSum_evalAt a
  apply HasSum.unique h
  convert hder using 1
  ext n
  simp [coeff_hasseDeriv, mul_comm, mul_assoc]

variable [NormOneClass R]

/-- An entire series whose Hasse derivatives all vanish at one point is zero.
This is injectivity of Taylor expansion, valid over coefficient rings with nilpotents. -/
theorem IsEntire.eq_zero_of_forall_evalAt_hasseDeriv_eq_zero (hf : f.IsEntire) (a : R)
    (h : ∀ k, (PowerSeries.hasseDeriv k f).evalAt a = 0) : f = 0 := by
  -- Work on a disc large enough that translation by -a is bounded.
  let c : ℝ := ‖a‖ + 1
  let : Fact (0 < c) := ⟨by dsimp [c]; positivity⟩
  let S := IsRestricted.subring (R := R) c
  have hnorm (r : R) : ‖algebraMap R S r‖ = ‖r‖ :=
    MvPowerSeries.norm_algebraMap_isRestrictedSubring (c := fun _ : Unit ↦ c) r
  have hmap (r : R) : (algebraMap R S r : R⟦X⟧) = C r :=
    MvPowerSeries.coe_algebraMap_isRestrictedSubring r
  let : IsBoundedSMul R S := .of_norm_smul_le fun r g ↦ by
    simpa only [Algebra.smul_def, hnorm]
      using norm_mul_le (algebraMap R S r) g
  let x : S := ⟨X, isEntire_X.isRestricted c⟩
  have hx : ‖x‖ = c := TauCeti.PowerSeries.norm_X
  have ha : ‖x - algebraMap R S a‖ ≤ c := by
    have hbound : ‖x - algebraMap R S a‖ ≤ max ‖x‖ ‖algebraMap R S a‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (IsUltrametricDist.norm_add_le_max x (-algebraMap R S a))
    apply hbound.trans
    rw [hx, hnorm]
    exact max_le le_rfl (by dsimp [c]; linarith)
  let t : S →ₐ[R] S :=
    { IsRestricted.evalAtHom R ha with
      commutes' := fun r ↦ by
        exact (IsRestricted.evalAtHom_apply ha _).trans (by rw [hmap, evalAt_C]) }
  have ht : Continuous t := AddMonoidHomClass.continuous_of_bound t 1 fun g ↦ by
    calc
      ‖t g‖ = ‖(g : R⟦X⟧).evalAt (x - algebraMap R S a)‖ :=
        congrArg norm (IsRestricted.evalAtHom_apply ha g)
      _ ≤ (g : R⟦X⟧).gaussNorm norm c :=
        norm_evalAt_le_gaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted g.2) ha
      _ = 1 * ‖g‖ := by rw [one_mul]; exact (TauCeti.PowerSeries.norm_eq_gaussNorm g).symm
  -- The translated series is zero coefficientwise; translating back recovers f.
  have hz : f.evalAt (x + algebraMap R S a) = 0 := by
    apply Subtype.ext
    ext k
    simpa [x, h k] using hf.coeff_evalAt_X_add_C a c k
  have htval : t (x + algebraMap R S a) = x := by
    rw [map_add, AlgHom.commutes]
    have htx : t x = x - algebraMap R S a := by
      dsimp [t]
      rw [IsRestricted.evalAtHom_apply]
      exact evalAt_X _
    rw [htx, sub_add_cancel]
  have hfx : f.evalAt x = 0 := by
    rw [← htval, ← hf.map_evalAt t ht, hz, map_zero]
  have hcoeff (k : ℕ) : coeff k ((f.evalAt x : S) : R⟦X⟧) = coeff k f := by
    simpa [x, evalAt_at_zero, ← coeff_zero_eq_constantCoeff, coeff_hasseDeriv] using
      hf.coeff_evalAt_X_add_C (0 : R) c k
  ext k
  simpa [hfx] using (hcoeff k).symm

end PowerSeries
