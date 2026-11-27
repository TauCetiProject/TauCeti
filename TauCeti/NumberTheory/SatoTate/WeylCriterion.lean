/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.AlgebraicGeometry.EllipticCurve.FrobeniusAngle
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GoodPrimes.Finite
import TauCeti.RepresentationTheory.SU2.Weyl.Angle
import TauCeti.RepresentationTheory.SU2.Weyl.Criterion

/-!
# The Weyl criterion for elliptic Frobenius angles

For an elliptic curve over `ℚ`, average the Frobenius angles over the good primes up to a cutoff.
These averages converge against all continuous test functions to the `SU(2)` Weyl density
precisely when the averages of `U_d(cos θ_p)` tend to zero for every positive degree `d`. These
Chebyshev values are the characters of the symmetric powers of the normalized Frobenius classes.

See K. S. Kedlaya, *Notes on analytic number theory*, §§24.2 and 24.5.
-/

public section

open Filter MeasureTheory Polynomial TauCeti
open scoped BigOperators Topology

namespace WeierstrassCurve

/-- The Frobenius angles of an elliptic curve over `ℚ` are equidistributed for
`(2/π) sin² θ dθ` exactly when every positive-degree symmetric-power character has good-prime
average tending to zero. Both averages use the same good primes up to the cutoff. -/
theorem tendsto_frobeniusAngle_average_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 Real.pi) →
      Tendsto (fun x : ℕ ↦
        (∑ p ∈ E.goodReductionPrimes x, f (E.frobeniusAngle p)) /
          (E.goodReductionPrimes x).card)
        atTop (𝓝 ((2 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2))) ↔
    ∀ d : ℕ, d ≠ 0 →
      Tendsto (fun x : ℕ ↦
        (∑ p ∈ E.goodReductionPrimes x,
          (Chebyshev.U ℝ d).eval (Real.cos (E.frobeniusAngle p))) /
          (E.goodReductionPrimes x).card) atTop (𝓝 0) := by
  simp_rw [← Finset.expect_eq_sum_div_card]
  let g (p : Nat.Primes) := SU2.torusExp (E.frobeniusAngle p)
  have hangle (p : Nat.Primes) : SU2.conjugacyAngle (g p) = E.frobeniusAngle p :=
    SU2.conjugacyAngle_torusExp ⟨E.frobeniusAngle_nonneg p, E.frobeniusAngle_le_pi p⟩
  let U (d : ℕ) (θ : ℝ) := (Chebyshev.U ℝ d).eval (Real.cos θ)
  have hchar (d : ℕ) (a : SU2) :
      (SU2.symPower d).character a = (U d (SU2.conjugacyAngle a) : ℂ) :=
    SU2.character_symPower_eq_chebyshevU_eval_cos_conjugacyAngle d a
  constructor
  · intro h d hd
    have hU : ContinuousOn (U d) (Set.Icc 0 Real.pi) :=
      ((Chebyshev.U ℝ d).continuous.comp Real.continuous_cos).continuousOn
    have hzero : (2 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, U d θ * Real.sin θ ^ 2 = 0 := by
      rw [← SU2.integral_comp_conjugacyAngle hU]
      apply Complex.ofReal_injective
      rw [← integral_complex_ofReal, Complex.ofReal_zero]
      simp only [← hchar, SU2.integral_character_symPower, ite_eq_right hd]
    simpa only [hzero, U] using h (U d) hU
  · intro h f hf
    have hχ (d : ℕ) (hd : d ≠ 0) :
        Tendsto (fun x ↦ 𝔼 p ∈ E.goodReductionPrimes x, (SU2.symPower d).character (g p))
          atTop (𝓝 0) := by
      have hh := (Complex.continuous_ofReal.tendsto 0).comp (h d hd)
      simpa [Function.comp_def, hchar, hangle, U, Finset.expect_eq_sum_div_card,
        Complex.ofReal_div] using hh
    have hc : Continuous (f ∘ SU2.conjugacyAngle) :=
      hf.comp_continuous SU2.continuous_conjugacyAngle SU2.conjugacyAngle_mem_Icc
    let F : C(SU2, ℂ) := ⟨Complex.ofReal ∘ f ∘ SU2.conjugacyAngle,
      Complex.continuous_ofReal.comp hc⟩
    have hinv (u a : SU2) : F (u * a * u⁻¹) = F a := by
      have hconj : IsConj (u * a * u⁻¹) a := (isConj_iff.mpr ⟨u, rfl⟩).symm
      simp [F, SU2.conjugacyAngle_eq_of_isConj hconj]
    have hl := (SU2.tendsto_expect_classFunction_iff E.goodReductionPrimes g
      E.eventually_goodReductionPrimes_nonempty).mpr hχ F hinv
    have hl' := (Complex.continuous_re.tendsto _).comp hl
    simpa [F, Function.comp_def, hangle, Finset.expect_eq_sum_div_card, ← Complex.ofReal_div,
      integral_complex_ofReal, SU2.integral_comp_conjugacyAngle hf] using hl'

end WeierstrassCurve
