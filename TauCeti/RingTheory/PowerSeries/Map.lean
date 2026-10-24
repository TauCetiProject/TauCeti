/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.MulDistinguished
import TauCeti.Analysis.Normed.Ring.MulUnit

/-!
# Distinguished series under norm-preserving coefficient maps

A norm-preserving coefficient homomorphism preserves the distinguished degree of a power
series, and also multiplicative distinguishedness. The latter uses the fact that a
norm-preserving homomorphism preserves multiplicative units even when it is not surjective.
These statements let Weierstrass division and preparation be compared after isometric
coefficient extension without rechecking the distinguished-divisor hypotheses.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Definitions 1.20 and 1.24.
-/

public section

namespace TauCeti.PowerSeries

section SeminormedRing

variable {R S : Type*} [SeminormedRing R] [SeminormedRing S]
  {c : ℝ} {s : ℕ} {f : PowerSeries R}

/-- A norm-preserving coefficient homomorphism preserves distinguishedness, with the same
radius and degree. Neither completeness nor surjectivity is required. -/
theorem IsDistinguished.map (hf : IsDistinguished c s f) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) : IsDistinguished c s (PowerSeries.map φ f) := by
  have hn : (PowerSeries.map φ f).gaussNorm norm c = f.gaussNorm norm c := by
    simp only [PowerSeries.gaussNorm_eq, PowerSeries.coeff_map, hφ]
  exact ⟨by simpa only [PowerSeries.coeff_map, hφ, hn] using hf.norm_coeff_mul_pow_eq,
    fun n hn' ↦ by simpa only [PowerSeries.coeff_map, hφ, hn] using
      hf.norm_coeff_mul_pow_lt n hn'⟩

end SeminormedRing

section NormedRing

variable {R S : Type*} [NormedRing R] [SeminormedRing S]
  {c : ℝ} {s : ℕ} {f : PowerSeries R}

/-- A norm-preserving coefficient homomorphism preserves multiplicative distinguishedness,
even without a multiplicative coefficient norm or a surjectivity hypothesis. -/
theorem IsMulDistinguished.map (hf : IsMulDistinguished c s f) (φ : R →+* S)
    (hφ : ∀ a, ‖φ a‖ = ‖a‖) : IsMulDistinguished c s (PowerSeries.map φ f) := by
  have : NormOneClass R := hf.normOneClass
  refine ⟨hf.toIsDistinguished.map φ hφ, ?_⟩
  rw [PowerSeries.coeff_map]
  exact hf.isNormMulUnit_coeff.map φ.toMonoidHom hφ

end NormedRing

end TauCeti.PowerSeries
