/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Coleman.Measure
public import TauCeti.NumberTheory.Padics.Measure.RootAveraging.Polynomial
public import TauCeti.NumberTheory.Padics.Measure.RootTranslation

/-!
# Integral root averaging and descent

The sum of the `p` root translates of an integral power series is `p` times its
Frobenius-after-psi projection, after embedding the coefficients into the integers of `ℂ_p`.
The root translates are topological evaluations: their arguments may have nonzero constant
terms. All series carry the coefficientwise p-adic topology.

The average descends uniquely to an integral series before Frobenius, namely `psiSeries p F`.
Thus neither division by `p` in the receiving integer ring nor an inverse substitution is
needed to recover psi. The identity follows from `Coleman.Measure`'s trace specialization
`sum_rootTranslation_eq_map_frobeniusHom_trace` together with `Coleman.trace_eq_p_mul_psiSeries`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  §3.5.3–3.5.5, equations (3-5), (3-6), and (3-9).
-/

public section

open PowerSeries TauCeti TauCeti.IwasawaAveraging
open PadicComplex (integralCoefficientMap)
open scoped PowerSeries.WithPiTopology

namespace IsPrimitiveRoot

variable {p : ℕ} [Fact p.Prime] {ζ : 𝓞_ℂ_[p]}

/-- A series descends the integral root average before Frobenius if and only if it is psi
of the original series. This characterizes both the existence and uniqueness of descent. -/
theorem mul_map_subst_eq_sum_rootTranslation_iff (hζ : IsPrimitiveRoot ζ p)
    (F G : ℤ_[p]⟦X⟧) :
    (p : PowerSeries 𝓞_ℂ_[p]) * map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] G) =
      ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F ↔
      G = psiSeries p F := by
  rw [hζ.sum_rootTranslation_eq_map_frobeniusHom_trace, Coleman.trace_eq_p_mul_psiSeries,
    map_mul, map_natCast, map_mul, map_natCast]
  have hp : (p : PowerSeries 𝓞_ℂ_[p]) ≠ 0 := by
    intro h
    have h' := congrArg (fun S : PowerSeries 𝓞_ℂ_[p] ↦ ((constantCoeff S : 𝓞_ℂ_[p]) : ℂ_[p])) h
    have : (p : ℂ_[p]) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  rw [mul_right_inj' hp, (PowerSeries.map_injective (integralCoefficientMap p)
    (PadicComplex.integralCoefficientMap_injective p)).eq_iff,
    (Coleman.frobeniusHom_injective (p := p)).eq_iff]

-- The characterization provides an actual unique integral preimage, without dividing by `p`.
example (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∃! G : ℤ_[p]⟦X⟧, (p : PowerSeries 𝓞_ℂ_[p]) * map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] G) =
      ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F := by
  simp_rw [hζ.mul_map_subst_eq_sum_rootTranslation_iff]
  exact existsUnique_eq

-- The series `(1 + X)⁻¹` has coefficients `(-1)^n`, which do not tend to zero.
-- Nevertheless its root average vanishes, since the atom at `-1` is supported on units.
example (hζ : IsPrimitiveRoot ζ p) :
    ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ)
      (binomialSeries ℤ_[p] (-1 : ℤ_[p])) = 0 := by
  have hu : ¬ (p : ℤ_[p]) ∣ -1 :=
    fun h ↦ PadicInt.p_nonunit (isUnit_of_dvd_unit h (by simp))
  rw [hζ.sum_rootTranslation_eq_map_frobeniusHom_trace, Coleman.trace_eq_p_mul_psiSeries,
    psiSeries_binomialSeries_of_not_dvd hu]
  simp

end IsPrimitiveRoot
