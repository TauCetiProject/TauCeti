/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Radical

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Nullstellensatz

/-!
# Finite infinitesimal quotients of affinoid algebras

An affinoid algebra over a complete nonarchimedean field is noetherian. Its quotient by any
ideal with maximal radical is finite over the coefficient field; in particular, this applies
to every positive power of a maximal ideal. Combined with
`Ideal.iInf_isMaximal_pow_eq_bot`, these finite quotients separate elements of the algebra.
These are the algebraic inputs to the closed-graph argument for automatic continuity.

No norm or topology on the affinoid algebra is selected. The results include nonreduced and
zero algebras, and the zeroth-power quotient is included in the finite-power statement.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.5 and 6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

variable {K A : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CommRing A] [Algebra K A]

/-- Every affinoid algebra over a complete nonarchimedean field is noetherian. -/
theorem isNoetherianRing (hA : IsAffinoidAlgebra K A) : IsNoetherianRing A := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  let := MvPowerSeries.isNoetherianRing_isRestricted_subring
    (K := K) (c := fun _ : Fin n ↦ 1)
  exact isNoetherianRing_of_surjective _ A π.toRingHom hπ

/-- An affinoid quotient whose defining ideal has maximal radical is finite over the
coefficient field. -/
theorem finite_quotient_of_isMaximal_radical (hA : IsAffinoidAlgebra K A) (I : Ideal A)
    [I.radical.IsMaximal] : Module.Finite K (A ⧸ I) := by
  let := hA.isNoetherianRing
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  have := MvPowerSeries.finite_quotient_of_surjective hπ I.radical
  exact I.moduleFinite_quotient_of_radical (IsNoetherian.noetherian _)

/-- Quotients of an affinoid algebra by all powers of a maximal ideal are finite over the
coefficient field, including the zero quotient for exponent zero. -/
theorem finite_quotient_pow (hA : IsAffinoidAlgebra K A) (m : Ideal A) [m.IsMaximal]
    (n : ℕ) : Module.Finite K (A ⧸ m ^ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  · have : (m ^ n).radical.IsMaximal := by
      simpa only [Ideal.radical_pow m hn, Ideal.IsPrime.radical] using
        (inferInstance : m.IsMaximal)
    exact hA.finite_quotient_of_isMaximal_radical (m ^ n)

end TauCeti.IsAffinoidAlgebra
