/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.NoetherNormalization
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.KrullDimension
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.RingTheory.KrullDimension.Basic

/-!
# Krull dimension of affinoid algebras

A nonzero affinoid algebra `A` over a complete nonarchimedean field is finite over an injectively
embedded Tate algebra in exactly `dim A` variables. In particular `A` has finite Krull dimension,
so the dimension theory of noetherian rings of finite Krull dimension applies to it.

The normalisation comes from `TauCeti.IsAffinoidAlgebra.exists_finite_injective`, and its number of
variables is the Krull dimension by
`TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral`, since finite injective extensions
preserve Krull dimension.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.2.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- **Affinoid Noether normalisation in the dimension of the algebra.** A nonzero affinoid
algebra `A` is finite over an injectively embedded Tate algebra in `n` variables, where `n` is
the Krull dimension of `A`. Every such normalisation has this number of variables, by
`TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral`. -/
theorem exists_ringKrullDim_eq_finite_injective [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    ∃ n : ℕ, ringKrullDim A = n ∧
      ∃ g : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →ₐ[K] A,
        Function.Injective g ∧ g.Finite := by
  obtain ⟨n, g, hg, hfin⟩ := hA.exists_finite_injective
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let := g.toRingHom.toAlgebra
  have : Module.Finite T A := hfin
  have : Algebra.IsIntegral T A := Algebra.IsIntegral.of_finite T A
  have : FaithfulSMul T A := (faithfulSMul_iff_algebraMap_injective T A).mpr hg
  refine ⟨n, ?_, g, hg, hfin⟩
  simpa using MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral (K := K) (σ := Fin n) (A := A)

/-- A nonzero affinoid algebra has finite Krull dimension. -/
theorem finiteRingKrullDim [Nontrivial A] (hA : IsAffinoidAlgebra K A) : FiniteRingKrullDim A := by
  obtain ⟨n, hn, -⟩ := hA.exists_ringKrullDim_eq_finite_injective
  exact .of_ringKrullDim_eq_natCast hn

end TauCeti.IsAffinoidAlgebra
