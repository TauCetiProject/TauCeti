/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.NoetherNormalization
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.KrullDimension
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# Krull dimension of affinoid algebras

A nonzero affinoid algebra `A` over a complete nonarchimedean field is finite over an injectively
embedded Tate algebra in exactly `dim A` variables. In particular `A` has finite Krull dimension,
so the dimension theory of noetherian rings of finite Krull dimension applies to it.

The normalisation comes from `TauCeti.IsAffinoidAlgebra.exists_finite_injective`, and its number of
variables is the Krull dimension by
`TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral`, since finite injective extensions
preserve Krull dimension.

When `A` is a domain, every maximal ideal `m` of `A` has height `dim A`. The Tate algebra
`T = K⟨X₁, …, Xₙ⟩` of a normalisation is a unique factorisation domain, hence integrally closed, so
going down holds for the integral extension `T → A` of domains. Thus `m` has height at least that
of its contraction to `T`, a maximal ideal of height `n = dim A`.

For a general affinoid algebra the corresponding statements are componentwise. Applied to the
affinoid domains `A ⧸ P`, the domain case shows that a maximal ideal `m ⊇ P` has height
`dim (A ⧸ P)` in `A ⧸ P`. Hence the height of `m` is the largest dimension of an irreducible
component `V(P)` of `Spec A` through `m`. Components of different dimensions may occur, so a
maximal ideal can have height smaller than `dim A`: in `K⟨T⟩ × K` the maximal ideal `K⟨T⟩ × 0` has
height zero although the ring has dimension one.

## Main results

* `TauCeti.IsAffinoidAlgebra.exists_ringKrullDim_eq_finite_injective`: a nonzero affinoid algebra
  is finite over an injectively embedded Tate algebra in `dim A` variables.
* `TauCeti.IsAffinoidAlgebra.height_eq_ringKrullDim_of_isDomain`: every maximal ideal of an
  affinoid domain `A` has height `dim A`.
* `TauCeti.IsAffinoidAlgebra.height_map_quotientMk_eq_ringKrullDim_quotient`: for a prime `P`
  contained in a maximal ideal `m`, the image of `m` in `A ⧸ P` has height `dim (A ⧸ P)`.
* `TauCeti.IsAffinoidAlgebra.exists_mem_minimalPrimes_height_eq_ringKrullDim_quotient`: the height
  of a maximal ideal `m` is the dimension of an irreducible component through `m`, and it bounds
  the dimension of every such component by
  `TauCeti.IsAffinoidAlgebra.ringKrullDim_quotient_le_height`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.2.
* B. Conrad, *Irreducible components of rigid spaces*, Ann. Inst. Fourier 49 (1999), 473–541,
  Lemma 2.1.5.
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

/-- **Heights of maximal ideals of affinoid domains.** Every maximal ideal of an affinoid domain
`A` has height `dim A`. -/
theorem height_eq_ringKrullDim_of_isDomain [IsDomain A] (hA : IsAffinoidAlgebra K A)
    (m : Ideal A) [m.IsMaximal] : (m.height : WithBot ℕ∞) = ringKrullDim A := by
  -- A normalisation `T = K⟨X₁, …, Xₙ⟩ → A` gives `dim A = n`. Since `T` is integrally closed and
  -- `A` is a domain, going down gives `m` the height of its contraction to `T`, a maximal ideal of
  -- height `n`.
  obtain ⟨n, hn, g, hg, hfin⟩ := hA.exists_ringKrullDim_eq_finite_injective
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let := g.toRingHom.toAlgebra
  have : Module.Finite T A := hfin
  have : Algebra.IsIntegral T A := Algebra.IsIntegral.of_finite T A
  have : IsNoetherianRing T := MvPowerSeries.isNoetherianRing_isRestricted_subring
  have : IsNoetherianRing A := hA.isNoetherianRing
  have : FaithfulSMul T A := (faithfulSMul_iff_algebraMap_injective T A).mpr hg
  have : (m.under T).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  rw [hn, Ideal.height_eq_height_under_of_quasiFinite (R := T) m,
    Ideal.height_eq_natCard_of_isMaximal_isRestricted_subring, Nat.card_fin]
  norm_cast

/-- **Heights of maximal ideals on irreducible closed subsets.** For a prime `P` of an affinoid
algebra `A` contained in a maximal ideal `m`, the image of `m` in the affinoid domain `A ⧸ P` has
height `dim (A ⧸ P)`. -/
theorem height_map_quotientMk_eq_ringKrullDim_quotient (hA : IsAffinoidAlgebra K A)
    {P m : Ideal A} [P.IsPrime] [m.IsMaximal] (hPm : P ≤ m) :
    ((m.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) = ringKrullDim (A ⧸ P) := by
  have : (m.map (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  exact (hA.quotient P).height_eq_ringKrullDim_of_isDomain _

/-- Every irreducible closed subset `V(P)` of `Spec A` through a maximal ideal `m` of an affinoid
algebra `A` has dimension at most the height of `m`. -/
theorem ringKrullDim_quotient_le_height (hA : IsAffinoidAlgebra K A) {P m : Ideal A} [P.IsPrime]
    [m.IsMaximal] (hPm : P ≤ m) : ringKrullDim (A ⧸ P) ≤ m.height := by
  rw [← hA.height_map_quotientMk_eq_ringKrullDim_quotient hPm]
  exact_mod_cast Ideal.height_map_quotientMk_le hPm

/-- **Heights of maximal ideals of affinoid algebras.** The height of a maximal ideal `m` of an
affinoid algebra `A` is the dimension of some irreducible component `V(P)` of `Spec A` through
`m`, and is at least the dimension of every irreducible component through `m`, by
`TauCeti.IsAffinoidAlgebra.ringKrullDim_quotient_le_height`. Different components through `m` may
have different dimensions. -/
theorem exists_mem_minimalPrimes_height_eq_ringKrullDim_quotient (hA : IsAffinoidAlgebra K A)
    (m : Ideal A) [m.IsMaximal] :
    ∃ P ∈ minimalPrimes A, P ≤ m ∧ (m.height : WithBot ℕ∞) = ringKrullDim (A ⧸ P) := by
  have : IsNoetherianRing A := hA.isNoetherianRing
  obtain ⟨P, hP, hPm, h⟩ := m.exists_mem_minimalPrimes_height_map_quotientMk_eq
  have : P.IsPrime := hP.1.1
  exact ⟨P, hP, hPm, h ▸ hA.height_map_quotientMk_eq_ringKrullDim_quotient hPm⟩

end TauCeti.IsAffinoidAlgebra
