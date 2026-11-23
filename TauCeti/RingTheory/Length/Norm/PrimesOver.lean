/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Length.Norm.Basic
public import TauCeti.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# The order of a norm, over the primes above a prime

Let `B₀` be a domain finite over a ring `A₀`, `p` a prime of `A₀` such that the localization
`A = (A₀)_p` is Noetherian of dimension at most one, `K` the fraction field of `A` and `L` that of
`B₀`. For `r ≠ 0` in `L`,
`ord_A N_{L/K}(r) = Σ_{q ∣ p} [κ(q) : κ(p)] ord_{(B₀)_q}(r)`, the sum running over the primes `q`
of `B₀` above `p` (Fulton, *Intersection Theory*, Appendix A.3, in the global form of
Example A.3.1 / Proposition 1.4(b)). This is `TauCeti.ordFrac_norm_eq_finprod_primesOver`, written
multiplicatively in `ℤᵐ⁰`, with the orders taken in arbitrary localizations `R q` of `B₀` at `q`
(such as the local rings of a scheme at the points of a fibre) and the residue degree read as the
`A`-length of the residue field of `R q`.

It is derived from `TauCeti.ordFrac_norm_eq_finprod_of_isLocalization`, the local form
`TauCeti.ordFrac_norm_eq_finprod` (where `A` is local and the sum runs over the maximal ideals of a
domain `B` finite over `A`) with `B` a localization of `B₀` and the orders taken in localizations of
`B₀` at the primes `m ∩ B₀`. It is applied to the semilocal ring `B = (B₀)_p`, finite over `A`, and
reindexed along the bijection `IsLocalization.AtPrime.maximalSpectrumEquivPrimesOver` between the
maximal ideals of `B` and the primes of `B₀` over `p`; the residue degrees are compared through
`B ⧸ m ≅ κ(B_m) ≅ κ(R q)`.

This is the coefficient identity behind the pushforward of principal divisors along a morphism
that is finite over an affine neighbourhood of a codimension-one point.
-/

public section

open Algebra IsLocalRing

namespace TauCeti

section PrimesOver

variable {A₀ B₀ A K L : Type*} [CommRing A₀] [CommRing B₀] [IsDomain B₀]
  [Algebra A₀ B₀] [Module.Finite A₀ B₀] (p : Ideal A₀) [p.IsPrime]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra A₀ A]
  [IsLocalization.AtPrime A p] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B₀ L] [IsFractionRing B₀ L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra A₀ L] [IsScalarTower A₀ A L] [IsScalarTower A₀ B₀ L]
  (R : p.primesOver B₀ → Type*) [∀ q, CommRing (R q)] [∀ q, IsLocalRing (R q)]
  [∀ q, IsNoetherianRing (R q)] [∀ q, Ring.KrullDimLE 1 (R q)]
  [∀ q, Algebra B₀ (R q)] [∀ q, IsLocalization.AtPrime (R q) q.val] [∀ q, Algebra (R q) L]
  [∀ q, IsScalarTower B₀ (R q) L] [∀ q, IsFractionRing (R q) L] [∀ q, Algebra A (R q)]
  [∀ q, Algebra A₀ (R q)] [∀ q, IsScalarTower A₀ A (R q)] [∀ q, IsScalarTower A₀ B₀ (R q)]

/-- **The order of a norm, over the primes above `p`** (Fulton, *Intersection Theory*,
Appendix A.3). Let `B₀` be a domain finite over a ring `A₀`, `p` a prime of `A₀` with
`A = (A₀)_p` Noetherian of dimension at most one, and `R q` a localization of `B₀` at each prime
`q` over `p`. For `r ≠ 0` in the fraction field `L` of `B₀`,
`ord_A N_{L/K}(r) = Σ_q [κ(R q) : κ(A)] ord_{R q}(r)`, written multiplicatively in `ℤᵐ⁰`, with the
residue degree read as the `A`-length of the residue field of `R q`. -/
theorem ordFrac_norm_eq_finprod_primesOver {r : L} (hr : r ≠ 0) :
    Ring.ordFrac A (Algebra.norm K r) =
      ∏ᶠ q, Ring.ordFrac (R q) r ^ (Module.length A (ResidueField (R q))).toNat := by
  -- The elements of `A₀ \ p` become units in `A`, hence in `L`, so they are nonzero in `B₀`.
  have hS : algebraMapSubmonoid B₀ p.primeCompl ≤ nonZeroDivisors B₀ := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ not_isUnit_zero (M₀ := L) ?_
    simpa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A₀ B₀ L, h] using
      (IsLocalization.map_units A (⟨a, ha⟩ : p.primeCompl)).map (algebraMap A L)
  -- The semilocal ring `B = (B₀)_p`, a domain finite over `A` with fraction field `L`.
  let B := Localization (algebraMapSubmonoid B₀ p.primeCompl)
  let _ : Algebra A B := localizationAlgebra p.primeCompl B₀
  have : IsScalarTower A₀ A B := isScalarTower_localizationAlgebra p.primeCompl B₀
  have : Module.Finite A B := Module.Finite.of_isLocalization A₀ B₀ p.primeCompl
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  let _ : Algebra B L :=
    IsLocalization.localizationAlgebraOfSubmonoidLe B L _ (nonZeroDivisors B₀) hS
  have : IsScalarTower B₀ B L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B L _ (nonZeroDivisors B₀) hS
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isLocalization (algebraMapSubmonoid B₀ p.primeCompl) B L hS
  have : IsScalarTower A₀ B L := .to₁₃₄ A₀ B₀ B L
  have : IsScalarTower A B L := .of_algebraMap_eq' <| IsLocalization.ringHom_ext p.primeCompl <| by
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  let e := IsLocalization.AtPrime.maximalSpectrumEquivPrimesOver (S := B₀) p A B
  have (m : MaximalSpectrum B) :
      IsLocalization.AtPrime (R (e m)) (m.asIdeal.comap (algebraMap B₀ B)) := by
    convert (inferInstance : IsLocalization.AtPrime (R (e m)) (e m).val)
    exact (IsLocalization.AtPrime.coe_maximalSpectrumEquivPrimesOver_apply p A B m).symm
  rw [ordFrac_norm_eq_finprod_of_isLocalization (K := K) (B := B)
    (algebraMapSubmonoid B₀ p.primeCompl) (fun m ↦ R (e m)) hr, ← finprod_comp_equiv e]
  congr! with m
  -- The residue degree: `B ⧸ m ≅ κ(B_m) ≅ κ(R q)` as `A`-modules.
  rw [← MaximalSpectrum.length_residueField_localization_eq]
  let f : Localization.AtPrime m.asIdeal ≃ₐ[B₀] R (e m) :=
    IsLocalization.algEquiv (m.asIdeal.comap (algebraMap B₀ B)).primeCompl _ _
  exact (ResidueField.mapAlgEquiv <|
    (f.restrictScalars A₀).extendScalarsOfIsLocalization A p.primeCompl).toLinearEquiv.length_eq

end PrimesOver

end TauCeti
