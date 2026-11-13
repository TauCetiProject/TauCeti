/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Length.Norm
public import TauCeti.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# The order of a norm, over the primes above a prime

Let `B₀` be a domain finite over a domain `A₀`, `p` a prime of `A₀` such that the localization
`A = (A₀)_p` is Noetherian of dimension at most one, `K` the fraction field of `A` and `L` that of
`B₀`. For `r ≠ 0` in `L`,
`ord_A N_{L/K}(r) = Σ_{q ∣ p} [κ(q) : κ(p)] ord_{(B₀)_q}(r)`, the sum running over the primes `q`
of `B₀` above `p` (Fulton, *Intersection Theory*, Appendix A.3, in the global form of
Example A.3.1 / Proposition 1.4(b)). This is `TauCeti.ordFrac_norm_eq_finprod_primesOver`, written
multiplicatively in `ℤᵐ⁰`, with the orders taken in arbitrary localizations `R q` of `B₀` at `q`
(such as the local rings of a scheme at the points of a fibre) and the residue degree read as the
`A`-length of the residue field of `R q`.

It is derived from the local form `TauCeti.ordFrac_norm_eq_finprod` (where `A` is local and the
sum runs over the maximal ideals of a domain `B` finite over `A`) in two steps:

* `TauCeti.ordFrac_norm_eq_finprod_of_isLocalization`: the local form when `B` is a localization
  of a ring `B₀` and the orders are taken in localizations of `B₀` (rather than of `B`) at the
  primes `m ∩ B₀`;
* `TauCeti.ordFrac_norm_eq_finprod_primesOver`: the case of the semilocal ring `B = (B₀)_p`,
  finite over `A`, reindexed along the bijection
  `IsLocalization.AtPrime.maximalSpectrumEquivPrimesOver` between the maximal ideals of `B` and
  the primes of `B₀` over `p`; the residue degrees are compared through `B ⧸ m ≅ κ(B_m) ≅ κ(R q)`.

This is the coefficient identity behind the pushforward of principal divisors along a morphism
that is finite over an affine neighbourhood of a codimension-one point.
-/

public section

open Algebra IsLocalRing

namespace TauCeti

section BaseRing

variable {A K B L B₀ : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [CommRing B₀] [Algebra B₀ B]
  (S : Submonoid B₀) [IsLocalization S B] [Algebra B₀ L] [IsScalarTower B₀ B L]
  (R : MaximalSpectrum B → Type*) [∀ m, CommRing (R m)] [∀ m, IsDomain (R m)]
  [∀ m, IsNoetherianRing (R m)] [∀ m, Ring.KrullDimLE 1 (R m)] [∀ m, Algebra B₀ (R m)]
  [∀ m, IsLocalization.AtPrime (R m) (m.asIdeal.comap (algebraMap B₀ B))] [∀ m, Algebra (R m) L]
  [∀ m, IsScalarTower B₀ (R m) L] [∀ m, IsFractionRing (R m) L]

include S in
/-- **The order of a norm, over a base ring** (Fulton, *Intersection Theory*, Appendix A.3).
`TauCeti.ordFrac_norm_eq_finprod` when `B` is a localization of a ring `B₀` and the orders are
taken in localizations `R m` of `B₀` at the primes `m ∩ B₀`. This is the form met on a scheme
finite over an affine neighbourhood of a point: `B₀` is the ring of the affine preimage, `B` its
semilocalization over the point, and `R m` the local rings of the points of the fibre. -/
theorem ordFrac_norm_eq_finprod_of_isLocalization {r : L} (hr : r ≠ 0) :
    Ring.ordFrac A (Algebra.norm K r) =
      ∏ᶠ m, Ring.ordFrac (R m) r ^ (Module.length A (B ⧸ m.asIdeal)).toNat := by
  -- Each `R m` is a localization of `B` at `m`, through `B_m ≃ₐ[B₀] R m`.
  have (m : MaximalSpectrum B) : IsLocalization.AtPrime (Localization.AtPrime m.asIdeal)
      (m.asIdeal.comap (algebraMap B₀ B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S _ m.asIdeal
  let e (m : MaximalSpectrum B) : Localization.AtPrime m.asIdeal ≃ₐ[B₀] R m :=
    IsLocalization.algEquiv (m.asIdeal.comap (algebraMap B₀ B)).primeCompl _ _
  let (m : MaximalSpectrum B) : Algebra B (R m) :=
    ((e m).toRingHom.comp (algebraMap B (Localization.AtPrime m.asIdeal))).toAlgebra
  have (m : MaximalSpectrum B) : IsLocalization.AtPrime (R m) m.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv m.asIdeal.primeCompl
      (AlgEquiv.ofRingEquiv (f := (e m).toRingEquiv) fun _ ↦ rfl)
  have (m : MaximalSpectrum B) : IsScalarTower B (R m) L := .of_algebraMap_eq' <|
    IsLocalization.ringHom_ext S <| RingHom.ext fun x ↦ by
      change algebraMap B L (algebraMap B₀ B x) =
        algebraMap (R m) L (e m (algebraMap B (Localization.AtPrime m.asIdeal) (algebraMap B₀ B x)))
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply]
  exact ordFrac_norm_eq_finprod R hr

end BaseRing

section PrimesOver

variable {A₀ B₀ A K L : Type*} [CommRing A₀] [IsDomain A₀] [CommRing B₀] [IsDomain B₀]
  [Algebra A₀ B₀] [Module.Finite A₀ B₀] [FaithfulSMul A₀ B₀] (p : Ideal A₀) [p.IsPrime]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra A₀ A]
  [IsLocalization.AtPrime A p] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B₀ L] [IsFractionRing B₀ L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra A₀ L] [IsScalarTower A₀ A L] [IsScalarTower A₀ B₀ L]
  (R : p.primesOver B₀ → Type*) [∀ q, CommRing (R q)] [∀ q, IsDomain (R q)]
  [∀ q, IsLocalRing (R q)] [∀ q, IsNoetherianRing (R q)] [∀ q, Ring.KrullDimLE 1 (R q)]
  [∀ q, Algebra B₀ (R q)] [∀ q, IsLocalization.AtPrime (R q) q.1] [∀ q, Algebra (R q) L]
  [∀ q, IsScalarTower B₀ (R q) L] [∀ q, IsFractionRing (R q) L] [∀ q, Algebra A (R q)]
  [∀ q, Algebra A₀ (R q)] [∀ q, IsScalarTower A₀ A (R q)] [∀ q, IsScalarTower A₀ B₀ (R q)]

/-- **The order of a norm, over the primes above `p`** (Fulton, *Intersection Theory*,
Appendix A.3). Let `B₀` be a domain finite over a domain `A₀`, `p` a prime of `A₀` with
`A = (A₀)_p` Noetherian of dimension at most one, and `R q` a localization of `B₀` at each prime
`q` over `p`. For `r ≠ 0` in the fraction field `L` of `B₀`,
`ord_A N_{L/K}(r) = Σ_q [κ(R q) : κ(A)] ord_{R q}(r)`, written multiplicatively in `ℤᵐ⁰`, with the
residue degree read as the `A`-length of the residue field of `R q`. -/
theorem ordFrac_norm_eq_finprod_primesOver {r : L} (hr : r ≠ 0) :
    Ring.ordFrac A (Algebra.norm K r) =
      ∏ᶠ q, Ring.ordFrac (R q) r ^ (Module.length A (ResidueField (R q))).toNat := by
  have hS : algebraMapSubmonoid B₀ p.primeCompl ≤ nonZeroDivisors B₀ :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ p.primeCompl_le_nonZeroDivisors
  -- The semilocal ring `B = (B₀)_p`, a domain finite over `A` with fraction field `L`.
  let B := Localization (algebraMapSubmonoid B₀ p.primeCompl)
  let _ : Algebra A B := localizationAlgebra p.primeCompl B₀
  have : IsScalarTower A₀ A B := isScalarTower_localizationAlgebra p.primeCompl B₀
  have : Module.Finite A B := Module.Finite.of_isLocalization A₀ B₀ p.primeCompl
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  let _ : Algebra B L := (IsLocalization.lift (M := algebraMapSubmonoid B₀ p.primeCompl) (S := B)
    (g := algebraMap B₀ L) fun s ↦ IsUnit.mk0 _ fun h ↦
      nonZeroDivisors.coe_ne_zero (⟨s, hS s.2⟩ : nonZeroDivisors B₀) <|
        IsFractionRing.injective B₀ L (h.trans (map_zero _).symm)).toAlgebra
  have : IsScalarTower B₀ B L := .of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isLocalization (algebraMapSubmonoid B₀ p.primeCompl) B L hS
  have : IsScalarTower A B L := .of_algebraMap_eq' <| IsLocalization.ringHom_ext p.primeCompl <|
    RingHom.ext fun a ↦ by
      change algebraMap A L (algebraMap A₀ A a) =
        algebraMap B L (algebraMap A B (algebraMap A₀ A a))
      rw [← IsScalarTower.algebraMap_apply A₀ A L, ← IsScalarTower.algebraMap_apply A₀ A B,
        IsScalarTower.algebraMap_apply A₀ B₀ B, ← IsScalarTower.algebraMap_apply B₀ B L,
        ← IsScalarTower.algebraMap_apply A₀ B₀ L]
  let e := IsLocalization.AtPrime.maximalSpectrumEquivPrimesOver (S := B₀) p A B
  have (m : MaximalSpectrum B) :
      IsLocalization.AtPrime (R (e m)) (m.asIdeal.comap (algebraMap B₀ B)) := by
    convert (inferInstance : IsLocalization.AtPrime (R (e m)) (e m).1)
    exact (IsLocalization.AtPrime.coe_maximalSpectrumEquivPrimesOver_apply p A B m).symm
  rw [ordFrac_norm_eq_finprod_of_isLocalization (K := K) (B := B)
    (algebraMapSubmonoid B₀ p.primeCompl) (fun m ↦ R (e m)) hr, ← finprod_comp_equiv e]
  congr! with m
  -- The residue degree: `B ⧸ m ≅ κ(B_m) ≅ κ(R q)` as `A`-modules.
  rw [← MaximalSpectrum.length_residueField_localization_eq]
  have : IsLocalization.AtPrime (Localization.AtPrime m.asIdeal)
      (m.asIdeal.comap (algebraMap B₀ B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (algebraMapSubmonoid B₀ p.primeCompl) _ m.asIdeal
  let f : Localization.AtPrime m.asIdeal ≃ₐ[B₀] R (e m) :=
    IsLocalization.algEquiv (m.asIdeal.comap (algebraMap B₀ B)).primeCompl _ _
  let f' : Localization.AtPrime m.asIdeal ≃ₐ[A] R (e m) := AlgEquiv.ofRingEquiv
    (f := f.toRingEquiv) fun a ↦ by
      change f.toRingHom.comp (algebraMap A _) a = algebraMap A (R (e m)) a
      congr 1
      refine IsLocalization.ringHom_ext p.primeCompl <| RingHom.ext fun a ↦ ?_
      change f (algebraMap A _ (algebraMap A₀ A a)) = algebraMap A (R (e m)) (algebraMap A₀ A a)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A₀ B₀, f.commutes, ← IsScalarTower.algebraMap_apply]
  exact (ResidueField.mapAlgEquiv f').toLinearEquiv.length_eq

end PrimesOver

end TauCeti
