/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import TauCeti.RingTheory.Kaehler.FormallyEtale
public import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Smooth algebras over regular rings are regular

Let `R` be a regular ring and `S` a finitely presented `R`-algebra which is smooth at a prime `q`.
Then the local ring `S_q` is regular. In particular an `R`-algebra smooth over a regular ring,
for instance over a field, is a regular ring.

Near `q`, some localization `S_g` is standard smooth over `R`, so `Ω[S_g⁄R]` has a basis
`d a₁, …, d aₙ` of differentials of elements of `S_g`. Sending `Xᵢ ↦ aᵢ` then makes `S_g` étale
over the polynomial ring `P = R[X₁, …, Xₙ]`, by the Jacobi–Zariski criterion
`TauCeti.formallyEtale_of_bijective_mapBaseChange`. The polynomial ring over a regular ring is
regular (Mathlib's `MvPolynomial.isRegularRing_of_isRegularRing`), and the localization of an
étale algebra at a prime is flat and unramified over the corresponding localization of `P`, so
regularity ascends by `TauCeti.IsRegularLocalRing.of_flat_of_formallyUnramified`.

## Main declarations

* `TauCeti.isRegularLocalRing_localization_of_isSmoothAt`: the localization of a finitely
  presented algebra over a regular ring at a prime where it is smooth is a regular local ring;
* `TauCeti.IsRegularRing.of_smooth`: a smooth algebra over a regular ring is a regular ring.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 23.7, for the ascent of regularity along the
  flat local homomorphism `P_p → S_q`.
-/

public section

namespace TauCeti

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The localization of a standard smooth algebra over a regular ring at a prime is regular. -/
private theorem isRegularLocalRing_localization_of_isStandardSmooth [IsRegularRing R]
    [Algebra.IsStandardSmooth R S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : Nontrivial S :=
    ⟨0, 1, fun h ↦ Ideal.IsPrime.ne_top ‹_› (q.eq_top_iff_one.mpr (h ▸ q.zero_mem))⟩
  obtain ⟨-, I, b, hb⟩ :=
    (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential (R := R) (S := S)).mp
      inferInstance
  choose a ha using fun i ↦ hb ⟨i, rfl⟩
  have : Finite I := Module.Finite.finite_basis b
  -- `S` is étale over `P = R[Xᵢ]` via `Xᵢ ↦ aᵢ`, since the `d aᵢ` form a basis of `Ω[S⁄R]`.
  let P := MvPolynomial I R
  let := (MvPolynomial.aeval (R := R) a).toAlgebra
  have : IsScalarTower R P S := .of_algebraMap_eq fun r ↦ by
    simp [P, RingHom.algebraMap_toAlgebra]
  have hX (i : I) : algebraMap P S (MvPolynomial.X i) = a i := by
    simp [P, RingHom.algebraMap_toAlgebra]
  have hD (i : I) : map R R P S (mvPolynomialBasis R I i) = D R S (a i) := by
    rw [mvPolynomialBasis_apply, map_D]
    rw [hX]
  have : Algebra.FormallyEtale P S :=
    formallyEtale_of_bijective_mapBaseChange <|
      bijective_mapBaseChange_of_basis (mvPolynomialBasis R I) b fun i ↦ by
        simpa only [hD] using (ha i)
  have : Algebra.FinitePresentation P S := .of_restrict_scalars_finitePresentation R P S
  have : Algebra.Etale P S := {}
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  -- Localize at `q` and at the prime `p` of `P` below it; `P_p` is regular.
  let p := q.under P
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) q p rfl
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp P _ _
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars P _ _
  exact IsRegularLocalRing.of_flat_of_formallyUnramified (R := Localization.AtPrime p)

/-- Let `R` be a regular ring and `S` a finitely presented `R`-algebra which is smooth at the prime
`q`. Then the local ring `S_q` is regular. -/
theorem isRegularLocalRing_localization_of_isSmoothAt [IsRegularRing R]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] [Algebra.IsSmoothAt R q] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨g, hg, _⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q
  have hd : Disjoint (Submonoid.powers g : Set S) q := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨q', _, rfl⟩ : ∃ q' : Ideal (Localization.Away g), q'.IsPrime ∧ q'.under S = q :=
    ⟨_, IsLocalization.isPrime_of_isPrime_disjoint _ _ q ‹_› hd,
      IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hd⟩
  have := isRegularLocalRing_localization_of_isStandardSmooth (R := R) q'
  exact .of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization _ q').symm.toRingEquiv

/-- A smooth algebra over a regular ring is a regular ring. -/
theorem IsRegularRing.of_smooth [IsRegularRing R] [Algebra.Smooth R S] : IsRegularRing S where
  __ := Algebra.FiniteType.isNoetherianRing R S
  isRegularLocalRing_localization q _ := isRegularLocalRing_localization_of_isSmoothAt (R := R) q

end TauCeti
