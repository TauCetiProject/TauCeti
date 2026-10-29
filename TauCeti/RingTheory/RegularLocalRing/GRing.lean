/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.RegularLocalRing.RegularAlgebraMap

/-!
# G-rings

A ring `R` is a *G-ring* if it is Noetherian and, for every prime `p` of `R`, the completion map
`R_p → R̂_p` of the local ring `R_p` at its maximal ideal is a regular ring map (Stacks,
Definition 15.51.1). Since `R̂_p` is flat over the Noetherian ring `R_p`, this says that the
*formal fibres* `κ(q) ⊗[R_p] R̂_p`, for `q` a prime of `R_p`, are geometrically regular. Being a
G-ring is the first half of quasi-excellence; the second is the J-2 condition on regular loci.

## Main definitions and results

* `TauCeti.Excellence.IsGRing R`: `R` is a G-ring.
* `TauCeti.Excellence.isGRing_iff`: a Noetherian ring is a G-ring if and only if all its formal
  fibres are geometrically regular; flatness of the completions is automatic.
* `TauCeti.Excellence.regularAlgebraMap_adicCompletion_of_ringEquiv`: regularity of the completion
  map of a local ring only depends on the local ring up to isomorphism.
* `TauCeti.Excellence.regularAlgebraMap_adicCompletion_of_isAdicComplete`: the completion map of a
  complete local ring is regular.
* `TauCeti.Excellence.IsGRing.of_ringEquiv`: being a G-ring is invariant under ring isomorphisms.
* `TauCeti.Excellence.IsGRing.of_isLocalization`: a localization of a G-ring is a G-ring.
* `TauCeti.Excellence.IsGRing.of_isArtinianRing`: an Artinian ring is a G-ring, as each of its
  local rings is its own completion. This covers fields, the zero ring and the dual numbers.
* `TauCeti.Excellence.IsGRing.of_isAdicComplete`: a complete Noetherian local ring of dimension at
  most one is a G-ring, for instance a complete discrete valuation ring such as `k⟦X⟧` or `ℤ_[p]`.
  The Stacks Project shows that every complete Noetherian local ring is a G-ring; that is not proved
  here.

## References

* The Stacks Project, Section 15.51 (G-rings), Definition 15.51.1.
-/

public section

universe u

open IsLocalRing PowerSeries

namespace TauCeti.Excellence

/-- A ring `R` is a *G-ring* if it is Noetherian and for every prime `p` of `R` the completion
`R_p → R̂_p` of the local ring at `p` along its maximal ideal is a regular ring map, that is, `R_p`
has geometrically regular formal fibres (Stacks, Definition 15.51.1). -/
class IsGRing (R : Type u) [CommRing R] : Prop where
  /-- A G-ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing R
  /-- The completion of the local ring of a G-ring at a prime is a regular algebra. -/
  regularAlgebraMap_adicCompletion (p : Ideal R) [p.IsPrime] :
    RegularAlgebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))

attribute [instance] IsGRing.isNoetherianRing IsGRing.regularAlgebraMap_adicCompletion

/-- A Noetherian ring is a G-ring if and only if its formal fibres are geometrically regular: for
all primes `p` of `R` and `q` of `R_p`, the fibre `κ(q) ⊗[R_p] R̂_p` of the completion `R̂_p` is a
geometrically regular `κ(q)`-algebra. Flatness of `R̂_p` over `R_p` holds for every Noetherian
ring. -/
theorem isGRing_iff {R : Type u} [CommRing R] :
    IsGRing R ↔ IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime]
      (q : Ideal (Localization.AtPrime p)) [q.IsPrime],
      GeometricallyRegular q.ResidueField
        (q.Fiber (AdicCompletion (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p))) :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ _ _ _ ↦ inferInstance⟩,
    fun ⟨_, h⟩ ↦ ⟨inferInstance, fun p _ ↦ ⟨inferInstance, h p⟩⟩⟩

/-- Regularity of the completion map `A → Â` of a local ring along its maximal ideal is invariant
under isomorphisms of local rings. -/
theorem regularAlgebraMap_adicCompletion_of_ringEquiv {A A' : Type u} [CommRing A] [CommRing A']
    [IsLocalRing A] [IsLocalRing A'] (e : A ≃+* A')
    [RegularAlgebraMap A (AdicCompletion (maximalIdeal A) A)] :
    RegularAlgebraMap A' (AdicCompletion (maximalIdeal A') A') := by
  let : Algebra A A' := e.toRingHom.toAlgebra
  let e' : A ≃ₐ[A] A' := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have := (AdicCompletion.congrₐ e' (map_ringEquiv_maximalIdeal e)).regularAlgebraMap
  exact .of_bijective_algebraMap e.bijective

/-- The completion map `A → Â` of a local ring that is complete along its maximal ideal is
regular. -/
theorem regularAlgebraMap_adicCompletion_of_isAdicComplete (A : Type u) [CommRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] :
    RegularAlgebraMap A (AdicCompletion (maximalIdeal A) A) :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal A)).regularAlgebraMap

namespace IsGRing

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Being a G-ring is invariant under ring isomorphisms. -/
theorem of_ringEquiv [IsGRing R] (e : R ≃+* S) : IsGRing S where
  isNoetherianRing := isNoetherianRing_of_ringEquiv R e
  regularAlgebraMap_adicCompletion q _ :=
    regularAlgebraMap_adicCompletion_of_ringEquiv
      (Localization.localRingEquiv (q.comap e) q e rfl)

/-- A localization of a G-ring is a G-ring. -/
theorem of_isLocalization [Algebra R S] [IsGRing R] (M : Submonoid R) [IsLocalization M S] :
    IsGRing S where
  isNoetherianRing := IsLocalization.isNoetherianRing M S inferInstance
  regularAlgebraMap_adicCompletion q _ := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact regularAlgebraMap_adicCompletion_of_ringEquiv
      (IsLocalization.algEquiv (q.comap (algebraMap R S)).primeCompl
        (Localization.AtPrime (q.comap (algebraMap R S))) (Localization.AtPrime q)).toRingEquiv

/-- The localization `Localization M` of a G-ring is a G-ring. -/
instance localization [IsGRing R] (M : Submonoid R) : IsGRing (Localization M) :=
  of_isLocalization M

/-- An Artinian ring is a G-ring. This covers fields and the zero ring. -/
instance (priority := 100) of_isArtinianRing [IsArtinianRing R] : IsGRing R where
  isNoetherianRing := inferInstance
  regularAlgebraMap_adicCompletion p _ :=
    regularAlgebraMap_adicCompletion_of_isAdicComplete (Localization.AtPrime p)

/-- A Noetherian local ring of dimension at most one that is complete along its maximal ideal is a
G-ring. This covers complete discrete valuation rings such as `k⟦X⟧` and `ℤ_[p]`. -/
theorem of_isAdicComplete [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [IsAdicComplete (maximalIdeal R) R] : IsGRing R where
  isNoetherianRing := inferInstance
  regularAlgebraMap_adicCompletion p _ := by
    -- A prime of `R` is either minimal, with Artinian local ring, or the maximal ideal.
    rcases Ring.krullDimLE_one_iff.mp ‹_› p ‹_› with hp | hp
    · have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
      have : IsArtinianRing (Localization.AtPrime p) :=
        IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      exact regularAlgebraMap_adicCompletion_of_isAdicComplete _
    · obtain rfl := IsLocalRing.eq_maximalIdeal hp
      have := regularAlgebraMap_adicCompletion_of_isAdicComplete R
      exact regularAlgebraMap_adicCompletion_of_ringEquiv
        (IsLocalization.atUnits R (maximalIdeal R).primeCompl
          (S := Localization.AtPrime (maximalIdeal R))
          fun _ hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx).toRingEquiv

end IsGRing

/-! ### Checks -/

/-- A field is a G-ring. -/
example (k : Type u) [Field k] : IsGRing k := inferInstance

/-- The zero ring is a G-ring. -/
example (k : Type u) [Field k] : IsGRing (k ⧸ (⊤ : Ideal k)) := inferInstance

/-- The dual numbers `k[ε]/(ε²)` are a G-ring: being a G-ring does not require reducedness. -/
example (k : Type u) [Field k] : IsGRing (TrivSqZeroExt k k) :=
  have : Module.Finite k (TrivSqZeroExt k k) := inferInstanceAs (Module.Finite k (k × k))
  -- The `k`-module structure of `TrivSqZeroExt k k` is the product one, which is not reducibly
  -- the one induced by the `k`-algebra structure, so the scalar tower is checked by hand.
  have : IsScalarTower k (TrivSqZeroExt k k) (TrivSqZeroExt k k) :=
    ⟨fun a b c ↦ by ext <;> simp <;> ring⟩
  have : IsArtinianRing (TrivSqZeroExt k k) := .of_finite k _
  inferInstance

/-- The power series ring `k⟦X⟧` over a field, a complete discrete valuation ring, is a G-ring. -/
example (k : Type u) [Field k] : IsGRing k⟦X⟧ :=
  have : IsAdicComplete (maximalIdeal k⟦X⟧) k⟦X⟧ := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  .of_isAdicComplete

end TauCeti.Excellence
