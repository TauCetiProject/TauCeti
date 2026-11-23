/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.AdicCompletion.PrimitiveIdempotent

/-!
# Idempotents of monoid algebras over complete rings

Let `R` be a commutative ring, complete with respect to an ideal `I`, `φ : R →+* k` a surjective
ring homomorphism with kernel `I`, and `G` a finite monoid, typically a finite group. The main case
is a complete discrete valuation ring `O` with residue field `k`, where `φ` is the residue map and
`O[G] → k[G]` is the reduction of the group algebra modulo the maximal ideal.

The monoid algebra `R[G]` is a finite free `R`-module, hence `I`-adically complete, and the
coefficient map `R[G] → k[G]` is onto with kernel `I • R[G]`. So idempotents of `k[G]` lift to
idempotents of `R[G]` (`IsAdicComplete.exists_isIdempotentElem_eq`), an idempotent of `R[G]` is
primitive exactly when its reduction is (`TauCeti.isPrimitiveIdempotent_map_iff`), and primitive
idempotents of `k[G]` lift to primitive idempotents of `R[G]`. The kernel `I • R[G]` is not
nilpotent in general (`p • ℤ_p[G]`), so Mathlib's lifting along a nil kernel does not apply.

## Main results

* `TauCeti.MonoidAlgebra.instIsAdicComplete`: `R[G]` is `I`-adically complete for finite `G`.
* `TauCeti.MonoidAlgebra.exists_isIdempotentElem_mapRingHom_eq`: every idempotent of `k[G]` is
  the reduction of an idempotent of `R[G]`.
* `TauCeti.MonoidAlgebra.isPrimitiveIdempotent_mapRingHom_iff`: an idempotent of `R[G]` is
  primitive exactly when its reduction in `k[G]` is.
* `TauCeti.MonoidAlgebra.exists_isPrimitiveIdempotent_mapRingHom_eq`: every primitive idempotent of
  `k[G]` is the reduction of a primitive idempotent of `R[G]`.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Propositions 9.4.3 and 9.4.5.
* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
-/

public section

namespace TauCeti.MonoidAlgebra

variable {R : Type*} [CommRing R] (I : Ideal R) {G : Type*}

/-- The monoid algebra of a finite monoid over an `I`-adically complete ring is `I`-adically
complete, being a finite free module. -/
instance instIsAdicComplete [IsAdicComplete I R] [Finite G] :
    IsAdicComplete I (MonoidAlgebra R G) where
  toIsHausdorff := IsHausdorff.of_free I _
  toIsPrecomplete := IsPrecomplete.of_finite I _

variable [Monoid G] {k : Type*} [CommRing k] {φ : R →+* k}

/-- The coefficient map along a surjection is surjective. -/
theorem mapRingHom_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (MonoidAlgebra.mapRingHom G φ) := fun p ↦
  (MonoidAlgebra.mem_rangeS_mapRingHom_iff φ p).mpr fun m ↦ hφ (p.coeff m)

variable {I}

/-- The coefficient map along `φ` with kernel `I` kills exactly `I • R[G]`. -/
theorem mapRingHom_eq_zero_iff_of_ker_eq (hφI : RingHom.ker φ = I) {x : MonoidAlgebra R G} :
    MonoidAlgebra.mapRingHom G φ x = 0 ↔ x ∈ I • (⊤ : Submodule R (MonoidAlgebra R G)) := by
  rw [mapRingHom_eq_zero_iff, hφI]

variable [IsAdicComplete I R] [Finite G]

/-- **Idempotents of `k[G]` lift to `R[G]`.** For a ring `R` complete with respect to an ideal `I`,
a surjection `φ : R →+* k` with kernel `I`, and a finite monoid `G`, every idempotent of `k[G]` is
the reduction of an idempotent of `R[G]`. -/
theorem exists_isIdempotentElem_mapRingHom_eq (hφ : Function.Surjective φ)
    (hφI : RingHom.ker φ = I) {ε : MonoidAlgebra k G} (hε : IsIdempotentElem ε) :
    ∃ e : MonoidAlgebra R G, IsIdempotentElem e ∧ MonoidAlgebra.mapRingHom G φ e = ε :=
  IsAdicComplete.exists_isIdempotentElem_eq I _ (fun _ ↦ mapRingHom_eq_zero_iff_of_ker_eq hφI)
    (mapRingHom_surjective hφ ε) hε

/-- **An idempotent of `R[G]` is primitive exactly when its reduction in `k[G]` is.** Here `R` is
complete with respect to an ideal `I`, `φ : R →+* k` is a surjection with kernel `I`, and `G` is a
finite monoid; for a complete discrete valuation ring `O` with residue field `k` this is the
reduction `O[G] → k[G]`. -/
theorem isPrimitiveIdempotent_mapRingHom_iff (hφ : Function.Surjective φ)
    (hφI : RingHom.ker φ = I) {e : MonoidAlgebra R G} (he : IsIdempotentElem e) :
    IsPrimitiveIdempotent (MonoidAlgebra.mapRingHom G φ e) ↔ IsPrimitiveIdempotent e :=
  isPrimitiveIdempotent_map_iff _ (fun _ ↦ mapRingHom_eq_zero_iff_of_ker_eq hφI)
    (mapRingHom_surjective hφ) he

/-- **Primitive idempotents of `k[G]` lift to primitive idempotents of `R[G]`.** Here `R` is
complete with respect to an ideal `I`, `φ : R →+* k` is a surjection with kernel `I`, and `G` is a
finite monoid. -/
theorem exists_isPrimitiveIdempotent_mapRingHom_eq (hφ : Function.Surjective φ)
    (hφI : RingHom.ker φ = I) {ε : MonoidAlgebra k G} (hε : IsPrimitiveIdempotent ε) :
    ∃ e : MonoidAlgebra R G, IsPrimitiveIdempotent e ∧ MonoidAlgebra.mapRingHom G φ e = ε :=
  exists_isPrimitiveIdempotent_eq _ (fun _ ↦ mapRingHom_eq_zero_iff_of_ker_eq hφI)
    (mapRingHom_surjective hφ) hε

end TauCeti.MonoidAlgebra
