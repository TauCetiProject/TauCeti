/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Retracts of formally smooth algebras

An `R`-algebra `A` is a retract of an `R`-algebra `C` if there are `R`-algebra homomorphisms
`α : A →ₐ[R] C` and `β : C →ₐ[R] A` with `β ∘ α = id`. If `C` is formally smooth over `R`, then
so is `A`: an infinitesimal lifting problem for `A` becomes one for `C` after composing with `β`,
and a solution for `C` gives one for `A` after composing with `α`.

Geometrically, a retract of a formally smooth scheme over a base is formally smooth over it. This
is the local input to the stability of smooth morphisms of schemes under retracts.

## Main results

* `Algebra.FormallySmooth.of_retract`: a retract of a formally smooth algebra is formally smooth.
* `RingHom.FormallySmooth.of_retract`: the same statement for ring homomorphisms.

## References

* The Stacks Project, [Tag 00TL](https://stacks.math.columbia.edu/tag/00TL), for the
  infinitesimal lifting characterisation of formal smoothness.
-/

public section

namespace Algebra.FormallySmooth

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]

/-- **A retract of a formally smooth algebra is formally smooth.** If `A` is a retract of a
formally smooth `R`-algebra `C`, through `α : A →ₐ[R] C` and `β : C →ₐ[R] A` with `β ∘ α = id`,
then `A` is formally smooth over `R`. -/
theorem of_retract [FormallySmooth R C] (α : A →ₐ[R] C) (β : C →ₐ[R] A)
    (h : β.comp α = AlgHom.id R A) : FormallySmooth R A := by
  refine iff_comp_surjective.mpr fun B _ _ I hI g ↦ ?_
  obtain ⟨l, hl⟩ := comp_surjective R C I hI (g.comp β)
  refine ⟨l.comp α, ?_⟩
  rw [← AlgHom.comp_assoc, hl, AlgHom.comp_assoc, h, AlgHom.comp_id]

end Algebra.FormallySmooth

namespace RingHom.FormallySmooth

variable {R A C : Type*} [CommRing R] [CommRing A] [CommRing C]

/-- **A retract of a formally smooth ring homomorphism is formally smooth.** Let `φ : R →+* A`,
and let `α : A →+* C` and `β : C →+* A` satisfy `β ∘ α = id`. If `α ∘ φ` is formally smooth,
then so is `φ`. -/
theorem of_retract {φ : R →+* A} (α : A →+* C) (β : C →+* A) (h : β.comp α = RingHom.id A)
    (hφ : (α.comp φ).FormallySmooth) : φ.FormallySmooth := by
  algebraize [φ, α.comp φ]
  have hβ : β.comp (α.comp φ) = φ := by rw [← RingHom.comp_assoc, h, RingHom.id_comp]
  exact Algebra.FormallySmooth.of_retract (C := C) ⟨α, fun _ ↦ rfl⟩
    ⟨β, fun r ↦ congr($hβ r)⟩ (AlgHom.ext fun a ↦ congr($h a))

end RingHom.FormallySmooth
