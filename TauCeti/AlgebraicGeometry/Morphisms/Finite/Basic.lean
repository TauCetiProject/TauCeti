/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Global sections of finite morphisms

For a finite morphism `f : X ⟶ Spec R`, the global sections `Γ(X, ⊤)` form a finite
`R`-module. `AlgebraicGeometry.Scheme.Hom.moduleFinite_appTop` states this for an existing
`R`-algebra structure compatible with the map of global sections. It transports Mathlib's
`Scheme.Hom.finite_appTop` across the canonical isomorphism `R ≅ Γ(Spec R, ⊤)`.

This finiteness is used to compute the rank of a finite morphism over a field as the dimension
of its global sections.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A finite morphism to the spectrum of a commutative ring has module-finite global sections,
for any `R`-algebra structure on `Γ(X, ⊤)` given by the map of global sections. -/
theorem Scheme.Hom.moduleFinite_appTop {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsFinite f] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Module.Finite R Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap, hf, CommRingCat.hom_comp]
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)

end AlgebraicGeometry
