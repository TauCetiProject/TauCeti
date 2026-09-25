/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Pushing coefficients of a monoid algebra forward along a map

Functoriality of `MonoidAlgebra.mapDomain`, the map `R[M] → R[N]` induced by a map `M → N` of the
index types, in the form of the corresponding `Finsupp.mapDomain` lemmas: the identity induces the
identity, a composite induces the composite, and a surjection induces a surjection. Mathlib states
the first two only for the bundled ring and algebra homomorphisms `mapDomainRingHom` and
`mapDomainAlgHom`; the unbundled forms are what a computation with the coefficients of an
inverse system of group algebras uses.

## Main results

* `MonoidAlgebra.mapDomain_id`, `MonoidAlgebra.mapDomain_mapDomain`: the functor laws.
* `MonoidAlgebra.mapDomain_surjective`: the map induced by a surjection is surjective.
-/

public section

namespace MonoidAlgebra

variable {R : Type*} [Semiring R] {M N O : Type*}

/-- Pushing the coefficients forward along the identity does nothing. -/
@[simp]
theorem mapDomain_id (x : MonoidAlgebra R M) : mapDomain id x = x :=
  ext <| by rw [coeff_mapDomain, Finsupp.mapDomain_id]

/-- Pushing the coefficients forward along two maps in turn is pushing them forward along the
composite. -/
@[simp]
theorem mapDomain_mapDomain (f : M → N) (g : N → O) (x : MonoidAlgebra R M) :
    mapDomain g (mapDomain f x) = mapDomain (g ∘ f) x :=
  ext <| by rw [coeff_mapDomain, coeff_mapDomain, coeff_mapDomain, Finsupp.mapDomain_comp]

/-- Pushing the coefficients forward along a surjection is surjective. -/
theorem mapDomain_surjective {f : M → N} (hf : Function.Surjective f) :
    Function.Surjective (mapDomain (R := R) f) := fun y ↦ by
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  exact ⟨ofCoeff x, ext <| by rw [coeff_mapDomain, coeff_ofCoeff, hx]⟩

end MonoidAlgebra
