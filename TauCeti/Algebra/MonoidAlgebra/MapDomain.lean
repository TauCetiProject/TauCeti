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
inverse system of group algebras uses. Also: the image of `mapDomain f` commutes with a monomial
`single n r` as soon as every `f m` commutes with `n` and `r` is central.

## Main results

* `MonoidAlgebra.mapDomain_id`, `MonoidAlgebra.mapDomain_mapDomain`: the functor laws.
* `MonoidAlgebra.mapDomain_surjective`: the map induced by a surjection is surjective.
* `MonoidAlgebra.mapDomain_commute_single`: the image of `mapDomain f` commutes with `single n r`
  when the values of `f` commute with `n` and `r` is central.
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

/-- The image of `mapDomain f` commutes with the monomial `single n r` when every value of `f`
commutes with `n` and `r` is central. -/
theorem mapDomain_commute_single [Mul N] {f : M → N} {n : N} {r : R} (hm : ∀ m, Commute (f m) n)
    (hr : ∀ s, Commute s r) (x : MonoidAlgebra R M) : Commute (mapDomain f x) (single n r) := by
  induction x using induction_linear with
  | zero => simp only [mapDomain_zero]; exact Commute.zero_left _
  | add x y hx hy => rw [mapDomain_add]; exact hx.add_left hy
  | single m s => rw [mapDomain_single]; exact single_commute_single (hm m) (hr s)

end MonoidAlgebra
