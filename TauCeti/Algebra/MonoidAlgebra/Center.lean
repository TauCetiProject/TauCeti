/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# The centre of a monoid algebra

A ring homomorphism `f : R →+* S` of commutative semirings induces the ring homomorphism
`MonoidAlgebra.mapRingHom G f : R[G] →+* S[G]` applying `f` to the coefficients. It carries the
centre of `R[G]` into the centre of `S[G]` (`MonoidAlgebra.mapRingHom_mem_center`), because
`S[G]` is spanned over its central scalars `S` by the elements `of S G g`, the images of the
`of R G g`. The restriction is `MonoidAlgebra.centerMapRingHom G f : Z(R[G]) →+* Z(S[G])`.

For `G` finite, `Z(R[G])` is a submodule of the finite `R`-module `R[G]`, so it is a finite
`R`-module when `R` is Noetherian, and hence an Artinian ring when `R` is Artinian.

## Main definitions

* `MonoidAlgebra.centerMapRingHom G f`: the ring homomorphism `Z(R[G]) →+* Z(S[G])` induced by
  `f : R →+* S`.
* `MonoidAlgebra.toCenter`: for a commutative monoid `G`, the isomorphism of `R[G]` with its centre.

## Main results

* `MonoidAlgebra.mapRingHom_mem_center`: the coefficient map preserves centrality.
* `MonoidAlgebra.centerMapRingHom_algebraMap`: the map on centres is compatible with the scalars.
* `TauCeti.moduleFinite_center_monoidAlgebra`, `TauCeti.isArtinianRing_center_monoidAlgebra`: for
  `G` finite, `Z(R[G])` is a finite `R`-module when `R` is Noetherian, and an Artinian ring when
  `R` is Artinian (instances).
-/

public section

namespace MonoidAlgebra

variable {R S : Type*} (G : Type*) [CommSemiring R] [CommSemiring S] [Monoid G]

/-- **The coefficient map preserves centrality.** For `f : R →+* S` and `x` in the centre of
`R[G]`, the image of `x` in `S[G]` is central: it commutes with the scalars `S`, which are central,
and with each `single g 1`, the image of the element `single g 1` of `R[G]`. -/
theorem mapRingHom_mem_center (f : R →+* S) {x : R[G]}
    (hx : x ∈ Subalgebra.center R R[G]) :
    mapRingHom G f x ∈ Subalgebra.center S S[G] := by
  rw [Subalgebra.mem_center_iff] at hx ⊢
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => rw [add_mul, mul_add, hy, hz]
  | single g s =>
    have hg : of S G g = mapRingHom G f (of R G g) := by simp
    rw [single_eq_algebraMap_mul_of, mul_assoc, Algebra.left_comm, hg, ← map_mul, ← map_mul, hx]

/-- The ring homomorphism `Z(R[G]) →+* Z(S[G])` of centres induced by a ring homomorphism
`f : R →+* S`: the restriction of `MonoidAlgebra.mapRingHom G f`. -/
noncomputable def centerMapRingHom (f : R →+* S) :
    Subalgebra.center R R[G] →+* Subalgebra.center S S[G] :=
  ((mapRingHom G f).comp (Subalgebra.center R R[G]).toSubsemiring.subtype).codRestrict
    (Subalgebra.center S S[G]).toSubsemiring fun x ↦ mapRingHom_mem_center G f x.property

@[simp]
theorem coe_centerMapRingHom (f : R →+* S) (x : Subalgebra.center R R[G]) :
    (centerMapRingHom G f x : S[G]) = mapRingHom G f x := by
  simp [centerMapRingHom]

/-- The map on centres sends the scalar `r` to the scalar `f r`. -/
@[simp]
theorem centerMapRingHom_algebraMap (f : R →+* S) (r : R) :
    centerMapRingHom G f (algebraMap R (Subalgebra.center R R[G]) r) =
      algebraMap S (Subalgebra.center S S[G]) (f r) :=
  Subtype.ext <| RingHom.congr_fun (mapRingHom_comp_algebraMap f) r

/-- For a commutative monoid `G`, every element of `R[G]` is central, so `R[G]` is isomorphic to its
centre: the identification sends `x` to `x`, read as an element of the centre. -/
noncomputable def toCenter {k G : Type*} [CommSemiring k] [CommMonoid G] :
    MonoidAlgebra k G ≃ₐ[k] Subalgebra.center k (MonoidAlgebra k G) :=
  ((Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top k _)).trans Subalgebra.topEquiv).symm

/-- `toCenter x` is `x`, read in the monoid algebra. -/
@[simp]
theorem coe_toCenter {k G : Type*} [CommSemiring k] [CommMonoid G] (x : MonoidAlgebra k G) :
    (toCenter x : MonoidAlgebra k G) = x :=
  (rfl)

end MonoidAlgebra

namespace TauCeti

variable {R G : Type*}

/-- The centre of `R[G]` is a finite `R`-module, over a Noetherian commutative ring `R` and for a
finite group (or monoid) `G`. -/
instance moduleFinite_center_monoidAlgebra [CommRing R] [IsNoetherianRing R] [Monoid G]
    [Finite G] : Module.Finite R (Subalgebra.center R (MonoidAlgebra R G)) :=
  have : IsNoetherian R (Subalgebra.center R (MonoidAlgebra R G)) :=
    isNoetherian_submodule' (Subalgebra.toSubmodule (Subalgebra.center R (MonoidAlgebra R G)))
  inferInstance

/-- The centre of `R[G]` is an Artinian ring, over an Artinian commutative ring `R` and for a
finite group (or monoid) `G`. -/
instance isArtinianRing_center_monoidAlgebra [CommRing R] [IsArtinianRing R] [Monoid G]
    [Finite G] : IsArtinianRing (Subalgebra.center R (MonoidAlgebra R G)) :=
  IsArtinianRing.of_finite R _

end TauCeti
