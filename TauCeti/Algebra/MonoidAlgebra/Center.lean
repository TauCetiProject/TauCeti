/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Changing the coefficients of the centre of a monoid algebra

A ring homomorphism `f : R →+* S` of commutative semirings induces the ring homomorphism
`MonoidAlgebra.mapRingHom M f`, which applies `f` to every coefficient of an element of the monoid
algebra `R[M]`. It carries the centre of `R[M]` into the centre of `S[M]`: a central element
commutes with every basis element `single m 1`, so its image commutes with every
`single m 1 = mapRingHom M f (single m 1)`, and the scalar multiples of these span `S[M]`. The
restriction is the ring homomorphism `MonoidAlgebra.centerMapRingHom M f` between the centres; for
the reduction `O → k` of a complete local ring to its residue field it is the reduction of central
elements of a group algebra, along which central idempotents are lifted.

## Main definitions

* `MonoidAlgebra.centerMapRingHom M f`: the map `Z(R[M]) →+* Z(S[M])` induced by `f : R →+* S`.

## Main results

* `MonoidAlgebra.mapRingHom_mem_center`: changing the coefficients preserves centrality.
* `MonoidAlgebra.centerMapRingHom_algebraMap`: the map on centres is compatible with the scalars.
-/

public section

namespace MonoidAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Monoid M]

/-- **Changing the coefficients preserves centrality.** If `z` is central in `R[M]`, then applying
a ring homomorphism `f : R →+* S` to its coefficients gives a central element of `S[M]`. -/
theorem mapRingHom_mem_center (f : R →+* S) {z : MonoidAlgebra R M}
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R M)) :
    mapRingHom M f z ∈ Subalgebra.center S (MonoidAlgebra S M) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro b
  induction b using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, mul_zero]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | single m s =>
    have h := congrArg (mapRingHom M f) (hz (single m 1))
    rw [map_mul, map_mul, mapRingHom_single, map_one] at h
    rw [← mul_one s, ← smul_single', smul_mul_assoc, h, mul_smul_comm]

variable (M) in
/-- The ring homomorphism `Z(R[M]) →+* Z(S[M])` between the centres of the monoid algebras induced
by a ring homomorphism `f : R →+* S`: the restriction of `MonoidAlgebra.mapRingHom M f`, which
applies `f` to every coefficient. -/
noncomputable def centerMapRingHom (f : R →+* S) :
    Subalgebra.center R (MonoidAlgebra R M) →+* Subalgebra.center S (MonoidAlgebra S M) :=
  ((mapRingHom M f).comp (Subalgebra.center R (MonoidAlgebra R M)).val.toRingHom).codRestrict _
    fun z ↦ mapRingHom_mem_center f z.property

/-- The underlying element of the image of a central element `z` under `centerMapRingHom M f` is
`mapRingHom M f z`. -/
@[simp]
theorem coe_centerMapRingHom (f : R →+* S) (z : Subalgebra.center R (MonoidAlgebra R M)) :
    (centerMapRingHom M f z : MonoidAlgebra S M) = mapRingHom M f z :=
  (rfl)

/-- The map on centres sends the scalar `r` to the scalar `f r`. -/
@[simp]
theorem centerMapRingHom_algebraMap (f : R →+* S) (r : R) :
    centerMapRingHom M f (algebraMap R (Subalgebra.center R (MonoidAlgebra R M)) r) =
      algebraMap S (Subalgebra.center S (MonoidAlgebra S M)) (f r) :=
  Subtype.ext <| RingHom.congr_fun (mapRingHom_comp_algebraMap f) r

end MonoidAlgebra
