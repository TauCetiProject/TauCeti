/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.InvariantDerivation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.OneParameter

/-!
# Exponential one-parameter subgroups of closed subgroups

If a subgroup tangent vector has a locally nilpotent ambient invariant derivation,
its entire polynomial exponential curve vanishes on the subgroup's defining Hopf ideal.
Consequently every algebra-valued parameter gives a point of the subgroup, including
parameters in nonreduced algebras. This strengthens ideal preservation by the exponential
at parameter one to factorization of the polynomial curve itself. Over an algebraically
closed field, since a finite-type group and every closed subgroup share the Lie algebra of
their identity components, every exponential curve factors through the identity component.

The argument uses `HopfIdeal.leftInvariantDerivation_mem` to preserve the ideal under
every iterate, and `Bialgebra.expPointPolynomial` for the polynomial curve.

## Main declarations

* `TauCeti.HopfIdeal.expPointPolynomial_apply_eq_zero`: the polynomial exponential curve of a
  subgroup tangent vector vanishes on the defining Hopf ideal.
* `TauCeti.HopfIdeal.expPointAt_mem_quotientPointsSubgroup`: every algebra-valued point on the
  exponential curve lies in the closed subgroup.
* `TauCeti.HopfIdeal.expPointAt_mem_quotientPointsSubgroup_identityComponent`: over an
  algebraically closed field, the exponential curve of a subgroup tangent vector lies in the
  identity component of the subgroup.
* `TauCeti.HopfAlgebra.expPointAt_mem_quotientPointsSubgroup_identityComponentHopfIdeal`: over an
  algebraically closed field, every exponential curve of `G` lies in `G°`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 11 and 12.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

namespace TauCeti

section General

namespace HopfIdeal

open TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Algebra ℚ H]

/-- The entire polynomial exponential curve of a subgroup tangent vector vanishes on
the defining Hopf ideal. -/
theorem expPointPolynomial_apply_eq_zero (I : HopfIdeal R H)
    {d : Derivation R H (CounitAlgebra R H R)} (hd : d ∈ I.lieSubalgebra (B := R))
    (hD : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0) {x : H} (hx : x ∈ I) :
    expPointPolynomial d hD x = 0 := by
  have hi (n : ℕ) :=
    Set.MapsTo.iterate (s := (I.toIdeal : Set H))
      (fun _ hy => I.leftInvariantDerivation_mem hd hy) n hx
  ext n
  rw [coeff_expPointPolynomial, Polynomial.coeff_zero]
  apply I.counit_eq_zero
  apply mem_toIdeal.mp
  rw [Algebra.smul_def]
  exact I.toIdeal.mul_mem_left _ (hi n)

/-- Every algebra-valued point of the exponential curve lies in the closed subgroup. -/
theorem expPointAt_mem_quotientPointsSubgroup (I : HopfIdeal R H)
    {d : Derivation R H (CounitAlgebra R H R)} (hd : d ∈ I.lieSubalgebra (B := R))
    (hD : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0)
    {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    expPointAt d hD t ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R B) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  rw [expPointAt_apply, I.expPointPolynomial_apply_eq_zero hd hD hx, map_zero]

end HopfIdeal

end General

section IdentityComponent

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} [Algebra ℚ H]

/-- Over an algebraically closed field, every algebra-valued point on the exponential curve of a
tangent vector to a closed subgroup lies in the identity component of that subgroup, since
`Lie(I°) = Lie(I)`. -/
theorem HopfIdeal.expPointAt_mem_quotientPointsSubgroup_identityComponent
    (I : HopfIdeal k H) {d : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hd : d ∈ I.lieSubalgebra (B := k))
    (hD : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    {B : Type v} [CommRing B] [Algebra k B] (t : B) :
    Bialgebra.expPointAt d hD t ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k B) :=
  I.identityComponent.expPointAt_mem_quotientPointsSubgroup
    (I.lieSubalgebra_identityComponent ▸ hd) hD t

/-- Over an algebraically closed field, every algebra-valued point on an exponential curve of `G`
lies in the identity component `G°`. -/
theorem HopfAlgebra.expPointAt_mem_quotientPointsSubgroup_identityComponentHopfIdeal
    {d : Derivation k H (Bialgebra.CounitAlgebra k H k)}
    (hD : ∀ h : H, ∃ n, (Bialgebra.leftInvariantDerivation d)^[n] h = 0)
    {B : Type v} [CommRing B] [Algebra k B] (t : B) :
    Bialgebra.expPointAt d hD t ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k B) :=
  (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).expPointAt_mem_quotientPointsSubgroup
    (HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top (k := k) (H := H) ▸
      LieSubalgebra.mem_top d) hD t

end IdentityComponent

end TauCeti
