/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
public import TauCeti.RingTheory.Etale.Reduced
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Finite étale quotients by subgroups containing the identity component

Over an algebraically closed field, the coinvariants of a closed subgroup containing the
identity component form a finite étale algebra. For normal subgroups this is the coordinate
algebra of the represented quotient. Neither the ambient group nor the subgroup needs to
be reduced, and finiteness of the invariant algebra does not require normality.

The identity-component coinvariants are the functions on the finite component group.
For a normal subgroup containing the identity component, the quotient is therefore a
finite étale quotient of the component group.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, quotients and component groups.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7 and 16.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/- The component coordinate map and its scheme-theoretic kernel come from
`Connected.ComponentGroup.Coordinate`. Faithfully flat descent identifies its range
with the identity-component coinvariants. -/
/-- The functions invariant under the identity component are exactly the pullbacks of
functions on the finite component group, including for nonreduced affine groups. -/
@[simp]
theorem coinvariants_identityComponentHopfIdeal_eq_range
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).coinvariants =
      (componentCoordinateMap H).range := by
  let C := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))
  let _ : Algebra.IsGeometricallyReduced k C := isGeometricallyReduced_of_smooth k C
  have hmap : (componentCoordinateHom H).hom.toAlgHom = componentCoordinateMap H :=
    AlgHom.ext (componentCoordinateHom_apply H)
  rw [← hmap, ← kernelHopfIdeal_componentCoordinateHom H]
  apply CommHopfAlgCat.coinvariants_kernelHopfIdeal_eq_range
  apply (CommHopfAlgCat.faithfullyFlat_iff_injective_of_isGeometricallyReduced
    (componentCoordinateHom H)).mpr
  exact componentCoordinateHom_injective H

/-- The constant component coordinate algebra is canonically isomorphic to the
identity-component coinvariants, including for nonreduced affine groups. -/
noncomputable def componentCoinvariantsIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.of k
        (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) ≅
      CommHopfAlgCat.coinvariants (isNormal_identityComponentHopfIdeal H) := by
  let C := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))
  let _ : Algebra.IsGeometricallyReduced k C := isGeometricallyReduced_of_smooth k C
  let f := CommHopfAlgCat.liftCoinvariants (isNormal_identityComponentHopfIdeal H)
    (componentCoordinateHom H) (kernelHopfIdeal_componentCoordinateHom H).le
  have hff := (CommHopfAlgCat.faithfullyFlat_iff_injective_of_isGeometricallyReduced
    (componentCoordinateHom H)).mpr (componentCoordinateHom_injective H)
  have hbij := CommHopfAlgCat.bijective_liftCoinvariants_of_faithfullyFlat
    (isNormal_identityComponentHopfIdeal H) (componentCoordinateHom H) hff
    (kernelHopfIdeal_componentCoordinateHom H)
  let _ : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hbij
  exact asIso f

/-- The comparison with coinvariants recovers the component coordinate morphism after
composition with the coinvariant inclusion. -/
@[reassoc (attr := simp)]
theorem componentCoinvariantsIso_hom_comp (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentCoinvariantsIso H).hom ≫
        CommHopfAlgCat.coinvariantsι (isNormal_identityComponentHopfIdeal H) =
      componentCoordinateHom H := by
  ext x
  exact CommHopfAlgCat.coe_liftCoinvariants_apply
    (isNormal_identityComponentHopfIdeal H) (componentCoordinateHom H)
    (kernelHopfIdeal_componentCoordinateHom H).le x

/-- The invariant functions of a subgroup containing the identity component are
finite-dimensional. Normality and reducedness are not required. -/
theorem moduleFinite_coinvariants_of_le_identityComponentHopfIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : I ≤ HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) :
    Module.Finite k I.coinvariants := by
  let f := componentCoordinateMap H
  let _ : Module.Finite k f.range := Module.Finite.of_surjective
    f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  have hsub : I.coinvariants ≤ f.range := (HopfIdeal.coinvariants_mono hI).trans_eq
    (coinvariants_identityComponentHopfIdeal_eq_range H)
  let j := Subalgebra.inclusion hsub
  exact Module.Finite.of_injective j.toLinearMap (Subalgebra.inclusion_injective hsub)

/-- The invariant algebra of a subgroup containing the identity component is étale,
even when the ambient group or the subgroup is nonreduced. -/
theorem algebraEtale_coinvariants_of_le_identityComponentHopfIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hI : I ≤ HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) :
    Algebra.Etale k I.coinvariants := by
  let f := componentCoordinateMap H
  let C := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))
  let _ : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field k C
  let e := AlgEquiv.ofInjective f (componentCoordinateMap_injective H)
  let _ : IsReduced f.range := isReduced_of_injective e.symm.toRingHom e.symm.injective
  have hsub : I.coinvariants ≤ f.range := (HopfIdeal.coinvariants_mono hI).trans_eq
    (coinvariants_identityComponentHopfIdeal_eq_range H)
  let j := Subalgebra.inclusion hsub
  let _ : IsReduced I.coinvariants := isReduced_of_injective j (Subalgebra.inclusion_injective hsub)
  let _ := moduleFinite_coinvariants_of_le_identityComponentHopfIdeal H I hI
  exact algebraEtale_of_finite_of_isReduced k I.coinvariants

end TauCeti.FiniteTypeCommHopfAlgCat
