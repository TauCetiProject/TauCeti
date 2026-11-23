/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Map
import TauCeti.Algebra.Lie.AdjointAction.Regular

/-!
# Adjoint orbits under affine isogenies

Over an algebraically closed field, an affine isogeny is surjective on rational points.
Its differential therefore maps each rational adjoint orbit onto the corresponding orbit.
When the differential is injective, it also reflects conjugacy. In characteristic zero it
is a Lie algebra isomorphism, preserves and reflects ad-nilpotence, and preserves the
dimensions of the actual scheme-theoretic adjoint orbits. An isogeny with étale kernel, over any
commutative base ring, also preserves and reflects ad-nilpotence.

Over an algebraically closed field of characteristic zero the differential therefore identifies
the sets of rational adjoint orbits (`TauCeti.CommHopfAlgCat.IsIsogeny.adjointOrbitOrderIso`).
This identification is an order isomorphism for the closure order, so it matches orbit closures,
and it matches nilpotent orbits with nilpotent orbits
(`TauCeti.CommHopfAlgCat.IsIsogeny.isNilpotentAd_adjointOrbitOrderIso_iff`).

The coordinate arrow `f : H ⟶ K` represents `Spec K → Spec H`, so the differential and
orbit comparisons go from the cotangent dual of `K` to that of `H`. These results apply in
particular to semisimple central isogenies. For a reductive group, the ad-nilpotent locus
also contains the center; the ad-nilpotence comparison here does not identify that locus
with the zero-central-coordinate nilpotent cone. Nor does an orbit comparison identify
centralizers or their component groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 18.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3.
-/

public section

namespace TauCeti.CommHopfAlgCat.IsIsogeny

open Derivation

universe u v

/-- An isogeny with étale kernel preserves and reflects ad-nilpotence, in any characteristic and
over any commutative base ring. Neither group needs to be smooth or of finite type. -/
theorem isNilpotent_ad_dualCotangentMap_iff_of_etaleKernel {R : Type u} [CommRing R]
    {H K : _root_.CommHopfAlgCat.{v} R} {f : H ⟶ K} (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual R (Bialgebra.CotangentSpace R K)) :
    IsNilpotent (LieAlgebra.ad R _ (dualCotangentMap f.hom x)) ↔
      IsNilpotent (LieAlgebra.ad R _ x) := by
  rw [← hf.cotangentDualLieEquivOfEtaleKernel_apply hker x]
  exact (hf.cotangentDualLieEquivOfEtaleKernel hker).isNilpotent_ad_apply_iff x

/-- A characteristic-zero affine isogeny preserves and reflects ad-nilpotence.
For semisimple Lie algebras this is the comparison of nilpotent elements. -/
theorem isNilpotent_ad_dualCotangentMap_iff_of_charZero {k : Type u} [Field k] [CharZero k]
    {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K} (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    IsNilpotent (LieAlgebra.ad k _ (dualCotangentMap f.hom x)) ↔
      IsNilpotent (LieAlgebra.ad k _ x) := by
  rw [← hf.cotangentDualLieEquivOfCharZero_apply x]
  exact hf.cotangentDualLieEquivOfCharZero.isNilpotent_ad_apply_iff x

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {f : H ⟶ K}

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

section CharZero

variable [CharZero k]

/-- A characteristic-zero affine isogeny preserves and reflects rational adjoint conjugacy.
Together with bijectivity of its differential, this identifies the sets of adjoint orbits. -/
theorem exists_basePointsRepresentation_eq_iff_of_charZero (hf : IsIsogeny f)
    (x y : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    (∃ g : WithConv (H →ₐ[k] k),
      Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x) =
        dualCotangentMap f.hom y) ↔
    ∃ g : WithConv (K →ₐ[k] k), Comodule.basePointsRepresentation (H := K) _ g x = y := by
  let _ := hf.finiteType_target
  exact CommHopfAlgCat.exists_basePointsRepresentation_eq_iff_of_injective hf.injective
    hf.dualCotangentMap_bijective_of_charZero.injective x y

/-- The actual scheme-theoretic adjoint orbits of corresponding elements have equal
dimensions under a characteristic-zero affine isogeny. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_eq_of_charZero (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap (H := H)
      ((dualCotangentMap f.hom x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
      (Module.isUnimodular_mk_one _))) =
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap (H := K)
      ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k K) × k)
      (Module.isUnimodular_mk_one x))) := by
  let _ := hf.finiteType_target
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad,
    topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  rw [← hf.cotangentDualLieEquivOfCharZero_apply x,
    hf.cotangentDualLieEquivOfCharZero.finrank_range_ad_apply x]

section OrbitOrder

/-- **Adjoint orbits under an isogeny.** Over an algebraically closed field of characteristic
zero, the differential of an affine isogeny `Spec K → Spec H` identifies the rational adjoint
orbits of `Spec K` with those of `Spec H`, as ordered sets for the closure order: the orbit of
`x` corresponds to the orbit of `dφ x`, and one orbit lies in the closure of another exactly when
the same holds for the corresponding orbits. The finite type of `K` follows from that of `H`
(`TauCeti.CommHopfAlgCat.IsIsogeny.finiteType_target`). -/
noncomputable def adjointOrbitOrderIso (hf : IsIsogeny f) :
    haveI := hf.finiteType_target
    Comodule.VectorOrbit k K (Module.Dual k (Bialgebra.CotangentSpace k K)) ≃o
      Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
  let _ := hf.finiteType_target
  Comodule.VectorOrbit.orderIsoOfSurjective (mapDomain_surjective_of_injective k f hf.injective)
    hf.cotangentDualLieEquivOfCharZero.toLinearEquiv fun g x ↦ by
      simpa [cotangentDualLieEquivOfCharZero_apply] using
        f.hom.dualCotangentMap_basePointsRepresentation g x

/-- The isogeny sends the adjoint orbit of `x` to the adjoint orbit of `dφ x`. -/
@[simp]
theorem adjointOrbitOrderIso_mk (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    hf.adjointOrbitOrderIso (Comodule.VectorOrbit.mk x) =
      Comodule.VectorOrbit.mk (dualCotangentMap f.hom x) := by
  let _ := hf.finiteType_target
  rw [adjointOrbitOrderIso, Comodule.VectorOrbit.orderIsoOfSurjective_mk,
    LieEquiv.coe_toLinearEquiv, cotangentDualLieEquivOfCharZero_apply]

/-- The inverse correspondence sends the adjoint orbit of `y` to the adjoint orbit of the
unique preimage of `y` under the differential. -/
@[simp]
theorem adjointOrbitOrderIso_symm_mk (hf : IsIsogeny f)
    (y : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    haveI := hf.finiteType_target
    hf.adjointOrbitOrderIso.symm (Comodule.VectorOrbit.mk y) =
      Comodule.VectorOrbit.mk (hf.cotangentDualLieEquivOfCharZero.symm y) := by
  let _ := hf.finiteType_target
  rw [OrderIso.symm_apply_eq, adjointOrbitOrderIso_mk, ← hf.cotangentDualLieEquivOfCharZero_apply,
    LieEquiv.apply_symm_apply]

/-- An isogeny matches nilpotent adjoint orbits with nilpotent adjoint orbits. -/
@[simp]
theorem isNilpotentAd_adjointOrbitOrderIso_iff (hf : IsIsogeny f)
    (O : haveI := hf.finiteType_target
      Comodule.VectorOrbit k K (Module.Dual k (Bialgebra.CotangentSpace k K))) :
    haveI := hf.finiteType_target
    (hf.adjointOrbitOrderIso O).IsNilpotentAd ↔ O.IsNilpotentAd := by
  let _ := hf.finiteType_target
  induction O using Comodule.VectorOrbit.ind with | h x
  rw [adjointOrbitOrderIso_mk, Comodule.VectorOrbit.isNilpotentAd_mk_iff,
    Comodule.VectorOrbit.isNilpotentAd_mk_iff, isNilpotent_ad_dualCotangentMap_iff_of_charZero hf]

end OrbitOrder

end CharZero

end TauCeti.CommHopfAlgCat.IsIsogeny
