/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit
import TauCeti.Algebra.Lie.AdjointAction.Regular

/-!
# Adjoint orbits under affine isogenies

Over an algebraically closed field, an affine isogeny is surjective on rational points.
Its differential therefore maps each rational adjoint orbit onto the corresponding orbit.
When the differential is injective, it also reflects conjugacy. In characteristic zero it
is a Lie algebra isomorphism, preserves and reflects ad-nilpotence, and preserves the
dimensions of the actual scheme-theoretic adjoint orbits.

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

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {f : H ⟶ K}

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

/-- An affine isogeny maps a rational adjoint orbit onto the corresponding orbit, even
when the isogeny is inseparable. This is a statement about sets of rational Lie algebra
points, not about points over arbitrary coefficient algebras. -/
theorem image_range_basePointsRepresentation (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    dualCotangentMap f.hom '' Set.range (fun g : WithConv (K →ₐ[k] k) =>
      Comodule.basePointsRepresentation (H := K) _ g x) =
    Set.range (fun g : WithConv (H →ₐ[k] k) =>
      Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x)) := by
  let _ := hf.finiteType_target
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨BialgHom.mapDomain f.hom g, (f.hom.dualCotangentMap_basePointsRepresentation g x).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨q, hq⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective k f hf.injective g
    have hq' : BialgHom.mapDomain (A := k) f.hom q = g := hq
    exact ⟨_, ⟨q, rfl⟩, (f.hom.dualCotangentMap_basePointsRepresentation q x).trans
      (congrArg (fun p => Comodule.basePointsRepresentation (H := H) _ p
        (dualCotangentMap f.hom x)) hq')⟩

/-- If the differential of an affine isogeny is injective, two rational Lie algebra
points are conjugate exactly when their images are conjugate. -/
theorem exists_basePointsRepresentation_eq_iff_of_injective (hf : IsIsogeny f)
    (hinj : Function.Injective (dualCotangentMap f.hom))
    (x y : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    (∃ g : WithConv (H →ₐ[k] k),
      Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x) =
        dualCotangentMap f.hom y) ↔
    ∃ g : WithConv (K →ₐ[k] k), Comodule.basePointsRepresentation (H := K) _ g x = y := by
  let _ := hf.finiteType_target
  constructor
  · intro h
    have hm : dualCotangentMap f.hom y ∈ Set.range (fun g : WithConv (H →ₐ[k] k) =>
        Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x)) := h
    rw [← hf.image_range_basePointsRepresentation x] at hm
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hm
    exact ⟨g, hinj hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨BialgHom.mapDomain f.hom g, (f.hom.dualCotangentMap_basePointsRepresentation g x).symm⟩

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
  have hinj : Function.Injective (dualCotangentMap f.hom) := by
    intro x y h
    apply hf.cotangentDualLieEquivOfCharZero.injective
    simpa only [LieEquiv.coe_coe, cotangentDualLieEquivOfCharZero_apply] using h
  exact hf.exists_basePointsRepresentation_eq_iff_of_injective hinj x y

omit [IsAlgClosed k] in
/-- A characteristic-zero affine isogeny preserves and reflects ad-nilpotence.
For semisimple Lie algebras this is the comparison of nilpotent elements. -/
theorem isNilpotent_ad_dualCotangentMap_iff_of_charZero (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    IsNilpotent (LieAlgebra.ad k _ (dualCotangentMap f.hom x)) ↔
      IsNilpotent (LieAlgebra.ad k _ x) := by
  let e := hf.cotangentDualLieEquivOfCharZero
  rw [← hf.cotangentDualLieEquivOfCharZero_apply x, ← LieAlgebra.conj_ad_apply]
  exact IsNilpotent.map_iff (f := e.toLinearEquiv.conjAlgEquiv k)
    (e.toLinearEquiv.conjAlgEquiv k).injective

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
  let e := hf.cotangentDualLieEquivOfCharZero
  have he : e x = dualCotangentMap f.hom x := hf.cotangentDualLieEquivOfCharZero_apply x
  have hker := e.finrank_ker_ad_apply x
  rw [he] at hker
  have hdim := e.toLinearEquiv.finrank_eq
  have hH := (LieAlgebra.ad k _ (dualCotangentMap f.hom x)).finrank_range_add_finrank_ker
  have hK := (LieAlgebra.ad k _ x).finrank_range_add_finrank_ker
  norm_cast
  omega

end CharZero

end TauCeti.CommHopfAlgCat.IsIsogeny
