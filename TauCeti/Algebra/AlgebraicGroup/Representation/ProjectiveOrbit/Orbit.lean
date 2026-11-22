/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Orbit
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Quotient

/-!
# Comparison between scheme-theoretic orbits and projective-orbit quotient models

For a reduced finite-type affine algebraic group `G = Spec H` over an algebraically closed field
`k` acting on a finite-type `k`-scheme `X` with rational point `x : Spec k ⟶ X`, every orbit
scheme `orbitOver G x` (and every reduced homogeneous scheme `X`) is canonically isomorphic over
`Spec k` to Chevalley's projective-orbit quotient model representing `G / Stab_G(x)`, intertwining
the projective-orbit map `toProjectiveOrbit` with the orbit projection / orbit morphism.

## Main declarations

* `TauCeti.SchemeAction.exists_projectiveOrbit_iso_orbitOver`: every orbit scheme `orbitOver G x`
  is isomorphic over `Spec k` to a projective orbit scheme representing `G / Stab_G(x)`.
* `TauCeti.SchemeAction.exists_projectiveOrbit_iso_of_orbit_eq_univ`: every reduced homogeneous
  scheme `X` is isomorphic over `Spec k` to a projective orbit scheme representing `G / Stab_G(x)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.e–7.f.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (H : _root_.CommHopfAlgCat.{u} k) [Algebra.FiniteType k H]
  {X : Over (Spec (.of k))}
  [ModObj ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) X]
  [LocallyOfFiniteType X.hom] (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

local instance :
    LocallyOfFiniteType ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).hom :=
  (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec k H).mp inferInstance

local instance :
    CompactSpace ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of H)))

local instance [_root_.IsReduced H] :
    IsReduced ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))).left :=
  (affine_isReduced_iff (CommRingCat.of H)).mpr inferInstance

/-- **Every orbit scheme is isomorphic to Chevalley's projective-orbit quotient model.** For a
reduced finite-type affine group `Spec H` acting on a finite-type scheme over an algebraically
closed field, the orbit scheme `orbitOver (Spec H) x` is isomorphic over `Spec k` to a projective
orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and `toOrbit`. -/
theorem exists_projectiveOrbit_iso_orbitOver [_root_.IsReduced H] [CompactSpace X.left] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅
        orbitOver ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x),
      Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        toOrbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x := by
  obtain ⟨M, _, _, _, _, m, hm, isoQ, hproj⟩ :=
    HopfIdeal.exists_fppfHomogeneousQuotient_iso_projectiveOrbitPoints (stabilizerHopfIdeal H x)
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    representedQuotientIsoOrbitOver H x isoQ, ?_⟩
  have hcomp := congrArg Over.Hom.left
    (representedQuotientProjection_comp_representedQuotientIsoOrbitOver_hom H x isoQ)
  rw [Over.comp_left, congrArg Over.Hom.left hproj, orbitProjection_left] at hcomp
  exact hcomp

/-- **Every reduced homogeneous space is isomorphic to Chevalley's projective-orbit quotient
model.** In particular, every reduced finite-type homogeneous scheme `X` for a reduced finite-type
affine group `Spec H` over an algebraically closed field is isomorphic over `Spec k` to a
projective orbit scheme representing `G / Stab_G(x)`, intertwining `toProjectiveOrbit` and the
orbit morphism `Spec H ⟶ X`. -/
theorem exists_projectiveOrbit_iso_of_orbit_eq_univ [_root_.IsReduced H] [IsReduced X.left]
    (h : orbit ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x = Set.univ) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M)
      (_ : Module.Finite k M) (m : M) (hm : Module.IsUnimodular k m)
      (e : Over.mk (Comodule.projectiveOrbitToSpec (H := H) m hm) ≅ X),
      Comodule.toProjectiveOrbit (H := H) m hm ≫ e.hom.left =
        (orbitMap ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of k))) x).left := by
  have : CompactSpace X.left := Function.Surjective.compactSpace (orbitMap _ x).left.continuous
    ((surjective_iff _).mp ((surjective_orbitMap_iff_orbit_eq_univ _ x).mpr h))
  obtain ⟨M, _, _, _, _, m, hm, e, he⟩ := exists_projectiveOrbit_iso_orbitOver H x
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, m, hm,
    e ≪≫ orbitInclusionIso _ x h, ?_⟩
  rw [Iso.trans_hom, Over.comp_left, ← Category.assoc, he, orbitInclusionIso_hom,
    orbitInclusion_left]
  exact toOrbit_ι _ x

end TauCeti.SchemeAction
