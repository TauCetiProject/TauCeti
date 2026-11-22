/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ComplexifyRealify
public import TauCeti.Topology.VectorBundle.FiniteRank.Realification
public import TauCeti.Topology.VectorBundle.FiniteRank.Conjugate

/-!
# Complexification after realification of bundle cores

`complexifyRealifyIso` identifies the complexification of the underlying real bundle
of a complex finite-rank bundle core `A` with `A ⊕ conjugate(A)`. It is an actual
isomorphism of continuous vector bundles, natural in bundle maps and compatible with
pullback along arbitrary continuous base maps. No compactness or separation hypothesis
on the base is needed; rank zero and the empty base are included.

In real-part/imaginary-part block coordinates its fibre map is
`(a, b) ↦ (a + I b, a - I b)`. The conjugate transition on the second output block
is essential: that block is not a second copy of `A`. This is the bundle-level
comparison underlying the identity `c r = 1 + conjugation` in complex K-theory.

## References

* M. F. Atiyah, *K-Theory*, §1.2, realification and complexification.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

universe u v

variable {B : Type u} [TopologicalSpace B]

/-- The complexification of the realification of a complex bundle is the Whitney sum
of the bundle and its conjugate, with the original bundle first. -/
noncomputable def complexifyRealifyIso (A : FiniteRankBundleCore ℂ B) :
    (complexify B).obj ((realify B).obj A) ≅ whitneySum A ((conjugate B).obj A) :=
  constIso (fun _ => (Set.inter_self _).symm) (complexifyRealifyCoords A.rank)
    fun i j x _ _ =>
      (A.core.coordChange i j x).complexifyRealifyCoords_comp_complexifyCoords_realifyCoords

/-- The forward bundle comparison is the complex-linear coordinate splitting. -/
@[simp] theorem fiberMap_complexifyRealifyIso_hom (A : FiniteRankBundleCore ℂ B) (x : B) :
    (complexifyRealifyIso A).hom.fiberMap x =
      (complexifyRealifyCoords A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

/-- The inverse bundle comparison is the inverse coordinate splitting. -/
@[simp] theorem fiberMap_complexifyRealifyIso_inv (A : FiniteRankBundleCore ℂ B) (x : B) :
    (complexifyRealifyIso A).inv.fiberMap x =
      (complexifyRealifyCoords A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

/-- The splitting is natural for all continuous fibrewise complex-linear bundle maps. -/
@[reassoc] theorem complexifyRealifyIso_naturality {A D : FiniteRankBundleCore ℂ B}
    (f : A ⟶ D) :
    (complexify B).map ((realify B).map f) ≫ (complexifyRealifyIso D).hom =
      (complexifyRealifyIso A).hom ≫ whitneyMap f ((conjugate B).map f) := by
  apply hom_ext
  intro x
  simp only [fiberMap_comp, fiberMap_complexify_map, fiberMap_realify_map,
    fiberMap_complexifyRealifyIso_hom, fiberMap_whitneyMap, fiberMap_conjugate_map]
  exact (f.fiberMap x).complexifyRealifyCoords_comp_complexifyCoords_realifyCoords

variable {X : Type v} [TopologicalSpace X]

/-- Pullback of the forward splitting map is the forward map of the pulled-back splitting. -/
@[simp] theorem pullbackMap_complexifyRealifyIso_hom (A : FiniteRankBundleCore ℂ B) (f : C(X, B)) :
    pullbackMap (complexifyRealifyIso A).hom f = (complexifyRealifyIso (A.pullback f)).hom := by
  apply hom_ext
  intro x
  exact (fiberMap_pullbackMap (complexifyRealifyIso A).hom f x).trans
    ((fiberMap_complexifyRealifyIso_hom A (f x)).trans
      (fiberMap_complexifyRealifyIso_hom (A.pullback f) x).symm)

/-- Pullback of the splitting is the splitting of the pulled-back bundle. The two
sides use the strict pullback comparisons of coordinate functors and Whitney sums. -/
@[simp] theorem pullbackFunctor_mapIso_complexifyRealifyIso
    (A : FiniteRankBundleCore ℂ B) (f : C(X, B)) :
    (pullbackFunctor f).mapIso (complexifyRealifyIso A) =
      complexifyRealifyIso (A.pullback f) := by
  apply Iso.ext
  rw [Functor.mapIso_hom, pullbackFunctor_map, pullbackMap_complexifyRealifyIso_hom]

/-- Pullback of the inverse splitting map is the inverse map of the pulled-back splitting. -/
@[simp] theorem pullbackMap_complexifyRealifyIso_inv (A : FiniteRankBundleCore ℂ B) (f : C(X, B)) :
    pullbackMap (complexifyRealifyIso A).inv f = (complexifyRealifyIso (A.pullback f)).inv := by
  rw [← pullbackFunctor_map (f := f), ← Functor.mapIso_inv,
    pullbackFunctor_mapIso_complexifyRealifyIso]

end TauCeti.FiniteRankBundleCore
