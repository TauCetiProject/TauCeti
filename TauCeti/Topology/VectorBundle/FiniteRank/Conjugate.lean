/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Normed.Operator.IntrinsicStar
public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback

/-!
# Conjugation of complex finite-rank bundle cores

Conjugating the transition matrices of a complex bundle gives its conjugate bundle.
`CoordinateFunctor.conjugate` uses Mathlib's intrinsic star of operators, not the
adjoint: its value on `f` is `v ↦ conj (f (conj v))`, coordinatewise.
The resulting `FiniteRankBundleCore.conjugate` is an additive functor on actual
point-indexed vector-bundle cores, with no hypothesis on the base.

`doubleConjugateIso` and `doubleConjugateNatIso` identify double conjugation with
the identity, by the identity map on every fibre. Conjugation commutes with
pullback by `conjugatePullbackIso`, naturally in bundle maps. It preserves trivial
bundles by `CoordinateFunctor.mapCoreTrivialIso`, and, being additive, preserves
Whitney biproducts. All constructions include rank zero and empty bases.

The chartwise construction uses `CoordinateFunctor.mapCore` and Mathlib's
intrinsic star on `WithConv` continuous linear maps.

## References

* M. F. Atiyah, *K-Theory*, §1.2, conjugate bundles.
-/

public section

open Bundle CategoryTheory WithConv

namespace TauCeti

namespace CoordinateFunctor

/-- Conjugation of complex coordinate spaces and their linear maps, with unchanged dimension. -/
-- The rank function must reduce for the dependent coordinate models of `mapCore`.
@[expose]
noncomputable def conjugate : CoordinateFunctor ℂ ℂ where
  rank n := n
  map f := (star (toConv f)).ofConv
  continuous_map _ _ := ContinuousLinearMap.continuous_intrinsicStar
  map_id _ := congrArg ofConv ContinuousLinearMap.intrinsicStar_id
  map_comp g f := congrArg ofConv (ContinuousLinearMap.intrinsicStar_comp' g f)

@[simp] theorem rank_conjugate (n : ℕ) : conjugate.rank n = n := (rfl)

/-- The conjugated operator is the intrinsic star, not the adjoint. -/
@[simp] theorem map_conjugate {m n : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    conjugate.map f = (star (toConv f)).ofConv := (rfl)

end CoordinateFunctor

namespace FiniteRankBundleCore

universe u v

variable (B : Type u) [TopologicalSpace B]

/-- The conjugate bundle functor, obtained by conjugating all transition matrices. -/
-- The object projection must reduce when matching the dependent fibre-map types.
@[expose]
noncomputable def conjugate : FiniteRankBundleCore ℂ B ⥤ FiniteRankBundleCore ℂ B :=
  CoordinateFunctor.conjugate.functor B

/-- Conjugation preserves addition of bundle maps and hence Whitney biproducts. -/
instance : (conjugate B).Additive :=
  CoordinateFunctor.conjugate.functor_additive fun f g =>
    congrArg ofConv (star_add (toConv f) (toConv g))

variable {B}

theorem conjugate_obj (A : FiniteRankBundleCore ℂ B) :
    (conjugate B).obj A = CoordinateFunctor.conjugate.mapCore A := (rfl)

theorem conjugate_map {A D : FiniteRankBundleCore ℂ B} (f : A ⟶ D) :
    (conjugate B).map f = CoordinateFunctor.conjugate.mapHom f := (rfl)

@[simp] theorem rank_conjugate_obj (A : FiniteRankBundleCore ℂ B) :
    ((conjugate B).obj A).rank = A.rank := (rfl)

@[simp] theorem localTriv_baseSet_conjugate_obj (A : FiniteRankBundleCore ℂ B) (i : B) :
    (((conjugate B).obj A).core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transitions of the conjugate core are the intrinsic conjugates of the transitions. -/
@[simp] theorem coordChange_conjugate_obj (A : FiniteRankBundleCore ℂ B) (i j x : B) :
    ((conjugate B).obj A).core.coordChange i j x =
      (star (toConv (A.core.coordChange i j x))).ofConv := (rfl)

/-- On each fibre the conjugated bundle map is the intrinsic conjugate of the original map. -/
@[simp] theorem fiberMap_conjugate_map {A D : FiniteRankBundleCore ℂ B} (f : A ⟶ D) (x : B) :
    ((conjugate B).map f).fiberMap x = (star (toConv (f.fiberMap x))).ofConv :=
  CoordinateFunctor.fiberMap_mapHom _ f x

/-- Double conjugation is isomorphic to the original bundle by the identity on every fibre. -/
noncomputable def doubleConjugateIso (A : FiniteRankBundleCore ℂ B) :
    (conjugate B).obj ((conjugate B).obj A) ≅ A :=
  constIso (fun _ => rfl) (ContinuousLinearEquiv.refl ℂ _) fun i j x _ _ => by
    -- Work on standard coordinate spaces, rather than the inherited core-fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)).comp
        (star (toConv (star (toConv (A.core.coordChange i j x))).ofConv)).ofConv =
        (A.core.coordChange i j x).comp (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)) := by
      simp
    exact h

@[simp] theorem fiberMap_doubleConjugateIso_hom (A : FiniteRankBundleCore ℂ B) (x : B) :
    (doubleConjugateIso A).hom.fiberMap x = ContinuousLinearMap.id ℂ (Fin A.rank → ℂ) := by
  rw [doubleConjugateIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_doubleConjugateIso_inv (A : FiniteRankBundleCore ℂ B) (x : B) :
    (doubleConjugateIso A).inv.fiberMap x = ContinuousLinearMap.id ℂ (Fin A.rank → ℂ) := by
  rw [doubleConjugateIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- The double-conjugation comparison is natural in bundle maps. -/
@[reassoc] theorem doubleConjugateIso_naturality {A D : FiniteRankBundleCore ℂ B} (f : A ⟶ D) :
    (conjugate B).map ((conjugate B).map f) ≫ (doubleConjugateIso D).hom =
      (doubleConjugateIso A).hom ≫ f := by
  apply hom_ext
  intro x
  simp only [fiberMap_comp, fiberMap_conjugate_map, fiberMap_doubleConjugateIso_hom]
  -- State the operator identity on standard coordinates to fix the fibre instances.
  have h : (ContinuousLinearMap.id ℂ (Fin D.rank → ℂ)).comp
      (star (toConv (star (toConv (f.fiberMap x))).ofConv)).ofConv =
      (f.fiberMap x).comp (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)) := by
    simp
  exact h

variable (B) in
/-- Double conjugation is naturally isomorphic to the identity functor. -/
noncomputable def doubleConjugateNatIso : conjugate B ⋙ conjugate B ≅ 𝟭 _ :=
  NatIso.ofComponents doubleConjugateIso doubleConjugateIso_naturality

@[simp] theorem doubleConjugateNatIso_app (A : FiniteRankBundleCore ℂ B) :
    (doubleConjugateNatIso B).app A = doubleConjugateIso A := (rfl)

variable (B) in
/-- Conjugation is an equivalence of the bundle-core category with itself. -/
-- The functor projections must reduce to type the dependent unit and counit comparisons.
@[expose]
noncomputable def conjugateEquivalence : FiniteRankBundleCore ℂ B ≌ FiniteRankBundleCore ℂ B where
  functor := conjugate B
  inverse := conjugate B
  unitIso := (doubleConjugateNatIso B).symm
  counitIso := doubleConjugateNatIso B
  functor_unitIso_comp A := by
    apply hom_ext
    intro x
    simp only [Functor.comp_obj, Iso.symm_hom,
      doubleConjugateNatIso, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      fiberMap_comp, fiberMap_conjugate_map, fiberMap_doubleConjugateIso_hom,
      fiberMap_doubleConjugateIso_inv, fiberMap_id]
    -- The category's dependent fibres use these standard coordinate spaces.
    have h : (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)).comp
        (star (toConv (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)))).ofConv =
        ContinuousLinearMap.id ℂ (Fin A.rank → ℂ) := by
      simp
    exact h

@[simp] theorem conjugateEquivalence_functor : (conjugateEquivalence B).functor = conjugate B :=
  (rfl)

@[simp] theorem conjugateEquivalence_inverse : (conjugateEquivalence B).inverse = conjugate B :=
  (rfl)

@[simp] theorem conjugateEquivalence_unitIso :
    (conjugateEquivalence B).unitIso = (doubleConjugateNatIso B).symm := (rfl)

@[simp] theorem conjugateEquivalence_counitIso :
    (conjugateEquivalence B).counitIso = doubleConjugateNatIso B := (rfl)

/-- Conjugation is an equivalence, with inverse conjugation. -/
instance : (conjugate B).IsEquivalence := (conjugateEquivalence B).isEquivalence_functor

variable {X : Type v} [TopologicalSpace X]

/-- Conjugation commutes with pullback, by the identity in every coordinate fibre. -/
noncomputable def conjugatePullbackIso (A : FiniteRankBundleCore ℂ B) (f : C(X, B)) :
    (conjugate X).obj (A.pullback f) ≅ ((conjugate B).obj A).pullback f :=
  constIso (fun _ => rfl) (ContinuousLinearEquiv.refl ℂ _) fun i j x _ _ => by
    simp only [coordChange_conjugate_obj, coordChange_pullback]
    -- State the identity on standard coordinates to fix the inherited fibre instances.
    have h : (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)).comp
        (star (toConv (A.core.coordChange (f i) (f j) (f x)))).ofConv =
        (star (toConv (A.core.coordChange (f i) (f j) (f x)))).ofConv.comp
          (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)) := by
      simp
    exact h

@[simp] theorem fiberMap_conjugatePullbackIso_hom (A : FiniteRankBundleCore ℂ B)
    (f : C(X, B)) (x : X) :
    (conjugatePullbackIso A f).hom.fiberMap x =
      ContinuousLinearMap.id ℂ (Fin A.rank → ℂ) := by
  rw [conjugatePullbackIso]
  exact fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_conjugatePullbackIso_inv (A : FiniteRankBundleCore ℂ B)
    (f : C(X, B)) (x : X) :
    (conjugatePullbackIso A f).inv.fiberMap x =
      ContinuousLinearMap.id ℂ (Fin A.rank → ℂ) := by
  rw [conjugatePullbackIso]
  exact fiberMap_constIso_inv _ _ _ x

/-- The pullback comparison is natural in bundle maps. -/
@[reassoc] theorem conjugatePullbackIso_naturality {A D : FiniteRankBundleCore ℂ B}
    (a : A ⟶ D) (f : C(X, B)) :
    (conjugate X).map (pullbackMap a f) ≫ (conjugatePullbackIso D f).hom =
      (conjugatePullbackIso A f).hom ≫ pullbackMap ((conjugate B).map a) f := by
  apply hom_ext
  intro x
  simp only [fiberMap_comp, fiberMap_conjugate_map, fiberMap_pullbackMap,
    fiberMap_conjugatePullbackIso_hom]
  -- State the identity on the common standard coordinate models.
  have h : (ContinuousLinearMap.id ℂ (Fin D.rank → ℂ)).comp
      (star (toConv (a.fiberMap (f x)))).ofConv =
      (star (toConv (a.fiberMap (f x)))).ofConv.comp
        (ContinuousLinearMap.id ℂ (Fin A.rank → ℂ)) := by
    simp
  exact h

/-- Pullback and conjugation commute as functors. -/
noncomputable def conjugatePullbackNatIso (f : C(X, B)) :
    pullbackFunctor f ⋙ conjugate X ≅ conjugate B ⋙ pullbackFunctor f :=
  NatIso.ofComponents (fun A => conjugatePullbackIso A f)
    (fun a => conjugatePullbackIso_naturality a f)

@[simp] theorem conjugatePullbackNatIso_app (f : C(X, B)) (A : FiniteRankBundleCore ℂ B) :
    (conjugatePullbackNatIso f).app A = conjugatePullbackIso A f := (rfl)

end FiniteRankBundleCore
end TauCeti
