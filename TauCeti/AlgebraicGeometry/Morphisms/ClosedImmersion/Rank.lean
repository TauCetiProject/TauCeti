/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.LocallyFree

/-!
# Closed immersions between finite flat schemes of equal rank

A closed immersion between schemes finite and flat over the same base is an isomorphism
if their rank functions agree. This works over arbitrary schemes, including nonreduced bases,
and does not require local finite presentation. It detects when an inclusion of finite flat
closed subschemes is equality.

The algebraic input is Mathlib's
`Module.bijective_of_surjective_of_rankAtStalk_eq`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- A closed immersion between schemes finite and flat over the same base is an isomorphism
exactly when their rank functions over the base agree. -/
theorem Scheme.Hom.isIso_iff_finrank_comp_eq (i : X ⟶ Y) (g : Y ⟶ S)
    [IsClosedImmersion i] [IsFinite g] [Flat g] [Flat (i ≫ g)] :
    IsIso i ↔ (i ≫ g).finrank = g.finrank := by
  refine ⟨fun _ ↦ Scheme.Hom.finrank_comp_left_of_isIso i g, fun h ↦ ?_⟩
  -- Isomorphisms are local on the target; pull back a cover of the common base.
  wlog hS : ∃ R, S = Spec R generalizing X Y S with H
  · rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover
        (P := .isomorphisms Scheme) (S.affineCover.pullback₁ g)]
    intro a
    let j := S.affineCover.f a
    let e := pullbackRightPullbackFstIso g j i
    have he : pullback.snd i (pullback.fst g j) ≫ pullback.snd g j =
        e.hom ≫ pullback.snd (i ≫ g) j :=
      (pullbackRightPullbackFstIso_hom_snd g j i).symm
    have : Flat (pullback.snd i (pullback.fst g j) ≫ pullback.snd g j) := by
      rw [he]; infer_instance
    refine H (pullback.snd i (pullback.fst g j)) (pullback.snd g j) ?_ ⟨_, rfl⟩
    ext s
    rw [he, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_snd,
      Scheme.Hom.finrank_pullback_snd, h]
  obtain ⟨R, rfl⟩ := hS
  -- Finite morphisms to an affine scheme have affine sources, so use their spectra.
  wlog hY : ∃ A, Y = Spec A generalizing X Y with H
  · have : IsAffine Y := isAffine_of_isAffineHom g
    rw [← isIso_comp_right_iff i Y.isoSpec.hom]
    have : Flat ((i ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv ≫ g) := by
      simpa using (inferInstance : Flat (i ≫ g))
    refine H (i ≫ Y.isoSpec.hom) (Y.isoSpec.inv ≫ g) ?_ ⟨_, rfl⟩
    rw [Category.assoc, Iso.hom_inv_id_assoc,
      Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.inv g]
    exact h
  obtain ⟨A, rfl⟩ := hY
  wlog hX : ∃ B, X = Spec B generalizing X with H
  · have : IsAffine X := isAffine_of_isAffineHom i
    rw [← isIso_comp_left_iff X.isoSpec.inv i]
    have : Flat ((X.isoSpec.inv ≫ i) ≫ g) := by
      rw [Category.assoc]; infer_instance
    refine H (X.isoSpec.inv ≫ i) ?_ ⟨_, rfl⟩
    rw [Category.assoc, Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.inv (i ≫ g)]
    exact h
  obtain ⟨B, rfl⟩ := hX
  -- On coordinates a closed immersion is surjective, and equal ranks force injectivity.
  obtain ⟨φ, rfl⟩ := Spec.map_surjective i
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hs : Function.Surjective φ.hom := by
    have he : φ = (Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop ≫
        (Scheme.ΓSpecIso B).hom := by simp
    rw [he, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).surjective.comp
      (((IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2).comp
        (ConcreteCategory.bijective_of_isIso _).surjective)
  have : IsFinite (Spec.map φ ≫ Spec.map ψ) := inferInstance
  have hfin : (ψ ≫ φ).hom.Finite := by
    rwa [← Spec.map_comp, IsFinite.SpecMap_iff] at ‹IsFinite (Spec.map φ ≫ Spec.map ψ)›
  have hflat : (ψ ≫ φ).hom.Flat := by
    rwa [← Spec.map_comp, Flat.SpecMap_iff] at ‹Flat (Spec.map φ ≫ Spec.map ψ)›
  have hψfin : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp inferInstance
  have hψflat : ψ.hom.Flat := (Flat.SpecMap_iff (f := ψ)).mp inferInstance
  let := ψ.hom.toAlgebra
  let := (ψ ≫ φ).hom.toAlgebra
  let F : A →ₐ[R] B := ⟨φ.hom, fun _ ↦ rfl⟩
  have : Module.Finite R A := hψfin
  have : Module.Flat R A := hψflat
  have : Module.Finite R B := hfin
  have : Module.Flat R B := hflat
  rw [isIso_SpecMap_iff]
  apply Module.bijective_of_surjective_of_rankAtStalk_eq (φ := F.toLinearMap) hs
  intro m _
  have hm := congrFun h (⟨m, inferInstance⟩ : PrimeSpectrum R)
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat,
    Scheme.Hom.finrank_SpecMap_eq_finrank hψfin hψflat] at hm
  rw [← RingHom.algebraMap_toAlgebra ψ.hom,
    ← RingHom.algebraMap_toAlgebra (ψ ≫ φ).hom, RingHom.finrank_algebraMap,
    RingHom.finrank_algebraMap] at hm
  exact hm.symm

end AlgebraicGeometry
