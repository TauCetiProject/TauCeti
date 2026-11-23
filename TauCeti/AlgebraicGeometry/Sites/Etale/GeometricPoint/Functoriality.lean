/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Basic
public import TauCeti.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.IsSepClosed

/-!
# Pushforward functoriality and algebraic-closure comparisons

This file extends `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint` with:

* **Pushforward along scheme morphisms**: the functor `GeometricPoint.map f` along `f : X ⟶ Y`,
  with `mapId` and `mapComp`.
* **Algebraic vs. separable closures**: `ofAlgClosure` and `ofSepToAlgClosure`, showing that
  `Spec kbar ⟶ Spec ksep` is an isomorphism in `GeometricPoint S` if and only if the base field is
  perfect, while always inducing an isomorphism of points and étale stalks
  (`isIso_toPointFunctor_map`, `stalkIso`).

## References

* The Stacks Project, [Tag 03PO](https://stacks.math.columbia.edu/tag/03PO) and
  [Tag 04FN](https://stacks.math.columbia.edu/tag/04FN).
-/

public section

universe u

open CategoryTheory Opposite AlgebraicGeometry Scheme

namespace TauCeti.AlgebraicGeometry.Scheme.GeometricPoint

section Map

-- Exposed so `((map f).obj s).Ω` and `((map f).obj s).hom` unfold in statements of `mapId`
-- and `mapComp`.
/-- Pushforward of geometric points along a scheme morphism `f : X ⟶ Y`, sending `s` to
`s.hom ≫ f`. -/
@[expose, simps obj_hom map_hom]
noncomputable def map {X Y : Scheme.{u}} (f : X ⟶ Y) : GeometricPoint X ⥤ GeometricPoint Y where
  obj s := ⟨s.Ω, s.hom ≫ f⟩
  map φ := ⟨φ.hom, by rw [← Category.assoc, φ.w]⟩

/-- Pushforward along `𝟙 X` is naturally isomorphic to the identity functor. -/
noncomputable def mapId (X : Scheme.{u}) : map (𝟙 X) ≅ 𝟭 (GeometricPoint X) :=
  NatIso.ofComponents
    (fun s ↦ isoMk (Iso.refl _) (by
      rw [Iso.refl_hom]
      exact (Category.id_comp s.hom).trans (Category.comp_id s.hom).symm))
    (fun φ ↦ by
      ext : 1
      simp only [comp_hom, map_map_hom, Functor.id_map]
      exact (congrArg (φ.hom ≫ ·) ((isoMk_hom_hom (Iso.refl _) _).trans (Iso.refl_hom _))).trans
        ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
          (congrArg (· ≫ φ.hom) ((isoMk_hom_hom (Iso.refl _) _).trans (Iso.refl_hom _)).symm))))

/-- The component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_hom_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (isoMk_hom_hom (Iso.refl _) _).trans (Iso.refl_hom _)

/-- The inverse component of `mapId X` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapId_inv_app_hom {X : Scheme.{u}} (s : GeometricPoint X) :
    ((mapId X).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (isoMk_inv_hom (Iso.refl _) _).trans (Iso.refl_inv _)

/-- Pushforward along a composite `f ≫ g` is naturally isomorphic to the composite of the
pushforwards. -/
noncomputable def mapComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents
    (fun s ↦ isoMk (Iso.refl _) (by
      rw [Iso.refl_hom]
      exact (Category.id_comp ((s.hom ≫ f) ≫ g)).trans (Category.assoc s.hom f g)))
    (fun φ ↦ by
      ext : 1
      simp only [comp_hom, Functor.comp_map, map_map_hom]
      exact (congrArg (φ.hom ≫ ·) ((isoMk_hom_hom
          (Iso.refl (Spec (.of ((map (f ≫ g)).obj _).Ω))) _).trans (Iso.refl_hom _))).trans
        ((Category.comp_id _).trans ((Category.id_comp _).symm.trans
          (congrArg (· ≫ φ.hom) ((isoMk_hom_hom
            (Iso.refl (Spec (.of ((map (f ≫ g)).obj _).Ω))) _).trans (Iso.refl_hom _)).symm))))

/-- The component of `mapComp f g` at `s` has the identity as underlying scheme morphism. -/
@[simp]
theorem mapComp_hom_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).hom.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (isoMk_hom_hom (Iso.refl _) _).trans (Iso.refl_hom _)

/-- The inverse component of `mapComp f g` at `s` has the identity as underlying scheme
morphism. -/
@[simp]
theorem mapComp_inv_app_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : GeometricPoint X) :
    ((mapComp f g).inv.app s).hom = 𝟙 (Spec (.of s.Ω)) :=
  (isoMk_inv_hom (Iso.refl _) _).trans (Iso.refl_inv _)

end Map

section Closures

variable {S : Scheme.{u}}

/-- The canonical morphism from the algebraically closed geometric point over `s` to `s`,
exhibiting that algebraically closed points give the same stalks as separably closed ones. -/
noncomputable def ofAlgClosure (s : GeometricPoint S) :
    ofOver s.hom (AlgebraicClosure s.Ω) ⟶ s :=
  homOfRingHom (algebraMap s.Ω (AlgebraicClosure s.Ω)) rfl

/-- The ring homomorphism underlying `ofAlgClosure s` is `algebraMap s.Ω (AlgebraicClosure s.Ω)`. -/
@[simp]
theorem Hom.ringHom_ofAlgClosure (s : GeometricPoint S) :
    (ofAlgClosure s).ringHom = algebraMap s.Ω (AlgebraicClosure s.Ω) :=
  Hom.ringHom_homOfRingHom _ _

/-- `ofAlgClosure s` is an isomorphism in `GeometricPoint S` if and only if `s.Ω` is already
algebraically closed (whereas `(toPointFunctor S).map (ofAlgClosure s)` is always an isomorphism
by `isIso_toPointFunctor_map`). -/
theorem isIso_ofAlgClosure_iff (s : GeometricPoint S) :
    IsIso (ofAlgClosure s) ↔ IsAlgClosed s.Ω := by
  rw [Hom.isIso_iff_ringHom_surjective, Hom.ringHom_ofAlgClosure,
    ← IsAlgClosed.iff_algebraMap_surjective s.Ω (AlgebraicClosure s.Ω)]

/-- For a separably closed separable extension `Ω` of a field `K`, `ofAlgClosure (ofOver a Ω)` is
an isomorphism in `GeometricPoint S` if and only if `K` is perfect. -/
theorem isIso_ofAlgClosure_ofOver_iff_perfectField {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra K Ω] [Algebra.IsSeparable K Ω] :
    IsIso (ofAlgClosure (ofOver a Ω)) ↔ PerfectField K := by
  rw [isIso_ofAlgClosure_iff]
  exact IsSepClosed.isAlgClosed_iff_perfectField K Ω

/-- The canonical morphism from `ofOver a (AlgebraicClosure K)` to `ofOver a (SeparableClosure K)`.
It is an isomorphism in `GeometricPoint S` if and only if `K` is perfect
(`isIso_ofSepToAlgClosure_iff_perfectField`), while its image under `toPointFunctor S` is always
an isomorphism (`isIso_toPointFunctor_map`). -/
noncomputable def ofSepToAlgClosure {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    ofOver a (AlgebraicClosure K) ⟶ ofOver a (SeparableClosure K) :=
  homOfRingHom (algebraMap (SeparableClosure K) (AlgebraicClosure K)) <| by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]

/-- The ring homomorphism underlying `ofSepToAlgClosure a` is the canonical inclusion
`SeparableClosure K →+* AlgebraicClosure K`. -/
@[simp]
theorem Hom.ringHom_ofSepToAlgClosure {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    (ofSepToAlgClosure a).ringHom = algebraMap (SeparableClosure K) (AlgebraicClosure K) :=
  Hom.ringHom_homOfRingHom _ _

/-- `ofSepToAlgClosure a` is an isomorphism in `GeometricPoint S` if and only if `K` is perfect. -/
theorem isIso_ofSepToAlgClosure_iff_perfectField {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ S) :
    IsIso (ofSepToAlgClosure a) ↔ PerfectField K := by
  rw [Hom.isIso_iff_ringHom_surjective, Hom.ringHom_ofSepToAlgClosure]
  have : Algebra.IsAlgebraic (SeparableClosure K) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (L := SeparableClosure K) (A := AlgebraicClosure K)
  rw [← IsAlgClosed.iff_algebraMap_surjective (SeparableClosure K) (AlgebraicClosure K),
    IsSepClosed.isAlgClosed_iff_perfectField K (SeparableClosure K)]

end Closures

end TauCeti.AlgebraicGeometry.Scheme.GeometricPoint
