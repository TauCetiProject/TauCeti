/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.TensorPow.Skeleton
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
import Mathlib.CategoryTheory.Monoidal.Transport
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# The symmetric monoidal category of `C^n` finite-rank cores and its Picard group

`ContMDiffFiniteRankBundleCore I n B` bundles a point-indexed finite-rank vector-bundle core
`A : FiniteRankBundleCore 𝕜 B` with `C^n` regularity of its transition functions for a model with
corners `I` on `B`. Its morphisms are coordinate bundle maps `A.toCore ⟶ D.toCore` whose glued
maps of total spaces are `C^n`. Over a complex manifold (`I = 𝓘(ℂ, EB)` and `n = ∞`), this is the
category of holomorphic finite-rank vector-bundle cores and holomorphic bundle morphisms.

Because `FiniteRankBundleCore.contMDiff_totalSpaceMap_monoidalTensorHom` and the monoidal coherence
regularity theorems of `TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal` require no
completeness of `𝕜`, transporting the monoidal, braided, and symmetric axioms along the faithful
forgetful functor `forgetToCore` equips `ContMDiffFiniteRankBundleCore I n B` with a symmetric
monoidal structure, whose generic tensor powers `TauCeti.tensorPow` match powers in
`CategoryTheory.Skeleton` (`TauCeti.toSkeleton_tensorPow`).

The commutative group `ContMDiffPicardGroup I n B` is the group of units
`(Skeleton (ContMDiffFiniteRankBundleCore I n B))ˣ` of isomorphism classes of tensor-invertible
`C^n` cores; for `I = 𝓘(ℂ, EB)` and `n = ∞`, this is the holomorphic Picard group of `B`. Over a
nonempty base every invertible `C^n` core has rank one, and without completeness of `𝕜` a
nowhere-vanishing `C^n` section of a rank-one `C^n` core makes `homFromTensorUnitOfSection` an
isomorphism with explicit inverse `homToTensorUnitOfSectionNeZero`
(`isoTensorUnitOfSectionNeZero`, `isIso_homFromTensorUnitOfSection_iff`), so a rank-one `C^n` core
is isomorphic to `𝟙_` if and only if it admits a nowhere-vanishing `C^n` section
(`nonempty_iso_tensorUnit_iff_exists_section_ne_zero`). Over a complete scalar field:

* every `C^n` morphism with bijective fibre maps is an isomorphism (`isIso_iff_bijective`);
* every rank-one `C^n` core `A` satisfies `A.dual ⊗ A ≅ 𝟙_` (`dualTensorIsoUnit`), hence defines a
  class `ContMDiffPicardGroup.ofRankOne A` compatible with tensor products, duals, and tensor
  powers;
* a rank-one `C^n` core represents `1` in `ContMDiffPicardGroup I n B` if and only if it admits a
  nowhere-vanishing `C^n` section, equivalently a global linear trivialization in the maximal `C^n`
  atlas (`ofRankOne_eq_one_iff_exists_section_ne_zero`,
  `ofRankOne_eq_one_iff_exists_trivialization_baseSet_eq_univ`).

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, §1.1.
-/

public section

open Bundle CategoryTheory MonoidalCategory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

universe u v

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω)
  (B : Type u) [TopologicalSpace B] [ChartedSpace HB B]

/-- A point-indexed finite-rank vector-bundle core over `B` whose transition functions are `C^n`
with respect to `I`. Over `𝓘(ℂ, EB)` at regularity `∞`, these are holomorphic vector-bundle
cores. -/
structure ContMDiffFiniteRankBundleCore where
  /-- The underlying topological finite-rank point-indexed core. -/
  toCore : FiniteRankBundleCore 𝕜 B
  /-- `C^n` regularity of all chart transition functions. -/
  isContMDiff : toCore.core.IsContMDiff I n := by infer_instance

namespace ContMDiffFiniteRankBundleCore

variable {I n B}

instance instIsContMDiff (A : ContMDiffFiniteRankBundleCore I n B) :
    A.toCore.core.IsContMDiff I n :=
  A.isContMDiff

@[ext] theorem ext {A D : ContMDiffFiniteRankBundleCore I n B}
    (h : A.toCore = D.toCore) : A = D := by
  cases A; cases D; cases h; rfl

/-- A `C^n` bundle morphism between `C^n` finite-rank cores: a coordinate bundle morphism whose
glued map of total spaces is `C^n`. -/
structure Hom (A D : ContMDiffFiniteRankBundleCore I n B) where
  /-- The underlying coordinate bundle morphism. -/
  toHom : A.toCore ⟶ D.toCore
  /-- `C^n` regularity of the glued map of total spaces. -/
  contMDiff_totalSpaceMap : ContMDiff
    (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜))
    (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜)) n toHom.totalSpaceMap

@[ext] theorem Hom.ext {A D : ContMDiffFiniteRankBundleCore I n B} {f g : Hom A D}
    (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; cases h; rfl

instance : Category (ContMDiffFiniteRankBundleCore I n B) where
  Hom := Hom
  id A := ⟨𝟙 A.toCore, CoordinateHom.contMDiff_totalSpaceMap_id A.toCore.core⟩
  comp f g := ⟨f.toHom ≫ g.toHom,
    CoordinateHom.contMDiff_totalSpaceMap_comp g.contMDiff_totalSpaceMap f.contMDiff_totalSpaceMap⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[ext] theorem hom_ext {A D : ContMDiffFiniteRankBundleCore I n B} {f g : A ⟶ D}
    (h : f.toHom = g.toHom) : f = g :=
  Hom.ext h

@[simp] theorem id_toHom (A : ContMDiffFiniteRankBundleCore I n B) :
    (𝟙 A : A ⟶ A).toHom = 𝟙 A.toCore := (rfl)

@[simp] theorem comp_toHom {A D C : ContMDiffFiniteRankBundleCore I n B} (f : A ⟶ D) (g : D ⟶ C) :
    (f ≫ g).toHom = f.toHom ≫ g.toHom := (rfl)

variable (I n B) in
/-- The faithful functor forgetting `C^n` regularity of transitions and morphisms. -/
abbrev forgetToCore : ContMDiffFiniteRankBundleCore I n B ⥤ FiniteRankBundleCore 𝕜 B where
  obj A := A.toCore
  map f := f.toHom

@[simp] theorem forgetToCore_obj (A : ContMDiffFiniteRankBundleCore I n B) :
    (forgetToCore I n B).obj A = A.toCore := (rfl)

@[simp] theorem forgetToCore_map {A D : ContMDiffFiniteRankBundleCore I n B} (f : A ⟶ D) :
    (forgetToCore I n B).map f = f.toHom := (rfl)

instance : (forgetToCore I n B).Faithful where
  map_injective h := hom_ext h

/-- Lift an isomorphism of underlying finite-rank cores whose forward and inverse total-space maps
are `C^n` to an isomorphism in `ContMDiffFiniteRankBundleCore I n B`. -/
def isoMk {A D : ContMDiffFiniteRankBundleCore I n B} (e : A.toCore ≅ D.toCore)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜)) n e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n e.inv.totalSpaceMap) :
    A ≅ D where
  hom := ⟨e.hom, he_hom⟩
  inv := ⟨e.inv, he_inv⟩
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

@[simp] theorem isoMk_hom_toHom {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A.toCore ≅ D.toCore)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜)) n e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n e.inv.totalSpaceMap) :
    (isoMk e he_hom he_inv).hom.toHom = e.hom := (rfl)

@[simp] theorem isoMk_inv_toHom {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A.toCore ≅ D.toCore)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜)) n e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n e.inv.totalSpaceMap) :
    (isoMk e he_hom he_inv).inv.toHom = e.inv := (rfl)

/-- Every categorical isomorphism in `ContMDiffFiniteRankBundleCore I n B` glues to a `C^n`
diffeomorphism of total spaces covering the identity of `B`. -/
def isoToDiffeomorph {A D : ContMDiffFiniteRankBundleCore I n B} (e : A ≅ D) :
    A.toCore.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.toCore.rank → 𝕜)⟯ D.toCore.core.TotalSpace :=
  FiniteRankBundleCore.isoToDiffeomorph ((forgetToCore I n B).mapIso e)
    e.hom.contMDiff_totalSpaceMap e.inv.contMDiff_totalSpaceMap

@[simp] theorem coe_isoToDiffeomorph {A D : ContMDiffFiniteRankBundleCore I n B} (e : A ≅ D) :
    ⇑(isoToDiffeomorph e) = e.hom.toHom.totalSpaceMap :=
  FiniteRankBundleCore.coe_isoToDiffeomorph _ _ _

@[simp] theorem coe_isoToDiffeomorph_symm {A D : ContMDiffFiniteRankBundleCore I n B} (e : A ≅ D) :
    ⇑(isoToDiffeomorph e).symm = e.inv.toHom.totalSpaceMap :=
  FiniteRankBundleCore.coe_isoToDiffeomorph_symm _ _ _

variable (I n B) in
/-- The trivial `C^n` finite-rank core of rank `r` over `B`. -/
-- Expose the underlying core so the dependent fibre model reduces to `Fin r → 𝕜`.
@[expose]
def trivial (r : ℕ) : ContMDiffFiniteRankBundleCore I n B :=
  ⟨FiniteRankBundleCore.trivial 𝕜 B r, inferInstance⟩

@[simp] theorem toCore_trivial (r : ℕ) :
    (trivial I n B r).toCore = FiniteRankBundleCore.trivial 𝕜 B r := (rfl)

/-- A fixed continuous linear equivalence intertwining two `C^n` cores with equal chart domains
induces an isomorphism in `ContMDiffFiniteRankBundleCore I n B`. -/
noncomputable def constIso {A D : ContMDiffFiniteRankBundleCore I n B}
    (hbase : ∀ i, A.toCore.core.baseSet i = D.toCore.core.baseSet i)
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin D.toCore.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜)).comp
          (A.toCore.core.coordChange i j x) =
        (D.toCore.core.coordChange i j x).comp
          (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜))) :
    A ≅ D :=
  let Φ := FiniteRankBundleCore.constIsoDiffeomorph (I := I) (n := n) hbase e he
  isoMk (FiniteRankBundleCore.constIso (fun i ↦ (hbase i).le) e he)
    (FiniteRankBundleCore.coe_constIsoDiffeomorph (I := I) (n := n) hbase e he ▸ Φ.contMDiff)
    (FiniteRankBundleCore.coe_constIsoDiffeomorph_symm (I := I) (n := n) hbase e he ▸
      Φ.symm.contMDiff)

@[simp] theorem constIso_hom_toHom {A D : ContMDiffFiniteRankBundleCore I n B}
    (hbase : ∀ i, A.toCore.core.baseSet i = D.toCore.core.baseSet i)
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin D.toCore.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜)).comp
          (A.toCore.core.coordChange i j x) =
        (D.toCore.core.coordChange i j x).comp
          (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜))) :
    (constIso hbase e he).hom.toHom =
      (FiniteRankBundleCore.constIso (fun i ↦ (hbase i).le) e he).hom := (rfl)

@[simp] theorem constIso_inv_toHom {A D : ContMDiffFiniteRankBundleCore I n B}
    (hbase : ∀ i, A.toCore.core.baseSet i = D.toCore.core.baseSet i)
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin D.toCore.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜)).comp
          (A.toCore.core.coordChange i j x) =
        (D.toCore.core.coordChange i j x).comp
          (e : (Fin A.toCore.rank → 𝕜) →L[𝕜] (Fin D.toCore.rank → 𝕜))) :
    (constIso hbase e he).inv.toHom =
      (FiniteRankBundleCore.constIso (fun i ↦ (hbase i).le) e he).inv := (rfl)

/-! ### Symmetric monoidal structure -/

instance : MonoidalCategoryStruct (ContMDiffFiniteRankBundleCore I n B) where
  tensorObj A D := ⟨A.toCore ⊗ D.toCore, inferInstance⟩
  whiskerLeft A _ _ g := ⟨A.toCore ◁ g.toHom,
    FiniteRankBundleCore.contMDiff_totalSpaceMap_whiskerLeft A.toCore g.toHom
      g.contMDiff_totalSpaceMap⟩
  whiskerRight f D := ⟨f.toHom ▷ D.toCore,
    FiniteRankBundleCore.contMDiff_totalSpaceMap_whiskerRight f.toHom f.contMDiff_totalSpaceMap
      D.toCore⟩
  tensorHom f g := ⟨f.toHom ⊗ₘ g.toHom,
    FiniteRankBundleCore.contMDiff_totalSpaceMap_monoidalTensorHom f.toHom g.toHom
      f.contMDiff_totalSpaceMap g.contMDiff_totalSpaceMap⟩
  tensorUnit := trivial I n B 1
  associator A D C := isoMk (α_ A.toCore D.toCore C.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_associator_hom A.toCore D.toCore C.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_associator_inv A.toCore D.toCore C.toCore)
  leftUnitor A := isoMk (λ_ A.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_leftUnitor_hom A.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_leftUnitor_inv A.toCore)
  rightUnitor A := isoMk (ρ_ A.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_rightUnitor_hom A.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_rightUnitor_inv A.toCore)

@[simp] theorem tensorObj_toCore (A D : ContMDiffFiniteRankBundleCore I n B) :
    (A ⊗ D).toCore = A.toCore ⊗ D.toCore := (rfl)

@[simp] theorem tensorUnit_toCore :
    (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore = 𝟙_ (FiniteRankBundleCore 𝕜 B) := (rfl)

@[simp] theorem localTriv_baseSet_tensorObj (A D : ContMDiffFiniteRankBundleCore I n B) (i : B) :
    ((A ⊗ D).toCore.core.localTriv i).baseSet =
      A.toCore.core.baseSet i ∩ D.toCore.core.baseSet i :=
  FiniteRankBundleCore.localTriv_baseSet_tensorObj A.toCore D.toCore i

@[simp] theorem coordChange_tensorUnit (i j x : B) :
    (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.core.coordChange i j x =
      ContinuousLinearMap.id 𝕜
        (Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜) := (rfl)

@[simp] theorem whiskerLeft_toHom (A : ContMDiffFiniteRankBundleCore I n B)
    {D C : ContMDiffFiniteRankBundleCore I n B} (g : D ⟶ C) :
    (A ◁ g).toHom = A.toCore ◁ g.toHom := (rfl)

@[simp] theorem whiskerRight_toHom {A D : ContMDiffFiniteRankBundleCore I n B} (f : A ⟶ D)
    (C : ContMDiffFiniteRankBundleCore I n B) :
    (f ▷ C).toHom = f.toHom ▷ C.toCore := (rfl)

@[simp] theorem tensorHom_toHom {A₁ D₁ A₂ D₂ : ContMDiffFiniteRankBundleCore I n B}
    (f : A₁ ⟶ D₁) (g : A₂ ⟶ D₂) :
    (f ⊗ₘ g).toHom = f.toHom ⊗ₘ g.toHom := (rfl)

@[simp] theorem associator_hom_toHom (A D C : ContMDiffFiniteRankBundleCore I n B) :
    (α_ A D C).hom.toHom = (α_ A.toCore D.toCore C.toCore).hom := (rfl)

@[simp] theorem associator_inv_toHom (A D C : ContMDiffFiniteRankBundleCore I n B) :
    (α_ A D C).inv.toHom = (α_ A.toCore D.toCore C.toCore).inv := (rfl)

@[simp] theorem leftUnitor_hom_toHom (A : ContMDiffFiniteRankBundleCore I n B) :
    (λ_ A).hom.toHom = (λ_ A.toCore).hom := (rfl)

@[simp] theorem leftUnitor_inv_toHom (A : ContMDiffFiniteRankBundleCore I n B) :
    (λ_ A).inv.toHom = (λ_ A.toCore).inv := (rfl)

@[simp] theorem rightUnitor_hom_toHom (A : ContMDiffFiniteRankBundleCore I n B) :
    (ρ_ A).hom.toHom = (ρ_ A.toCore).hom := (rfl)

@[simp] theorem rightUnitor_inv_toHom (A : ContMDiffFiniteRankBundleCore I n B) :
    (ρ_ A).inv.toHom = (ρ_ A.toCore).inv := (rfl)

instance : MonoidalCategory (ContMDiffFiniteRankBundleCore I n B) :=
  Monoidal.induced (forgetToCore I n B)
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _
      whiskerLeft_eq := fun A {_ _} f ↦ by
        have h : A.toCore ◁ f.toHom =
            (Iso.refl _).inv ≫ (A.toCore ◁ f.toHom) ≫ (Iso.refl _).hom := by simp
        exact h
      whiskerRight_eq := fun {_ _} f D ↦ by
        have h : f.toHom ▷ D.toCore =
            (Iso.refl _).inv ≫ (f.toHom ▷ D.toCore) ≫ (Iso.refl _).hom := by simp
        exact h
      tensorHom_eq := fun {_ _ _ _} f g ↦ by
        have h : f.toHom ⊗ₘ g.toHom =
            (Iso.refl _).inv ≫ (f.toHom ⊗ₘ g.toHom) ≫ (Iso.refl _).hom := by simp
        exact h
      associator_eq := fun A D C ↦ by
        have h : (α_ A.toCore D.toCore C.toCore).hom =
            (((Iso.refl _).symm ≪≫ ((Iso.refl _).symm ⊗ᵢ Iso.refl _)) ≪≫
              α_ A.toCore D.toCore C.toCore ≪≫
              ((Iso.refl _ ⊗ᵢ Iso.refl _) ≪≫ Iso.refl _)).hom := by simp
        exact h
      leftUnitor_eq := fun A ↦ by
        have h : (λ_ A.toCore).hom =
            (((Iso.refl _).symm ≪≫ ((Iso.refl _).symm ⊗ᵢ Iso.refl _)) ≪≫
              λ_ A.toCore).hom := by simp
        exact h
      rightUnitor_eq := fun A ↦ by
        have h : (ρ_ A.toCore).hom =
            (((Iso.refl _).symm ≪≫ (Iso.refl _ ⊗ᵢ (Iso.refl _).symm)) ≪≫
              ρ_ A.toCore).hom := by simp
        exact h }

instance : (forgetToCore I n B).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      left_unitality := fun A ↦ by
        have h : (λ_ A.toCore).hom =
            ((Iso.refl (𝟙_ (FiniteRankBundleCore 𝕜 B))).hom ▷ A.toCore) ≫
              (Iso.refl (𝟙_ (FiniteRankBundleCore 𝕜 B) ⊗ A.toCore)).hom ≫
              (λ_ A.toCore).hom := by simp
        exact h
      right_unitality := fun A ↦ by
        have h : (ρ_ A.toCore).hom =
            (A.toCore ◁ (Iso.refl (𝟙_ (FiniteRankBundleCore 𝕜 B))).hom) ≫
              (Iso.refl (A.toCore ⊗ 𝟙_ (FiniteRankBundleCore 𝕜 B))).hom ≫
              (ρ_ A.toCore).hom := by simp
        exact h }

@[simp] theorem forgetToCore_ε :
    Functor.LaxMonoidal.ε (forgetToCore I n B) = 𝟙 (𝟙_ (FiniteRankBundleCore 𝕜 B)) := (rfl)

@[simp] theorem forgetToCore_μ (A D : ContMDiffFiniteRankBundleCore I n B) :
    Functor.LaxMonoidal.μ (forgetToCore I n B) A D = 𝟙 (A.toCore ⊗ D.toCore) := (rfl)

instance : BraidedCategory (ContMDiffFiniteRankBundleCore I n B) :=
  BraidedCategory.ofFaithful (forgetToCore I n B)
    (fun A D ↦ isoMk (β_ A.toCore D.toCore)
      (FiniteRankBundleCore.contMDiff_totalSpaceMap_braiding_hom A.toCore D.toCore)
      (FiniteRankBundleCore.contMDiff_totalSpaceMap_braiding_inv A.toCore D.toCore))
    (fun _ _ ↦ FiniteRankBundleCore.hom_ext fun _ ↦ by simp)

@[simp] theorem braiding_hom_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    (β_ A D).hom.toHom = (β_ A.toCore D.toCore).hom := (rfl)

@[simp] theorem braiding_inv_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    (β_ A D).inv.toHom = (β_ A.toCore D.toCore).inv := (rfl)

instance : (forgetToCore I n B).Braided where
  braided _ _ := FiniteRankBundleCore.hom_ext fun _ ↦ by simp

noncomputable instance : SymmetricCategory (ContMDiffFiniteRankBundleCore I n B) :=
  SymmetricCategory.ofFaithful (forgetToCore I n B)

/-- A `C^n` core whose transition maps on chart overlaps are all the identity, equipped with a
continuous linear equivalence of its model fibre with `Fin r → 𝕜`, is isomorphic in
`ContMDiffFiniteRankBundleCore I n B` to the trivial core of rank `r`. -/
def isoTrivialOfCoordChangeEqId (A : ContMDiffFiniteRankBundleCore I n B) {r : ℕ}
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
    (h : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      A.toCore.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.toCore.rank → 𝕜)) :
    A ≅ trivial I n B r :=
  isoMk (FiniteRankBundleCore.isoTrivialOfCoordChangeEqId A.toCore e h)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom A.toCore e h)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_inv A.toCore e h)

@[simp] theorem isoTrivialOfCoordChangeEqId_hom_toHom
    (A : ContMDiffFiniteRankBundleCore I n B) {r : ℕ}
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
    (h : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      A.toCore.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.toCore.rank → 𝕜)) :
    (isoTrivialOfCoordChangeEqId A e h).hom.toHom =
      (FiniteRankBundleCore.isoTrivialOfCoordChangeEqId A.toCore e h).hom := (rfl)

@[simp] theorem isoTrivialOfCoordChangeEqId_inv_toHom
    (A : ContMDiffFiniteRankBundleCore I n B) {r : ℕ}
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
    (h : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      A.toCore.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.toCore.rank → 𝕜)) :
    (isoTrivialOfCoordChangeEqId A e h).inv.toHom =
      (FiniteRankBundleCore.isoTrivialOfCoordChangeEqId A.toCore e h).inv := (rfl)

/-- The underlying topological core of `tensorPow A m` is `tensorPow A.toCore m`. -/
@[simp] theorem toCore_tensorPow (A : ContMDiffFiniteRankBundleCore I n B) :
    ∀ m : ℕ, (tensorPow A m).toCore = tensorPow A.toCore m
  | 0 => rfl
  | m + 1 => by rw [tensorPow_succ, tensorPow_succ, tensorObj_toCore, toCore_tensorPow A m]

/-- Isomorphic `C^n` cores over a nonempty base have the same rank. -/
theorem rank_eq_of_iso [Nonempty B] {A D : ContMDiffFiniteRankBundleCore I n B} (e : A ≅ D) :
    A.toCore.rank = D.toCore.rank :=
  FiniteRankBundleCore.rank_eq_of_iso ((forgetToCore I n B).mapIso e)

/-- Over a nonempty base, any left factor in a `C^n` tensor-product isomorphism with the monoidal
unit has rank one. -/
theorem rank_eq_one_of_tensor_iso_tensorUnit [Nonempty B]
    {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) : A.toCore.rank = 1 :=
  FiniteRankBundleCore.rank_eq_one_of_tensor_iso_tensorUnit ((forgetToCore I n B).mapIso e)

end ContMDiffFiniteRankBundleCore

/-! ### The `C^n` and holomorphic Picard group -/

/-- The `C^n` Picard group of `B` with respect to `I`: the commutative group of isomorphism classes
of tensor-invertible `C^n` finite-rank vector-bundle cores over `B`. For `I = 𝓘(ℂ, EB)` and
`n = ∞`, this is the holomorphic Picard group of `B`. -/
abbrev ContMDiffPicardGroup : Type (max u v) :=
  (Skeleton (ContMDiffFiniteRankBundleCore I n B))ˣ

namespace ContMDiffPicardGroup

/-- The forgetful homomorphism from the `C^n` Picard group to the topological Picard group of
continuous finite-rank cores. -/
noncomputable def forgetToCoreHom :
    ContMDiffPicardGroup I n B →* (Skeleton (FiniteRankBundleCore 𝕜 B))ˣ :=
  Units.map (Skeleton.monoidHom (ContMDiffFiniteRankBundleCore.forgetToCore I n B))

@[simp] theorem val_forgetToCoreHom_apply (L : ContMDiffPicardGroup I n B) :
    (forgetToCoreHom I n B L : Skeleton (FiniteRankBundleCore 𝕜 B)) =
      (ContMDiffFiniteRankBundleCore.forgetToCore I n B).mapSkeleton.obj
        (L : Skeleton (ContMDiffFiniteRankBundleCore I n B)) := (rfl)

variable {I n B}

/-- Construct an element of `ContMDiffPicardGroup I n B` from a `C^n` core `A`, a tensor-inverse
`D`, and an isomorphism `A ⊗ D ≅ 𝟙_`. -/
noncomputable def mkOfTensorIsoUnit {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    ContMDiffPicardGroup I n B :=
  Units.mkOfMulEqOne (toSkeleton A) (toSkeleton D) <| by
    rw [← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨e⟩

@[simp]
theorem val_mkOfTensorIsoUnit {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    (mkOfTensorIsoUnit e : Skeleton (ContMDiffFiniteRankBundleCore I n B)) = toSkeleton A :=
  (rfl)

@[simp]
theorem val_inv_mkOfTensorIsoUnit {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    (↑(mkOfTensorIsoUnit e)⁻¹ : Skeleton (ContMDiffFiniteRankBundleCore I n B)) = toSkeleton D :=
  (rfl)

@[simp] theorem forgetToCoreHom_mkOfTensorIsoUnit
    {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    forgetToCoreHom I n B (mkOfTensorIsoUnit e) =
      Units.mkOfMulEqOne (toSkeleton A.toCore) (toSkeleton D.toCore) (by
        rw [← Skeleton.toSkeleton_tensorObj]
        exact Quotient.sound ⟨(ContMDiffFiniteRankBundleCore.forgetToCore I n B).mapIso e⟩) :=
  Units.ext <| by
    rw [val_forgetToCoreHom_apply, val_mkOfTensorIsoUnit, Units.val_mkOfMulEqOne]
    exact (ContMDiffFiniteRankBundleCore.forgetToCore I n B).mapSkeleton_obj_toSkeleton A

/-- Two tensor-invertible `C^n` cores define the same class in `ContMDiffPicardGroup I n B` if and
only if they are isomorphic in `ContMDiffFiniteRankBundleCore I n B`. -/
theorem mkOfTensorIsoUnit_eq_mkOfTensorIsoUnit_iff
    {A D A' D' : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B))
    (e' : A' ⊗ D' ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    mkOfTensorIsoUnit e = mkOfTensorIsoUnit e' ↔ Nonempty (A ≅ A') := by
  rw [Units.ext_iff, val_mkOfTensorIsoUnit, val_mkOfTensorIsoUnit]
  exact Quotient.eq

/-- A tensor-invertible `C^n` core represents `1` in `ContMDiffPicardGroup I n B` if and only if it
is isomorphic to the monoidal unit `𝟙_`. -/
theorem mkOfTensorIsoUnit_eq_one_iff {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    mkOfTensorIsoUnit e = 1 ↔ Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
  rw [Units.ext_iff, val_mkOfTensorIsoUnit, Units.val_one, Skeleton.one_eq]
  exact Quotient.eq

/-- The `m`-th power of a class in `ContMDiffPicardGroup I n B` is trivial if and only if the `m`-th
tensor power of its representative core is isomorphic to `𝟙_`. -/
theorem pow_mkOfTensorIsoUnit_eq_one_iff {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) (m : ℕ) :
    mkOfTensorIsoUnit e ^ m = 1 ↔
      Nonempty (tensorPow A m ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, val_mkOfTensorIsoUnit,
    ← toSkeleton_tensorPow A m, Units.val_one, Skeleton.one_eq]
  exact Quotient.eq

/-- Over a nonempty base, any representative of a class in `ContMDiffPicardGroup I n B` has rank
one. -/
theorem rank_out_eq_one [Nonempty B] (L : ContMDiffPicardGroup I n B) :
    (L : Skeleton (ContMDiffFiniteRankBundleCore I n B)).out.toCore.rank = 1 := by
  have hmul : toSkeleton
      ((L : Skeleton (ContMDiffFiniteRankBundleCore I n B)).out ⊗
        (↑L⁻¹ : Skeleton (ContMDiffFiniteRankBundleCore I n B)).out) =
      toSkeleton (𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
    rw [← Skeleton.mul_eq, ← Skeleton.one_eq, Units.mul_inv]
  obtain ⟨e⟩ := Quotient.exact hmul
  exact ContMDiffFiniteRankBundleCore.rank_eq_one_of_tensor_iso_tensorUnit e

end ContMDiffPicardGroup

namespace ContMDiffFiniteRankBundleCore

variable {I n B}

/-- Every `C^n` section `σ` of `A` defines a `C^n` bundle morphism `𝟙_ ⟶ A` sending the unit basis
vector `1` over `x` to `σ x`. -/
noncomputable def homFromTensorUnitOfSection (A : ContMDiffFiniteRankBundleCore I n B)
    (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x))) :
    𝟙_ (ContMDiffFiniteRankBundleCore I n B) ⟶ A := by
  let i₀ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank := ⟨0, by simp⟩
  let L := ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)
    (Fin A.toCore.rank → 𝕜) (ContinuousLinearMap.proj i₀)
  have hchart (j : B) : ContMDiffOn I 𝓘(𝕜, Fin A.toCore.rank → 𝕜) n
      (fun x ↦ (A.toCore.core.localTriv j ⟨x, σ x⟩).2) (A.toCore.core.baseSet j) := by
    have : MemTrivializationAtlas (A.toCore.core.localTriv j) := ⟨⟨j, rfl⟩⟩
    exact ((A.toCore.core.localTriv j).contMDiffOn_section_iff
      (A.toCore.core.isOpen_baseSet j) subset_rfl).mp hσ.contMDiffOn
  let a : (𝟙_ (FiniteRankBundleCore 𝕜 B)) ⟶ A.toCore :=
    { operator := fun i j ↦
        ⟨fun x ↦ L (A.toCore.core.localTriv j ⟨x.val, σ x.val⟩).2,
          L.continuous.comp <|
            (continuousOn_iff_continuous_domRestrict.1
              (hchart j).continuousOn).comp
              (continuous_subtypeVal.subtype_mk fun x ↦ x.property.2)⟩
      compatible := fun i i' j j' x _ _ hj hj' c ↦ by
        simp only [L, ContinuousMap.coe_mk, ContinuousLinearMap.smulRightL_apply_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
          FiniteRankBundleCore.coordChange_tensorUnit, ContinuousLinearMap.id_apply,
          VectorBundleCore.localTriv_apply, _root_.map_smul]
        exact congrArg (c i₀ • ·) (A.toCore.core.coordChange_comp _ j j' x
          ⟨⟨A.toCore.core.mem_baseSet_at x, hj⟩, hj'⟩ (σ x)) }
  refine ⟨a, CoordinateHom.contMDiff_totalSpaceMap a fun i j ↦
    (L.contMDiff.comp_contMDiffOn ((hchart j).mono inter_subset_right)).congr fun x hx ↦
      (CoordinateHom.operator_eq a i j ⟨x, hx⟩).symm⟩

@[simp]
theorem fiberMap_homFromTensorUnitOfSection_apply (A : ContMDiffFiniteRankBundleCore I n B)
    (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (x : B) (c : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜) :
    (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x c =
      c ⟨0, by simp⟩ • (σ x : Fin A.toCore.rank → 𝕜) := by
  let v : Fin A.toCore.rank → 𝕜 := σ x
  rw [CoordinateHom.fiberMap_def]
  simp only [homFromTensorUnitOfSection,
    ContinuousLinearMap.smulRightL_apply_apply, VectorBundleCore.localTriv_apply]
  exact congrArg (c ⟨0, by simp⟩ • ·)
    (A.toCore.core.coordChange_self _ x (A.toCore.core.mem_baseSet_at x) v)

/-- For a rank-one `C^n` core `A` and a nowhere-vanishing `C^n` section `σ`, the `C^n` bundle
morphism `A ⟶ 𝟙_` dividing fibrewise by `σ`, sending `σ x` to the unit basis vector `1` over
every `x` (without assuming completeness of `𝕜`). -/
noncomputable def homToTensorUnitOfSectionNeZero (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    A ⟶ 𝟙_ (ContMDiffFiniteRankBundleCore I n B) := by
  let k₀ : Fin A.toCore.rank := ⟨0, by simp [hA]⟩
  let : Unique (Fin A.toCore.rank) := ⟨⟨k₀⟩, fun k ↦ Fin.ext (by omega)⟩
  let E₀ : (Fin A.toCore.rank → 𝕜) →L[𝕜]
      (Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.proj k₀) (fun _ ↦ 1)
  let L' : 𝕜 →L[𝕜]
      ((Fin A.toCore.rank → 𝕜) →L[𝕜]
        (Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜)) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) E₀
  let s (i : B) (x : B) : 𝕜 := (A.toCore.core.localTriv i ⟨x, σ x⟩).2 k₀
  have hs (i : B) : ContMDiffOn I 𝓘(𝕜) n (s i) (A.toCore.core.baseSet i) := by
    have : MemTrivializationAtlas (A.toCore.core.localTriv i) := ⟨⟨i, rfl⟩⟩
    exact (ContinuousLinearMap.proj k₀).contMDiff.comp_contMDiffOn <|
      ((A.toCore.core.localTriv i).contMDiffOn_section_iff
        (A.toCore.core.isOpen_baseSet i) subset_rfl).mp hσ.contMDiffOn
  have hs₀ (i : B) {x : B} (hx : x ∈ A.toCore.core.baseSet i) : s i x ≠ 0 :=
    fun h0 ↦ hσ₀ x <|
      ((A.toCore.core.localTriv i).linearEquivAt 𝕜 x hx).map_eq_zero_iff.mp <|
        funext fun k ↦ (Unique.eq_default k).symm ▸ h0
  have hsinv (i : B) :
      ContMDiffOn I 𝓘(𝕜) n (fun x ↦ (s i x)⁻¹) (A.toCore.core.baseSet i) :=
    fun x hx ↦ (contDiffAt_inv 𝕜 (hs₀ i hx)).contMDiffAt.comp_contMDiffWithinAt x (hs i x hx)
  let b : A.toCore ⟶ (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore :=
    { operator := fun i _ ↦
        ⟨fun x ↦ L' (s i x.val)⁻¹,
          L'.continuous.comp <|
            (continuousOn_iff_continuous_domRestrict.1 (hsinv i).continuousOn).comp
              (continuous_subtypeVal.subtype_mk fun x ↦ x.property.1)⟩
      compatible := fun i i' _ _ x hi hi' _ _ v ↦ by
        set c := A.toCore.core.coordChange i i' x (fun _ ↦ 1) k₀
        have hT : A.toCore.core.coordChange i i' x =
            c • ContinuousLinearMap.id 𝕜 (Fin A.toCore.rank → 𝕜) :=
          (A.toCore.core.coordChange i i' x).eq_smul_id_of_unique
        have hs_eq : s i' x = c * s i x := by
          have hcomp := congrFun (A.toCore.core.coordChange_comp (A.toCore.core.indexAt x)
            i i' x ⟨⟨A.toCore.core.mem_baseSet_at x, hi⟩, hi'⟩ (σ x)) k₀
          rw [hT] at hcomp
          simpa only [s, VectorBundleCore.localTriv_apply, smul_apply,
            ContinuousLinearMap.id_apply, Pi.smul_apply, smul_eq_mul] using hcomp.symm
        have hc : c ≠ 0 := fun hc0 ↦ hs₀ i' hi' (by rw [hs_eq, hc0, zero_mul])
        ext l
        simp only [L', E₀, ContinuousMap.coe_mk, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.proj_apply,
          coordChange_tensorUnit, hT, smul_apply, Pi.smul_apply, smul_eq_mul, mul_one,
          hs_eq, mul_inv_rev]
        rw [mul_assoc, inv_mul_cancel_left₀ hc] }
  exact ⟨b, CoordinateHom.contMDiff_totalSpaceMap b fun i j ↦
    (L'.contMDiff.comp_contMDiffOn ((hsinv i).mono inter_subset_left)).congr fun x hx ↦
      (CoordinateHom.operator_eq b i j ⟨x, hx⟩).symm⟩

@[simp]
theorem fiberMap_homToTensorUnitOfSectionNeZero_apply (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) (x : B) (v : Fin A.toCore.rank → 𝕜) :
    (A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀).toHom.fiberMap x v =
      fun _ ↦ ((σ x : Fin A.toCore.rank → 𝕜) ⟨0, by simp [hA]⟩)⁻¹ * v ⟨0, by simp [hA]⟩ := by
  let vσ : Fin A.toCore.rank → 𝕜 := σ x
  have hself : (A.toCore.core.localTriv (A.toCore.core.indexAt x) ⟨x, σ x⟩).2
      ⟨0, by simp [hA]⟩ = (σ x : Fin A.toCore.rank → 𝕜) ⟨0, by simp [hA]⟩ := by
    simpa only [VectorBundleCore.localTriv_apply] using
      congrFun (A.toCore.core.coordChange_self _ x (A.toCore.core.mem_baseSet_at x) vσ)
        ⟨0, by simp [hA]⟩
  ext l
  rw [CoordinateHom.fiberMap_def]
  simp only [homToTensorUnitOfSectionNeZero, ContinuousMap.coe_mk,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.proj_apply, smul_apply, hself, Pi.smul_apply, smul_eq_mul, mul_one]

@[simp]
theorem homToTensorUnitOfSectionNeZero_comp_homFromTensorUnitOfSection
    (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1)
    (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀ ≫ A.homFromTensorUnitOfSection σ hσ = 𝟙 A := by
  refine hom_ext <| FiniteRankBundleCore.hom_ext fun x ↦ ?_
  let k₀ : Fin A.toCore.rank := ⟨0, by simp [hA]⟩
  let vσ : Fin A.toCore.rank → 𝕜 := σ x
  have hσk₀ : vσ k₀ ≠ 0 := fun h0 ↦
    hσ₀ x (funext fun k ↦ (Fin.ext (by omega) : k = k₀) ▸ h0)
  have hf (c : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜) :
      (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x c = c ⟨0, by simp⟩ • vσ :=
    A.fiberMap_homFromTensorUnitOfSection_apply σ hσ x c
  have hb (v : Fin A.toCore.rank → 𝕜) :
      (A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀).toHom.fiberMap x v =
        fun _ ↦ (vσ k₀)⁻¹ * v k₀ :=
    A.fiberMap_homToTensorUnitOfSectionNeZero_apply hA σ hσ hσ₀ x v
  ext v k
  obtain rfl : k = k₀ := Fin.ext (by omega)
  simp only [comp_toHom, id_toHom, FiniteRankBundleCore.fiberMap_comp,
    FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, hf, hb, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm _ (v k₀), inv_mul_cancel_right₀ hσk₀]

@[simp]
theorem homFromTensorUnitOfSection_comp_homToTensorUnitOfSectionNeZero
    (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1)
    (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    A.homFromTensorUnitOfSection σ hσ ≫ A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀ =
      𝟙 (𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
  refine hom_ext <| FiniteRankBundleCore.hom_ext fun x ↦ ?_
  let k₀ : Fin A.toCore.rank := ⟨0, by simp [hA]⟩
  let vσ : Fin A.toCore.rank → 𝕜 := σ x
  have hσk₀ : vσ k₀ ≠ 0 := fun h0 ↦
    hσ₀ x (funext fun k ↦ (Fin.ext (by omega) : k = k₀) ▸ h0)
  have hf (c : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜) :
      (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x c = c ⟨0, by simp⟩ • vσ :=
    A.fiberMap_homFromTensorUnitOfSection_apply σ hσ x c
  have hb (v : Fin A.toCore.rank → 𝕜) :
      (A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀).toHom.fiberMap x v =
        fun _ ↦ (vσ k₀)⁻¹ * v k₀ :=
    A.fiberMap_homToTensorUnitOfSectionNeZero_apply hA σ hσ hσ₀ x v
  ext c l
  obtain rfl : l = ⟨0, by simp⟩ := Fin.ext (Nat.lt_one_iff.mp l.isLt)
  simp only [comp_toHom, id_toHom, FiniteRankBundleCore.fiberMap_comp,
    FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, hf, hb, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm (c ⟨0, by simp⟩), inv_mul_cancel_left₀ hσk₀]

/-- A nowhere-vanishing `C^n` section `σ` of a rank-one `C^n` core `A` induces an isomorphism
`A ≅ 𝟙_` in `ContMDiffFiniteRankBundleCore I n B` (without completeness of `𝕜`), whose inverse is
`A.homFromTensorUnitOfSection σ hσ`. -/
noncomputable def isoTensorUnitOfSectionNeZero (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B) where
  hom := A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀
  inv := A.homFromTensorUnitOfSection σ hσ
  hom_inv_id := A.homToTensorUnitOfSectionNeZero_comp_homFromTensorUnitOfSection hA σ hσ hσ₀
  inv_hom_id := A.homFromTensorUnitOfSection_comp_homToTensorUnitOfSectionNeZero hA σ hσ hσ₀

@[simp]
theorem isoTensorUnitOfSectionNeZero_hom (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    (A.isoTensorUnitOfSectionNeZero hA σ hσ hσ₀).hom =
      A.homToTensorUnitOfSectionNeZero hA σ hσ hσ₀ := (rfl)

@[simp]
theorem isoTensorUnitOfSectionNeZero_inv (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (hσ₀ : ∀ x, σ x ≠ 0) :
    (A.isoTensorUnitOfSectionNeZero hA σ hσ hσ₀).inv =
      A.homFromTensorUnitOfSection σ hσ := (rfl)

/-- For a rank-one `C^n` core `A`, `A.homFromTensorUnitOfSection σ hσ : 𝟙_ ⟶ A` is an isomorphism
in `ContMDiffFiniteRankBundleCore I n B` if and only if `σ` is nowhere-vanishing (without
completeness of `𝕜`). -/
theorem isIso_homFromTensorUnitOfSection_iff (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x))) :
    IsIso (A.homFromTensorUnitOfSection σ hσ) ↔ ∀ x, σ x ≠ 0 := by
  refine ⟨fun h x h0 ↦ ?_, fun hσ₀ ↦ (A.isoTensorUnitOfSectionNeZero hA σ hσ hσ₀).isIso_inv⟩
  let vσ : Fin A.toCore.rank → 𝕜 := σ x
  have hv₀ : vσ = 0 := h0
  have hzero : (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x (fun _ ↦ 1) = 0 := by
    have hf : (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x (fun _ ↦ 1) = (1 : 𝕜) • vσ :=
      A.fiberMap_homFromTensorUnitOfSection_apply σ hσ x (fun _ ↦ 1)
    rw [hf, hv₀, smul_zero]
  have h1 := congrArg (fun f : 𝟙_ (ContMDiffFiniteRankBundleCore I n B) ⟶
      𝟙_ (ContMDiffFiniteRankBundleCore I n B) ↦ f.toHom.fiberMap x (fun _ ↦ 1) ⟨0, by simp⟩)
    (IsIso.hom_inv_id (A.homFromTensorUnitOfSection σ hσ))
  simp only [comp_toHom, id_toHom, FiniteRankBundleCore.fiberMap_comp,
    FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, hzero, map_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- A rank-one `C^n` core is isomorphic to `𝟙_` in `ContMDiffFiniteRankBundleCore I n B` if and
only if it admits a nowhere-vanishing `C^n` section. -/
theorem nonempty_iso_tensorUnit_iff_exists_section_ne_zero
    (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) ↔
      ∃ σ : Π x, A.toCore.core.Fiber x,
        ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
          (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)) ∧
        ∀ x, σ x ≠ 0 := by
  constructor
  · rintro ⟨e⟩
    let i₀ : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank := ⟨0, by simp⟩
    let v₀ : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜 := fun _ ↦ 1
    have hv₀ : v₀ ≠ 0 := fun h ↦ one_ne_zero (congrFun h i₀)
    let s₀ : B → (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.core.TotalSpace :=
      fun x ↦ ⟨x, v₀⟩
    have hs₀ : ContMDiff I
        (I.prod 𝓘(𝕜, Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜)) n s₀ :=
      fun _ ↦ Bundle.contMDiffAt_totalSpace_iff.mpr ⟨contMDiffAt_id, by
        rw [FiniteRankBundleCore.trivializationAt_core]
        simp only [s₀, VectorBundleCore.localTriv_apply, coordChange_tensorUnit,
          ContinuousLinearMap.id_apply]
        exact contMDiffAt_const⟩
    refine ⟨fun x ↦ e.inv.toHom.fiberMap x v₀,
      (e.inv.contMDiff_totalSpaceMap.comp hs₀).congr fun x ↦
        (e.inv.toHom.totalSpaceMap_mk x v₀).symm,
      fun x h0 ↦ hv₀ ?_⟩
    let z : Fin A.toCore.rank → 𝕜 := 0
    have h0' : e.inv.toHom.fiberMap x v₀ = z := h0
    have h1 := congrArg (fun f : 𝟙_ (ContMDiffFiniteRankBundleCore I n B) ⟶
        𝟙_ (ContMDiffFiniteRankBundleCore I n B) ↦ f.toHom.fiberMap x v₀) e.inv_hom_id
    simp only [comp_toHom, id_toHom, FiniteRankBundleCore.fiberMap_comp,
      FiniteRankBundleCore.fiberMap_id, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, h0'] at h1
    exact h1 ▸ (e.hom.toHom.fiberMap x).map_zero
  · rintro ⟨σ, hσ, hσ₀⟩
    exact ⟨A.isoTensorUnitOfSectionNeZero hA σ hσ hσ₀⟩

end ContMDiffFiniteRankBundleCore

end General

/-! ### Duals, rank-one invertibility, and global triviality over a complete scalar field -/

section Complete

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {B : Type u} [TopologicalSpace B] [ChartedSpace HB B]

namespace ContMDiffFiniteRankBundleCore

/-- Over a complete scalar field, a `C^n` morphism between `C^n` finite-rank cores is an
isomorphism if and only if it is bijective on every fibre. -/
theorem isIso_iff_bijective {A D : ContMDiffFiniteRankBundleCore I n B} (f : A ⟶ D) :
    IsIso f ↔ ∀ x, Function.Bijective (f.toHom.fiberMap x) := by
  constructor
  · intro hf
    exact (FiniteRankBundleCore.isIso_iff_bijective f.toHom).1
      ((forgetToCore I n B).map_isIso f)
  · intro hbij
    have : IsIso f.toHom := (FiniteRankBundleCore.isIso_iff_bijective f.toHom).2 hbij
    let ha := FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap
      f.toHom f.contMDiff_totalSpaceMap
    let Φ := f.toHom.toDiffeomorph ha hbij
    have hinv_eq : (inv f.toHom).totalSpaceMap = ⇑Φ.symm := funext fun p ↦ EquivLike.injective Φ <|
      by
        rw [Φ.apply_symm_apply, CoordinateHom.coe_toDiffeomorph,
          ← Function.comp_apply (f := f.toHom.totalSpaceMap), ← CoordinateHom.totalSpaceMap_comp]
        exact (congrFun (congrArg CoordinateHom.totalSpaceMap (IsIso.inv_hom_id f.toHom)) p).trans
          (congrFun (CoordinateHom.totalSpaceMap_id D.toCore.core) p)
    refine ⟨⟨⟨inv f.toHom, hinv_eq ▸ Φ.symm.contMDiff⟩,
      hom_ext (IsIso.hom_inv_id f.toHom), hom_ext (IsIso.inv_hom_id f.toHom)⟩⟩

/-- The `C^n` dual of a `C^n` finite-rank core. -/
-- Expose the underlying core so the dependent fibre model reduces to `A.toCore.dual`.
@[expose]
noncomputable def dual (A : ContMDiffFiniteRankBundleCore I n B) :
    ContMDiffFiniteRankBundleCore I n B :=
  ⟨A.toCore.dual, inferInstance⟩

@[simp] theorem toCore_dual (A : ContMDiffFiniteRankBundleCore I n B) :
    A.dual.toCore = A.toCore.dual := (rfl)

/-- For a rank-one `C^n` core `A`, `A.dual ⊗ A` is canonically isomorphic in
`ContMDiffFiniteRankBundleCore I n B` to the monoidal unit. -/
noncomputable def dualTensorIsoUnit (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    A.dual ⊗ A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B) :=
  isoTrivialOfCoordChangeEqId (A.dual ⊗ A)
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin 1 ↦ 𝕜) (finCongr (by simp [hA])))
    fun _ _ _ hi hj ↦ A.toCore.coordChange_dual_tensor_eq_id hA hi hj

@[simp] theorem dualTensorIsoUnit_hom_toHom (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    (A.dualTensorIsoUnit hA).hom.toHom = (A.toCore.dualTensorIsoUnit hA).hom :=
  FiniteRankBundleCore.hom_ext fun x ↦
    (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ _ x).trans
      (FiniteRankBundleCore.fiberMap_dualTensorIsoUnit_hom A.toCore hA x).symm

@[simp] theorem dualTensorIsoUnit_inv_toHom (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    (A.dualTensorIsoUnit hA).inv.toHom = (A.toCore.dualTensorIsoUnit hA).inv :=
  FiniteRankBundleCore.hom_ext fun x ↦
    (FiniteRankBundleCore.fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ _ x).trans
      (FiniteRankBundleCore.fiberMap_dualTensorIsoUnit_inv A.toCore hA x).symm

/-- A rank-one `C^n` core is isomorphic to `𝟙_` in `ContMDiffFiniteRankBundleCore I n B` if and
only if its total space admits a global linear trivialization in the maximal `C^n` atlas. -/
theorem nonempty_iso_tensorUnit_iff_exists_trivialization_baseSet_eq_univ
    (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) ↔
      ∃ (e : Trivialization (Fin A.toCore.rank → 𝕜)
          (π (Fin A.toCore.rank → 𝕜) A.toCore.core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B (Fin A.toCore.rank → 𝕜) I n).maximalAtlas
            A.toCore.core.TotalSpace ∧
        e.baseSet = univ := by
  have hfin : Module.finrank 𝕜 (Fin A.toCore.rank → 𝕜) = 1 := by
    rw [Module.finrank_fin_fun, hA]
  rw [A.nonempty_iso_tensorUnit_iff_exists_section_ne_zero hA,
    ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero hfin]

end ContMDiffFiniteRankBundleCore

namespace ContMDiffPicardGroup

/-- The Picard-group class of a rank-one `C^n` core `A`, with inverse `A.dual`. -/
noncomputable def ofRankOne (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) : ContMDiffPicardGroup I n B :=
  mkOfTensorIsoUnit ((β_ A A.dual) ≪≫ A.dualTensorIsoUnit hA)

@[simp] theorem val_ofRankOne (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    (ofRankOne A hA : Skeleton (ContMDiffFiniteRankBundleCore I n B)) = toSkeleton A := (rfl)

@[simp] theorem forgetToCoreHom_ofRankOne (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    forgetToCoreHom I n B (ofRankOne A hA) =
      Units.mkOfMulEqOne (toSkeleton A.toCore) (toSkeleton A.toCore.dual) (by
        rw [← Skeleton.toSkeleton_tensorObj]
        exact Quotient.sound ⟨(β_ A.toCore A.toCore.dual) ≪≫ A.toCore.dualTensorIsoUnit hA⟩) :=
  Units.ext <| by
    rw [val_forgetToCoreHom_apply, val_ofRankOne, Units.val_mkOfMulEqOne]
    exact (ContMDiffFiniteRankBundleCore.forgetToCore I n B).mapSkeleton_obj_toSkeleton A

@[simp] theorem ofRankOne_tensorUnit
    (h : (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank = 1) :
    ofRankOne (𝟙_ (ContMDiffFiniteRankBundleCore I n B)) h = 1 :=
  Units.ext <| by rw [val_ofRankOne, Units.val_one, Skeleton.one_eq]

@[simp] theorem ofRankOne_tensor (A D : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (hD : D.toCore.rank = 1) :
    ofRankOne (A ⊗ D) (by simp [hA, hD]) = ofRankOne A hA * ofRankOne D hD :=
  Units.ext <| by
    rw [val_ofRankOne, Units.val_mul, val_ofRankOne, val_ofRankOne]
    exact Skeleton.toSkeleton_tensorObj A D

@[simp] theorem ofRankOne_dual (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    ofRankOne A.dual (by simp [hA]) = (ofRankOne A hA)⁻¹ :=
  Units.ext <| by rw [val_ofRankOne, ofRankOne, val_inv_mkOfTensorIsoUnit]

@[simp] theorem ofRankOne_tensorPow (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (m : ℕ) :
    ofRankOne (tensorPow A m) (by simp [hA]) = ofRankOne A hA ^ m :=
  Units.ext <| by
    rw [val_ofRankOne, Units.val_pow_eq_pow_val, val_ofRankOne]
    exact toSkeleton_tensorPow A m

/-- Two rank-one `C^n` cores define the same class in `ContMDiffPicardGroup I n B` if and only if
they are isomorphic in `ContMDiffFiniteRankBundleCore I n B`. -/
theorem ofRankOne_eq_ofRankOne_iff (A D : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (hD : D.toCore.rank = 1) :
    ofRankOne A hA = ofRankOne D hD ↔ Nonempty (A ≅ D) :=
  mkOfTensorIsoUnit_eq_mkOfTensorIsoUnit_iff _ _

/-- A rank-one `C^n` core represents `1` in `ContMDiffPicardGroup I n B` if and only if it is
isomorphic to the monoidal unit `𝟙_`. -/
theorem ofRankOne_eq_one_iff (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    ofRankOne A hA = 1 ↔ Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :=
  mkOfTensorIsoUnit_eq_one_iff _

/-- A rank-one `C^n` core represents `1` in `ContMDiffPicardGroup I n B` if and only if it admits a
nowhere-vanishing `C^n` section. -/
theorem ofRankOne_eq_one_iff_exists_section_ne_zero (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    ofRankOne A hA = 1 ↔
      ∃ σ : Π x, A.toCore.core.Fiber x,
        ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
          (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)) ∧
        ∀ x, σ x ≠ 0 :=
  (ofRankOne_eq_one_iff A hA).trans (A.nonempty_iso_tensorUnit_iff_exists_section_ne_zero hA)

/-- A rank-one `C^n` core represents `1` in `ContMDiffPicardGroup I n B` if and only if its total
space admits a global linear trivialization in the maximal `C^n` atlas. -/
theorem ofRankOne_eq_one_iff_exists_trivialization_baseSet_eq_univ
    (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    ofRankOne A hA = 1 ↔
      ∃ (e : Trivialization (Fin A.toCore.rank → 𝕜)
          (π (Fin A.toCore.rank → 𝕜) A.toCore.core.Fiber)) (_ : e.IsLinear 𝕜),
        e.toOpenPartialHomeomorph ∈
          (contMDiffFiberwiseLinear B (Fin A.toCore.rank → 𝕜) I n).maximalAtlas
            A.toCore.core.TotalSpace ∧
        e.baseSet = univ :=
  (ofRankOne_eq_one_iff A hA).trans
    (A.nonempty_iso_tensorUnit_iff_exists_trivialization_baseSet_eq_univ hA)

end ContMDiffPicardGroup

end Complete

end TauCeti
