/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# The symmetric monoidal category of `C^n` finite-rank cores and its Picard group

`ContMDiffFiniteRankBundleCore I n B` bundles a point-indexed finite-rank vector-bundle core
`A : FiniteRankBundleCore 𝕜 B` with `C^n` regularity of its transition functions for a model with
corners `I` on `B`. Its morphisms are coordinate bundle maps `A.toCore ⟶ D.toCore` whose glued
maps of total spaces are `C^n`. Over a complex manifold (`I = 𝓘(ℂ, EB)` and `n = ∞`), this is the
category of holomorphic finite-rank vector-bundle cores and holomorphic bundle morphisms.

Because `FiniteRankBundleCore.contMDiff_totalSpaceMap_monoidalTensorHom` and the monoidal coherence
regularity theorems of `TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Monoidal` require no
completeness of `𝕜`, the faithful forgetful functor `forgetToCore` equips
`ContMDiffFiniteRankBundleCore I n B` with a symmetric monoidal structure, together with
right-recursive tensor powers matching powers in `CategoryTheory.Skeleton`.

The commutative group `ContMDiffPicardGroup I n B` is the group of units
`(Skeleton (ContMDiffFiniteRankBundleCore I n B))ˣ` of isomorphism classes of tensor-invertible
`C^n` cores; for `I = 𝓘(ℂ, EB)` and `n = ∞`, this is the holomorphic Picard group of `B`. Over a
nonempty base every invertible `C^n` core has rank one. Conversely, over a complete scalar field:

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
@[expose]
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
  isoMk (FiniteRankBundleCore.constIso hbase e he)
    (FiniteRankBundleCore.coe_constIsoDiffeomorph (I := I) (n := n) hbase e he ▸ Φ.contMDiff)
    (FiniteRankBundleCore.coe_constIsoDiffeomorph_symm (I := I) (n := n) hbase e he ▸
      Φ.symm.contMDiff)

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
  tensorUnit := ⟨𝟙_ (FiniteRankBundleCore 𝕜 B), inferInstance⟩
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

instance : MonoidalCategory (ContMDiffFiniteRankBundleCore I n B) where
  tensorHom_def f g := hom_ext (MonoidalCategory.tensorHom_def f.toHom g.toHom)
  id_tensorHom_id A D := hom_ext (MonoidalCategory.id_tensorHom_id A.toCore D.toCore)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ :=
    hom_ext (MonoidalCategory.tensorHom_comp_tensorHom f₁.toHom f₂.toHom g₁.toHom g₂.toHom)
  whiskerLeft_id A D := hom_ext (MonoidalCategory.whiskerLeft_id A.toCore D.toCore)
  id_whiskerRight A D := hom_ext (MonoidalCategory.id_whiskerRight A.toCore D.toCore)
  associator_naturality f g h :=
    hom_ext (MonoidalCategory.associator_naturality f.toHom g.toHom h.toHom)
  leftUnitor_naturality f := hom_ext (MonoidalCategory.leftUnitor_naturality f.toHom)
  rightUnitor_naturality f := hom_ext (MonoidalCategory.rightUnitor_naturality f.toHom)
  pentagon A D C E := hom_ext (MonoidalCategory.pentagon A.toCore D.toCore C.toCore E.toCore)
  triangle A D := hom_ext (MonoidalCategory.triangle A.toCore D.toCore)

instance : (forgetToCore I n B).LaxMonoidal where
  ε := 𝟙 _
  μ _ _ := 𝟙 _
  μ_natural_left _ _ := by simp
  μ_natural_right _ _ := by simp
  associativity _ _ _ := by simp
  left_unitality _ := by simp
  right_unitality _ := by simp

instance : (forgetToCore I n B).OplaxMonoidal where
  η := 𝟙 _
  δ _ _ := 𝟙 _
  δ_natural_left _ _ := by simp
  δ_natural_right _ _ := by simp
  oplax_associativity _ _ _ := by simp
  oplax_left_unitality _ := by simp
  oplax_right_unitality _ := by simp

instance : (forgetToCore I n B).Monoidal where
  ε_η := Category.id_comp _
  η_ε := Category.id_comp _
  μ_δ _ _ := Category.id_comp _
  δ_μ _ _ := Category.id_comp _

instance : SymmetricCategory (ContMDiffFiniteRankBundleCore I n B) where
  braiding A D := isoMk (β_ A.toCore D.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_braiding_hom A.toCore D.toCore)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_braiding_inv A.toCore D.toCore)
  braiding_naturality_right A _ _ g :=
    hom_ext (BraidedCategory.braiding_naturality_right A.toCore g.toHom)
  braiding_naturality_left f D :=
    hom_ext (BraidedCategory.braiding_naturality_left f.toHom D.toCore)
  hexagon_forward A D C :=
    hom_ext (BraidedCategory.hexagon_forward A.toCore D.toCore C.toCore)
  hexagon_reverse A D C :=
    hom_ext (BraidedCategory.hexagon_reverse A.toCore D.toCore C.toCore)
  symmetry A D := hom_ext (SymmetricCategory.symmetry A.toCore D.toCore)

@[simp] theorem braiding_hom_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    (β_ A D).hom.toHom = (β_ A.toCore D.toCore).hom := (rfl)

@[simp] theorem braiding_inv_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    (β_ A D).inv.toHom = (β_ A.toCore D.toCore).inv := (rfl)

instance : (forgetToCore I n B).Braided where
  braided _ _ := (Category.id_comp _).trans (Category.comp_id _).symm

/-- A `C^n` core whose transition maps on chart overlaps are all the identity, equipped with a
continuous linear equivalence of its model fibre with `Fin 1 → 𝕜`, is isomorphic in
`ContMDiffFiniteRankBundleCore I n B` to the monoidal unit. -/
def isoTensorUnitOfCoordChangeEqId (A : ContMDiffFiniteRankBundleCore I n B)
    (e : (Fin A.toCore.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.toCore.core.baseSet i → x ∈ A.toCore.core.baseSet j →
      A.toCore.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.toCore.rank → 𝕜)) :
    A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B) :=
  isoMk (FiniteRankBundleCore.isoTensorUnitOfCoordChangeEqId A.toCore e h)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_isoTensorUnitOfCoordChangeEqId_hom A.toCore e h)
    (FiniteRankBundleCore.contMDiff_totalSpaceMap_isoTensorUnitOfCoordChangeEqId_inv A.toCore e h)

/-- Right-recursive `m`-th tensor power of a `C^n` finite-rank core. -/
-- Expose the recursive equation so the dependent fibre model reduces on concrete exponents.
@[expose]
def tensorPower (A : ContMDiffFiniteRankBundleCore I n B) :
    ℕ → ContMDiffFiniteRankBundleCore I n B
  | 0 => 𝟙_ (ContMDiffFiniteRankBundleCore I n B)
  | m + 1 => tensorPower A m ⊗ A

@[simp] theorem tensorPower_zero (A : ContMDiffFiniteRankBundleCore I n B) :
    A.tensorPower 0 = 𝟙_ (ContMDiffFiniteRankBundleCore I n B) := (rfl)

@[simp] theorem tensorPower_succ (A : ContMDiffFiniteRankBundleCore I n B) (m : ℕ) :
    A.tensorPower (m + 1) = A.tensorPower m ⊗ A := (rfl)

@[simp] theorem toCore_tensorPower (A : ContMDiffFiniteRankBundleCore I n B) :
    ∀ m : ℕ, (A.tensorPower m).toCore = A.toCore.tensorPower m
  | 0 => rfl
  | m + 1 => congrArg (· ⊗ A.toCore) (toCore_tensorPower A m)

/-- The `m`-th tensor power of a `C^n` bundle morphism. -/
def tensorPowerHom {A D : ContMDiffFiniteRankBundleCore I n B} (f : A ⟶ D) :
    ∀ m : ℕ, A.tensorPower m ⟶ D.tensorPower m
  | 0 => 𝟙 _
  | m + 1 => tensorPowerHom f m ⊗ₘ f

/-- A `C^n` isomorphism of cores induces a `C^n` isomorphism between their `m`-th tensor powers. -/
def tensorPowerCongr {A D : ContMDiffFiniteRankBundleCore I n B} (e : A ≅ D) :
    ∀ m : ℕ, A.tensorPower m ≅ D.tensorPower m
  | 0 => Iso.refl _
  | m + 1 => tensorPowerCongr e m ⊗ᵢ e

/-- The first tensor power of a `C^n` core is canonically isomorphic to the core itself. -/
def tensorPowerOne (A : ContMDiffFiniteRankBundleCore I n B) : A.tensorPower 1 ≅ A :=
  λ_ A

/-- Every tensor power of the monoidal unit in `ContMDiffFiniteRankBundleCore I n B` is canonically
isomorphic to the monoidal unit. -/
def tensorUnitTensorPowerIso :
    ∀ m : ℕ, (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).tensorPower m ≅
      𝟙_ (ContMDiffFiniteRankBundleCore I n B)
  | 0 => Iso.refl _
  | m + 1 => (tensorUnitTensorPowerIso m ⊗ᵢ Iso.refl _) ≪≫ λ_ _

/-- Addition of exponents in `C^n` tensor powers turns into a tensor product. -/
def tensorPowerAdd (A : ContMDiffFiniteRankBundleCore I n B) (m : ℕ) :
    ∀ k : ℕ, A.tensorPower (m + k) ≅ A.tensorPower m ⊗ A.tensorPower k
  | 0 => (ρ_ (A.tensorPower m)).symm
  | k + 1 => (tensorPowerAdd A m k ⊗ᵢ Iso.refl A) ≪≫ α_ (A.tensorPower m) (A.tensorPower k) A

/-- Tensor powers distribute over tensor products of `C^n` cores via the symmetric braiding. -/
def tensorTensorPowerIso (A D : ContMDiffFiniteRankBundleCore I n B) :
    ∀ m : ℕ, (A ⊗ D).tensorPower m ≅ A.tensorPower m ⊗ D.tensorPower m
  | 0 => (λ_ (𝟙_ (ContMDiffFiniteRankBundleCore I n B))).symm
  | m + 1 =>
    (tensorTensorPowerIso A D m ⊗ᵢ Iso.refl (A ⊗ D)) ≪≫
      { hom := tensorμ (A.tensorPower m) (D.tensorPower m) A D
        inv := tensorδ (A.tensorPower m) (D.tensorPower m) A D
        hom_inv_id := tensorμ_tensorδ _ _ _ _
        inv_hom_id := tensorδ_tensorμ _ _ _ _ }

@[simp] theorem toSkeleton_tensorPower (A : ContMDiffFiniteRankBundleCore I n B) :
    ∀ m : ℕ, toSkeleton (A.tensorPower m) = toSkeleton A ^ m
  | 0 => by rw [tensorPower_zero, pow_zero]; rfl
  | m + 1 => by
    rw [tensorPower_succ, Skeleton.toSkeleton_tensorObj, toSkeleton_tensorPower A m, pow_succ]

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

theorem mkOfTensorIsoUnit_eq_mkOfTensorIsoUnit_iff
    {A D A' D' : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B))
    (e' : A' ⊗ D' ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    mkOfTensorIsoUnit e = mkOfTensorIsoUnit e' ↔ Nonempty (A ≅ A') := by
  rw [Units.ext_iff, val_mkOfTensorIsoUnit, val_mkOfTensorIsoUnit]
  exact Quotient.eq

theorem mkOfTensorIsoUnit_eq_one_iff {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :
    mkOfTensorIsoUnit e = 1 ↔ Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
  rw [Units.ext_iff, val_mkOfTensorIsoUnit, Units.val_one, Skeleton.one_eq]
  exact Quotient.eq

theorem pow_mkOfTensorIsoUnit_eq_one_iff {A D : ContMDiffFiniteRankBundleCore I n B}
    (e : A ⊗ D ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) (m : ℕ) :
    mkOfTensorIsoUnit e ^ m = 1 ↔
      Nonempty (A.tensorPower m ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, val_mkOfTensorIsoUnit,
    ← A.toSkeleton_tensorPower m, Units.val_one, Skeleton.one_eq]
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
  let L := ContinuousLinearMap.smulRightL 𝕜 (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)
    (Fin A.toCore.rank → 𝕜) (ContinuousLinearMap.proj i₀)
  have hchart (j : B) : ContMDiffOn I 𝓘(𝕜, Fin A.toCore.rank → 𝕜) n
      (fun x ↦ (A.toCore.core.localTriv j ⟨x, σ x⟩).2) (A.toCore.core.baseSet j) := by
    have : MemTrivializationAtlas (A.toCore.core.localTriv j) := ⟨⟨j, rfl⟩⟩
    exact ((A.toCore.core.localTriv j).contMDiffOn_section_iff
      (A.toCore.core.isOpen_baseSet j) subset_rfl).mp hσ.contMDiffOn
  let a : (𝟙_ (FiniteRankBundleCore 𝕜 B)) ⟶ A.toCore :=
    { operator := fun i j ↦
        ⟨fun x ↦ L (A.toCore.core.localTriv j ⟨x.1, σ x.1⟩).2,
          L.continuous.comp <|
            (continuousOn_iff_continuous_domRestrict.1
              (hchart j).continuousOn).comp
              (continuous_subtype_val.subtype_mk fun x ↦ x.2.2)⟩
      compatible := fun i i' j j' x _ _ hj hj' c ↦ by
        let v : Fin A.toCore.rank → 𝕜 := σ x
        have htriv (k : B) : (A.toCore.core.localTriv k ⟨x, σ x⟩).2 =
            A.toCore.core.coordChange (A.toCore.core.indexAt x) k x v := rfl
        simp only [L, ContinuousMap.coe_mk, ContinuousLinearMap.smulRightL_apply_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
          FiniteRankBundleCore.coordChange_tensorUnit, htriv, _root_.map_smul]
        change c i₀ • A.toCore.core.coordChange j j' x
            (A.toCore.core.coordChange (A.toCore.core.indexAt x) j x v) =
          c i₀ • A.toCore.core.coordChange (A.toCore.core.indexAt x) j' x v
        rw [A.toCore.core.coordChange_comp _ j j' x
          ⟨⟨A.toCore.core.mem_baseSet_at x, hj⟩, hj'⟩] }
  refine ⟨a, CoordinateHom.contMDiff_totalSpaceMap a fun i j ↦
    (L.contMDiff.comp_contMDiffOn ((hchart j).mono inter_subset_right)).congr fun x hx ↦
      (CoordinateHom.operator_eq a i j ⟨x, hx⟩).symm⟩

@[simp]
theorem fiberMap_homFromTensorUnitOfSection_apply (A : ContMDiffFiniteRankBundleCore I n B)
    (σ : Π x, A.toCore.core.Fiber x)
    (hσ : ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
      (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)))
    (x : B) (c : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜) :
    (A.homFromTensorUnitOfSection σ hσ).toHom.fiberMap x c = c ⟨0, by simp⟩ • σ x := by
  let v : Fin A.toCore.rank → 𝕜 := σ x
  have hself : (A.toCore.core.localTriv (A.toCore.core.indexAt x) ⟨x, σ x⟩).2 = v :=
    A.toCore.core.coordChange_self _ x (A.toCore.core.mem_baseSet_at x) v
  rw [CoordinateHom.fiberMap_def]
  change (c ⟨0, by simp⟩ •
    (A.toCore.core.localTriv (A.toCore.core.indexAt x) ⟨x, σ x⟩).2) = c ⟨0, by simp⟩ • v
  rw [hself]

end ContMDiffFiniteRankBundleCore

end General

/-! ### Duals, rank-one invertibility, and global triviality over a complete scalar field -/

section Complete

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {B : Type u} [TopologicalSpace B] [ChartedSpace HB B]

namespace FiniteRankBundleCore

omit [CompleteSpace 𝕜] in
/-- Every continuous linear endomorphism of a one-dimensional coordinate space `Fin r → 𝕜`
(`r = 1`) is scalar multiplication by its single matrix entry. -/
private theorem clm_eq_smul_id_of_eq_one {r : ℕ} (hr : r = 1)
    (T : (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜)) :
    T = T (fun _ ↦ 1) ⟨0, by omega⟩ • ContinuousLinearMap.id 𝕜 (Fin r → 𝕜) := by
  set k₀ : Fin r := ⟨0, by omega⟩
  have huniq : ∀ k : Fin r, k = k₀ := fun k ↦ Fin.ext (by omega)
  ext v k
  have hv : v = v k₀ • (fun _ : Fin r ↦ (1 : 𝕜)) := by
    ext l
    rw [huniq l]
    simp
  conv_lhs => rw [hv]
  rw [map_smul, huniq k]
  simp [mul_comm]

/-- For a rank-one core `A`, the tensor product `A.dual ⊗ A` has identity transitions on all chart
overlaps: each transition of `A` is multiplication by a nonzero scalar, its transpose is the same
scalar, and the reverse transition multiplies by its inverse. -/
theorem coordChange_dual_tensor_eq_id (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1)
    {i j x : B} (hi : x ∈ (A.dual ⊗ A).core.baseSet i) (hj : x ∈ (A.dual ⊗ A).core.baseSet j) :
    (A.dual ⊗ A).core.coordChange i j x =
      ContinuousLinearMap.id 𝕜 (Fin (A.dual ⊗ A).rank → 𝕜) := by
  have hiA : x ∈ A.core.baseSet i := hi.2
  have hjA : x ∈ A.core.baseSet j := hj.2
  set k₀ : Fin A.rank := ⟨0, by omega⟩
  set T := A.core.coordChange i j x
  set S := A.core.coordChange j i x
  set c := T (fun _ ↦ 1) k₀
  set d := S (fun _ ↦ 1) k₀
  have hT : T = c • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    clm_eq_smul_id_of_eq_one hA T
  have hS : S = d • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    clm_eq_smul_id_of_eq_one hA S
  have hdc : d * c = 1 := by
    have hcomp := A.core.coordChange_comp i j i x ⟨⟨hiA, hjA⟩, hiA⟩ (fun _ ↦ 1)
    rw [A.core.coordChange_self i x hiA] at hcomp
    have hk₀ := congrFun hcomp k₀
    change (S (T (fun _ ↦ 1))) k₀ = 1 at hk₀
    rw [hT, hS] at hk₀
    simpa [mul_comm] using hk₀
  have hS_tr : S.piTranspose = d • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
    rw [hS, ← ContinuousLinearMap.piTransposeL_apply, map_smul,
      ContinuousLinearMap.piTransposeL_apply, ContinuousLinearMap.piTranspose_id]
  change S.piTranspose.kronecker T = ContinuousLinearMap.id 𝕜 (Fin (A.rank * A.rank) → 𝕜)
  rw [hS_tr, hT, ContinuousLinearMap.smul_kronecker, ContinuousLinearMap.kronecker_smul,
    smul_smul, hdc, one_smul, ContinuousLinearMap.id_kronecker_id]

/-- Canonical evaluation isomorphism `A.dual ⊗ A ≅ 𝟙_` for a rank-one core `A`. -/
noncomputable def dualTensorIsoUnit (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1) :
    A.dual ⊗ A ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B) :=
  isoTensorUnitOfCoordChangeEqId (A.dual ⊗ A)
    (ContinuousLinearEquiv.piCongrLeft 𝕜
      (fun _ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank ↦ 𝕜) (finCongr (by simp [hA])))
    fun _ _ _ hi hj ↦ A.coordChange_dual_tensor_eq_id hA hi hj

end FiniteRankBundleCore

namespace ContMDiffFiniteRankBundleCore

/-- Over a complete scalar field, a `C^n` morphism between `C^n` finite-rank cores is an
isomorphism if and only if it is bijective on every fibre: finite-dimensional chart inversion makes
the inverse bundle map `C^n`. -/
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
    have hinv_eq : (inv f.toHom).totalSpaceMap = ⇑Φ.symm := funext fun p ↦ Φ.injective <| by
      change ⇑Φ ((inv f.toHom).totalSpaceMap p) = ⇑Φ (Φ.symm p)
      rw [Φ.apply_symm_apply, CoordinateHom.coe_toDiffeomorph]
      let v : Fin D.toCore.rank → 𝕜 := p.2
      have h1 : (inv f.toHom).totalSpaceMap p = ⟨p.1, (inv f.toHom).fiberMap p.1 v⟩ :=
        (inv f.toHom).totalSpaceMap_mk p.1 v
      have h2 : f.toHom.totalSpaceMap ⟨p.1, (inv f.toHom).fiberMap p.1 v⟩ =
          ⟨p.1, f.toHom.fiberMap p.1 ((inv f.toHom).fiberMap p.1 v)⟩ :=
        f.toHom.totalSpaceMap_mk p.1 _
      have h3 := congrArg (fun k : D.toCore ⟶ D.toCore ↦ k.fiberMap p.1 v)
        (IsIso.inv_hom_id f.toHom)
      simp only [FiniteRankBundleCore.fiberMap_comp, FiniteRankBundleCore.fiberMap_id,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h3
      rw [h1, h2, h3]
    refine ⟨⟨⟨inv f.toHom, hinv_eq ▸ Φ.symm.contMDiff⟩,
      hom_ext (IsIso.hom_inv_id f.toHom), hom_ext (IsIso.inv_hom_id f.toHom)⟩⟩

/-- The `C^n` dual of a `C^n` finite-rank core. -/
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
  isoTensorUnitOfCoordChangeEqId (A.dual ⊗ A)
    (ContinuousLinearEquiv.piCongrLeft 𝕜
      (fun _ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank ↦ 𝕜) (finCongr (by simp [hA])))
    fun _ _ _ hi hj ↦ A.toCore.coordChange_dual_tensor_eq_id hA hi hj

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
    let i₀ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank := ⟨0, by simp⟩
    let v₀ : Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜 := fun _ ↦ 1
    have hv₀ : v₀ ≠ 0 := fun h ↦ one_ne_zero (congrFun h i₀)
    let s₀ : B → (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.core.TotalSpace :=
      fun x ↦ ⟨x, v₀⟩
    have hs₀ : ContMDiff I
        (I.prod 𝓘(𝕜, Fin (𝟙_ (ContMDiffFiniteRankBundleCore I n B)).toCore.rank → 𝕜)) n s₀ :=
      fun _ ↦ Bundle.contMDiffAt_totalSpace_iff.mpr ⟨contMDiffAt_id, by
        rw [FiniteRankBundleCore.trivializationAt_core]; exact contMDiffAt_const⟩
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
    let f := A.homFromTensorUnitOfSection σ hσ
    have hf : IsIso f := (isIso_iff_bijective f).mpr fun x ↦ by
      let i₀ : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank := ⟨0, by simp⟩
      let v : Fin A.toCore.rank → 𝕜 := σ x
      set k₀ : Fin A.toCore.rank := ⟨0, by omega⟩
      have huniq : ∀ k : Fin A.toCore.rank, k = k₀ := fun k ↦ Fin.ext (by omega)
      have hvk₀ : v k₀ ≠ 0 := fun h0 ↦ hσ₀ x <| funext fun k ↦ by rw [huniq k]; exact h0
      refine ⟨fun c d hcd ↦ ?_, fun w ↦ ⟨fun _ ↦ w k₀ * (v k₀)⁻¹, ?_⟩⟩
      · rw [fiberMap_homFromTensorUnitOfSection_apply,
          fiberMap_homFromTensorUnitOfSection_apply] at hcd
        ext i; rw [show i = i₀ from Fin.ext (Nat.lt_one_iff.mp i.2)]
        exact mul_right_cancel₀ hvk₀ (congrFun hcd k₀)
      · rw [fiberMap_homFromTensorUnitOfSection_apply]
        ext k; rw [huniq k]
        exact inv_mul_cancel_right₀ hvk₀ (w k₀)
    exact ⟨(asIso f).symm⟩

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

@[simp] theorem ofRankOne_tensor (A D : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (hD : D.toCore.rank = 1) :
    ofRankOne (A ⊗ D) (by simp [hA, hD]) = ofRankOne A hA * ofRankOne D hD :=
  Units.ext <| by
    rw [val_ofRankOne, Units.val_mul, val_ofRankOne, val_ofRankOne]
    exact Skeleton.toSkeleton_tensorObj A D

@[simp] theorem ofRankOne_dual (A : ContMDiffFiniteRankBundleCore I n B) (hA : A.toCore.rank = 1) :
    ofRankOne A.dual (by simp [hA]) = (ofRankOne A hA)⁻¹ :=
  Units.ext <| by rw [val_ofRankOne, ofRankOne, val_inv_mkOfTensorIsoUnit]

@[simp] theorem ofRankOne_tensorPower (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (m : ℕ) :
    ofRankOne (A.tensorPower m) (by simp [hA]) = ofRankOne A hA ^ m :=
  Units.ext <| by
    rw [val_ofRankOne, Units.val_pow_eq_pow_val, val_ofRankOne]
    exact A.toSkeleton_tensorPower m

theorem ofRankOne_eq_ofRankOne_iff (A D : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) (hD : D.toCore.rank = 1) :
    ofRankOne A hA = ofRankOne D hD ↔ Nonempty (A ≅ D) :=
  mkOfTensorIsoUnit_eq_mkOfTensorIsoUnit_iff _ _

theorem ofRankOne_eq_one_iff (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    ofRankOne A hA = 1 ↔ Nonempty (A ≅ 𝟙_ (ContMDiffFiniteRankBundleCore I n B)) :=
  mkOfTensorIsoUnit_eq_one_iff _

theorem ofRankOne_eq_one_iff_exists_section_ne_zero (A : ContMDiffFiniteRankBundleCore I n B)
    (hA : A.toCore.rank = 1) :
    ofRankOne A hA = 1 ↔
      ∃ σ : Π x, A.toCore.core.Fiber x,
        ContMDiff I (I.prod 𝓘(𝕜, Fin A.toCore.rank → 𝕜)) n
          (fun x ↦ TotalSpace.mk' (Fin A.toCore.rank → 𝕜) x (σ x)) ∧
        ∀ x, σ x ≠ 0 :=
  (ofRankOne_eq_one_iff A hA).trans (A.nonempty_iso_tensorUnit_iff_exists_section_ne_zero hA)

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
