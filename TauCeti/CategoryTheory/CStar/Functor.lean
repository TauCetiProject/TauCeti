/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Dagger.Endomorphism
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear

/-!
# Linear dagger functors between complex C⋆-categories

A `ℂ`-linear dagger functor `F : C ⥤ D` between complex C⋆-categories induces unital complex
`⋆`-algebra homomorphisms `F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)` on endomorphism
C⋆-algebras. Combining C⋆-algebraic contractivity and isometricity of injective `⋆`-homomorphisms
with the Hom-space C⋆-identity `‖f‖ = √‖f ≫ dagger f‖` yields the fundamental rigidity properties
of functors between C⋆-categories:

* **Automatic contractivity**: every `ℂ`-linear dagger functor `F : C ⥤ D` satisfies
  `‖F.map f‖ ≤ ‖f‖` on all Hom spaces (`CategoryTheory.Functor.norm_map_le`), hence acts on each
  Hom space as a contractive continuous linear map (`CategoryTheory.Functor.mapCLM`) and has a
  norm-closed two-sided kernel ideal (`CategoryTheory.Functor.isClosed_kerIdeal_hom`).
* **Isometry of faithful functors**: if `F` is also faithful, then `‖F.map f‖ = ‖f‖` on every Hom
  space (`CategoryTheory.Functor.norm_map`), so `F.map` embeds each Hom space linearly
  isometrically onto a closed subspace (`CategoryTheory.Functor.mapLinearIsometry`,
  `CategoryTheory.Functor.isClosed_range_map`) and embeds each `End X` order-isomorphically.
* **Pullback along fully faithful functors**: any `ℂ`-linear dagger category admitting a fully
  faithful `ℂ`-linear dagger functor into a C⋆-category inherits a unique `CStarCategory`
  structure (`CategoryTheory.Functor.FullyFaithful.cstarCategory`), supplying instances for
  `InducedCategory` and `ObjectProperty.FullSubcategory`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W⋆-categories*, Pacific J. Math. **120** (1985), 79–109,
  Section 1.
* R. Longo and J. E. Roberts, *A theory of dimension*, K-Theory **11** (1997), 103–159, Section 2.
-/

public section

noncomputable section

open CategoryTheory TauCeti
open scoped NNReal

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

/-! ### Automatic contractivity, closed kernels, and faithful isometry on C⋆-categories -/

section CStar

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [CStarCategory C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [CStarCategory D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [CategoryTheory.Linear ℂ E]
  [DaggerCategory E] [CStarCategory E]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-- **Automatic contractivity**: every `ℂ`-linear dagger functor between complex C⋆-categories is
norm-contractive on all Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  rw [← sqrt_norm_comp_dagger_self (F.map f), ← sqrt_norm_comp_dagger_self f]
  apply Real.sqrt_le_sqrt
  have h := NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X) (End.of (f ≫ dagger f))
  simpa only [mapEndStarAlgHom_of, F.map_comp, F.map_dagger, End.norm_of] using h

/-- `ℝ≥0`-norm contractivity of a `ℂ`-linear dagger functor between C⋆-categories. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- Every `ℂ`-linear dagger functor between C⋆-categories is distance-nonincreasing on Hom
spaces. -/
theorem dist_map_le {X Y : C} (f g : X ⟶ Y) : dist (F.map f) (F.map g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← F.map_sub]
  exact F.norm_map_le (f - g)

/-- Every `ℂ`-linear dagger functor between C⋆-categories is `1`-Lipschitz on Hom spaces. -/
theorem lipschitzWith_map (X Y : C) :
    LipschitzWith 1 (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  LipschitzWith.of_dist_le_mul fun f g => by
    simpa only [NNReal.coe_one, one_mul] using F.dist_map_le f g

/-- Every `ℂ`-linear dagger functor between C⋆-categories is continuous on Hom spaces. -/
theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.lipschitzWith_map X Y).continuous

/-- Action of a `ℂ`-linear dagger functor on Hom spaces bundled as a contractive continuous linear
map `(X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y)`. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  (F.mapLinearMap ℂ).mkContinuous 1 fun f => by
    rw [coe_mapLinearMap, one_mul]
    exact F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_apply {X Y : C} (f : X ⟶ Y) :
    F.mapCLM X Y f = F.map f := (rfl)

/-- Forgetting continuity from `Functor.mapCLM` recovers `Functor.mapLinearMap ℂ`. -/
@[simp] theorem toLinearMap_mapCLM (X Y : C) :
    (F.mapCLM X Y).toLinearMap = F.mapLinearMap ℂ := (rfl)

/-- The operator norm of `F.mapCLM X Y` is at most `1`. -/
theorem norm_mapCLM_le_one (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `Functor.mapCLM` on the identity functor is the identity continuous linear map. -/
@[simp] theorem mapCLM_id (X Y : C) :
    (𝟭 C).mapCLM X Y = ContinuousLinearMap.id ℂ (X ⟶ Y) := by
  ext
  rfl

/-- `Functor.mapCLM` respects composition of `ℂ`-linear dagger functors. -/
theorem mapCLM_comp (G : D ⥤ E) [G.Additive] [G.Linear ℂ] [G.PreservesDagger] (X Y : C) :
    (F ⋙ G).mapCLM X Y = (G.mapCLM (F.obj X) (F.obj Y)).comp (F.mapCLM X Y) := by
  ext
  rfl

/-- `Functor.mapEndStarAlgHom ℂ X` is monotone with respect to the spectral orders on `End X` and
`End (F.obj X)`. -/
theorem mapEndStarAlgHom_mono (X : C) : Monotone (F.mapEndStarAlgHom ℂ X) :=
  OrderHomClass.mono (F.mapEndStarAlgHom ℂ X)

/-- The kernel of `F.mapLinearMap ℂ` on `X ⟶ Y` is norm-closed. -/
theorem isClosed_ker_mapLinearMap (X Y : C) :
    IsClosed (LinearMap.ker (F.mapLinearMap ℂ (X := X) (Y := Y)) : Set (X ⟶ Y)) :=
  (F.mapCLM X Y).isClosed_ker

/-- Each Hom component `F.kerIdeal.hom X Y` of the kernel ideal of a `ℂ`-linear dagger functor is
norm-closed in `X ⟶ Y`. -/
theorem isClosed_kerIdeal_hom (X Y : C) :
    IsClosed (F.kerIdeal.hom X Y : Set (X ⟶ Y)) := by
  convert F.isClosed_ker_mapLinearMap X Y using 1
  ext f
  simp

/-- Each Hom submodule `F.kerIdeal.homSubmodule ℂ X Y` of a `ℂ`-linear dagger functor is
norm-closed in `X ⟶ Y`. -/
theorem isClosed_kerIdeal_homSubmodule (X Y : C) :
    IsClosed (F.kerIdeal.homSubmodule ℂ X Y : Set (X ⟶ Y)) := by
  convert F.isClosed_kerIdeal_hom X Y using 1
  ext f
  simp

/-- Each Hom submodule `F.kerIdeal.homSubmodule ℂ X Y` of a `ℂ`-linear dagger functor is a complete
Banach subspace. -/
instance completeSpace_kerIdeal_homSubmodule (X Y : C) :
    CompleteSpace (F.kerIdeal.homSubmodule ℂ X Y) :=
  (F.isClosed_kerIdeal_homSubmodule X Y).completeSpace_coe

/-- **Faithful `ℂ`-linear dagger functors are isometric**: if `F` is faithful, then `F.map`
preserves norms on every Hom space. -/
@[simp] theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  rw [← sqrt_norm_comp_dagger_self (F.map f), ← sqrt_norm_comp_dagger_self f]
  congr 1
  have h := NonUnitalStarAlgHom.norm_map (F.mapEndStarAlgHom ℂ X)
    (F.mapEndStarAlgHom_injective ℂ X) (End.of (f ≫ dagger f))
  simpa only [mapEndStarAlgHom_of, F.map_comp, F.map_dagger, End.norm_of] using h

/-- Faithful `ℂ`-linear dagger functors preserve `ℝ≥0`-norms on every Hom space. -/
@[simp] theorem nnNorm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ = ‖f‖₊ :=
  Subtype.ext (F.norm_map f)

/-- Faithful `ℂ`-linear dagger functors preserve distances on every Hom space. -/
@[simp] theorem dist_map [F.Faithful] {X Y : C} (f g : X ⟶ Y) :
    dist (F.map f) (F.map g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm, ← F.map_sub, F.norm_map]

/-- A faithful `ℂ`-linear dagger functor acts as an isometry on each Hom space. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Isometry.of_dist_eq F.dist_map

/-- Action of a faithful `ℂ`-linear dagger functor on Hom spaces bundled as a `ℂ`-linear
isometry `(X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y)`. -/
def mapLinearIsometry [F.Faithful] (X Y : C) : (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] {X Y : C} (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- Converting `Functor.mapLinearIsometry` to a continuous linear map recovers `Functor.mapCLM`. -/
@[simp] theorem toContinuousLinearMap_mapLinearIsometry [F.Faithful] (X Y : C) :
    (F.mapLinearIsometry X Y).toContinuousLinearMap = F.mapCLM X Y := by
  ext
  rfl

/-- Because Hom spaces of `C` are complete, the image of each Hom space under a faithful `ℂ`-linear
dagger functor is norm-closed in `F.obj X ⟶ F.obj Y`. -/
theorem isClosed_range_map [F.Faithful] (X Y : C) :
    IsClosed (Set.range (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :=
  (F.isometry_map X Y).isUniformInducing.isComplete_range.isClosed

/-- A faithful `ℂ`-linear dagger functor reflects and preserves the spectral order on `End X`. -/
@[simp] theorem mapEndStarAlgHom_le_iff [F.Faithful] {X : C} {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (F.mapEndStarAlgHom ℂ X) (F.mapEndStarAlgHom_injective ℂ X)

/-- A fully faithful `ℂ`-linear dagger functor induces a `ℂ`-linear isometric equivalence on each
Hom space. -/
def FullyFaithful.mapLinearIsometryEquiv {F : C ⥤ D} [F.Additive] [F.Linear ℂ] [F.PreservesDagger]
    (hF : F.FullyFaithful) (X Y : C) : (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv := hF.preimage_map
  right_inv := hF.map_preimage
  map_add' _ _ := F.map_add
  map_smul' _ _ := F.map_smul _ _
  norm_map' :=
    let _ := hF.faithful
    F.norm_map

/-- Forward evaluation of `FullyFaithful.mapLinearIsometryEquiv`. -/
@[simp] theorem FullyFaithful.mapLinearIsometryEquiv_apply {F : C ⥤ D} [F.Additive] [F.Linear ℂ]
    [F.PreservesDagger] (hF : F.FullyFaithful) {X Y : C} (f : X ⟶ Y) :
    hF.mapLinearIsometryEquiv X Y f = F.map f := (rfl)

/-- Inverse evaluation of `FullyFaithful.mapLinearIsometryEquiv`. -/
@[simp] theorem FullyFaithful.mapLinearIsometryEquiv_symm_apply {F : C ⥤ D} [F.Additive]
    [F.Linear ℂ] [F.PreservesDagger] (hF : F.FullyFaithful) {X Y : C} (g : F.obj X ⟶ F.obj Y) :
    (hF.mapLinearIsometryEquiv X Y).symm g = hF.preimage g := (rfl)

end CStar

/-! ### Pulling back `CStarCategory` along fully faithful `ℂ`-linear dagger functors -/

section Pullback

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [CStarCategory D]

/-- Pull back a `CStarCategory` structure along a fully faithful `ℂ`-linear dagger functor
`F : C ⥤ D`, giving `f : X ⟶ Y` the norm `‖F.map f‖`. -/
@[instance_reducible]
def FullyFaithful.cstarCategory {F : C ⥤ D} [F.Additive] [F.Linear ℂ] [F.PreservesDagger]
    (hF : F.FullyFaithful) : CStarCategory C where
  homNorm X Y := ⟨fun f => ‖F.map f‖⟩
  homMetricSpace X Y := MetricSpace.induced F.map hF.homEquiv.injective inferInstance
  hom_dist_eq X Y f g :=
    (dist_eq_norm_neg_add (F.map f) (F.map g)).trans
      (congrArg Norm.norm
        (by simp only [F.map_add, F.map_neg] : F.map (-f + g) = -F.map f + F.map g).symm)
  hom_norm_smul_le X Y c f := by
    simpa only [F.map_smul] using norm_smul_le c (F.map f)
  homCompleteSpace X Y :=
    let : MetricSpace (X ⟶ Y) := MetricSpace.induced F.map hF.homEquiv.injective inferInstance
    let e : (X ⟶ Y) ≃ᵢ (F.obj X ⟶ F.obj Y) :=
      { toEquiv := hF.homEquiv
        isometry_toFun := fun _ _ => rfl }
    e.completeSpace_iff.2 inferInstance
  norm_comp_le f g := by
    simpa only [F.map_comp] using norm_comp_le (F.map f) (F.map g)
  norm_comp_dagger_self f := by
    simpa only [F.map_comp, F.map_dagger] using norm_comp_dagger_self (F.map f)
  exists_comp_dagger_eq f := by
    obtain ⟨h', hh'⟩ := exists_comp_dagger_eq (F.map f)
    refine ⟨hF.preimage h', hF.map_injective ?_⟩
    simp only [F.map_comp, F.map_dagger, hF.map_preimage, hh']

end Pullback

end CategoryTheory.Functor

/-! ### Induced categories and full subcategories of C⋆-categories -/

namespace TauCeti

section Subcategories

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C]

/-- Any category induced from a complex C⋆-category along an object map `F : T → C` is canonically
a complex C⋆-category. -/
instance inducedCategoryCStarCategory {T : Type u₂} (F : T → C) :
    CStarCategory (InducedCategory C F) :=
  (fullyFaithfulInducedFunctor F).cstarCategory

/-- Any full subcategory `P.FullSubcategory` of a complex C⋆-category is canonically a complex
C⋆-category. -/
instance fullSubcategoryCStarCategory (P : ObjectProperty C) :
    CStarCategory P.FullSubcategory :=
  P.fullyFaithfulι.cstarCategory

end Subcategories

end TauCeti

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
  [CStarCategory C]

/-- Unwrapping an arrow in `InducedCategory C F` preserves its norm. -/
@[simp] theorem InducedCategory.norm_hom {T : Type u₂} {F : T → C}
    {X Y : InducedCategory C F} (f : X ⟶ Y) : ‖f.hom‖ = ‖f‖ := (rfl)

/-- Wrapping an arrow via `InducedCategory.homMk` preserves its norm. -/
@[simp] theorem InducedCategory.norm_homMk {T : Type u₂} {F : T → C}
    {X Y : InducedCategory C F} (f : F X ⟶ F Y) :
    ‖InducedCategory.homMk (F := F) f‖ = ‖f‖ := (rfl)

/-- Unwrapping an arrow in `P.FullSubcategory` preserves its norm. -/
theorem ObjectProperty.FullSubcategory.norm_hom {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X ⟶ Y) : ‖f.hom‖ = ‖f‖ := (rfl)

/-- Wrapping an arrow via `ObjectProperty.homMk` preserves its norm. -/
@[simp] theorem ObjectProperty.norm_homMk {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) :
    ‖(ObjectProperty.homMk f : X ⟶ Y)‖ = ‖f‖ := (rfl)

end CategoryTheory
