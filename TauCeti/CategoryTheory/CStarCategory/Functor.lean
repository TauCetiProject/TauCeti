/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.CategoryTheory.CStarCategory.End
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.FullyFaithful
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# Automatic contractivity and isometricity of linear dagger functors

Every `ℂ`-linear dagger-preserving functor `F : C ⥤ D` between C*-categories is automatically
norm-contractive (`‖F.map f‖ ≤ ‖f‖`), hence continuous on Hom spaces with closed kernel morphism
ideal `F.kerIdeal`. The proof passes through the endomorphism `⋆`-algebra homomorphism
`F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)`, which is contractive between C*-algebras,
applied to `End.of (f ≫ dagger f)` using the C*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`.

When `F` is faithful, `F.mapEndStarAlgHom ℂ X` is injective and therefore isometric and
order-reflecting on `End X`, upgrading `F.map` to a linear isometry on every Hom space (and a
linear isometric equivalence when `F` is also full). Conversely, norm preservation on all arrows
characterizes faithfulness of `F`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-! ### Automatic contractivity, Hom-space CLM, and closed kernel ideal -/

/-- Any `ℂ`-linear dagger functor between C*-categories is automatically norm-contractive on
morphisms. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc
    ‖F.map f‖ ^ 2 = ‖F.map f ≫ dagger (F.map f)‖ :=
      (CStarCategory.norm_comp_dagger_self (F.map f)).symm
    _ = ‖F.mapEndStarAlgHom ℂ X (End.of (f ≫ dagger f))‖ := by
      simp [← End.norm_asHom]
    _ ≤ ‖End.of (f ≫ dagger f)‖ :=
      NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X) (End.of (f ≫ dagger f))
    _ = ‖f‖ ^ 2 := by rw [End.norm_of, CStarCategory.norm_comp_dagger_self]

/-- Nonnegative-norm version of `CategoryTheory.Functor.norm_map_le`. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- The action of a `ℂ`-linear dagger functor on Hom spaces bundled as a continuous linear map. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  (F.mapLinearMap ℂ).mkContinuous 1 fun f => by
    simpa using F.norm_map_le f

/-- Evaluation of `F.mapCLM` applies `F.map`. -/
@[simp] theorem mapCLM_apply (X Y : C) (f : X ⟶ Y) :
    F.mapCLM X Y f = F.map f := (rfl)

/-- Forgetting continuity from `F.mapCLM` recovers `F.mapLinearMap ℂ`. -/
@[simp] theorem mapCLM_toLinearMap (X Y : C) :
    (F.mapCLM X Y).toLinearMap = F.mapLinearMap ℂ := (rfl)

/-- The operator norm of `F.mapCLM X Y` is at most `1`. -/
theorem norm_mapCLM_le (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `F.map` is `1`-Lipschitz on every Hom space. -/
theorem lipschitzWith_map (X Y : C) :
    LipschitzWith 1 (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnNorm (F.mapLinearMap ℂ) 1 fun f => by
    simpa using F.nnNorm_map_le f

/-- `F.map` is continuous on every Hom space. -/
@[fun_prop] theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapCLM X Y).continuous

/-- Each Hom-space component of the kernel morphism ideal `F.kerIdeal` of a `ℂ`-linear dagger
functor between C*-categories is norm-closed. -/
theorem isClosed_kerIdeal (X Y : C) : IsClosed (F.kerIdeal.hom X Y : Set (X ⟶ Y)) := by
  have hset : (F.kerIdeal.hom X Y : Set (X ⟶ Y)) = ((F.mapCLM X Y).ker : Set (X ⟶ Y)) := by
    ext f
    simp
  rw [hset]
  exact (F.mapCLM X Y).isClosed_ker

/-- `F.mapEndStarAlgHom ℂ X` is monotone with respect to the spectral order on `End`. -/
theorem mapEndStarAlgHom_mono (X : C) : Monotone (F.mapEndStarAlgHom ℂ X) :=
  OrderHomClass.mono (F.mapEndStarAlgHom ℂ X)

/-- `F.mapEndStarAlgHom ℂ X` preserves positive endomorphisms. -/
theorem mapEndStarAlgHom_nonneg (X : C) {a : End X} (ha : 0 ≤ a) :
    0 ≤ F.mapEndStarAlgHom ℂ X a :=
  map_nonneg (F.mapEndStarAlgHom ℂ X) ha

/-! ### Faithful and fully faithful linear dagger functors -/

/-- A faithful `ℂ`-linear dagger functor between C*-categories is isometric on morphisms. -/
@[simp] theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc
    ‖F.map f‖ ^ 2 = ‖F.map f ≫ dagger (F.map f)‖ :=
      (CStarCategory.norm_comp_dagger_self (F.map f)).symm
    _ = ‖F.mapEndStarAlgHom ℂ X (End.of (f ≫ dagger f))‖ := by
      simp [← End.norm_asHom]
    _ = ‖End.of (f ≫ dagger f)‖ :=
      NonUnitalStarAlgHom.norm_map (F.mapEndStarAlgHom ℂ X)
        (F.mapEndStarAlgHom_injective ℂ X) (End.of (f ≫ dagger f))
    _ = ‖f‖ ^ 2 := by rw [End.norm_of, CStarCategory.norm_comp_dagger_self]

/-- Nonnegative-norm version of `CategoryTheory.Functor.norm_map`. -/
@[simp] theorem nnNorm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ = ‖f‖₊ :=
  Subtype.ext (F.norm_map f)

/-- A faithful `ℂ`-linear dagger functor induces an isometry on every Hom space. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.isometry_of_norm (F.mapLinearMap ℂ) F.norm_map

/-- The Hom-space action of a faithful `ℂ`-linear dagger functor bundled as a `ℂ`-linear
isometry. -/
def mapLinearIsometry [F.Faithful] (X Y : C) :
    (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `F.mapLinearIsometry` applies `F.map`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- A `ℂ`-linear dagger functor between C*-categories is faithful if and only if it preserves the
norm of every morphism. -/
theorem faithful_iff_forall_norm_map_eq :
    F.Faithful ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ‖F.map f‖ = ‖f‖ := by
  refine ⟨fun _ _ _ f => F.norm_map f, fun h => ⟨fun {X Y} f g hfg => ?_⟩⟩
  refine sub_eq_zero.mp (norm_eq_zero.mp ?_)
  rw [← h (f - g), F.map_sub, hfg, sub_self, norm_zero]

/-- A faithful `ℂ`-linear dagger functor reflects and preserves the spectral order on `End X`. -/
@[simp] theorem mapEndStarAlgHom_le_iff [F.Faithful] (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (F.mapEndStarAlgHom ℂ X) (F.mapEndStarAlgHom_injective ℂ X)

/-- A faithful `ℂ`-linear dagger functor reflects and preserves positivity in `End X`. -/
@[simp] theorem mapEndStarAlgHom_nonneg_iff [F.Faithful] (X : C) {a : End X} :
    0 ≤ F.mapEndStarAlgHom ℂ X a ↔ 0 ≤ a := by
  simpa only [map_zero] using F.mapEndStarAlgHom_le_iff X (a := 0) (b := a)

/-- The Hom-space action of a fully faithful `ℂ`-linear dagger functor bundled as a `ℂ`-linear
isometric equivalence. -/
def mapLinearIsometryEquiv [F.Full] [F.Faithful] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  __ := F.homLinearEquiv ℂ X Y
  norm_map' f := by simp

/-- Forward evaluation of `F.mapLinearIsometryEquiv` applies `F.map`. -/
@[simp] theorem mapLinearIsometryEquiv_apply [F.Full] [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f := by
  simp [mapLinearIsometryEquiv]

/-- Inverse evaluation of `F.mapLinearIsometryEquiv` applies `F.preimage`. -/
@[simp] theorem mapLinearIsometryEquiv_symm_apply [F.Full] [F.Faithful] (X Y : C)
    (g : F.obj X ⟶ F.obj Y) :
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g := by
  apply (F.mapLinearIsometryEquiv X Y).injective
  simp [mapLinearIsometryEquiv]

/-- Taking `F.preimage` along a fully faithful `ℂ`-linear dagger functor preserves norms. -/
@[simp] theorem norm_preimage [F.Full] [F.Faithful] {X Y : C} (g : F.obj X ⟶ F.obj Y) :
    ‖F.preimage g‖ = ‖g‖ := by
  simpa using (F.mapLinearIsometryEquiv X Y).symm.norm_map g

end CategoryTheory.Functor

namespace CategoryTheory.Iso

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]

/-- Conjugation by a unitary isomorphism is norm-preserving on endomorphism C*-algebras. -/
@[simp] theorem norm_endStarAlgEquiv {X Y : C} (e : X ≅ Y) (he : IsUnitary e.hom) (a : End X) :
    ‖e.endStarAlgEquiv ℂ he a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map (e.endStarAlgEquiv ℂ he) a

/-- Conjugation by a unitary isomorphism is an order isomorphism on endomorphism C*-algebras. -/
theorem endStarAlgEquiv_le_iff {X Y : C} (e : X ≅ Y) (he : IsUnitary e.hom)
    {a b : End X} :
    e.endStarAlgEquiv ℂ he a ≤ e.endStarAlgEquiv ℂ he b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (e.endStarAlgEquiv ℂ he).toStarAlgHom
    (e.endStarAlgEquiv ℂ he).injective

end CategoryTheory.Iso
