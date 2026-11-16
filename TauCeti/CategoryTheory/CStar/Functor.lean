/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Dagger.Functor
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Linear dagger functors between C⋆-categories

An additive `R`-linear dagger-preserving functor `F : C ⥤ D` induces a unital `⋆`-algebra
homomorphism `F.mapEndStarAlgHom R X : End X →⋆ₐ[R] End (F.obj X)` on each endomorphism algebra
(and a `⋆`-algebra equivalence when `F` is full and faithful).

When `C` and `D` are complex C⋆-categories, every complex linear dagger-preserving functor is
automatically contractive on every Hom space (`‖F.map f‖ ≤ ‖f‖`), hence continuous with a closed
kernel on each Hom space and order-preserving on endomorphism algebras. If in addition `F` is
faithful, then `F` is isometric on every Hom space (`‖F.map f‖ = ‖f‖`), its image on each Hom space
is closed, and `F.mapEndStarAlgHom ℂ X` is an order embedding.

## Main declarations

* `CategoryTheory.Functor.mapEndStarAlgHom`: the unital `⋆`-algebra homomorphism
  `End X →⋆ₐ[R] End (F.obj X)` induced by a linear dagger-preserving functor.
* `CategoryTheory.Functor.mapEndStarAlgEquiv`: the unital `⋆`-algebra equivalence
  `End X ≃⋆ₐ[R] End (F.obj X)` for a full and faithful linear dagger-preserving functor.
* `CategoryTheory.Functor.norm_map_le`: automatic contractivity `‖F.map f‖ ≤ ‖f‖` of any complex
  linear dagger-preserving functor between C⋆-categories.
* `CategoryTheory.Functor.mapCLM`, `CategoryTheory.Functor.opNorm_mapCLM_le_one`,
  `CategoryTheory.Functor.isClosed_setOf_map_eq_zero`: the bounded linear action on Hom spaces and
  closedness of its kernel.
* `CategoryTheory.Functor.norm_map`, `CategoryTheory.Functor.isometry_map`,
  `CategoryTheory.Functor.mapLinearIsometry`, `CategoryTheory.Functor.isClosed_range_map`:
  faithful complex linear dagger-preserving functors between C⋆-categories are isometric with
  closed range on each Hom space.
* `CategoryTheory.Functor.mapLinearIsometryEquiv`: linear isometric equivalences on Hom spaces for
  full and faithful complex linear dagger-preserving functors.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

section Algebraic

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  [DaggerCategory C] [DaggerCategory D]
  (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An additive `R`-linear dagger-preserving functor induces a unital `⋆`-algebra homomorphism on
each endomorphism algebra. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) where
  __ := F.mapEndAlgHom R X
  map_star' f := by ext; simp

/-- The induced `⋆`-algebra homomorphism acts by the functor on underlying endomorphisms. -/
@[simp]
theorem mapEndStarAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndStarAlgHom R X f).asHom = F.map f.asHom :=
  F.mapEndAlgHom_asHom R X f

/-- Forgetting star compatibility recovers `Functor.mapEndAlgHom`. -/
@[simp]
theorem mapEndStarAlgHom_toAlgHom (X : C) :
    (F.mapEndStarAlgHom R X : End X →ₐ[R] End (F.obj X)) = F.mapEndAlgHom R X := (rfl)

/-- A faithful linear dagger-preserving functor embeds each endomorphism `⋆`-algebra. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_injective R X

/-- A linear dagger-preserving functor bijective on `X ⟶ X` induces a bijective `⋆`-algebra
homomorphism on `End X`. -/
theorem mapEndStarAlgHom_bijective (X : C)
    (h : Function.Bijective (F.map : (X ⟶ X) → (F.obj X ⟶ F.obj X))) :
    Function.Bijective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_bijective R X h

/-- The identity functor induces the identity `⋆`-algebra homomorphism on endomorphisms. -/
@[simp]
theorem mapEndStarAlgHom_id (X : C) :
    (𝟭 C).mapEndStarAlgHom R X = StarAlgHom.id R (End X) := by
  ext f
  rw [mapEndStarAlgHom_asHom]
  rfl

/-- `mapEndStarAlgHom` is functorial under functor composition. -/
@[simp]
theorem mapEndStarAlgHom_comp {E : Type u₃} [Category.{v₃} E] [Preadditive E]
    [DaggerCategory E] [CategoryTheory.Linear R E]
    (G : D ⥤ E) [G.Additive] [G.Linear R] [G.PreservesDagger] (X : C) :
    (F ⋙ G).mapEndStarAlgHom R X =
      (G.mapEndStarAlgHom R (F.obj X)).comp (F.mapEndStarAlgHom R X) := by
  ext f
  simp

/-- A full and faithful linear dagger-preserving functor induces a unital `⋆`-algebra equivalence
on each endomorphism algebra. -/
def mapEndStarAlgEquiv [F.Full] [F.Faithful] (X : C) : End X ≃⋆ₐ[R] End (F.obj X) :=
  StarAlgEquiv.ofBijective (F.mapEndStarAlgHom R X)
    (F.mapEndStarAlgHom_bijective R X ⟨F.map_injective, F.map_surjective⟩)

/-- The forward action of `mapEndStarAlgEquiv` applies `F.map` to the underlying arrow. -/
@[simp]
theorem mapEndStarAlgEquiv_asHom [F.Full] [F.Faithful] (X : C) (f : End X) :
    (F.mapEndStarAlgEquiv R X f).asHom = F.map f.asHom :=
  F.mapEndStarAlgHom_asHom R X f

/-- The inverse action of `mapEndStarAlgEquiv` applies `F.preimage` to the underlying arrow. -/
@[simp]
theorem mapEndStarAlgEquiv_symm_asHom [F.Full] [F.Faithful] (X : C) (g : End (F.obj X)) :
    ((F.mapEndStarAlgEquiv R X).symm g).asHom = F.preimage g.asHom := by
  apply F.map_injective
  have h := congrArg End.asHom ((F.mapEndStarAlgEquiv R X).apply_symm_apply g)
  simpa only [mapEndStarAlgEquiv_asHom, map_preimage] using h

/-- Coercing `mapEndStarAlgEquiv` to a `⋆`-algebra homomorphism recovers `mapEndStarAlgHom`. -/
@[simp]
theorem mapEndStarAlgEquiv_toStarAlgHom [F.Full] [F.Faithful] (X : C) :
    (F.mapEndStarAlgEquiv R X).toStarAlgHom = F.mapEndStarAlgHom R X := by
  ext f
  simp

end Algebraic

section CStar

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear ℂ C] [CategoryTheory.Linear ℂ D]
  [DaggerCategory C] [DaggerCategory D]
  [DaggerPreadditive C] [DaggerPreadditive D]
  [DaggerLinear ℂ C] [DaggerLinear ℂ D]
  [CStarCategory C] [CStarCategory D]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-- **Automatic contractivity**: every complex linear dagger-preserving functor between
C⋆-categories is contractive on every Hom space. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  have hsq : ‖F.map f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [← CStarCategory.norm_self_comp_dagger, ← CStarCategory.norm_self_comp_dagger,
      ← F.map_dagger, ← F.map_comp]
    have hle := NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X)
      (End.of (f ≫ dagger f))
    simpa only [← End.norm_asHom, mapEndStarAlgHom_asHom] using hle
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The action of a complex linear dagger-preserving functor on a Hom space, bundled as a
contractive continuous linear map. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  (F.mapLinearMap ℂ).mkContinuous 1 fun f => by
    simpa [one_mul] using F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp]
theorem mapCLM_apply {X Y : C} (f : X ⟶ Y) : F.mapCLM X Y f = F.map f := (rfl)

/-- The operator norm of `F.mapCLM X Y` is at most `1`. -/
theorem opNorm_mapCLM_le_one (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A complex linear dagger-preserving functor between C⋆-categories is `1`-Lipschitz on every
Hom space. -/
theorem lipschitzWith_map (X Y : C) :
    LipschitzWith 1 (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  LipschitzWith.of_dist_le_mul fun f g => by
    rw [dist_eq_norm, dist_eq_norm, ← F.map_sub, NNReal.coe_one, one_mul]
    exact F.norm_map_le (f - g)

/-- A complex linear dagger-preserving functor between C⋆-categories is continuous on every
Hom space. -/
@[fun_prop]
theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapCLM X Y).continuous

/-- The kernel `{f : X ⟶ Y | F.map f = 0}` of a linear dagger-preserving functor between
C⋆-categories is closed in `X ⟶ Y`. -/
theorem isClosed_setOf_map_eq_zero (X Y : C) :
    IsClosed {f : X ⟶ Y | F.map f = 0} :=
  (F.mapCLM X Y).isClosed_ker

/-- A linear dagger-preserving functor between C⋆-categories is monotone on endomorphism
algebras. -/
theorem mapEndStarAlgHom_mono (X : C) : Monotone (F.mapEndStarAlgHom ℂ X) :=
  OrderHomClass.mono (F.mapEndStarAlgHom ℂ X)

/-- A linear dagger-preserving functor between C⋆-categories preserves positivity in endomorphism
algebras. -/
theorem mapEndStarAlgHom_nonneg {X : C} {a : End X} (ha : 0 ≤ a) :
    0 ≤ F.mapEndStarAlgHom ℂ X a := by
  simpa only [map_zero] using F.mapEndStarAlgHom_mono X ha

section Faithful

variable [F.Faithful]

/-- **Automatic isometry**: every faithful complex linear dagger-preserving functor between
C⋆-categories preserves Hom norms. -/
@[simp]
theorem norm_map {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  have hsq : ‖F.map f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← CStarCategory.norm_self_comp_dagger, ← CStarCategory.norm_self_comp_dagger,
      ← F.map_dagger, ← F.map_comp]
    have heq := NonUnitalStarAlgHom.norm_map (F.mapEndStarAlgHom ℂ X)
      (F.mapEndStarAlgHom_injective ℂ X) (End.of (f ≫ dagger f))
    simpa only [← End.norm_asHom, mapEndStarAlgHom_asHom] using heq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A faithful complex linear dagger-preserving functor between C⋆-categories is an isometry on
every Hom space. -/
theorem isometry_map (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, dist_eq_norm, ← F.map_sub, F.norm_map]

/-- The action of a faithful linear dagger-preserving functor on a Hom space, bundled as a linear
isometry. -/
def mapLinearIsometry (X Y : C) : (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp]
theorem mapLinearIsometry_apply {X Y : C} (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- Coercing `Functor.mapLinearIsometry` to a continuous linear map recovers `Functor.mapCLM`. -/
@[simp]
theorem mapLinearIsometry_toContinuousLinearMap (X Y : C) :
    (F.mapLinearIsometry X Y).toContinuousLinearMap = F.mapCLM X Y := by
  ext f
  rfl

/-- The image of a Hom space under a faithful linear dagger-preserving functor between
C⋆-categories is closed. -/
theorem isClosed_range_map (X Y : C) :
    IsClosed (Set.range (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :=
  (F.isometry_map X Y).isUniformInducing.isComplete_range.isClosed

/-- A faithful linear dagger-preserving functor induces an order embedding on endomorphism
algebras. -/
@[simp]
theorem mapEndStarAlgHom_le_iff (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (F.mapEndStarAlgHom ℂ X) (F.mapEndStarAlgHom_injective ℂ X)

/-- A faithful linear dagger-preserving functor preserves and reflects positivity in endomorphism
algebras. -/
@[simp]
theorem mapEndStarAlgHom_nonneg_iff (X : C) {a : End X} :
    0 ≤ F.mapEndStarAlgHom ℂ X a ↔ 0 ≤ a := by
  simpa only [map_zero] using F.mapEndStarAlgHom_le_iff X (a := 0) (b := a)

/-- A full and faithful complex linear dagger-preserving functor between C⋆-categories induces a
linear isometric equivalence on every Hom space. -/
def mapLinearIsometryEquiv [F.Full] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add
  map_smul' := F.map_smul
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometryEquiv`. -/
@[simp]
theorem mapLinearIsometryEquiv_apply [F.Full] {X Y : C} (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f := (rfl)

/-- The inverse of `Functor.mapLinearIsometryEquiv` applies `F.preimage`. -/
@[simp]
theorem mapLinearIsometryEquiv_symm_apply [F.Full] {X Y : C} (g : F.obj X ⟶ F.obj Y) :
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g := (rfl)

/-- Coercing `Functor.mapLinearIsometryEquiv` to a linear isometry recovers
`Functor.mapLinearIsometry`. -/
@[simp]
theorem mapLinearIsometryEquiv_toLinearIsometry [F.Full] (X Y : C) :
    (F.mapLinearIsometryEquiv X Y).toLinearIsometry = F.mapLinearIsometry X Y := by
  ext f
  rfl

end Faithful

end CStar

end CategoryTheory.Functor
