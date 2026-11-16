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
# Linear dagger functors between C*-categories

An additive `R`-linear dagger-preserving functor `F : C ⥤ D` induces star-algebra homomorphisms
`F.mapEndStarAlgHom R X : End X →⋆ₐ[R] End (F.obj X)` on endomorphisms. Between C*-categories,
the C*-identity on Hom spaces and automatic contractivity of C*-algebra homomorphisms force
every complex-linear dagger functor to be automatically contractive on all Hom spaces
(`‖F.map f‖ ≤ ‖f‖`), hence continuous (`F.mapCLM X Y`).

When `F` is faithful, the induced maps on endomorphisms are injective star-algebra homomorphisms,
hence isometric and order-embedding; it follows that `F` is isometric on all Hom spaces
(`F.mapLinearIsometry X Y`) with norm-closed ranges. A full and faithful complex-linear dagger
functor induces linear isometric equivalences on all Hom spaces (`F.mapLinearIsometryEquiv X Y`).

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

open CategoryTheory TauCeti

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

section StarAlgHom

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [DaggerCategory D]
variable (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [F.Additive] [F.Linear R] [F.PreservesDagger]

/-- An additive `R`-linear dagger-preserving functor induces a star-algebra homomorphism on
endomorphism algebras. -/
def mapEndStarAlgHom (X : C) : End X →⋆ₐ[R] End (F.obj X) where
  toFun := F.mapEndAlgHom R X
  map_one' := map_one (F.mapEndAlgHom R X)
  map_mul' := map_mul (F.mapEndAlgHom R X)
  map_zero' := _root_.map_zero (F.mapEndAlgHom R X)
  map_add' := _root_.map_add (F.mapEndAlgHom R X)
  commutes' := (F.mapEndAlgHom R X).commutes
  map_star' a := by
    apply End.ext
    simpa only [End.star_asHom, Functor.mapEndAlgHom_asHom] using F.map_dagger a.asHom

/-- Evaluation of the induced endomorphism star-algebra homomorphism on underlying arrows. -/
@[simp] theorem mapEndStarAlgHom_asHom (X : C) (a : End X) :
    (F.mapEndStarAlgHom R X a).asHom = F.map a.asHom :=
  F.mapEndAlgHom_asHom R X a

/-- Forgetting star-preservation recovers `Functor.mapEndAlgHom`. -/
@[simp] theorem mapEndStarAlgHom_toAlgHom (X : C) :
    (F.mapEndStarAlgHom R X).toAlgHom = F.mapEndAlgHom R X := by
  ext a
  rfl

/-- A faithful additive `R`-linear dagger-preserving functor embeds each endomorphism
star-algebra. -/
theorem mapEndStarAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndStarAlgHom R X) :=
  F.mapEndAlgHom_injective R X

end StarAlgHom

section CStar

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C] [CStarCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-- Every complex-linear dagger functor between C*-categories is automatically contractive on
Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc ‖F.map f‖ ^ 2 = ‖F.map f ≫ dagger (F.map f)‖ :=
        (CStarCategory.norm_self_comp_dagger (F.map f)).symm
    _ = ‖F.mapEndStarAlgHom ℂ X (End.of (f ≫ dagger f))‖ := by
        rw [← End.norm_asHom, mapEndStarAlgHom_asHom, Functor.map_comp, map_dagger]
    _ ≤ ‖End.of (f ≫ dagger f)‖ :=
        NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X).toNonUnitalStarAlgHom _
    _ = ‖f‖ ^ 2 := CStarCategory.norm_self_comp_dagger f

/-- Every complex-linear dagger functor between C*-categories is contractive in `nnnorm`. -/
theorem nnnorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- The action of a complex-linear dagger functor on a Hom space as a continuous linear map of
operator norm at most `1`. -/
noncomputable def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  (F.mapLinearMap ℂ (X := X) (Y := Y)).mkContinuous 1 fun f => by
    simpa only [coe_mapLinearMap, one_mul] using F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_apply (X Y : C) (f : X ⟶ Y) : F.mapCLM X Y f = F.map f := (rfl)

/-- The continuous linear map `F.mapCLM X Y` has operator norm at most `1`. -/
theorem norm_mapCLM_le (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A complex-linear dagger functor acts continuously on every Hom space. -/
@[fun_prop] theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapCLM X Y).continuous

/-- A faithful complex-linear dagger functor between C*-categories is isometric on all Hom
spaces. -/
theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc ‖F.map f‖ ^ 2 = ‖F.map f ≫ dagger (F.map f)‖ :=
        (CStarCategory.norm_self_comp_dagger (F.map f)).symm
    _ = ‖F.mapEndStarAlgHom ℂ X (End.of (f ≫ dagger f))‖ := by
        rw [← End.norm_asHom, mapEndStarAlgHom_asHom, Functor.map_comp, map_dagger]
    _ = ‖End.of (f ≫ dagger f)‖ :=
        NonUnitalStarAlgHom.norm_map (φ := (F.mapEndStarAlgHom ℂ X).toNonUnitalStarAlgHom)
          (F.mapEndStarAlgHom_injective ℂ X) _
    _ = ‖f‖ ^ 2 := CStarCategory.norm_self_comp_dagger f

/-- The action of a faithful complex-linear dagger functor on a Hom space as a linear isometry. -/
def mapLinearIsometry [F.Faithful] (X Y : C) : (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- A faithful complex-linear dagger functor acts as an isometry on each Hom space. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapLinearIsometry X Y).isometry

/-- The image of a Hom space under a faithful complex-linear dagger functor is closed. -/
theorem isClosed_range_map [F.Faithful] (X Y : C) :
    IsClosed (Set.range (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :=
  (F.isometry_map X Y).isUniformInducing.isComplete_range.isClosed

/-- On a faithful complex-linear dagger functor, the induced endomorphism star-algebra
homomorphism preserves and reflects the spectral order. -/
theorem mapEndStarAlgHom_le_iff [F.Faithful] (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (f := (F.mapEndStarAlgHom ℂ X).toNonUnitalStarAlgHom)
    (F.mapEndStarAlgHom_injective ℂ X)

/-- A full and faithful complex-linear dagger functor between C*-categories induces a linear
isometric equivalence on each Hom space. -/
noncomputable def mapLinearIsometryEquiv [F.Full] [F.Faithful] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearEquiv := LinearEquiv.ofBijective (F.mapLinearMap ℂ)
    ⟨F.map_injective, F.map_surjective⟩
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometryEquiv`. -/
@[simp] theorem mapLinearIsometryEquiv_apply [F.Full] [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f := (rfl)

/-- The inverse of `Functor.mapLinearIsometryEquiv` is `Functor.preimage`. -/
@[simp] theorem mapLinearIsometryEquiv_symm_apply [F.Full] [F.Faithful] (X Y : C)
    (g : F.obj X ⟶ F.obj Y) :
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g :=
  F.map_injective (by
    rw [← mapLinearIsometryEquiv_apply, LinearIsometryEquiv.apply_symm_apply, Functor.map_preimage])

end CStar

end CategoryTheory.Functor
