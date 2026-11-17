/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.CategoryTheory.Dagger.Functor

import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Automatic contractivity of dagger functors between C*-categories

A complex linear dagger-preserving functor `F` between C*-categories restricts, on each object
`X`, to a unital star algebra homomorphism `F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)`
of C*-algebras. Such homomorphisms are contractive, and isometric and order-embedding when
injective. The C*-identity `‖f‖² = ‖f†f‖` transfers both facts to arrows between different
objects: every such functor is contractive on Hom spaces (giving `F.mapCLM X Y` and continuity),
a faithful one is isometric (`F.mapLinearIsometry X Y`) with norm-closed ranges and order-embedding
on endomorphisms (`F.mapEndStarAlgHom_le_iff`), and a full and faithful one induces linear
isometric equivalences on all Hom spaces (`F.mapLinearIsometryEquiv X Y`).

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D]
  [∀ X Y : D, Norm (X ⟶ Y)] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

omit [DaggerPreadditive C] [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] in
/-- The square of the norm of `F.map f` is the norm of `F.map (f ≫ dagger f)`. -/
private theorem sq_norm_map {X Y : C} (f : X ⟶ Y) :
    ‖F.map f‖ ^ 2 = ‖F.mapEndStarAlgHom ℂ X (.of (f ≫ dagger f))‖ := by
  rw [End.norm_def, mapEndStarAlgHom_asHom, F.map_comp, F.map_dagger,
    CStarCategory.norm_self_comp_dagger]

/-- A complex linear dagger functor between C*-categories is contractive on Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  refine (pow_le_pow_iff_left₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- Every complex-linear dagger functor between C*-categories is contractive in `nnNorm`. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- The action of a complex-linear dagger functor on a Hom space as a continuous linear map of
operator norm at most `1`. -/
def mapCLM (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  letI := CStarCategory.normedAddCommGroup X Y
  letI := CStarCategory.normedSpace X Y
  letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  letI := CStarCategory.normedSpace (F.obj X) (F.obj Y)
  (F.mapLinearMap ℂ (X := X) (Y := Y)).mkContinuous 1 fun f => by
    simpa only [coe_mapLinearMap, one_mul] using F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_apply (X Y : C) (f : X ⟶ Y) : F.mapCLM X Y f = F.map f := (rfl)

/-- The continuous linear map `F.mapCLM X Y` has operator norm at most `1`. -/
theorem norm_mapCLM_le (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedSpace X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    letI := CStarCategory.normedSpace (F.obj X) (F.obj Y)
    ‖F.mapCLM X Y‖ ≤ 1 := by
  let := CStarCategory.normedAddCommGroup X Y
  let := CStarCategory.normedSpace X Y
  let := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  let := CStarCategory.normedSpace (F.obj X) (F.obj Y)
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- A complex-linear dagger functor acts continuously on every Hom space. -/
theorem continuous_map (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  letI := CStarCategory.normedAddCommGroup X Y
  letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  (F.mapCLM X Y).continuous

/-- A faithful complex linear dagger functor between C*-categories is isometric on Hom
spaces. -/
@[simp] theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  refine (pow_left_inj₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_map _ (F.mapEndStarAlgHom_injective ℂ X) _

/-- The action of a faithful complex-linear dagger functor on a Hom space as a linear isometry. -/
def mapLinearIsometry [F.Faithful] (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) :=
  letI := CStarCategory.normedAddCommGroup X Y
  letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  { toLinearMap := F.mapLinearMap ℂ
    norm_map' := F.norm_map }

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- A faithful complex-linear dagger functor acts as an isometry on each Hom space. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  letI := CStarCategory.normedAddCommGroup X Y
  letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  (F.mapLinearIsometry X Y).isometry

/-- The image of a Hom space under a faithful complex-linear dagger functor is closed. -/
theorem isClosed_range_map [F.Faithful] (X Y : C) :
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    IsClosed (Set.range (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) := by
  let := CStarCategory.normedAddCommGroup X Y
  let := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  have : CompleteSpace (X ⟶ Y) := CStarCategory.completeSpace X Y
  exact (F.isometry_map X Y).isUniformInducing.isComplete_range.isClosed

/-- On a faithful complex-linear dagger functor, the induced endomorphism star-algebra
homomorphism preserves and reflects the spectral order. -/
theorem mapEndStarAlgHom_le_iff [F.Faithful] (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (f := (F.mapEndStarAlgHom ℂ X).toNonUnitalStarAlgHom)
    (F.mapEndStarAlgHom_injective ℂ X)

/-- A full and faithful complex-linear dagger functor between C*-categories induces a linear
isometric equivalence on each Hom space. -/
def mapLinearIsometryEquiv [F.Full] [F.Faithful] (X Y : C) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) :=
  letI := CStarCategory.normedAddCommGroup X Y
  letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
  { toLinearEquiv := F.homLinearEquiv ℂ X Y
    norm_map' f := by rw [F.homLinearEquiv_apply ℂ]; exact F.norm_map f }

/-- Evaluation of `Functor.mapLinearIsometryEquiv`. -/
@[simp] theorem mapLinearIsometryEquiv_apply [F.Full] [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f :=
  F.homLinearEquiv_apply ℂ f

/-- The inverse of `Functor.mapLinearIsometryEquiv` is `Functor.preimage`. -/
@[simp] theorem mapLinearIsometryEquiv_symm_apply [F.Full] [F.Faithful] (X Y : C)
    (g : F.obj X ⟶ F.obj Y) :
    letI := CStarCategory.normedAddCommGroup X Y
    letI := CStarCategory.normedAddCommGroup (F.obj X) (F.obj Y)
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g :=
  F.homLinearEquiv_symm_apply ℂ g

end CategoryTheory.Functor
