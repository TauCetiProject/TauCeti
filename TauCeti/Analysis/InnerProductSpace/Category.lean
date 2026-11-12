/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# The dagger category of Hilbert spaces

`TauCeti.HilbertCat 𝕜` bundles complete inner product spaces over an `RCLike` field.
Its morphisms are Mathlib continuous linear maps, with their existing Banach-space
structures. Composition and addition give the native linear category structure, and
Mathlib's `ContinuousLinearMap.adjoint` supplies the conjugate-linear dagger.

Unitary arrows are precisely the maps underlying linear isometric equivalences.
The operator norm satisfies the C*-identity in categorical composition order; these
facts provide the Hilbert-space example for analytic categories.
-/

public section

noncomputable section

open CategoryTheory

universe u v

namespace TauCeti

/-- Complete inner product spaces over `𝕜`, with continuous linear maps as morphisms. -/
structure HilbertCat (𝕜 : Type u) [RCLike 𝕜] where
  /-- The underlying type. -/
  carrier : Type v
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace 𝕜 carrier]
  [completeSpace : CompleteSpace carrier]

attribute [instance] HilbertCat.normedAddCommGroup HilbertCat.innerProductSpace
  HilbertCat.completeSpace

namespace HilbertCat

variable {𝕜 : Type u} [RCLike 𝕜]

instance : CoeSort (HilbertCat.{u, v} 𝕜) (Type v) := ⟨carrier⟩

/-- Bundle a Hilbert space, retaining the supplied norm and inner product structures. -/
abbrev of (𝕜 : Type u) [RCLike 𝕜] (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : HilbertCat 𝕜 := ⟨E⟩

instance : Category (HilbertCat.{u, v} 𝕜) where
  Hom X Y := X →L[𝕜] Y
  id X := ContinuousLinearMap.id 𝕜 X
  comp f g := g.comp f
  id_comp _ := ContinuousLinearMap.comp_id _
  comp_id _ := ContinuousLinearMap.id_comp _
  assoc _ _ _ := (ContinuousLinearMap.comp_assoc _ _ _).symm

instance : ConcreteCategory (HilbertCat.{u, v} 𝕜) (fun X Y => X →L[𝕜] Y) where
  hom f := f
  ofHom f := f

/-- Hom spaces retain the continuous-linear-map normed group structure. -/
instance (X Y : HilbertCat.{u, v} 𝕜) : NormedAddCommGroup (X ⟶ Y) :=
  inferInstanceAs (NormedAddCommGroup (X →L[𝕜] Y))

instance (X Y : HilbertCat.{u, v} 𝕜) : NormedSpace 𝕜 (X ⟶ Y) :=
  inferInstanceAs (NormedSpace 𝕜 (X →L[𝕜] Y))

instance (X Y : HilbertCat.{u, v} 𝕜) : CompleteSpace (X ⟶ Y) :=
  inferInstanceAs (CompleteSpace (X →L[𝕜] Y))

instance : Preadditive (HilbertCat.{u, v} 𝕜) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X →L[𝕜] Y))
  add_comp _ _ _ _ _ _ := ContinuousLinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _ := ContinuousLinearMap.add_comp _ _ _

instance : Linear 𝕜 (HilbertCat.{u, v} 𝕜) where
  homModule X Y := inferInstanceAs (Module 𝕜 (X →L[𝕜] Y))
  smul_comp _ _ _ _ _ _ := ContinuousLinearMap.comp_smul _ _ _
  comp_smul _ _ _ _ _ _ := ContinuousLinearMap.smul_comp _ _ _

instance : DaggerCategory (HilbertCat.{u, v} 𝕜) where
  dagger f := ContinuousLinearMap.adjoint f
  dagger_id _ := ContinuousLinearMap.adjoint_id
  dagger_comp f g := ContinuousLinearMap.adjoint_comp g f
  dagger_dagger f := ContinuousLinearMap.adjoint_adjoint f

instance : DaggerPreadditive (HilbertCat.{u, v} 𝕜) where
  dagger_add f g := map_add ContinuousLinearMap.adjoint f g

instance : DaggerLinear 𝕜 (HilbertCat.{u, v} 𝕜) where
  dagger_smul r f := map_smulₛₗ ContinuousLinearMap.adjoint r f

variable {X Y Z : HilbertCat.{u, v} 𝕜}

/-- The concrete-category projection retains the underlying continuous linear map. -/
theorem hom_eq (f : X ⟶ Y) : ConcreteCategory.hom f = (f : X →L[𝕜] Y) := (rfl)

/-- The categorical identity is the continuous linear identity. -/
theorem id_eq_id (X : HilbertCat 𝕜) :
    (𝟙 X : X ⟶ X) = ContinuousLinearMap.id 𝕜 X := (rfl)

/-- Composition agrees with continuous-linear-map composition. -/
theorem comp_eq_comp (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g.comp f := (rfl)

/-- The categorical dagger is Mathlib's Hilbert-space adjoint. -/
theorem dagger_eq_adjoint (f : X ⟶ Y) : dagger f = ContinuousLinearMap.adjoint f := (rfl)

/-- The dagger satisfies the adjoint inner-product identity. -/
theorem inner_dagger_left (f : X ⟶ Y) (x : X) (y : Y) :
    inner 𝕜 (dagger f y) x = inner 𝕜 y (f x) :=
  ContinuousLinearMap.adjoint_inner_left f x y

/-- The operator norm is submultiplicative under composition. -/
theorem norm_comp_le (f : X ⟶ Y) (g : Y ⟶ Z) : ‖f ≫ g‖ ≤ ‖g‖ * ‖f‖ :=
  ContinuousLinearMap.opNorm_comp_le g f

/-- The dagger preserves the operator norm. -/
@[simp] theorem norm_dagger (f : X ⟶ Y) : ‖dagger f‖ = ‖f‖ :=
  ContinuousLinearMap.adjoint.norm_map f

/-- The C*-identity for Hilbert-space morphisms, in categorical composition order. -/
theorem norm_comp_dagger (f : X ⟶ Y) : ‖f ≫ dagger f‖ = ‖f‖ ^ 2 := by
  rw [comp_eq_comp, dagger_eq_adjoint, pow_two]
  exact ContinuousLinearMap.norm_adjoint_comp_self f

/-- A linear isometric equivalence gives a unitary Hilbert-space arrow. -/
theorem isUnitary_linearIsometryEquiv (e : X ≃ₗᵢ[𝕜] Y) :
    IsUnitary (C := HilbertCat 𝕜) (X := X) (Y := Y) (e : X →L[𝕜] Y) := by
  rw [isUnitary_iff]
  constructor <;> ext x <;>
    simp [comp_eq_comp, id_eq_id, dagger_eq_adjoint, hom_eq,
      LinearIsometryEquiv.adjoint_eq_symm]

/-- Recover the linear isometric equivalence from a unitary arrow. -/
def linearIsometryEquivOfUnitary (f : X ⟶ Y) (hf : IsUnitary f) :
    X ≃ₗᵢ[𝕜] Y where
  toLinearEquiv := LinearEquiv.ofLinearMap f.toLinearMap (dagger f).toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap hf.dagger_hom_id)
    (congrArg ContinuousLinearMap.toLinearMap hf.hom_dagger_id)
  norm_map' := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self f).2 hf.hom_dagger_id

/-- The recovered equivalence has the original arrow as its forward map. -/
theorem linearIsometryEquivOfUnitary_apply (f : X ⟶ Y) (hf : IsUnitary f) (x : X) :
    linearIsometryEquivOfUnitary f hf x = f x := (rfl)

/-- The inverse of the recovered equivalence is the dagger. -/
theorem linearIsometryEquivOfUnitary_symm_apply (f : X ⟶ Y) (hf : IsUnitary f)
    (y : Y) : (linearIsometryEquivOfUnitary f hf).symm y = dagger f y := (rfl)

/-- Unitary arrows between Hilbert spaces are exactly linear isometric equivalences. -/
def unitaryEquivLinearIsometryEquiv :
    { f : X ⟶ Y // IsUnitary f } ≃ (X ≃ₗᵢ[𝕜] Y) where
  toFun f := linearIsometryEquivOfUnitary f.1 f.2
  invFun e := ⟨(e : X →L[𝕜] Y), isUnitary_linearIsometryEquiv e⟩
  left_inv f := by apply Subtype.ext; ext x; rfl
  right_inv e := by ext x; rfl

/-- The unitary-to-isometry correspondence preserves evaluation. -/
@[simp] theorem unitaryEquivLinearIsometryEquiv_apply
    (f : { f : X ⟶ Y // IsUnitary f }) (x : X) :
    unitaryEquivLinearIsometryEquiv f x = f.1 x := (rfl)

/-- The inverse correspondence regards an isometry as its continuous linear map. -/
@[simp] theorem unitaryEquivLinearIsometryEquiv_symm_apply
    (e : X ≃ₗᵢ[𝕜] Y) (x : X) :
    (unitaryEquivLinearIsometryEquiv.symm e).1 x = e x := (rfl)

end HilbertCat

end TauCeti
