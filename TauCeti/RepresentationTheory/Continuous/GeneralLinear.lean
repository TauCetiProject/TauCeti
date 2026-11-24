/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.LinearMap.BaseChange
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subfield
import TauCeti.RepresentationTheory.Intertwining

/-!
# Matrix bridges for continuous representations

This file connects continuous matrix homomorphisms `Γ →ₜ* GL ι A` with continuous representations
`TauCeti.ContinuousRep Γ A V` on free modules of finite rank.

* **Matrix-to-representation** (`TauCeti.ContinuousRep.ofGL`, `TauCeti.ContinuousRep.ofGLCongr`):
  a continuous homomorphism `φ : Γ →ₜ* GL ι A` defines a continuous representation on `ι → A`
  acting by `Matrix.mulVecLin (φ g)`.
* **Representation-to-matrix** (`TauCeti.ContinuousRep.toGL`,
  `TauCeti.ContinuousRep.ofGLToGLIso`, `TauCeti.ContinuousRep.toGL_ofGL`): given a continuous
  representation on a module `V` carrying the `A`-module topology (`IsModuleTopology A V`) and a
  finite basis `b`, taking matrices in `b` yields a continuous homomorphism `Γ →ₜ* GL ι A` whose
  associated matrix representation is canonically isomorphic to `ρ`.
* **Subfield lifting** (`TauCeti.ContinuousRep.liftGL`,
  `TauCeti.ContinuousRep.map_subtype_liftGL`,
  `TauCeti.ContinuousRep.continuousMapGL_subtype_comp_liftGL`,
  `TauCeti.ContinuousRep.liftGL_unique`): a continuous homomorphism `Γ →ₜ* GL ι L` whose entries
  lie in a subfield `E` lifts uniquely and continuously to `Γ →ₜ* GL ι E`.
* **Scalar extension** (`TauCeti.ContinuousRep.baseChangeOfGLIso`): when `B ⊗[A] (ι → A)` carries
  the `B`-module topology, extending scalars of `ofGL φ` from `A` to `B` corresponds via
  `TensorProduct.piScalarRight` to applying `algebraMap A B` entrywise.

## Main definitions

* `TauCeti.ContinuousRep.ofGL`: continuous representation on `ι → A` attached to `Γ →ₜ* GL ι A`.
* `TauCeti.ContinuousRep.ofGLCongr`: canonical isomorphism between `ofGL φ₁` and `ofGL φ₂` for
  equal homomorphisms `φ₁ = φ₂`.
* `TauCeti.ContinuousRep.toGL`: continuous matrix homomorphism `Γ →ₜ* GL ι A` attached to a
  continuous representation and a finite basis.
* `TauCeti.ContinuousRep.ofGLToGLIso`: canonical isomorphism `Iso (ofGL (toGL ρ b)) ρ`.
* `TauCeti.ContinuousRep.continuousMapGL`: continuous `GL` map induced by a continuous ring
  homomorphism.
* `TauCeti.ContinuousRep.liftGL`: continuous lift of `Γ →ₜ* GL ι L` with entries in a subfield
  `E` to `Γ →ₜ* GL ι E`.
* `TauCeti.ContinuousRep.baseChangeOfGLIso`: canonical isomorphism identifying `(ofGL φ).baseChange
  B` with the entrywise image under `algebraMap A B`.

## Main results

* `TauCeti.ContinuousRep.toGL_ofGL`
* `TauCeti.ContinuousRep.map_subtype_liftGL`
* `TauCeti.ContinuousRep.map_subtype_liftGL_matrix`
* `TauCeti.ContinuousRep.map_subtype_liftGL_toGL`
* `TauCeti.ContinuousRep.continuousMapGL_subtype_comp_liftGL`
* `TauCeti.ContinuousRep.liftGL_unique`
* `TauCeti.ContinuousRep.baseChangeOfGLIso_apply`
-/

public section

open Matrix
open scoped TensorProduct Topology

namespace TauCeti.ContinuousRep

section OfGL

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [Fintype ι] [DecidableEq ι]

/-- **Continuous representation attached to a continuous matrix homomorphism.** An element `g : Γ`
acts on `ι → A` by left multiplication by the matrix `φ g`. -/
def ofGL (φ : Γ →ₜ* GL ι A) : ContinuousRep Γ A (ι → A) where
  toRepresentation :=
    { toFun g := Matrix.mulVecLin (φ g : Matrix ι ι A)
      map_one' := by
        ext v i
        simp
      map_mul' g h := by
        ext v i
        simp }
  continuous_action :=
    (Units.continuous_val.comp (φ.continuous.comp continuous_fst)).matrix_mulVec continuous_snd

@[simp]
theorem ofGL_apply (φ : Γ →ₜ* GL ι A) (g : Γ) (v : ι → A) :
    ofGL φ g v = (φ g : Matrix ι ι A).mulVec v :=
  (rfl)

/-- **Congruence isomorphism for `ofGL`.** Equal continuous matrix homomorphisms yield canonically
isomorphic continuous representations on `ι → A`. -/
def ofGLCongr {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) : Iso (ofGL φ₁) (ofGL φ₂) where
  toRepresentationEquiv := .mk (.refl A (ι → A)) fun g ↦ by
    ext v i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply,
      coe_toRepresentation, ofGL_apply, h]
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
theorem ofGLCongr_apply {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) (v : ι → A) :
    ofGLCongr h v = v :=
  (rfl)

@[simp]
theorem ofGLCongr_symm_apply {φ₁ φ₂ : Γ →ₜ* GL ι A} (h : φ₁ = φ₂) (v : ι → A) :
    (ofGLCongr h).symm v = v :=
  EquivLike.injective (ofGLCongr h) (by simp)

end OfGL

section ToGL

variable {Γ A V ι : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [AddCommGroup V] [Module A V] [TopologicalSpace V] [IsModuleTopology A V]
  [Fintype ι] [DecidableEq ι]

/-- **Continuous matrix homomorphism attached to a continuous representation and a finite basis.**
The matrix of `g : Γ` is `LinearMap.toMatrixAlgEquiv b (ρ g)`. Assumes `IsModuleTopology A V` so
that the coordinate map `b.equivFun` and hence the matrix entries are continuous. -/
noncomputable def toGL (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) : Γ →ₜ* GL ι A where
  toMonoidHom :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.toRepresentation.toHomUnits
  continuous_toFun := by
    refine Continuous.of_coeHom_comp ?_
    have hequiv : Continuous b.equivFun :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    refine continuous_matrix fun i j ↦ ?_
    exact ((_root_.continuous_apply i).comp (hequiv.comp (ρ.continuous_orbit (b j)))).congr
      fun g ↦ (LinearMap.toMatrixAlgEquiv_apply b (ρ g) i j).symm

@[simp]
theorem coe_toGL (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (g : Γ) :
    (toGL ρ b g : Matrix ι ι A) = LinearMap.toMatrixAlgEquiv b (ρ g) :=
  (rfl)

@[simp]
theorem coe_toGL_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (g : Γ) (i j : ι) :
    (toGL ρ b g : Matrix ι ι A) i j = b.repr (ρ g (b j)) i :=
  LinearMap.toMatrixAlgEquiv_apply b (ρ g) i j

/-- **Matrix realization isomorphism.** Choosing a finite basis `b` on a module `V` carrying the
`A`-module topology (`IsModuleTopology A V`) identifies `ofGL (toGL ρ b)` equivariantly and
homeomorphically with `ρ`. -/
noncomputable def ofGLToGLIso (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) :
    Iso (ofGL (toGL ρ b)) ρ :=
  .ofEquiv (Representation.Equiv.ofBasisAction ρ.toRepresentation (ofGL (toGL ρ b)).toRepresentation
    (.refl A V) b (fun g ↦ ρ g)
    (fun g v ↦ by simp only [LinearEquiv.refl_apply, coe_toRepresentation])
    (fun g w ↦ by
      simpa only [coe_toRepresentation, ofGL_apply, coe_toGL, LinearMap.toMatrixAlgEquiv,
        AlgEquiv.ofLinearEquiv_apply] using LinearMap.toMatrix_mulVec_repr b b (ρ g) w)).symm

@[simp]
theorem ofGLToGLIso_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (v : ι → A) :
    ofGLToGLIso ρ b v = b.equivFun.symm v := by
  rw [ofGLToGLIso, Iso.ofEquiv_apply]
  exact (Representation.Equiv.ofBasisAction_symm_apply (e := .refl A V) (b := b) (w := v)
    ..).trans (by simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply])

@[simp]
theorem ofGLToGLIso_symm_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (x : V) :
    (ofGLToGLIso ρ b).symm x = b.equivFun x :=
  EquivLike.injective (ofGLToGLIso ρ b) (by simp)

/-- Recovering a continuous matrix homomorphism from `ofGL` via the standard basis `Pi.basisFun`. -/
@[simp]
theorem toGL_ofGL (φ : Γ →ₜ* GL ι A) : toGL (ofGL φ) (Pi.basisFun A ι) = φ := by
  ext g i j
  simp [coe_toGL_apply, ofGL_apply, Matrix.mulVec_single, Matrix.col_apply]

end ToGL

section MapGL

/-- **Continuous `GL` map induced by a continuous ring homomorphism.** -/
def continuousMapGL {A B ι : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [Fintype ι] [DecidableEq ι]
    (f : A →+* B) (hf : Continuous f) : GL ι A →ₜ* GL ι B where
  toMonoidHom := Matrix.GeneralLinearGroup.map f
  continuous_toFun := hf.generalLinearGroup_map

/-- Applying `continuousMapGL f hf` agrees with `Matrix.GeneralLinearGroup.map f`. -/
@[simp]
theorem continuousMapGL_apply {A B ι : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [Fintype ι] [DecidableEq ι]
    (f : A →+* B) (hf : Continuous f) (g : GL ι A) :
    continuousMapGL f hf g = Matrix.GeneralLinearGroup.map f g :=
  (rfl)

end MapGL

section LiftGL

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

/-- **Lifting a continuous matrix homomorphism to a subfield.** If every matrix entry of
`ρ : Γ →ₜ* GL ι L` lies in a subfield `E`, then `ρ` lifts continuously to `Γ →ₜ* GL ι E`. -/
noncomputable def liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) : Γ →ₜ* GL ι E where
  toFun g := Matrix.GeneralLinearGroup.liftOfMem E (ρ g) (hE g)
  map_one' :=
    Matrix.GeneralLinearGroup.map_injective (f := SubringClass.subtype E) Subtype.val_injective <|
      by simp only [Matrix.GeneralLinearGroup.map_subtype_liftOfMem, map_one]
  map_mul' g h :=
    Matrix.GeneralLinearGroup.map_injective (f := SubringClass.subtype E) Subtype.val_injective <|
      by simp only [map_mul, Matrix.GeneralLinearGroup.map_subtype_liftOfMem]
  continuous_toFun :=
    (Topology.IsInducing.generalLinearGroup_map (n := ι) (f := SubringClass.subtype E)
      Topology.IsInducing.subtypeVal).continuous_iff.mpr <| by
        simpa only [Function.comp_def, Matrix.GeneralLinearGroup.map_subtype_liftOfMem] using
          map_continuous ρ

/-- Pushing `liftGL ρ E hE` forward along `SubringClass.subtype E` recovers `ρ`. -/
@[simp]
theorem map_subtype_liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (liftGL ρ E hE g) = ρ g :=
  Matrix.GeneralLinearGroup.map_subtype_liftOfMem E (ρ g) (hE g)

/-- Composing `liftGL ρ E hE` with `continuousMapGL (SubringClass.subtype E) continuous_subtypeVal`
recovers `ρ`. -/
@[simp]
theorem continuousMapGL_subtype_comp_liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [TopologicalSpace L] (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) :
    (continuousMapGL (SubringClass.subtype E) continuous_subtypeVal).comp
        (liftGL ρ E hE) = ρ := by
  ext1 g
  exact map_subtype_liftGL ρ E hE g

/-- The entries of `liftGL ρ E hE g` coerce to the entries of `ρ g`. -/
@[simp]
theorem coe_liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) (i j : ι) :
    ((liftGL ρ E hE g : Matrix ι ι E) i j : L) = (ρ g : Matrix ι ι L) i j :=
  Matrix.GeneralLinearGroup.coe_liftOfMem_apply E (ρ g) (hE g) i j

/-- Pushing the matrix of `liftGL ρ E hE g` forward along `Subtype.val` recovers `ρ g`. -/
@[simp]
theorem map_subtype_liftGL_matrix
    {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    (liftGL ρ E hE g : Matrix ι ι E).map Subtype.val = (ρ g : Matrix ι ι L) := by
  ext i j
  simp only [Matrix.map_apply, coe_liftGL]

/-- Pushing the matrix of `liftGL (toGL ρ b) E hE g` forward along `SubringClass.subtype E`
recovers `LinearMap.toMatrix b b (ρ g)`. -/
theorem map_subtype_liftGL_toGL {Γ V : Type*} [Group Γ] [TopologicalSpace Γ]
    [ContinuousInv Γ] [TopologicalSpace L] [IsTopologicalSemiring L]
    [AddCommGroup V] [Module L V] [TopologicalSpace V] [IsModuleTopology L V]
    (ρ : ContinuousRep Γ L V) (b : Module.Basis ι L V) (E : S)
    (hE : ∀ g i j, (toGL ρ b g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    (liftGL (toGL ρ b) E hE g : Matrix ι ι E).map (SubringClass.subtype E) =
      LinearMap.toMatrix b b (ρ g) := by
  rw [SubringClass.coe_subtype, map_subtype_liftGL_matrix, coe_toGL]
  exact AlgEquiv.ofLinearEquiv_apply ..

/-- **Uniqueness of `liftGL`.** A continuous homomorphism `Γ →ₜ* GL ι E` pushing forward to `ρ`
along `SubringClass.subtype E` equals `liftGL ρ E hE`. -/
theorem liftGL_unique {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {φ : Γ →ₜ* GL ι E}
    (hφ : ∀ g, Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (φ g) = ρ g) :
    φ = liftGL ρ E hE := by
  ext1 g
  exact Matrix.GeneralLinearGroup.map_injective (f := SubringClass.subtype E)
    Subtype.val_injective (by rw [hφ g, map_subtype_liftGL])

end LiftGL

section BaseChangeOfGL

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [Fintype ι] [DecidableEq ι]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B]
  [Algebra A B] [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] (ι → A))] [IsModuleTopology B (B ⊗[A] (ι → A))]

/-- **Extension of scalars of a matrix representation** identifies `B ⊗[A] (ι → A)` (equipped with
its `B`-module topology `IsModuleTopology B (B ⊗[A] (ι → A))`) with `ι → B` on which `Γ` acts by
the image matrices under `algebraMap A B`, through `TensorProduct.piScalarRight`. -/
def baseChangeOfGLIso (φ : Γ →ₜ* GL ι A) :
    Iso ((ofGL φ).baseChange B)
      (ofGL (ContinuousMonoidHom.comp
        (continuousMapGL (algebraMap A B) (continuous_algebraMap A B)) φ)) :=
  .ofEquiv (.mk (TensorProduct.piScalarRight A B B ι) fun g ↦ by
    have hrep : (ofGL φ).toRepresentation g = Matrix.mulVecLin (φ g : Matrix ι ι A) :=
      LinearMap.ext fun v ↦ by simp only [coe_toRepresentation, ofGL_apply, Matrix.mulVecLin_apply]
    refine LinearMap.ext fun x ↦ ?_
    have hmap :
        ((Matrix.GeneralLinearGroup.map (algebraMap A B) (φ g) : GL ι B) : Matrix ι ι B) =
          (φ g : Matrix ι ι A).map (algebraMap A B) := by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, toRepresentation_baseChange,
      Representation.baseChange_apply, hrep, TensorProduct.piScalarRight_baseChange_mulVecLin,
      coe_toRepresentation, ofGL_apply, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      continuousMapGL_apply, hmap])

/-- Underlying map of `baseChangeOfGLIso` as `TensorProduct.piScalarRight`. -/
@[simp]
theorem baseChangeOfGLIso_apply (φ : Γ →ₜ* GL ι A) (x : B ⊗[A] (ι → A)) :
    baseChangeOfGLIso B φ x = TensorProduct.piScalarRight A B B ι x :=
  (Iso.ofEquiv_apply _ x).trans (Representation.Equiv.mk_apply _ x)

theorem baseChangeOfGLIso_tmul (φ : Γ →ₜ* GL ι A) (b : B) (v : ι → A) :
    baseChangeOfGLIso B φ (b ⊗ₜ v) = fun i ↦ v i • b :=
  (baseChangeOfGLIso_apply B φ _).trans (TensorProduct.piScalarRightHom_tmul A B B ι b v)

@[simp]
theorem baseChangeOfGLIso_symm_apply (φ : Γ →ₜ* GL ι A) (w : ι → B) :
    (baseChangeOfGLIso B φ).symm w = (TensorProduct.piScalarRight A B B ι).symm w :=
  EquivLike.injective (baseChangeOfGLIso B φ) (by
    rw [Iso.apply_symm_apply, baseChangeOfGLIso_apply]
    exact ((TensorProduct.piScalarRight A B B ι).apply_symm_apply w).symm)

end BaseChangeOfGL

end TauCeti.ContinuousRep
