/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subfield
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Map

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Topology of general linear groups over subfields

If `E` is a closed subfield of a topological field `L`, the range of `GL ι E →* GL ι L`
along `SubringClass.subtype E` is closed in `GL ι L`, being cut out by entrywise membership in `E`.
Moreover, any continuous homomorphism `ρ : Γ →ₜ* GL ι L` whose entries lie in a subfield `E`
lifts uniquely and continuously to `Γ →ₜ* GL ι E`.

## Main definitions

* `ContinuousMonoidHom.liftGLOfMem`: continuous lift of `Γ →ₜ* GL ι L` with entries in a
  subfield `E` to `Γ →ₜ* GL ι E`.

## Main results

* `Matrix.GeneralLinearGroup.isClosed_range_map_subtype`: if `E` is closed in `L`, the range of
  `Matrix.GeneralLinearGroup.map (SubringClass.subtype E)` is closed in `GL ι L`.
* `ContinuousMonoidHom.map_subtype_liftGLOfMem`: pushing `ρ.liftGLOfMem E hE` forward along
  `SubringClass.subtype E` recovers `ρ`.
* `ContinuousMonoidHom.continuousMap_subtype_comp_liftGLOfMem`: composing `ρ.liftGLOfMem E hE`
  with `Matrix.GeneralLinearGroup.continuousMap (SubringClass.subtype E) continuous_subtypeVal`
  recovers `ρ`.
* `ContinuousMonoidHom.coe_liftGLOfMem_apply`: the entries of `ρ.liftGLOfMem E hE g` coerce to
  the entries of `ρ g`.
* `ContinuousMonoidHom.map_subtype_liftGLOfMem_matrix`: pushing the matrix of
  `ρ.liftGLOfMem E hE g` forward along `Subtype.val` recovers `ρ g`.
* `ContinuousMonoidHom.liftGLOfMem_unique`: uniqueness of the continuous subfield lift.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- **Closedness of the subfield general linear group.** If `E` is a closed subfield of a
topological field `L`, then the range of `GL ι E →* GL ι L` is closed in `GL ι L`. -/
theorem isClosed_range_map_subtype {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
    [TopologicalSpace L] [Fintype ι] [DecidableEq ι] {E : S} (hE : IsClosed (E : Set L)) :
    IsClosed ((Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range :
      Set (GL ι L)) := by
  have heq :
      ((Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range : Set (GL ι L)) =
        ⋂ i, ⋂ j, (fun A : GL ι L ↦ (A : Matrix ι ι L) i j) ⁻¹' (E : Set L) := by
    ext A
    simp only [SetLike.mem_coe, mem_range_map_subtype_iff, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    hE.preimage (Units.continuous_val.matrix_elem i j)

end Matrix.GeneralLinearGroup

namespace ContinuousMonoidHom

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

/-- **Lifting a continuous matrix homomorphism to a subfield.** If every matrix entry of
`ρ : Γ →ₜ* GL ι L` lies in a subfield `E`, then `ρ` lifts continuously to `Γ →ₜ* GL ι E`. -/
noncomputable def liftGLOfMem {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
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

/-- Pushing `ρ.liftGLOfMem E hE` forward along `SubringClass.subtype E` recovers `ρ`. -/
@[simp]
theorem map_subtype_liftGLOfMem {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (ρ.liftGLOfMem E hE g) = ρ g :=
  Matrix.GeneralLinearGroup.map_subtype_liftOfMem E (ρ g) (hE g)

/-- Composing `ρ.liftGLOfMem E hE` with `Matrix.GeneralLinearGroup.continuousMap` along
`SubringClass.subtype E` recovers `ρ`. -/
@[simp]
theorem continuousMap_subtype_comp_liftGLOfMem {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [TopologicalSpace L] (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {hf : Continuous (SubringClass.subtype E)} :
    (Matrix.GeneralLinearGroup.continuousMap (SubringClass.subtype E) hf).comp
        (ρ.liftGLOfMem E hE) = ρ := by
  ext1 g
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply,
    Matrix.GeneralLinearGroup.continuousMap_apply, map_subtype_liftGLOfMem]

/-- The entries of `ρ.liftGLOfMem E hE g` coerce to the entries of `ρ g`. -/
@[simp]
theorem coe_liftGLOfMem_apply {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) (i j : ι) :
    ((ρ.liftGLOfMem E hE g : Matrix ι ι E) i j : L) = (ρ g : Matrix ι ι L) i j :=
  Matrix.GeneralLinearGroup.coe_liftOfMem_apply E (ρ g) (hE g) i j

/-- Pushing the matrix of `ρ.liftGLOfMem E hE g` forward along `Subtype.val` recovers `ρ g`. -/
@[simp]
theorem map_subtype_liftGLOfMem_matrix
    {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    (ρ.liftGLOfMem E hE g : Matrix ι ι E).map Subtype.val = (ρ g : Matrix ι ι L) := by
  ext i j
  simp only [Matrix.map_apply, coe_liftGLOfMem_apply]

/-- **Uniqueness of `ContinuousMonoidHom.liftGLOfMem`.** A continuous homomorphism `Γ →ₜ* GL ι E`
pushing forward to `ρ` along `SubringClass.subtype E` equals `ρ.liftGLOfMem E hE`. -/
theorem liftGLOfMem_unique {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {φ : Γ →ₜ* GL ι E}
    (hφ : ∀ g, Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (φ g) = ρ g) :
    φ = ρ.liftGLOfMem E hE := by
  ext1 g
  exact Matrix.GeneralLinearGroup.map_injective (f := SubringClass.subtype E)
    Subtype.val_injective (by rw [hφ g, map_subtype_liftGLOfMem])

end ContinuousMonoidHom
