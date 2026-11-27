/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subfield

import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Descend
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

open TauCeti.CoefficientDescent

variable {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
  [Fintype ι] [DecidableEq ι]

private theorem entries_subset_range_subtype {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace L] (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) :
    entries (ρ : Γ →* GL ι L) ⊆ Set.range (SubringClass.subtype E) := by
  intro x hx
  obtain ⟨g, i, j, rfl⟩ := mem_entries_iff.mp hx
  exact ⟨⟨(ρ g : Matrix ι ι L) i j, hE g i j⟩, rfl⟩

/-- **Lifting a continuous matrix homomorphism to a subfield.** If every matrix entry of
`ρ : Γ →ₜ* GL ι L` lies in a subfield `E`, then `ρ` lifts continuously to `Γ →ₜ* GL ι E`. -/
noncomputable def liftGLOfMem {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) : Γ →ₜ* GL ι E where
  toMonoidHom := descend Subtype.val_injective (entries_subset_range_subtype ρ E hE)
  continuous_toFun := by
    refine (Topology.IsInducing.generalLinearGroup_map (n := ι) (f := SubringClass.subtype E)
      Topology.IsInducing.subtypeVal).continuous_iff.mpr ?_
    exact (map_continuous ρ).congr fun g ↦
      (map_descend Subtype.val_injective (entries_subset_range_subtype ρ E hE) g).symm

/-- Pushing `ρ.liftGLOfMem E hE` forward along `SubringClass.subtype E` recovers `ρ`. -/
@[simp]
theorem map_subtype_liftGLOfMem {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (ρ.liftGLOfMem E hE g) = ρ g :=
  map_descend Subtype.val_injective (entries_subset_range_subtype ρ E hE) g

/-- The entries of `ρ.liftGLOfMem E hE g` coerce to the entries of `ρ g`. -/
@[simp]
theorem coe_liftGLOfMem_apply {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) (i j : ι) :
    ((ρ.liftGLOfMem E hE g : Matrix ι ι E) i j : L) = (ρ g : Matrix ι ι L) i j :=
  map_descend_apply Subtype.val_injective (entries_subset_range_subtype ρ E hE) g i j

/-- Pushing the matrix of `ρ.liftGLOfMem E hE g` forward along `Subtype.val` recovers `ρ g`. -/
@[simp]
theorem map_subtype_liftGLOfMem_matrix
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    (ρ.liftGLOfMem E hE g : Matrix ι ι E).map Subtype.val = (ρ g : Matrix ι ι L) :=
  map_coe_descend Subtype.val_injective (entries_subset_range_subtype ρ E hE) g

/-- **Uniqueness of `ContinuousMonoidHom.liftGLOfMem`.** A continuous homomorphism `Γ →ₜ* GL ι E`
pushing forward to `ρ` along `SubringClass.subtype E` equals `ρ.liftGLOfMem E hE`. -/
theorem liftGLOfMem_unique {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : S)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {φ : Γ →ₜ* GL ι E}
    (hφ : ∀ g, Matrix.GeneralLinearGroup.map (SubringClass.subtype E) (φ g) = ρ g) :
    φ = ρ.liftGLOfMem E hE := by
  ext1 g
  exact DFunLike.congr_fun
    ((eq_descend_iff Subtype.val_injective (entries_subset_range_subtype ρ E hE)).mpr hφ) g

end ContinuousMonoidHom
