/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Projectivization.Product
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Standard product affine charts of multiprojective space as open partial homeomorphisms

Over a topological field `K`, a finite product `(i : ι) → ℙ K (Fin (n i + 1) → K)` of projective
spaces is covered by the standard product affine opens `Projectivization.piAffineOpen I`, which are
open in the product topology when `ι` is finite. Each flattened standard product affine chart
`Projectivization.piAffineChart I` is continuous on `piAffineOpen I` with continuous inverse, giving
an open partial homeomorphism `Projectivization.piAffineOpenPartialHomeomorph I` onto the flattened
coordinate space `(Σ i, Fin (n i)) → K`.

We also record the product-topology homeomorphism `TauCeti.piMatrixHomeomorph` flattening a family
of matrices `(i : ι) → Matrix (κ i) (μ i) α` to `(Σ i, κ i × μ i) → α`.

## Main declarations

* `TauCeti.piMatrixHomeomorph`: the homeomorphism `((i : ι) → Matrix (κ i) (μ i) α) ≃ₜ
  ((p : Σ i, κ i × μ i) → α)`.
* `Projectivization.isOpen_piAffineOpen`: for finite `ι`, each standard product affine open is open.
* `Projectivization.piAffineOpenPartialHomeomorph`: the standard product affine chart as an open
  partial homeomorphism onto `(Σ i, Fin (n i)) → K`.
* `Projectivization.isOpenEmbedding_piAffineChart_symm`: the inverse product chart is an open
  embedding.
* `Projectivization.interPiAffineOpenHomeomorph`: `piAffineChart I` identifies `X ∩ piAffineOpen I`
  homeomorphically with its coordinate image.
-/

public section

open Set Topology
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- Flatten a family of matrices `(i : ι) → Matrix (κ i) (μ i) α` to a single coordinate tuple
indexed by `Σ i, κ i × μ i`, as a homeomorphism for the entrywise product topologies. -/
def piMatrixHomeomorph {ι : Type*} (κ μ : ι → Type*) (α : Type*) [TopologicalSpace α] :
    ((i : ι) → Matrix (κ i) (μ i) α) ≃ₜ ((p : Σ i, κ i × μ i) → α) where
  toFun A p := A p.1 p.2.1 p.2.2
  invFun a i := Matrix.of fun j k ↦ a ⟨i, j, k⟩
  left_inv A := by
    ext i j k
    rfl
  right_inv a := by
    ext ⟨i, j, k⟩
    rfl
  continuous_toFun := continuous_pi fun p ↦ (continuous_apply p.1).matrix_elem p.2.1 p.2.2
  continuous_invFun := continuous_pi fun i ↦
    continuous_matrix fun j k ↦ continuous_apply (⟨i, j, k⟩ : Σ i, κ i × μ i)

@[simp]
theorem piMatrixHomeomorph_apply {ι : Type*} (κ μ : ι → Type*) (α : Type*) [TopologicalSpace α]
    (A : (i : ι) → Matrix (κ i) (μ i) α) (p : Σ i, κ i × μ i) :
    piMatrixHomeomorph κ μ α A p = A p.1 p.2.1 p.2.2 :=
  (rfl)

@[simp]
theorem piMatrixHomeomorph_symm_apply {ι : Type*} (κ μ : ι → Type*) (α : Type*)
    [TopologicalSpace α] (a : (p : Σ i, κ i × μ i) → α) (i : ι) (j : κ i) (k : μ i) :
    (piMatrixHomeomorph κ μ α).symm a i j k = a ⟨i, j, k⟩ :=
  (rfl)

end TauCeti

namespace Projectivization

section PiAffineOpen

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [T1Space K]
  {ι : Type*} [Finite ι] {κ : ι → Type*}

/-- For a finite index type `ι`, each standard product affine open of `(i : ι) → ℙ K (κ i → K)` is
open in the product topology. -/
theorem isOpen_piAffineOpen (I : ∀ i, κ i) : IsOpen (piAffineOpen (K := K) I) := by
  rw [piAffineOpen_def]
  exact isOpen_set_pi finite_univ fun i _ ↦ isOpen_affineOpen (I i)

end PiAffineOpen

section PiAffineChart

variable {K : Type*} [Field K] [TopologicalSpace K] {ι : Type*} {n : ι → ℕ}

/-- The inverse of a standard product affine chart is continuous. -/
theorem continuous_piAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    Continuous (piAffineChart (K := K) I).symm := by
  refine continuous_pi fun i ↦ ?_
  have hcoord : Continuous fun z : (Σ i, Fin (n i)) → K ↦ fun k ↦ z ⟨i, k⟩ :=
    continuous_pi fun k ↦ continuous_apply (⟨i, k⟩ : Σ i, Fin (n i))
  exact ((continuous_affineChart_symm (I i)).comp hcoord).congr fun z ↦
    (piAffineChart_symm_apply I z i).symm

variable [ContinuousMul K] [ContinuousInv₀ K]

/-- A standard product affine chart is continuous on its domain `piAffineOpen I`. -/
theorem continuousOn_piAffineChart (I : ∀ i, Fin (n i + 1)) :
    ContinuousOn (piAffineChart (K := K) I) (piAffineOpen I) := by
  rw [continuousOn_pi]
  rintro ⟨i, k⟩
  have hproj : ContinuousOn (fun p : (i : ι) → ℙ K (Fin (n i + 1) → K) ↦ p i) (piAffineOpen I) :=
    (continuous_apply i).continuousOn
  have hmaps : MapsTo (fun p : (i : ι) → ℙ K (Fin (n i + 1) → K) ↦ p i)
      (piAffineOpen I) (affineOpen (I i)) :=
    fun _ hp ↦ mem_piAffineOpen_iff.1 hp i
  exact (((continuous_apply k).continuousOn.comp (continuousOn_affineChart (I i))
    (mapsTo_univ _ _)).comp hproj hmaps).congr fun p _ ↦ piAffineChart_apply I p ⟨i, k⟩

/-- **The affine part of a subset of multiprojective space.** The standard product affine chart at
`I` restricts to a homeomorphism from `X ∩ piAffineOpen I` onto its coordinate image `Z` in
`(Σ i, Fin (n i)) → K`. -/
noncomputable def interPiAffineOpenHomeomorph
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z) :
    ↥(X ∩ piAffineOpen I) ≃ₜ Z :=
  ({ toPartialEquiv := piAffineChart I
     continuousOn_toFun := by simpa using continuousOn_piAffineChart I
     continuousOn_invFun := (continuous_piAffineChart_symm I).continuousOn } :
    PartialHomeomorph _ _).homeomorphOfImageSubsetSource (by simp) hZ

@[simp]
theorem coe_interPiAffineOpenHomeomorph_apply
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z)
    (y : ↥(X ∩ piAffineOpen I)) :
    (interPiAffineOpenHomeomorph hZ y : (Σ i, Fin (n i)) → K) = piAffineChart I y :=
  (rfl)

@[simp]
theorem coe_interPiAffineOpenHomeomorph_symm_apply
    {X : Set ((i : ι) → ℙ K (Fin (n i + 1) → K))} {I : ∀ i, Fin (n i + 1)}
    {Z : Set ((Σ i, Fin (n i)) → K)} (hZ : piAffineChart I '' (X ∩ piAffineOpen I) = Z)
    (z : Z) :
    ((interPiAffineOpenHomeomorph hZ).symm z : (i : ι) → ℙ K (Fin (n i + 1) → K)) =
      (piAffineChart I).symm z :=
  (rfl)

variable [T1Space K] [Finite ι]

/-- The standard product affine chart of `(i : ι) → ℙ K (Fin (n i + 1) → K)` at `I`, as an open
partial homeomorphism from `piAffineOpen I` onto `(Σ i, Fin (n i)) → K`. -/
noncomputable def piAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    OpenPartialHomeomorph ((i : ι) → ℙ K (Fin (n i + 1) → K)) ((Σ i, Fin (n i)) → K) where
  toPartialEquiv := piAffineChart I
  open_source := by simpa using isOpen_piAffineOpen I
  open_target := by simp
  continuousOn_toFun := by simpa using continuousOn_piAffineChart I
  continuousOn_invFun := (continuous_piAffineChart_symm I).continuousOn

@[simp]
theorem piAffineOpenPartialHomeomorph_toPartialEquiv (I : ∀ i, Fin (n i + 1)) :
    (piAffineOpenPartialHomeomorph (K := K) I).toPartialEquiv = piAffineChart I :=
  (rfl)

@[simp]
theorem coe_piAffineOpenPartialHomeomorph (I : ∀ i, Fin (n i + 1)) :
    ⇑(piAffineOpenPartialHomeomorph (K := K) I) = piAffineChart I :=
  (rfl)

@[simp]
theorem coe_piAffineOpenPartialHomeomorph_symm (I : ∀ i, Fin (n i + 1)) :
    ⇑(piAffineOpenPartialHomeomorph (K := K) I).symm = (piAffineChart I).symm :=
  (rfl)

/-- For finite `ι`, the inverse of a standard product affine chart is an open embedding onto
`piAffineOpen I`. -/
theorem isOpenEmbedding_piAffineChart_symm (I : ∀ i, Fin (n i + 1)) :
    IsOpenEmbedding (piAffineChart (K := K) I).symm :=
  coe_piAffineOpenPartialHomeomorph_symm (K := K) I ▸
    (piAffineOpenPartialHomeomorph (K := K) I).symm.isOpenEmbedding (by simp)

end PiAffineChart

end Projectivization
