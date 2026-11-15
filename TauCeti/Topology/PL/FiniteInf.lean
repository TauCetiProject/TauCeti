/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map

/-!
# Finite minima of affine functionals

A finite minimum of continuous affine functionals is piecewise affine.  The cells are the
polyhedra on which a fixed functional is no larger than every member of the finite family.
This is the chart calculation used by the inverse of a barycentric stellar identification: the
amount transferred from a starred face is its least barycentric coordinate.

The construction is the standard polyhedral decomposition from Rourke--Sanderson,
*Introduction to Piecewise-Linear Topology*, Chapter 1.  It supplies the affine charts needed
for PL compatibility of barycentric stellar identifications.
-/

public section

open Set Filter Topology TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

namespace Finset

/-- The cell on which the affine functional indexed by `i` is a minimum on `s`. -/
def infCell {ι : Type*} (s : Finset ι) (f : ι → (E →ᴬ[ℝ] ℝ)) (i : s) : Set E :=
  {x | ∀ j ∈ s, f i x ≤ f j x}

@[simp] theorem mem_infCell_iff {ι : Type*} (s : Finset ι) (f : ι → (E →ᴬ[ℝ] ℝ)) (i : s)
    (x : E) : x ∈ s.infCell f i ↔ ∀ j ∈ s, f i x ≤ f j x :=
  Iff.rfl

/-- A finite-minimum cell is an intersection of affine half-spaces. -/
theorem isConvexPolyhedron_infCell {ι : Type*} (s : Finset ι)
    (f : ι → (E →ᴬ[ℝ] ℝ)) (i : s) :
    TauCeti.IsConvexPolyhedron (s.infCell f i) := by
  have heq : s.infCell f i = {x | ∀ j : s, (f i - f j) x ≤ 0} := by
    ext x
    simp [infCell]
  rw [heq]
  exact TauCeti.isConvexPolyhedron_setOf_forall _

/-- The cells of a finite family cover the whole source space. -/
theorem subset_iUnion_infCell {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    (Set.univ : Set E) ⊆ ⋃ i : s, s.infCell f i := by
  intro x _
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun j => f j x) hs
  refine mem_iUnion.2 ⟨⟨i, hi⟩, ?_⟩
  exact hmin

/-- The finite affine infimum agrees with the active functional on its cell. -/
theorem infAffine_eq_of_mem_infCell {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) (i : s) {x : E} (hx : x ∈ s.infCell f i) :
    s.inf' hs (fun j => f j x) = f i x := by
  apply le_antisymm
  · exact s.inf'_le _ i.2
  · exact s.le_inf' hs _ (fun j hj => hx j hj)

/-- A finite minimum of continuous affine functionals is piecewise affine on the whole source. -/
theorem isPLOn_infAffine {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → (E →ᴬ[ℝ] ℝ)) :
    IsPLOn (fun x => s.inf' hs (fun i => f i x)) (Set.univ : Set E) := by
  let C : s → Set E := s.infCell f
  have hC : ∀ i, IsConvexPolyhedron (C i) := by
    intro i
    exact s.isConvexPolyhedron_infCell f i
  have hcov : (Set.univ : Set E) ⊆ ⋃ i, C i := by
    exact s.subset_iUnion_infCell hs f
  refine (isPiecewiseAffineOn_of_finite (C := C) (A := fun i => f i)
    hC hcov ?_).isPLOn
  intro i x hx
  exact s.infAffine_eq_of_mem_infCell hs f i hx.2

end Finset
