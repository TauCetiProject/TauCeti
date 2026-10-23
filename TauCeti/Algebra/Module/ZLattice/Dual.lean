/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# The dual lattice in a real inner product space

For a `ℤ`-submodule `L` of a real inner product space `E`, the *dual lattice*

`L^∨ = {x ∈ E | ⟪x, y⟫ ∈ ℤ for all y ∈ L}`

is Mathlib's `BilinForm.dualSubmodule` of the inner product `innerₗ E`, with `ℤ` as
the ring of coefficients. This file names that submodule `ZLattice.dual` and develops the part of
its theory that holds for a full lattice in a finite-dimensional space: the dual of a full lattice
is again a full lattice (`ZLattice.dual` carries `DiscreteTopology` and `IsZLattice` instances),
and taking the dual twice gives the lattice back (`ZLattice.dual_dual`).

Both facts come from the dual-basis description of Mathlib: the dual of the `ℤ`-span of an
`ℝ`-basis `b` is the `ℤ`-span of the basis dual to `b` for the inner product
(`ZLattice.dual_span_basis`), and a full lattice is the `ℤ`-span of an `ℝ`-basis. In particular the
`ℤ`-span of an orthonormal basis is its own dual (`ZLattice.dual_span_orthonormalBasis`), the
self-duality of `ℤⁿ ⊆ ℝⁿ`.

The dual is antitone, and it commutes with pulling a lattice back along a linear isometry
equivalence (`ZLattice.dual_comap`), so every notion defined from it is an isometry invariant.
Along a general continuous linear equivalence `e` of complete spaces the dual is pulled back along
the adjoint of `e⁻¹` instead (`ZLattice.dual_comap_continuousLinearEquiv`): the dual of `A L` is
`(A⁻¹)ᵀ L^∨`, the transport of dual lattices under a linear change of variables.

This is the dual lattice entering Poisson summation over a lattice, and the integrality,
evenness and unimodularity of a lattice in `TauCeti/Algebra/Module/ZLattice/Integral.lean` are
defined from it.

## Main definitions

* `ZLattice.dual L`: the dual of `L : Submodule ℤ E` with respect to the inner product.

## Notation

* `L^∨`: the dual lattice `ZLattice.dual L`, scoped in `ZLattice`.

## Main statements

* `ZLattice.mem_dual`: `x ∈ dual L` if and only if `⟪x, y⟫` is an integer for every `y ∈ L`.
* `ZLattice.dual_span_basis`: the dual of the `ℤ`-span of an `ℝ`-basis is the `ℤ`-span of its
  dual basis.
* `ZLattice.dual_span_orthonormalBasis`: the `ℤ`-span of an orthonormal basis is self-dual.
* `ZLattice.dual_dual`: the dual of the dual of a full lattice is the lattice itself.
* `ZLattice.dual_comap`: the dual commutes with pulling back along a linear isometry equivalence.
* `ZLattice.dual_comap_continuousLinearEquiv`: the dual of the pullback along a continuous linear
  equivalence `e` is the pullback of the dual along the adjoint of `e⁻¹`.
-/

public section

open Module Submodule
open LinearMap (BilinForm)
open scoped RealInnerProductSpace

universe u

namespace ZLattice

variable {E : Type u} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The dual lattice of `L : Submodule ℤ E`: the vectors whose inner product with every vector of
`L` is an integer. It is Mathlib's `BilinForm.dualSubmodule` of the inner product. -/
noncomputable def dual (L : Submodule ℤ E) : Submodule ℤ E :=
  BilinForm.dualSubmodule (innerₗ E) L

@[inherit_doc] scoped notation:max L "^∨" => ZLattice.dual L

theorem dual_def (L : Submodule ℤ E) : dual L = BilinForm.dualSubmodule (innerₗ E) L :=
  (rfl)

/-- A vector lies in the dual lattice exactly when its inner product with every vector of `L` is
an integer. -/
@[simp]
theorem mem_dual {L : Submodule ℤ E} {x : E} : x ∈ dual L ↔ ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫ = m := by
  simp only [dual_def, BilinForm.mem_dualSubmodule, Submodule.mem_one, innerₗ_apply_apply,
    algebraMap_int_eq, eq_intCast, eq_comm]

/-- Taking duals reverses inclusions. -/
theorem dual_anti {L M : Submodule ℤ E} (h : L ≤ M) : dual M ≤ dual L :=
  fun _ hx y hy ↦ hx y (h hy)

/-- `L` lies in the dual of `M` if and only if `M` lies in the dual of `L`: both say that `L` and
`M` pair integrally. -/
theorem le_dual_comm {L M : Submodule ℤ E} : L ≤ dual M ↔ M ≤ dual L := by
  have h : BilinForm.flip (innerₗ E) = innerₗ E := flip_innerₗ E
  rw [dual_def, dual_def, ← BilinForm.le_flip_dualSubmodule, h]

/-- Every lattice is contained in the dual of its dual. Equality holds for a full lattice in a
finite-dimensional space, `dual_dual`. -/
theorem le_dual_dual (L : Submodule ℤ E) : L ≤ dual (dual L) :=
  le_dual_comm.mpr le_rfl

/-- The dual of the `ℤ`-span of an `ℝ`-basis is the `ℤ`-span of the dual basis for the inner
product. -/
theorem dual_span_basis {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dual (span ℤ (Set.range b)) =
      span ℤ (Set.range (BilinForm.dualBasis (innerₗ E) TauCeti.nondegenerate_inner b)) :=
  BilinForm.dualSubmodule_span_of_basis (innerₗ E) TauCeti.nondegenerate_inner b

/-- The `ℤ`-span of an orthonormal basis is its own dual. -/
@[simp]
theorem dual_span_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    dual (span ℤ (Set.range b)) = span ℤ (Set.range b) := by
  classical
  have hb :
      BilinForm.dualBasis (innerₗ E) TauCeti.nondegenerate_inner b.toBasis = ⇑b := by
    rw [BilinForm.dualBasis_eq_iff]
    intro i j
    rw [innerₗ_apply_apply, OrthonormalBasis.coe_toBasis, b.inner_eq_ite]
    simp only [eq_comm]
  rw [← b.coe_toBasis, dual_span_basis, hb, b.coe_toBasis]

/-- The dual commutes with pulling a lattice back along a linear isometry equivalence. -/
@[simp]
theorem dual_comap (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) :
    dual (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) =
      ZLattice.comap ℝ (dual L) e.toLinearEquiv.toLinearMap := by
  ext x
  simp only [mem_comap, mem_dual, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  refine ⟨fun h z hz ↦ ?_, fun h y hy ↦ e.inner_map_map x y ▸ h _ hy⟩
  obtain ⟨m, hm⟩ := h (e.symm z) (by rwa [e.apply_symm_apply])
  exact ⟨m, by rwa [← e.inner_map_map, e.apply_symm_apply] at hm⟩

/-- The dual of the pullback of a lattice along a continuous linear equivalence `e` is the
pullback of the dual along the adjoint of `e⁻¹`. Read through images, the dual of `A L` is
`(A⁻¹)ᵀ L^∨` for a linear automorphism `A`. -/
@[simp]
theorem dual_comap_continuousLinearEquiv [CompleteSpace E] [CompleteSpace F] (L : Submodule ℤ E)
    (e : F ≃L[ℝ] E) :
    dual (ZLattice.comap ℝ L e.toLinearMap) =
      ZLattice.comap ℝ (dual L) (ContinuousLinearMap.adjoint (e.symm : E →L[ℝ] F)).toLinearMap := by
  ext x
  simp only [mem_comap, mem_dual, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearMap.coe_coe]
  refine ⟨fun h y hy ↦ ?_, fun h z hz ↦ ?_⟩
  · obtain ⟨m, hm⟩ := h (e.symm y) (by simpa using hy)
    exact ⟨m, by rwa [ContinuousLinearMap.adjoint_inner_left]⟩
  · obtain ⟨m, hm⟩ := h (e z) hz
    exact ⟨m, by simpa [ContinuousLinearMap.adjoint_inner_left] using hm⟩

section FiniteDimensional

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

instance : DiscreteTopology (dual L) := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  rw [dual_span_basis]
  infer_instance

instance : IsZLattice ℝ (dual L) where
  span_top := by
    obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
    rw [dual_span_basis]
    exact ZSpan.span_top _

/-- The dual of the dual of a full lattice in a finite-dimensional space is the lattice. -/
@[simp]
theorem dual_dual : dual (dual L) = L := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  exact BilinForm.dualSubmodule_dualSubmodule_of_basis (innerₗ E)
    TauCeti.nondegenerate_inner (BilinForm.isSymm_iff.mpr isSymm_inner) b

end FiniteDimensional

end ZLattice
