/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Scalar extension of dual lattices

Let `A → K` and `A' → K'` be maps from rings to fields, with compatible maps `A → A'` and
`K → K'`. A lattice spanned over `A` by a `K`-basis becomes the `A'`-span of its image
in `K' ⊗[K] V`. Taking its dual for a nondegenerate bilinear form commutes with this
extension. No flatness of `A'` over `A` is required: the assertion follows from the
dual bases over the two fields.

Applied to a trace form, this compares complementary modules under scalar extension,
including the semilocal scalar extensions used to study differents at completed places.
-/

public section

open Module LinearMap
open scoped TensorProduct

namespace LinearMap.BilinForm

variable {K K' V ι : Type*} [Field K] [Field K'] [Algebra K K']
  [AddCommGroup V] [Module K V] [Finite ι] [DecidableEq ι]

/-- The dual basis of a scalar-extended form is the scalar extension of its dual basis. -/
@[simp]
theorem dualBasis_baseChange (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) :
    (B.baseChange K').dualBasis (hB.baseChange K') (b.baseChange K') =
      (B.dualBasis hB b).baseChange K' := by
  apply DFunLike.coe_injective
  apply (dualBasis_eq_iff _ _ _).mpr
  intro i j
  simp [apply_dualBasis_left]

variable {A A' : Type*} [CommRing A] [CommRing A']
  [Algebra A K] [Algebra A A'] [Algebra A K'] [Algebra A' K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  [Module A V] [IsScalarTower A K V]

omit [DecidableEq ι] in
/-- The dual of a lattice commutes with extending scalars, when the lattice is spanned
by a basis of its ambient vector space. The extension is taken inside `K' ⊗[K] V`. -/
theorem dualSubmodule_baseChange_of_basis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule A V) (b : Basis ι K V) (hb : N = Submodule.span A (Set.range b)) :
    (B.baseChange K').dualSubmodule
        (Submodule.span A' ((fun x : V ↦ (1 : K') ⊗ₜ[K] x) '' (N : Set V))) =
      Submodule.span A' ((fun x : V ↦ (1 : K') ⊗ₜ[K] x) ''
        (B.dualSubmodule N : Set V)) := by
  classical
  have hspan (s : Set V) :
      Submodule.span A' ((fun x : V ↦ (1 : K') ⊗ₜ[K] x) '' Submodule.span A s) =
        Submodule.span A' ((fun x : V ↦ (1 : K') ⊗ₜ[K] x) '' s) := by
    let f : V →ₗ[A] K' ⊗[K] V := (TensorProduct.mk K K' V 1).restrictScalars A
    rw [show (fun x : V ↦ (1 : K') ⊗ₜ[K] x) = f from rfl, ← Submodule.map_coe,
      Submodule.map_span, Submodule.span_span_of_tower]
  rw [hb, dualSubmodule_span_of_basis B hB, hspan, hspan]
  simp only [← Set.range_comp, Function.comp_def, ← Basis.baseChange_apply]
  rw [dualSubmodule_span_of_basis _ (hB.baseChange K'), dualBasis_baseChange]

end LinearMap.BilinForm
