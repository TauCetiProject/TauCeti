/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod

/-!
# Graphs of Lie algebra homomorphisms

This file packages the graph of a Lie algebra homomorphism as a Lie subalgebra of the product.
The underlying submodule is `LinearMap.graph`; preservation of the Lie bracket is exactly the
condition that the map is a Lie algebra homomorphism.

The API follows Mathlib's `MonoidHom.graph` and Tau Ceti's `MonoidHomClass.graphEquiv`
formalizations for group homomorphisms.

## Main definitions

* `LieHom.graph`: the graph of a Lie algebra homomorphism as a Lie subalgebra.
* `LieHom.graphEquiv`: the canonical Lie equivalence from the source to the graph.

## Main results

* `LieHom.mem_graph_iff`: membership in the graph is equality with the image.
* `LieHom.graph_eq_range_prod`: the graph is the range of the product of the identity with the map.
-/

public section

universe u v w

variable {R : Type u} {L : Type v} {L₂ : Type w}
variable [CommRing R]
variable [LieRing L] [LieAlgebra R L]
variable [LieRing L₂] [LieAlgebra R L₂]

namespace LieHom

/-- The graph of a Lie algebra homomorphism, as a Lie subalgebra of the product. -/
def graph (f : L →ₗ⁅R⁆ L₂) : LieSubalgebra R (L × L₂) where
  toSubmodule := f.toLinearMap.graph
  lie_mem' {x y} hx hy := by
    simp only [LinearMap.graph, Set.mem_ofPred_eq, LieAlgebra.Prod.bracket_apply] at hx hy ⊢
    rw [hx, hy]
    exact (f.map_lie x.1 y.1).symm

/-- A pair belongs to the graph exactly when its second coordinate is the image of its first. -/
@[simp]
theorem mem_graph_iff (f : L →ₗ⁅R⁆ L₂) (x : L × L₂) :
    x ∈ f.graph ↔ x.2 = f x.1 :=
  Iff.rfl

/-- The graph of a Lie algebra homomorphism is the range of the product of the identity with
the homomorphism. -/
theorem graph_eq_range_prod (f : L →ₗ⁅R⁆ L₂) :
    f.graph = (LieHom.prod LieHom.id f).range := by
  rw [← LieSubalgebra.toSubmodule_inj]
  exact LinearMap.graph_eq_range_prod f.toLinearMap

/-- A Lie algebra is naturally equivalent to the graph of any homomorphism out of it. -/
noncomputable def graphEquiv (f : L →ₗ⁅R⁆ L₂) : L ≃ₗ⁅R⁆ f.graph :=
  ((LieHom.prod LieHom.id f).equivRangeOfInjective (by
      intro x y h
      exact congrArg Prod.fst h)).trans
    (LieEquiv.ofEq _ _
      (congrArg (fun s : LieSubalgebra R (L × L₂) ↦ (s : Set (L × L₂)))
        f.graph_eq_range_prod).symm)

/-- The canonical equivalence to the graph sends `x` to `(x, f x)`. -/
@[simp]
theorem coe_graphEquiv_apply (f : L →ₗ⁅R⁆ L₂) (x : L) :
    (f.graphEquiv x : L × L₂) = (x, f x) := by
  rw [graphEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  exact congrArg Subtype.val
    (LieHom.equivRangeOfInjective_apply (LieHom.prod LieHom.id f) _ x)

/-- The inverse of the canonical equivalence to the graph is first-coordinate projection. -/
@[simp]
theorem graphEquiv_symm_apply (f : L →ₗ⁅R⁆ L₂) (x : f.graph) :
    f.graphEquiv.symm x = x.1.1 := by
  have h := congrArg (fun y : f.graph ↦ (y : L × L₂).1)
    (f.graphEquiv.apply_symm_apply x)
  simpa only [coe_graphEquiv_apply] using h

end LieHom
