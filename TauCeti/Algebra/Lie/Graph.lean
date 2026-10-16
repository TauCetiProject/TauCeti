/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Prod

/-!
# Graphs of Lie algebra homomorphisms

This file packages the graph of a Lie algebra homomorphism as a Lie subalgebra of the product.
The underlying submodule is `LinearMap.graph`; preservation of the Lie bracket is exactly the
condition that the map is a Lie algebra homomorphism.

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
    change x.2 = f x.1 at hx
    change y.2 = f y.1 at hy
    change ⁅x.2, y.2⁆ = f ⁅x.1, y.1⁆
    rw [hx, hy, f.map_lie]

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
@[expose]
def graphEquiv (f : L →ₗ⁅R⁆ L₂) : L ≃ₗ⁅R⁆ f.graph where
  toFun x := ⟨(x, f x), by simp⟩
  invFun x := x.1.1
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp
  map_lie' {x y} := by
    apply Subtype.ext
    simp
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((mem_graph_iff f x).mp x.property).symm

/-- The canonical equivalence to the graph sends `x` to `(x, f x)`. -/
@[simp]
theorem coe_graphEquiv_apply (f : L →ₗ⁅R⁆ L₂) (x : L) :
    (f.graphEquiv x : L × L₂) = (x, f x) :=
  rfl

/-- The inverse of the canonical equivalence to the graph is first-coordinate projection. -/
@[simp]
theorem graphEquiv_symm_apply (f : L →ₗ⁅R⁆ L₂) (x : f.graph) :
    f.graphEquiv.symm x = x.1.1 :=
  rfl

end LieHom
