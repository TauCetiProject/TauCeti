/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Tensoring with a product of an ideal and a submodule

Let `I` be an ideal of `R` and `J` a submodule of an `R`-module `N`. Tensoring the inclusion
`I • J ⊆ J` with a module `M` lands in `I • (M ⊗[R] J)`.

## Main results

* `LinearMap.range_lTensor_inclusion_smul_le`: the range of `M ⊗[R] (I • J) → M ⊗[R] J` is
  contained in `I • ⊤`.
-/

public section

open TensorProduct

namespace LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The image of `M ⊗[R] (I • J)` in `M ⊗[R] J` is contained in `I • (M ⊗[R] J)`. -/
theorem range_lTensor_inclusion_smul_le (I : Ideal R) (J : Submodule R N) :
    range ((Submodule.inclusion (Submodule.smul_le_right : I • J ≤ J)).lTensor M) ≤
      (I • ⊤ : Submodule R (M ⊗[R] J)) := by
  rintro _ ⟨u, rfl⟩
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add]; exact add_mem hu hv
  | tmul m y =>
    -- In `J`, the element `y` of `I • J` lies in `I • ⊤`, since `I • J` is the image of `I • ⊤`.
    have hy : (y : N) ∈ (I • ⊤ : Submodule R J).map J.subtype := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have hz' : Submodule.inclusion Submodule.smul_le_right y = z := Subtype.ext hzy.symm
    rw [lTensor_tmul, hz']
    have := Submodule.mem_map_of_mem (f := TensorProduct.mk R M J m) hz
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this

end LinearMap
