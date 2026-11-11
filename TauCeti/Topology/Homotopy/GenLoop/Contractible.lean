/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Contractible spaces of generalized loops

If a space `E` contracts onto a point `e` through a homotopy fixing `e`, then applying this
homotopy pointwise contracts the space `Ω^ N E e` of generalized loops at `e`, with its
compact-open topology (`GenLoop.contractibleSpace_of_homotopyRel`). The basepoint must stay fixed
during the contraction: a homotopy that merely contracts `E` would move the loops off `e`.

A real topological vector space contracts onto any of its points along straight lines, which fix
that point, so its spaces of generalized loops are contractible.

## Main declarations

* `GenLoop.contractibleSpace_of_homotopyRel`: `Ω^ N E e` is contractible when the identity of `E`
  is homotopic to the constant map at `e` relative to `{e}`.
* The instance `GenLoop.contractibleSpace_of_module`: `Ω^ N E e` is contractible for a real
  topological vector space `E`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy

namespace GenLoop

variable {N E : Type*} [TopologicalSpace E] {e : E}

/-- **A contraction of a space onto a point fixing that point contracts its generalized loops.**
If the identity of `E` is homotopic to the constant map at `e` relative to `{e}`, then the space
`Ω^ N E e` of generalized loops at `e` is contractible. -/
theorem contractibleSpace_of_homotopyRel
    (H : (ContinuousMap.id E).HomotopyRel (ContinuousMap.const E e) {e}) :
    ContractibleSpace (Ω^ N E e) := by
  -- Apply `H` pointwise to a generalized loop; the result stays at `e` on the cube boundary
  -- because `H` fixes `e`.
  let K : C(I × Ω^ N E e, C(I^N, E)) :=
    ContinuousMap.curry ⟨fun q => H (q.1.1, q.1.2 q.2), by fun_prop⟩
  have hK (q : I × Ω^ N E e) (y : I^N) : K q y = H (q.1, q.2 y) := rfl
  refine (contractible_iff_id_nullhomotopic _).2 ⟨const, ⟨?_⟩⟩
  exact
    { toFun := fun q => ⟨K q, fun y hy => by
        rw [hK, boundary q.2 y hy]
        exact H.eq_fst q.1 rfl⟩
      continuous_toFun := K.continuous.subtype_mk _
      map_zero_left := fun γ => ext _ _ fun y => H.apply_zero (γ y)
      map_one_left := fun γ => ext _ _ fun y => H.apply_one (γ y) }

variable [AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The generalized loops in a real topological vector space are contractible, through the
straight-line contraction onto the basepoint. -/
instance contractibleSpace_of_module : ContractibleSpace (Ω^ N E e) :=
  contractibleSpace_of_homotopyRel
    { toFun := fun q => (q.1 : ℝ) • e + (1 - (q.1 : ℝ)) • q.2
      continuous_toFun := by fun_prop
      map_zero_left := fun z => by simp
      map_one_left := fun z => by simp
      prop' := fun t z hz => by
        rw [Set.mem_singleton_iff] at hz
        simp [hz, ← add_smul] }

end GenLoop
