/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake.Composition

/-!
# Fredholm criterion for the composition snake diagram

This module proves `ContinuousLinearMap.isFredholm_compSnakeMiddle_iff`: the middle vertical
operator `compSnakeMiddle T S` of the composition snake diagram is Fredholm if and only if the
composite `S ∘L T` is Fredholm. Together with `ContinuousLinearMap.index_compSnakeMiddle` and
`ContinuousLinearMap.IsFredholm.index_eq_add_of_exact`, this recovers index additivity under
composition along a snake diagram.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1.
* Mathlib's `CategoryTheory.kernelCokernelCompSequence`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]

/-- `compSnakeMiddle T S` is Fredholm if and only if the composite `S ∘L T` is Fredholm. Combined
with `index_compSnakeMiddle` and `index_upperTriangularBlock`, applying the snake index theorem to
`(T, compSnakeMiddle T S, S)` directly recovers `IsFredholm.index_comp`:
`(S ∘L T).index = (compSnakeMiddle T S).index = T.index + S.index = S.index + T.index`. -/
@[simp] theorem isFredholm_compSnakeMiddle_iff (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (compSnakeMiddle T S).IsFredholm ↔ (S ∘L T).IsFredholm := by
  have hconj : (S.compSnakeMiddleCodEquiv.symm : F × G →L[𝕜] F × G) ∘L compSnakeMiddle T S =
      ((ContinuousLinearMap.id 𝕜 F).prodMap (S ∘L T)) ∘L
        (T.compSnakeMiddleDomEquiv : E × F →L[𝕜] F × E) := by
    rw [T.compSnakeMiddle_eq_comp_prodMap_comp S]
    ext x <;> simp
  rw [isFredholm_iff_of_comp_eq T.compSnakeMiddleDomEquiv S.compSnakeMiddleCodEquiv.symm hconj,
    isFredholm_prodMap_iff]
  exact ⟨And.right, fun hST ↦ ⟨.id, hST⟩⟩

end ContinuousLinearMap
