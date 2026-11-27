/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.WeakDual.Annihilator
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Weak-star density and separation of points

For a topological module with separating continuous dual, a linear subspace of the dual is
weak-star dense exactly when its members separate points of the original space. This connects
weak-star approximation of functionals with scalar tests of vector-valued functions. The space
need not be complete or separable. The closure calculation uses the weak-star double-annihilator
theorem
`Submodule.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure`.

## References

* Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Set

namespace Submodule

variable {𝕜 X : Type*} [RCLike 𝕜] [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
  [SeparatingDual 𝕜 X]

/-- A linear family of continuous functionals is weak-star dense exactly when its common kernel
is zero. No completeness or separability assumption is needed. -/
theorem dense_toWeakDual_iff (Y : Submodule 𝕜 (StrongDual 𝕜 X)) :
    Dense (StrongDual.toWeakDual '' (Y : Set (StrongDual 𝕜 X))) ↔
      ∀ x : X, (∀ y ∈ Y, y x = 0) → x = 0 := by
  constructor
  · intro hY x hx
    have hzero : ∀ y : WeakDual 𝕜 X, y x = 0 := by
      intro y
      exact (isClosed_eq (WeakDual.eval_continuous x) continuous_const).closure_subset_iff.2
        (by
          rintro _ ⟨z, hz, rfl⟩
          simpa only [Set.mem_ofPred_eq, StrongDual.toWeakDual_apply] using hx z hz) (hY y)
    exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun y ↦ by
      simpa only [StrongDual.toWeakDual_apply] using hzero (StrongDual.toWeakDual y)
  · intro hY
    have hker : Y.orthogonalBilin (topDualPairing 𝕜 X) = ⊥ := by
      apply eq_bot_iff.2
      intro x hx
      exact hY x (by simpa only [mem_orthogonalBilin, topDualPairing_apply] using hx)
    rw [← LinearEquiv.coe_coe StrongDual.toWeakDual,
      ← Submodule.map_coe,
      Submodule.dense_iff_topologicalClosure_eq_top,
      ← Y.map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure, hker,
      orthogonalBilin_bot, map_top]
    exact LinearMap.range_eq_top.2 StrongDual.toWeakDual.surjective

end Submodule
