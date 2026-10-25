/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Pointwise operations on the weak dual

The addition and the scalar actions on `WeakDual 𝕜 E` are those of `E →L[𝕜] 𝕜`, so they are
computed pointwise. Registering `IsAddApply` and `IsSMulApply` makes the generic simp lemmas
`add_apply` and `smul_apply` available on `WeakDual 𝕜 E`, so that pointwise computations, such
as convex combinations of functionals, need not pass through `WeakDual.toStrongDual` or unfold
the type synonym.

It also records that, for ordered `E` and `𝕜`, the functionals that are nonnegative on
nonnegative elements form a weak-* closed set, `WeakDual.isClosed_setOf_map_nonneg`.
-/

public section

namespace WeakDual

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

instance instIsAddApply : IsAddApply (WeakDual 𝕜 E) where

instance instIsSMulApply (M : Type*) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : IsSMulApply M (WeakDual 𝕜 E) where

/-- The functionals that are nonnegative on nonnegative elements form a weak-* closed set. -/
theorem isClosed_setOf_map_nonneg [Preorder 𝕜] [ClosedIciTopology 𝕜] [LE E] :
    IsClosed {φ : WeakDual 𝕜 E | ∀ a, 0 ≤ a → 0 ≤ φ a} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_Ici.preimage (eval_continuous a)

end WeakDual
