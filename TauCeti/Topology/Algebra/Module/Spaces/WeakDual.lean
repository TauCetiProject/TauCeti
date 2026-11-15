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
the type synonym. Likewise, `WeakDual.instIsScalarTower` transfers a scalar tower `R`, `S` of
actions on `𝕜` to `WeakDual 𝕜 E`; over `RCLike 𝕜` it makes the real action on the weak dual
compatible with the `𝕜`-action.

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

/-- Scalar actions on `𝕜` that form a scalar tower induce a scalar tower on `WeakDual 𝕜 E`. For
`RCLike 𝕜` this makes the real action on `WeakDual 𝕜 E` compatible with the `𝕜`-action. -/
instance instIsScalarTower {R S : Type*} [Monoid R] [Monoid S] [SMul R S]
    [DistribMulAction R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜]
    [DistribMulAction S 𝕜] [SMulCommClass 𝕜 S 𝕜] [ContinuousConstSMul S 𝕜]
    [IsScalarTower R S 𝕜] : IsScalarTower R S (WeakDual 𝕜 E) :=
  inferInstanceAs (IsScalarTower R S (StrongDual 𝕜 E))

/-- The functionals that are nonnegative on nonnegative elements form a weak-* closed set. -/
theorem isClosed_setOf_map_nonneg [Preorder 𝕜] [ClosedIciTopology 𝕜] [LE E] :
    IsClosed {φ : WeakDual 𝕜 E | ∀ a, 0 ≤ a → 0 ≤ φ a} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_Ici.preimage (eval_continuous a)

end WeakDual
