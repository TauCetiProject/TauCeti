/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Symmetric operators: negation and limits

Facts about symmetric operators complementing Mathlib's
`Mathlib.Analysis.InnerProductSpace.Symmetric`:

* the negative of a symmetric linear map is symmetric (`LinearMap.IsSymmetric.neg`), and
  conversely (`LinearMap.isSymmetric_neg_iff`);
* the symmetric bounded operators form a closed subset of `E →L[𝕜] E`
  (`ContinuousLinearMap.isClosed_setOf_isSymmetric`), so a limit of symmetric bounded operators
  is symmetric. No completeness of `E` is needed: the condition `⟪T x, y⟫ = ⟪x, T y⟫` is closed
  in `T` for each pair `x, y`.

The same argument applies to operators `A : D →L[𝕜] H` from a normed space into an inner product
space that are symmetric relative to a fixed `ι : D →L[𝕜] H`, in the sense that
`⟪A x, ι y⟫ = ⟪ι x, A y⟫`: a limit of such operators is again symmetric relative to `ι`
(`ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto`).
-/

public section

open Filter
open scoped InnerProductSpace Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- The negative of a symmetric linear map is symmetric. -/
theorem IsSymmetric.neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (-T).IsSymmetric := by
  simpa using IsSymmetric.zero.sub hT

/-- A linear map is symmetric if and only if its negative is. -/
@[simp]
theorem isSymmetric_neg_iff {T : E →ₗ[𝕜] E} : (-T).IsSymmetric ↔ T.IsSymmetric :=
  ⟨fun h ↦ neg_neg T ▸ h.neg, IsSymmetric.neg⟩

end LinearMap

namespace ContinuousLinearMap

/-- The symmetric bounded operators form a closed subset of `E →L[𝕜] E`. -/
theorem isClosed_setOf_isSymmetric :
    IsClosed {T : E →L[𝕜] E | (T : E →ₗ[𝕜] E).IsSymmetric} := by
  simp only [LinearMap.IsSymmetric, coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (by fun_prop) (by fun_prop)

/-- **Limits preserve symmetry relative to an embedding.** If operators `A s : D →L[𝕜] H`
satisfy `⟪A s x, ι y⟫ = ⟪ι x, A s y⟫` and converge to `B` along a nontrivial filter, then `B`
satisfies `⟪B x, ι y⟫ = ⟪ι x, B y⟫`. -/
theorem inner_apply_eq_inner_apply_of_tendsto {α D H : Type*} [SeminormedAddCommGroup D]
    [NormedSpace 𝕜 D] [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι : D →L[𝕜] H}
    {A : α → D →L[𝕜] H} {B : D →L[𝕜] H} {l : Filter α} [l.NeBot] (hA : Tendsto A l (𝓝 B))
    (hSymm : ∀ s x y, ⟪A s x, ι y⟫_𝕜 = ⟪ι x, A s y⟫_𝕜) (x y : D) :
    ⟪B x, ι y⟫_𝕜 = ⟪ι x, B y⟫_𝕜 :=
  (isClosed_eq (f := fun T : D →L[𝕜] H ↦ ⟪T x, ι y⟫_𝕜) (g := fun T ↦ ⟪ι x, T y⟫_𝕜)
    (by fun_prop) (by fun_prop)).mem_of_tendsto hA (.of_forall fun s ↦ hSymm s x y)

end ContinuousLinearMap
