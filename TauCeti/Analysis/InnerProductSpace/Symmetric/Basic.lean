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

The same argument applies to operators `A : D →L[𝕜] H` from a topological vector space into an
inner product space that are symmetric relative to a fixed continuous linear map
`ι : D →L[𝕜] H`, in the sense that `⟪A x, ι y⟫ = ⟪ι x, A y⟫`. For a pair `x, y`, the operators
satisfying this identity form a closed set
(`ContinuousLinearMap.isClosed_setOf_inner_apply_eq_inner_apply`), so if operators converge along
a filter and satisfy the identity for `x, y` frequently along it, so does their limit
(`ContinuousLinearMap.inner_apply_eq_inner_apply_of_tendsto`); and if an operator satisfies it
for `x, y`, so does its negative (`ContinuousLinearMap.inner_neg_apply_eq_inner_neg_apply`).
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
theorem isSymmetric_neg_iff (T : E →ₗ[𝕜] E) : (-T).IsSymmetric ↔ T.IsSymmetric :=
  ⟨fun h ↦ neg_neg T ▸ h.neg, IsSymmetric.neg⟩

end LinearMap

namespace ContinuousLinearMap

/-- **The identity `⟪T x, ι y⟫ = ⟪ι x, T y⟫` is closed in `T`.** For a fixed continuous linear map
`ι : D →L[𝕜] H` and a pair `x, y : D`, the operators `T : D →L[𝕜] H` with
`⟪T x, ι y⟫ = ⟪ι x, T y⟫` form a closed subset of `D →L[𝕜] H`. -/
theorem isClosed_setOf_inner_apply_eq_inner_apply {D H : Type*} [AddCommGroup D]
    [TopologicalSpace D] [Module 𝕜 D] [ContinuousSMul 𝕜 D] [SeminormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (ι : D →L[𝕜] H) (x y : D) :
    IsClosed {T : D →L[𝕜] H | ⟪T x, ι y⟫_𝕜 = ⟪ι x, T y⟫_𝕜} :=
  isClosed_eq (by fun_prop) (by fun_prop)

/-- The symmetric bounded operators form a closed subset of `E →L[𝕜] E`. -/
theorem isClosed_setOf_isSymmetric :
    IsClosed {T : E →L[𝕜] E | (T : E →ₗ[𝕜] E).IsSymmetric} := by
  simp only [LinearMap.IsSymmetric, coe_coe, Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_setOf_inner_apply_eq_inner_apply (.id 𝕜 E) x y

/-- **Limits preserve symmetry relative to a continuous linear map.** Fix a continuous linear map
`ι : D →L[𝕜] H` and `x y : D`. If operators `A s : D →L[𝕜] H` converge to `B` along a filter `l`
and satisfy `⟪A s x, ι y⟫ = ⟪ι x, A s y⟫` for `s` frequently along `l`, then `B` satisfies
`⟪B x, ι y⟫ = ⟪ι x, B y⟫`. -/
theorem inner_apply_eq_inner_apply_of_tendsto {α D H : Type*} [AddCommGroup D]
    [TopologicalSpace D] [Module 𝕜 D] [ContinuousSMul 𝕜 D] [SeminormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {ι : D →L[𝕜] H} {A : α → D →L[𝕜] H} {B : D →L[𝕜] H} {l : Filter α}
    {x y : D} (hA : Tendsto A l (𝓝 B))
    (hSymm : ∃ᶠ s in l, ⟪A s x, ι y⟫_𝕜 = ⟪ι x, A s y⟫_𝕜) :
    ⟪B x, ι y⟫_𝕜 = ⟪ι x, B y⟫_𝕜 :=
  (isClosed_setOf_inner_apply_eq_inner_apply ι x y).mem_of_frequently_of_tendsto hSymm hA

/-- **Negation preserves symmetry relative to a continuous linear map.** Fix a continuous linear
map `ι : D →L[𝕜] H` and `x y : D`. If `B : D →L[𝕜] H` satisfies `⟪B x, ι y⟫ = ⟪ι x, B y⟫`, then
so does `-B`. -/
theorem inner_neg_apply_eq_inner_neg_apply {D H : Type*} [AddCommGroup D] [TopologicalSpace D]
    [Module 𝕜 D] [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι B : D →L[𝕜] H}
    {x y : D} (hB : ⟪B x, ι y⟫_𝕜 = ⟪ι x, B y⟫_𝕜) : ⟪(-B) x, ι y⟫_𝕜 = ⟪ι x, (-B) y⟫_𝕜 := by
  simp only [neg_apply, inner_neg_left, inner_neg_right, hB]

end ContinuousLinearMap
