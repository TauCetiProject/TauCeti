/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.HomotopyInvariance

/-!
# Homotopy invariance of pullbacks of finite-rank bundle cores

Over a paracompact R₁ base `X`, for instance a paracompact Hausdorff space, the pullbacks of a
finite-rank bundle core `A : FiniteRankBundleCore 𝕜 Y` along homotopic maps `f₀ f₁ : C(X, Y)` are
isomorphic in the category of finite-rank cores
(`TauCeti.FiniteRankBundleCore.nonempty_pullback_iso_pullback_of_homotopic`), and hence the pullback
of rank-`n` isomorphism classes depends only on the homotopy class of the map
(`TauCeti.FiniteRankBundleCore.pullbackRankClass_eq_of_homotopic`). The scalars `𝕜` form a complete
normed `ℝ`-algebra, such as `ℝ` or `ℂ`.

The isomorphism is the native-bundle cylinder transport
`ContinuousMap.Homotopic.exists_continuousLinearEquiv_pullback`, read in the preferred coordinates
of the pulled-back cores through `TauCeti.FiniteRankBundleCore.pullbackHomeomorph`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Theorem 1.6.
-/

public section

open Bundle CategoryTheory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {X : Type*} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type*} [TopologicalSpace Y]

/-- **Homotopy invariance of finite-rank cores.** Over a paracompact R₁ base, the pullbacks of a
finite-rank core along homotopic maps are isomorphic. -/
theorem nonempty_pullback_iso_pullback_of_homotopic (A : FiniteRankBundleCore 𝕜 Y)
    {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) : Nonempty (A.pullback f₀ ≅ A.pullback f₁) := by
  obtain ⟨Φ, hΦ, -⟩ := h.exists_continuousLinearEquiv_pullback (𝕜 := 𝕜)
    (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  refine ⟨isoOfContinuousEquiv Φ <| ((A.pullbackHomeomorph f₁).symm.continuous.comp <|
    hΦ.comp (A.pullbackHomeomorph f₀).continuous).congr fun p ↦ ?_⟩
  rw [Function.comp_apply, Function.comp_apply, pullbackHomeomorph_apply,
    pullbackHomeomorph_symm_apply]
  -- Both sides are `⟨p.proj, Φ p.proj p.snd⟩`: the fibre `(A.pullback f).core.Fiber x` of the
  -- pulled-back core and the fibre `((⇑f) *ᵖ A.core.Fiber) x` of Mathlib's pullback bundle both
  -- unfold to `Fin A.rank → 𝕜`, so the two total-space points agree by definition.
  rfl

/-- Pullback of rank-`n` isomorphism classes of finite-rank cores along a map out of a paracompact
R₁ base depends only on the homotopy class of the map. -/
theorem pullbackRankClass_eq_of_homotopic {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) (n : ℕ) :
    pullbackRankClass (𝕜 := 𝕜) f₀ n = pullbackRankClass f₁ n := by
  funext c
  induction c using Quotient.inductionOn with
  | h A =>
    obtain ⟨e⟩ := A.val.nonempty_pullback_iso_pullback_of_homotopic (𝕜 := 𝕜) h
    rw [pullbackRankClass_mk, pullbackRankClass_mk]
    exact Quotient.sound ⟨e⟩

end TauCeti.FiniteRankBundleCore
