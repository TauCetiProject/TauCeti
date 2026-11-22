/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Finite-rank bundle core presentation of the tangent bundle

Let `M` be a `C^1` manifold modelled on `I : ModelWithCorners 𝕜 E H`, equipped with a finite
basis `b : Module.Basis (Fin r) 𝕜 E` of its model space. Applying
`TauCeti.FiniteRankBundleCore.ofBundle` to `b.equivFunL` and `TangentSpace I` presents the
tangent bundle `TangentBundle I M` as a point-indexed finite-rank bundle core
`TauCeti.tangentFiniteRankCore I M b` of rank `r`.

## Main declarations

* `TauCeti.tangentFiniteRankCore`: the finite-rank core presenting `TangentSpace I`.
* `TauCeti.isContMDiff_tangentFiniteRankCore`: on a `C^(n+1)` manifold,
  `tangentFiniteRankCore I M b` is a `C^n` core.
* `TauCeti.coordChange_tangentFiniteRankCore`: its transitions are `tangentCoordChange I x₀ x₁ x`
  conjugated by `b.equivFunL`.
* `TauCeti.tangentFiniteRankCoreTotalSpaceDiffeomorph`: canonical `C^n` diffeomorphism identifying
  `(tangentFiniteRankCore I M b).core.TotalSpace` with `TangentBundle I M`, sending `⟨x, v⟩` to
  `⟨x, b.equivFunL.symm v⟩` and `⟨x, Pi.single i 1⟩` to `⟨x, b i⟩`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §3.
-/

public section

open Bundle CategoryTheory FiberBundle Module Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section TangentFiniteRank

variable [IsManifold I 1 M] {r : ℕ}

variable (I M) in
/-- The finite-rank bundle core presenting the tangent bundle `TangentSpace I` of `M`, using a
model-space basis `b : Basis (Fin r) 𝕜 E`. -/
noncomputable abbrev tangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) : FiniteRankBundleCore 𝕜 M :=
  FiniteRankBundleCore.ofBundle 𝕜 b.equivFunL (TangentSpace I)

omit [IsManifold I 1 M] in
/-- On a `C^(n+1)` manifold, `tangentFiniteRankCore I M b` is a `C^n` core. -/
theorem isContMDiff_tangentFiniteRankCore {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (b : Basis (Fin r) 𝕜 E) :
    have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentFiniteRankCore I M b).core.IsContMDiff I n :=
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  FiniteRankBundleCore.isContMDiff_ofBundle b.equivFunL (TangentSpace I : M → Type _)

/-- On the overlap of the charts at `x₀` and `x₁`, the transition map of
`tangentFiniteRankCore I M b` is `tangentCoordChange I x₀ x₁ x` conjugated by `b.equivFunL`. -/
theorem coordChange_tangentFiniteRankCore (b : Basis (Fin r) 𝕜 E) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source) :
    (tangentFiniteRankCore I M b).core.coordChange x₀ x₁ x =
      b.equivFunL.toContinuousLinearMap.comp
        ((tangentCoordChange I x₀ x₁ x).comp b.equivFunL.symm.toContinuousLinearMap) := by
  have h : ((trivializationAt E (TangentSpace I) x₀).coordChangeL 𝕜
      (trivializationAt E (TangentSpace I) x₁) x : E →L[𝕜] E) = tangentCoordChange I x₀ x₁ x :=
    (tangentBundleCore I M).trivializationAt_coordChangeL (α := x₀) (β := x₁) (x := x) ⟨hx₀, hx₁⟩
  exact (FiniteRankBundleCore.coordChange_ofBundle b.equivFunL (TangentSpace I) x₀ x₁ x).trans
    (congrArg (fun T : E →L[𝕜] E ↦ b.equivFunL.toContinuousLinearMap.comp
      (T.comp b.equivFunL.symm.toContinuousLinearMap)) h)

variable (I M) in
/-- Canonical `C^n` diffeomorphism identifying `(tangentFiniteRankCore I M b).core.TotalSpace` with
`TangentBundle I M` over the identity of `M`, sending a coordinate vector `v` over `x` to
`b.equivFunL.symm v`. -/
noncomputable def tangentFiniteRankCoreTotalSpaceDiffeomorph (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω) :
    (tangentFiniteRankCore I M b).core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (tangentFiniteRankCore I M b).rank → 𝕜), I.prod 𝓘(𝕜, E)⟯
      TangentBundle I M :=
  FiniteRankBundleCore.ofBundleTotalSpaceDiffeomorph b.equivFunL (TangentSpace I) I n

@[simp]
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_apply (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : (tangentFiniteRankCore I M b).core.TotalSpace) :
    tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n p = ⟨p.proj, b.equivFunL.symm p.snd⟩ :=
  (FiniteRankBundleCore.ofBundleTotalSpaceDiffeomorph_apply b.equivFunL (TangentSpace I)
    p).trans <|
    congrArg (TotalSpace.mk' E p.proj) <|
      (FiniteRankBundleCore.ofBundleFiberEquiv_apply b.equivFunL (TangentSpace I) p.proj
        p.snd).trans (TangentBundle.trivializationAt_symm_apply_self p.proj _)

/-- The `i`th standard basis vector over `x` in `tangentFiniteRankCore I M b` corresponds to the
tangent vector `b i` in `TangentBundle I M`. -/
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_single (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (x : M) (i : Fin r) :
    tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n ⟨x, (Pi.single i 1 : Fin r → 𝕜)⟩ =
      ⟨x, b i⟩ :=
  (tangentFiniteRankCoreTotalSpaceDiffeomorph_apply b n ⟨x, (Pi.single i 1 : Fin r → 𝕜)⟩).trans <|
    congrArg (TotalSpace.mk' E x) (Basis.equivFun_symm_single b i)

@[simp]
theorem tangentFiniteRankCoreTotalSpaceDiffeomorph_symm_apply (b : Basis (Fin r) 𝕜 E) (n : ℕ∞ω)
    (p : TangentBundle I M) :
    (tangentFiniteRankCoreTotalSpaceDiffeomorph I M b n).symm p = ⟨p.proj, b.equivFunL p.snd⟩ := by
  rw [tangentFiniteRankCoreTotalSpaceDiffeomorph,
    FiniteRankBundleCore.ofBundleTotalSpaceDiffeomorph_symm_apply,
    FiniteRankBundleCore.ofBundleFiberEquiv_symm_apply,
    TangentBundle.trivializationAt_apply_self]

end TangentFiniteRank

end TauCeti
