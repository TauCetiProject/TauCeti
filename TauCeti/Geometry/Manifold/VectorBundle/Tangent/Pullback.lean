/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Pulled-back tangent bundles along a map followed by a diffeomorphism

Let `Φ : M ≃ M'` be a `C^k` diffeomorphism, with `k ≥ n + 1`, let `g : B → M` be a `C^n` map, and
let `ℓ : B → M'` be a continuous map with `ℓ = Φ ∘ g`. The differential of `Φ` along `g` identifies
the pullbacks of the tangent bundles: at `x ∈ B` the differential
`dΦ_(g x) : T_(g x) M → T_(ℓ x) M'` is a linear isomorphism
(`Diffeomorph.mfderivToContinuousLinearEquiv`), and these isomorphisms form a `C^n` diffeomorphism
of total spaces `g* TM ≃ ℓ* TM'` over the identity of `B`
(`Diffeomorph.pullbackTangentDiffeomorph`). Over a complex model at `n = ω` it is a biholomorphism
of total spaces, so `g* TM` and `ℓ* TM'` are isomorphic holomorphic vector bundles.

This is how a statement about the tangent bundle along one map transfers to every translate of the
map by a diffeomorphism of the target: for instance, a splitting of the tangent bundle of
projective space along one line gives the same splitting along every line, since the projective
linear transformations act transitively on lines.

The smoothness of the forward map is that of the tangent map `TM → TM'` of `Φ`
(`ContMDiff.contMDiff_tangentMap`), read through the criterion for maps into a pullback bundle
(`Bundle.Pullback.contMDiff_iff`). The inverse is smooth because the fibres have finite rank
(`TauCeti.bundleDiffeomorph`).

## Main definitions

* `Diffeomorph.pullbackTangentDiffeomorph`: the `C^n` diffeomorphism `g* TM ≃ ℓ* TM'` given on the
  fibre over `x` by the differential of `Φ` at `g x`.
-/

public section

open Bundle Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E E' EB : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {H H' HB : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'} {IB : ModelWithCorners 𝕜 EB HB}
  {M M' B : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M'] [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold I 1 M] [IsManifold J 1 M'] {k n : WithTop ℕ∞}
  {K L : Type*} [FunLike K B M] [ContinuousMapClass K B M] [FunLike L B M']
  [ContinuousMapClass L B M']

/-- **The tangent bundle along a map followed by a diffeomorphism.** For a `C^k` diffeomorphism
`Φ : M ≃ M'` with `n + 1 ≤ k`, a `C^n` map `g : B → M` and a continuous map `ℓ : B → M'` with
`ℓ = Φ ∘ g`, the differentials `dΦ_(g x) : T_(g x) M → T_(ℓ x) M'` form a `C^n` diffeomorphism of
the total spaces of the pullbacks `g* TM` and `ℓ* TM'`, over the identity of `B`. For `n = ω` over
`ℂ` it is a biholomorphism of total spaces. -/
noncomputable def pullbackTangentDiffeomorph (Φ : M ≃ₘ^k⟮I, J⟯ M') (hk : n + 1 ≤ k)
    (g : K) (hg : ContMDiff IB I n g) (ℓ : L) (h : ∀ x, ℓ x = Φ (g x)) :
    TotalSpace E ((g : B → M) *ᵖ (TangentSpace I)) ≃ₘ^n⟮IB.prod 𝓘(𝕜, E), IB.prod 𝓘(𝕜, E')⟯
      TotalSpace E' ((ℓ : B → M') *ᵖ (TangentSpace J)) :=
  -- The fibres over `x` are the model spaces `E` and `E'`, by definition, so the differential of
  -- `Φ` at `g x` is a map between them.
  TauCeti.bundleDiffeomorph (fun x ↦ Φ.mfderivToContinuousLinearEquiv
      (fun h0 ↦ by simp [h0] at hk) (g x)) <| by
    have hℓ : ContMDiff IB J n ℓ :=
      ((Φ.contMDiff.of_le (le_self_add.trans hk)).comp hg).congr fun x ↦ h x
    refine (Pullback.contMDiff_iff ℓ hℓ).2 ⟨contMDiff_proj _, ?_⟩
    -- The lift to `TM'` is the tangent map of `Φ` after the lift to `TM`; their base points are
    -- `ℓ x` and `Φ (g x)`.
    have ht := (Φ.contMDiff.contMDiff_tangentMap hk).comp
      (Pullback.contMDiff_lift (F := E) (E := TangentSpace I) g hg)
    refine ht.congr fun p ↦ ?_
    exact TotalSpace.ext (h p.proj) (heq_of_eq (Φ.mfderivToContinuousLinearEquiv_apply _ _ _))

@[simp]
theorem pullbackTangentDiffeomorph_apply (Φ : M ≃ₘ^k⟮I, J⟯ M') (hk : n + 1 ≤ k)
    (g : K) (hg : ContMDiff IB I n g) (ℓ : L) (h : ∀ x, ℓ x = Φ (g x))
    (p : TotalSpace E ((g : B → M) *ᵖ (TangentSpace I))) :
    pullbackTangentDiffeomorph Φ hk g hg ℓ h p = ⟨p.proj, mfderiv I J Φ (g p.proj) p.snd⟩ := by
  refine (TauCeti.bundleDiffeomorph_apply _ _ p).trans ?_
  exact congrArg (fun v ↦ (⟨p.proj, v⟩ : TotalSpace E' ((ℓ : B → M') *ᵖ (TangentSpace J))))
    (Φ.mfderivToContinuousLinearEquiv_apply _ _ _)

/-- The inverse of `g* TM ≃ ℓ* TM'` is the inverse of the differential of `Φ` on each fibre. -/
@[simp]
theorem pullbackTangentDiffeomorph_symm_apply (Φ : M ≃ₘ^k⟮I, J⟯ M') (hk : n + 1 ≤ k)
    (g : K) (hg : ContMDiff IB I n g) (ℓ : L) (h : ∀ x, ℓ x = Φ (g x))
    (p : TotalSpace E' ((ℓ : B → M') *ᵖ (TangentSpace J))) :
    (pullbackTangentDiffeomorph Φ hk g hg ℓ h).symm p =
      ⟨p.proj, (Φ.mfderivToContinuousLinearEquiv (fun h0 ↦ by simp [h0] at hk) (g p.proj)).symm
        p.snd⟩ :=
  TauCeti.bundleDiffeomorph_symm_apply _ _ p

/-- The diffeomorphism `g* TM ≃ ℓ* TM'` lies over the identity of `B`. -/
theorem proj_pullbackTangentDiffeomorph (Φ : M ≃ₘ^k⟮I, J⟯ M') (hk : n + 1 ≤ k)
    (g : K) (hg : ContMDiff IB I n g) (ℓ : L) (h : ∀ x, ℓ x = Φ (g x))
    (p : TotalSpace E ((g : B → M) *ᵖ (TangentSpace I))) :
    (pullbackTangentDiffeomorph Φ hk g hg ℓ h p).proj = p.proj := by
  simp

end Diffeomorph
