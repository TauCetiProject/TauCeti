/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# Identifying an intrinsic normal bundle with another vector bundle

Let `f : M → N` be an embedding between finite-dimensional manifolds and `E₂` a vector bundle
over `M`. A family of continuous linear maps `g x : T_(f x) N → E₂ x`, each with kernel exactly
the tangent range `df_x(T_x M)` and with target of the dimension of the normal space, identifies
each normal space with the fibre `E₂ x` (`Manifold.IsImmersion.normalSpaceEquivOfKer`).
If `⟨x, v⟩ ↦ ⟨x, g x v⟩` is `C^m` on the pulled-back ambient tangent bundle, these fibrewise
equivalences are `C^m` on the intrinsic normal bundle
(`TauCeti.SmoothEmbedding.contMDiff_normalSpaceEquivOfKer`), so they assemble into a
`C^m` diffeomorphism of total spaces over the identity of `M`
(`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfKer`).

This is the common form of the identifications of the normal bundle of a Lagrangian embedding
with its cotangent bundle, and of a Legendrian embedding with the cotangent bundle plus a trivial
line bundle.
-/

public noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P W H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n m : ℕ∞ω} [IsManifold I (m + 1) M] [IsManifold J (m + 1) N] [IsManifold I 1 M]
  [IsManifold J 1 N]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, FiniteDimensional 𝕜 (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] [∀ x, T2Space (E₂ x)]
  [TopologicalSpace (TotalSpace W E₂)] [FiberBundle W E₂] [VectorBundle 𝕜 W E₂]
  (f : SmoothEmbedding I J n M N)

omit [VectorBundle 𝕜 W E₂] in
/-- **The identification of the normal bundle by a smooth family of maps is smooth.** For a
`C^n` embedding with `m + 1 ≤ n` and a family `g x : T_(f x) N → E₂ x` with kernels the tangent
ranges, if `⟨x, v⟩ ↦ ⟨x, g x v⟩` is `C^m` on the pulled-back ambient tangent bundle, then the
induced map from the intrinsic normal bundle, with model fibre `P` of the codimension, to `E₂` is
`C^m`. -/
theorem contMDiff_normalSpaceEquivOfKer (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E) (g : ∀ x, TangentSpace J (f x) →L[𝕜] E₂ x)
    (hg : ∀ x v, g x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hgdim : ∀ x, finrank 𝕜 (f.isImmersion.NormalSpace x hn) = finrank 𝕜 (E₂ x))
    (hgs : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, W)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' W (E := E₂) p.proj (g p.proj p.snd))) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(𝕜, P)) (I.prod 𝓘(𝕜, W)) m
      (fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' W (E := E₂) p.proj
          (f.isImmersion.normalSpaceEquivOfKer p.proj hn (g p.proj) (hg p.proj) (hgdim p.proj)
            p.snd)) := by
  let := f.normalSpaceFiberBundle hn hdim
  rw [f.contMDiff_normalBundle_iff hn hm hdim]
  refine hgs.congr fun ⟨x, v⟩ ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  exact congrArg (TotalSpace.mk' W x)
    (f.isImmersion.normalSpaceEquivOfKer_normalClass x hn (g x) (hg x) (hgdim x) v)

/-- **The normal bundle is diffeomorphic to any bundle it is identified with by a smooth family of
maps.** For a `C^n` embedding with `m + 1 ≤ n` and a family `g x : T_(f x) N → E₂ x` with kernels
the tangent ranges which is `C^m` on the pulled-back ambient tangent bundle, the intrinsic normal
bundle, with model fibre `P` of the codimension, is `C^m`-diffeomorphic to `E₂` over the identity
of `M`, by `[v] ↦ g x v` on each fibre. -/
def normalBundleDiffeomorphOfKer (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E) (g : ∀ x, TangentSpace J (f x) →L[𝕜] E₂ x)
    (hg : ∀ x v, g x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hgdim : ∀ x, finrank 𝕜 (f.isImmersion.NormalSpace x hn) = finrank 𝕜 (E₂ x))
    (hgs : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, W)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' W (E := E₂) p.proj (g p.proj p.snd))) :
    letI := f.normalSpaceFiberBundle hn hdim
    TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ≃ₘ^m⟮I.prod 𝓘(𝕜, P), I.prod 𝓘(𝕜, W)⟯
      TotalSpace W E₂ :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  TauCeti.bundleDiffeomorph
    (fun x ↦ f.isImmersion.normalSpaceEquivOfKer x hn (g x) (hg x) (hgdim x))
    (f.contMDiff_normalSpaceEquivOfKer hn hm hdim g hg hgdim hgs)

/-- The diffeomorphism sends a normal vector at `x` to the corresponding vector of `E₂ x`. -/
@[simp]
theorem normalBundleDiffeomorphOfKer_apply (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E) (g : ∀ x, TangentSpace J (f x) →L[𝕜] E₂ x)
    (hg : ∀ x v, g x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hgdim : ∀ x, finrank 𝕜 (f.isImmersion.NormalSpace x hn) = finrank 𝕜 (E₂ x))
    (hgs : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, W)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' W (E := E₂) p.proj (g p.proj p.snd)))
    (p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn)) :
    letI := f.normalSpaceFiberBundle hn hdim
    f.normalBundleDiffeomorphOfKer hn hm hdim g hg hgdim hgs p =
      ⟨p.proj,
        f.isImmersion.normalSpaceEquivOfKer p.proj hn (g p.proj) (hg p.proj) (hgdim p.proj)
          p.snd⟩ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.bundleDiffeomorph_apply _ _ p

/-- The inverse diffeomorphism sends a vector of `E₂ x` to the corresponding normal vector at
`x`. -/
@[simp]
theorem normalBundleDiffeomorphOfKer_symm_apply (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : finrank 𝕜 P = finrank 𝕜 V - finrank 𝕜 E) (g : ∀ x, TangentSpace J (f x) →L[𝕜] E₂ x)
    (hg : ∀ x v, g x v = 0 ↔ v ∈ f.isImmersion.tangentRange x hn)
    (hgdim : ∀ x, finrank 𝕜 (f.isImmersion.NormalSpace x hn) = finrank 𝕜 (E₂ x))
    (hgs : ContMDiff (I.prod 𝓘(𝕜, V)) (I.prod 𝓘(𝕜, W)) m
      (fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' W (E := E₂) p.proj (g p.proj p.snd)))
    (q : TotalSpace W E₂) :
    letI := f.normalSpaceFiberBundle hn hdim
    (f.normalBundleDiffeomorphOfKer hn hm hdim g hg hgdim hgs).symm q =
      ⟨q.proj,
        (f.isImmersion.normalSpaceEquivOfKer q.proj hn (g q.proj) (hg q.proj)
          (hgdim q.proj)).symm q.snd⟩ := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.bundleDiffeomorph_symm_apply _ _ q

end TauCeti.SmoothEmbedding
