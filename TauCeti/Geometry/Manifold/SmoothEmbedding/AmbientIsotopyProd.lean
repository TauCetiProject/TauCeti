/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopyClass
public import TauCeti.Topology.Homotopy.IsotopyProd

/-!
# Products of ambient-isotopic smooth embeddings

The geometric-topology roadmap treats the geometric presentation of a knot or link as a smooth
embedding and asks that ambient isotopy be defined generally, then specialised to those
presentations. `TauCeti.Topology.Homotopy.IsotopyProd` proves product closure for the general
continuous ambient-isotopy relation, and `TauCeti.Geometry.Manifold.SmoothEmbedding` bundles the
product of smooth embeddings. This file connects those two APIs.

This is deliberately a thin specialisation: it does not introduce a knot type or a new isotopy
notion. It says that the product presentation built from two pairs of ambient-isotopic smooth
embeddings is again ambient isotopic, with the statement phrased entirely in the bundled
`SmoothEmbedding` API.

## Main results

* `TauCeti.SmoothEmbedding.AmbientIsotopic.prodMap`: products preserve ambient isotopy of bundled
  smooth embeddings.
* `TauCeti.SmoothEmbedding.AmbientIsotopic.prodMap_setoid`: the same fact in setoid-relation form.
* `TauCeti.SmoothEmbedding.AmbientIsotopyClass.prodMap`: products of embeddings descend to
  products of ambient-isotopy classes.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {G₁ : Type*} [TopologicalSpace G₁] {G₂ : Type*} [TopologicalSpace G₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₁ : ModelWithCorners 𝕜 F₁ G₁} {J₂ : ModelWithCorners 𝕜 F₂ G₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  {n : ℕ∞ω}

namespace AmbientIsotopic

variable [IsManifold I₁ n M₁] [IsManifold I₂ n M₂] [IsManifold J₁ n N₁]
  [IsManifold J₂ n N₂]
  {f f' : SmoothEmbedding I₁ J₁ n M₁ N₁}
  {g g' : SmoothEmbedding I₂ J₂ n M₂ N₂}

/-- Products preserve ambient isotopy of bundled smooth embeddings.

If `f` is ambient isotopic to `f'` and `g` is ambient isotopic to `g'`, then the bundled product
embedding `f.prodMap g` is ambient isotopic to `f'.prodMap g'`. This is the smooth-embedding
specialisation of `TauCeti.AmbientIsotopic.prodMap`. -/
theorem prodMap (hff' : AmbientIsotopic f f') (hgg' : AmbientIsotopic g g') :
    AmbientIsotopic (f.prodMap g) (f'.prodMap g') := by
  rw [ambientIsotopic_def] at hff' hgg' ⊢
  obtain ⟨Φ, hΦ⟩ :=
    TauCeti.AmbientIsotopic.prodMap (TauCeti.ambientIsotopic_def.2 hff')
      (TauCeti.ambientIsotopic_def.2 hgg')
  refine ⟨Φ, ContinuousMap.ext fun x => ?_⟩
  rcases x with ⟨x₁, x₂⟩
  simpa [toContinuousMap_apply, prodMap_apply] using
    congr_fun (congrArg DFunLike.coe hΦ) (x₁, x₂)

/-- Product closure for the ambient-isotopy setoid on bundled smooth embeddings. -/
theorem prodMap_setoid
    (hff' : (setoid I₁ J₁ n M₁ N₁).r f f')
    (hgg' : (setoid I₂ J₂ n M₂ N₂).r g g') :
    (setoid (I₁.prod I₂) (J₁.prod J₂) n (M₁ × M₂) (N₁ × N₂)).r
      (f.prodMap g) (f'.prodMap g') :=
  setoid_r_iff.2 (prodMap (setoid_r_iff.1 hff') (setoid_r_iff.1 hgg'))

end AmbientIsotopic

namespace AmbientIsotopyClass

/-- The product of ambient-isotopy classes of bundled smooth embeddings.

This is the quotient-level operation induced by `SmoothEmbedding.prodMap`, using product closure
of ambient isotopy of bundled smooth embeddings. -/
def prodMap [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J₁ n N₁] [IsManifold J₂ n N₂] :
    AmbientIsotopyClass I₁ J₁ n M₁ N₁ →
      AmbientIsotopyClass I₂ J₂ n M₂ N₂ →
        AmbientIsotopyClass (I₁.prod I₂) (J₁.prod J₂) n (M₁ × M₂) (N₁ × N₂) :=
  map₂ (fun f g => f.prodMap g) fun {f f'} hff' {g g'} hgg' =>
    AmbientIsotopic.prodMap (f := f) (f' := f') (g := g) (g' := g') hff' hgg'

/-- Computation rule for `AmbientIsotopyClass.prodMap` on representatives. -/
@[simp]
theorem prodMap_mk_mk [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J₁ n N₁] [IsManifold J₂ n N₂]
    (f : SmoothEmbedding I₁ J₁ n M₁ N₁) (g : SmoothEmbedding I₂ J₂ n M₂ N₂) :
    prodMap (mk f) (mk g) = mk (f.prodMap g) :=
  map₂_mk_mk (fun f g => f.prodMap g)
    (fun {f f'} hff' {g g'} hgg' =>
      AmbientIsotopic.prodMap (f := f) (f' := f') (g := g) (g' := g') hff' hgg')
    f g

end AmbientIsotopyClass

end SmoothEmbedding

end TauCeti
