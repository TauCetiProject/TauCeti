/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.ContinuousAmbientIsotopy
public import TauCeti.Topology.Homotopy.AmbientIsotopicNaturality
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Naturality of continuous ambient isotopy for smooth embeddings

The geometric-topology roadmap asks that isotopy and ambient isotopy be defined once, in
generality, and then specialised to smooth embeddings such as geometric knot presentations.
`TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic` is that continuous ambient-isotopy relation
on bundled smooth embeddings. This file records its coordinate-change API.

The statements are formulated for already-constructed bundled smooth embeddings, together with
equalities identifying their underlying continuous maps after precomposition or postcomposition.
This avoids depending on Mathlib's still-axiomatized predicate-level composition theorem for
smooth embeddings, while still giving downstream knot and embedding presentations the relation
transport they need once they have built the relevant embeddings.

## Main results

* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.of_toContinuousMap_eq`: transport the
  relation across equality of underlying continuous maps.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.precomp_of_toContinuousMap_eq`: precompose
  both embeddings by a continuous source map, expressed through already-bundled embeddings.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.postcomp_homeomorph_of_toContinuousMap_eq`:
  postcompose both embeddings by a homeomorphism of ambient spaces.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.postcomp_diffeomorph_of_toContinuousMap_eq`:
  the same postcomposition result for a diffeomorphism, using its underlying homeomorphism.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.`
  `postcomp_homeomorph_precomp_of_toContinuousMap_eq`:
  the combined source and ambient coordinate-change form.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff
open ContinuousMap

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {K : Type*} [TopologicalSpace K] {K' : Type*} [TopologicalSpace K']
  {L : Type*} [TopologicalSpace L] {L' : Type*} [TopologicalSpace L']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {I' : ModelWithCorners 𝕜 F K} {J' : ModelWithCorners 𝕜 F' K'}
  {I'' : ModelWithCorners 𝕜 G L} {J'' : ModelWithCorners 𝕜 G' L'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace K M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace K' N']
  {P : Type*} [TopologicalSpace P] [ChartedSpace L P]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace L' Q]
  {n : ℕ∞ω}

namespace ContinuousAmbientIsotopic

variable {f g : SmoothEmbedding I J n M N}
  {f₁ g₁ : SmoothEmbedding I' J n M' N}
  {f₂ g₂ : SmoothEmbedding I J' n M N'}
  {f₃ g₃ : SmoothEmbedding I' J' n M' N'}

/-- Continuous ambient isotopy of bundled smooth embeddings is insensitive to replacing both
endpoints by bundled embeddings with the same underlying continuous maps. -/
theorem of_toContinuousMap_eq (hfg : ContinuousAmbientIsotopic f g)
    {f' g' : SmoothEmbedding I J n M N}
    (hf' : f'.toContinuousMap = f.toContinuousMap)
    (hg' : g'.toContinuousMap = g.toContinuousMap) :
    ContinuousAmbientIsotopic f' g' := by
  rw [continuousAmbientIsotopic_def] at hfg ⊢
  obtain ⟨Φ, hΦ⟩ := hfg
  exact ⟨Φ, by simpa [hf', hg'] using hΦ⟩

/-- Continuous ambient isotopy of bundled smooth embeddings can be checked on the underlying
continuous maps. This is useful when the endpoint maps have been rewritten by a construction
outside the bundled smooth-embedding API. -/
theorem iff_toContinuousMap_eq {f' g' : SmoothEmbedding I J n M N}
    (hf' : f'.toContinuousMap = f.toContinuousMap)
    (hg' : g'.toContinuousMap = g.toContinuousMap) :
    ContinuousAmbientIsotopic f' g' ↔ ContinuousAmbientIsotopic f g := by
  constructor
  · intro h
    exact of_toContinuousMap_eq h hf'.symm hg'.symm
  · intro h
    exact of_toContinuousMap_eq h hf' hg'

/-- Precomposing both endpoints by a continuous source map preserves continuous ambient isotopy,
provided the precomposed maps have already been bundled as smooth embeddings. -/
theorem precomp_of_toContinuousMap_eq (hfg : ContinuousAmbientIsotopic f g) (e : C(M', M))
    (hf₁ : f₁.toContinuousMap = f.toContinuousMap.comp e)
    (hg₁ : g₁.toContinuousMap = g.toContinuousMap.comp e) :
    ContinuousAmbientIsotopic f₁ g₁ := by
  rw [continuousAmbientIsotopic_def] at hfg ⊢
  have hpre :
      TauCeti.AmbientIsotopic (f.toContinuousMap.comp e) (g.toContinuousMap.comp e) :=
    TauCeti.AmbientIsotopic.precomp (TauCeti.ambientIsotopic_def.2 hfg) e
  simpa [hf₁, hg₁] using TauCeti.ambientIsotopic_def.1 hpre

/-- Postcomposing both endpoints by a homeomorphism of ambient spaces preserves continuous
ambient isotopy, provided the postcomposed maps have already been bundled as smooth embeddings. -/
theorem postcomp_homeomorph_of_toContinuousMap_eq (hfg : ContinuousAmbientIsotopic f g)
    (h : N ≃ₜ N')
    (hf₂ : f₂.toContinuousMap = (h : C(N, N')).comp f.toContinuousMap)
    (hg₂ : g₂.toContinuousMap = (h : C(N, N')).comp g.toContinuousMap) :
    ContinuousAmbientIsotopic f₂ g₂ := by
  rw [continuousAmbientIsotopic_def] at hfg ⊢
  have hpost :
      TauCeti.AmbientIsotopic ((h : C(N, N')).comp f.toContinuousMap)
        ((h : C(N, N')).comp g.toContinuousMap) :=
    TauCeti.AmbientIsotopic.postcomp_homeomorph (TauCeti.ambientIsotopic_def.2 hfg) h
  simpa [hf₂, hg₂] using TauCeti.ambientIsotopic_def.1 hpost

/-- Postcomposing both endpoints by a diffeomorphism of ambient manifolds preserves continuous
ambient isotopy, using the diffeomorphism's underlying homeomorphism. The hypotheses identify
the already-bundled endpoint embeddings with the corresponding postcompositions. -/
theorem postcomp_diffeomorph_of_toContinuousMap_eq (hfg : ContinuousAmbientIsotopic f g)
    (φ : N ≃ₘ^n⟮J, J'⟯ N')
    (hf₂ : f₂.toContinuousMap = (φ.toHomeomorph : C(N, N')).comp f.toContinuousMap)
    (hg₂ : g₂.toContinuousMap = (φ.toHomeomorph : C(N, N')).comp g.toContinuousMap) :
    ContinuousAmbientIsotopic f₂ g₂ :=
  postcomp_homeomorph_of_toContinuousMap_eq hfg φ.toHomeomorph hf₂ hg₂

/-- The two-sided coordinate-change form: precompose the source by a continuous map and
postcompose the ambient space by a homeomorphism, with the resulting endpoint maps supplied as
already-bundled smooth embeddings. -/
theorem postcomp_homeomorph_precomp_of_toContinuousMap_eq
    (hfg : ContinuousAmbientIsotopic f g) (h : N ≃ₜ N') (e : C(M', M))
    (hf₃ : f₃.toContinuousMap = (h : C(N, N')).comp (f.toContinuousMap.comp e))
    (hg₃ : g₃.toContinuousMap = (h : C(N, N')).comp (g.toContinuousMap.comp e)) :
    ContinuousAmbientIsotopic f₃ g₃ := by
  rw [continuousAmbientIsotopic_def] at hfg ⊢
  have hpostpre :
      TauCeti.AmbientIsotopic ((h : C(N, N')).comp (f.toContinuousMap.comp e))
        ((h : C(N, N')).comp (g.toContinuousMap.comp e)) :=
    TauCeti.AmbientIsotopic.postcomp_homeomorph_precomp
      (TauCeti.ambientIsotopic_def.2 hfg) h e
  simpa [hf₃, hg₃] using TauCeti.ambientIsotopic_def.1 hpostpre

/-- The two-sided coordinate-change form with a diffeomorphism on the ambient space. -/
theorem postcomp_diffeomorph_precomp_of_toContinuousMap_eq
    (hfg : ContinuousAmbientIsotopic f g) (φ : N ≃ₘ^n⟮J, J'⟯ N') (e : C(M', M))
    (hf₃ : f₃.toContinuousMap = (φ.toHomeomorph : C(N, N')).comp (f.toContinuousMap.comp e))
    (hg₃ : g₃.toContinuousMap = (φ.toHomeomorph : C(N, N')).comp (g.toContinuousMap.comp e)) :
    ContinuousAmbientIsotopic f₃ g₃ :=
  postcomp_homeomorph_precomp_of_toContinuousMap_eq hfg φ.toHomeomorph e hf₃ hg₃

/-- Setoid form of `precomp_of_toContinuousMap_eq`. -/
theorem precomp_setoid_of_toContinuousMap_eq
    (hfg : (setoid I J n M N).r f g) (e : C(M', M))
    (hf₁ : f₁.toContinuousMap = f.toContinuousMap.comp e)
    (hg₁ : g₁.toContinuousMap = g.toContinuousMap.comp e) :
    (setoid I' J n M' N).r f₁ g₁ :=
  setoid_r_iff.2 <| precomp_of_toContinuousMap_eq (setoid_r_iff.1 hfg) e hf₁ hg₁

/-- Setoid form of `postcomp_homeomorph_of_toContinuousMap_eq`. -/
theorem postcomp_homeomorph_setoid_of_toContinuousMap_eq
    (hfg : (setoid I J n M N).r f g) (h : N ≃ₜ N')
    (hf₂ : f₂.toContinuousMap = (h : C(N, N')).comp f.toContinuousMap)
    (hg₂ : g₂.toContinuousMap = (h : C(N, N')).comp g.toContinuousMap) :
    (setoid I J' n M N').r f₂ g₂ :=
  setoid_r_iff.2 <|
    postcomp_homeomorph_of_toContinuousMap_eq (setoid_r_iff.1 hfg) h hf₂ hg₂

/-- Setoid form of the two-sided coordinate-change lemma. -/
theorem postcomp_homeomorph_precomp_setoid_of_toContinuousMap_eq
    (hfg : (setoid I J n M N).r f g) (h : N ≃ₜ N') (e : C(M', M))
    (hf₃ : f₃.toContinuousMap = (h : C(N, N')).comp (f.toContinuousMap.comp e))
    (hg₃ : g₃.toContinuousMap = (h : C(N, N')).comp (g.toContinuousMap.comp e)) :
    (setoid I' J' n M' N').r f₃ g₃ :=
  setoid_r_iff.2 <|
    postcomp_homeomorph_precomp_of_toContinuousMap_eq (setoid_r_iff.1 hfg) h e hf₃ hg₃

end ContinuousAmbientIsotopic

end SmoothEmbedding

end TauCeti
