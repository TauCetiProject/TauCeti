/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Geometry.Manifold.PontryaginThom.Basic
public import TauCeti.Geometry.Sphere.Connected

/-!
# Degree of a Pontryagin–Thom collapse along a map meeting the core once

Let `τ : S × ℝᵏ → Q` be a framed tube around `f : S → Q` with compact core `S`, and let
`c : Q → Sᵏ` be its Pontryagin–Thom collapse onto the sphere
(`TauCeti.pontryaginThomSphereMap`). The core is exactly the preimage under `c` of the image
`c₀` of the origin of `ℝᵏ` (`TauCeti.IsFramedTube.pontryaginThomSphereMap_eq_iff`).

Let `σ : M → Q` be a map from a compact oriented `k`-manifold, `k ≥ 1`. The fibre of
`c ∘ σ : M → Sᵏ` over `c₀` is the set `σ⁻¹(f(S))` of points where `σ` meets the core. When it is
finite, the degree of `c ∘ σ` is the sum of the local indices of `c ∘ σ` over these points
(`TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_sum_localIndex`). This is the
intersection number of `σ` with the framed submanifold `f(S)`: by the identity
`(c ∘ σ)_*[M] = deg (c ∘ σ) • [Sᵏ]` it computes the effect of the collapse on the fundamental class
carried by `σ`.

Suppose now that `σ` meets the core in exactly one point `x`, and that `c ∘ σ` is a local
homeomorphism at `x`. For a smooth tube and a smooth `σ` transverse to the core at `x`, the inverse
function theorem in the normal coordinate of the tube gives this hypothesis; here it is assumed in
its topological form. Then `x` is the only preimage of `c₀` under `c ∘ σ`, the local index there is
`±1`, and so the degree of `c ∘ σ` is `±1`
(`TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one`). For connected
`M` the composite `c ∘ σ` therefore induces a bijection `Hₖ(M; ℤ) → Hₖ(Sᵏ; ℤ)`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp`). For `M = Sᵏ`
with `k ≥ 2` the orientation comes from simple connectivity, and the self-map `c ∘ σ` of the sphere
induces a bijection on `Hₖ(Sᵏ; ℤ)`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere`), as in
the proof of Lemma 7.6 of Barraud–Damian–Humilière–Oancea.

## Main results

* `TauCeti.IsFramedTube.pontryaginThomSphereMap_eq_iff`: the core is the fibre of the collapse
  over the image of the origin.
* `TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_sum_localIndex`: the degree of
  `c ∘ σ` is the sum of the local indices over the points where `σ` meets the core.
* `TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one`: a map meeting
  the core once, at a point where its composite with the collapse is a local homeomorphism, has
  composite of degree `±1`.
* `TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp`: for connected
  `M`, such a composite is bijective on `Hₖ(-; ℤ)`; the variant
  `TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere` treats
  `M = Sᵏ`, `k ≥ 2`, with no orientation hypotheses.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §§5 and 7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7, proof of Lemma 7.6.
-/

public section

open Metric Module Set

namespace TauCeti

namespace IsFramedTube

variable {S Q : Type} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace Q] [T2Space Q]
  {k : ℕ} {f : S → Q} {τ : S × (Fin k → ℝ) → Q}

/-- **The core is the fibre of the collapse over the image of the origin.** A point of `Q` is sent
by the collapse onto the sphere to the image of the origin of `ℝᵏ` exactly when it lies on the core
of the framed tube. -/
theorem pontryaginThomSphereMap_eq_iff (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) {m : Q} :
    pontryaginThomSphereMap h.isOpenEmbedding s₀ m = onePointHomeomorphSphere k s₀ (0 : Fin k → ℝ)
      ↔ m ∈ range f := by
  rw [← h.pontryaginThomCollapse_eq_zero_iff, coe_pontryaginThomSphereMap, Function.comp_apply,
    (onePointHomeomorphSphere k s₀).injective.eq_iff]

variable {M E : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (o : HomologicalOrientation M E k)
  (o' : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (EuclideanSpace ℝ (Fin k)) k)
  (hE : finrank ℝ E = k)

/-- **The degree of a collapse along a map is an intersection number.** Let `σ : M → Q` be a map
from a compact oriented `k`-manifold, `k ≥ 1`, meeting the core of a framed tube with fibre `ℝᵏ` in
finitely many points. Then the degree of the composite of `σ` with the Pontryagin–Thom collapse onto
`Sᵏ` is the sum of the local indices of this composite at these points. -/
theorem degree_pontryaginThomSphereMap_comp_eq_sum_localIndex (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (hk : 1 ≤ k) (σ : C(M, Q))
    (hσ : (σ ⁻¹' range f).Finite) :
    o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) = ∑ x ∈ hσ.toFinset,
      o.localIndex o' ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) x := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
    connectedSpace_euclideanSphere (by omega)
  -- The fibre of the composite over the image of the origin is `σ⁻¹(range f)`.
  have hpre : (pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ ⁻¹'
      {onePointHomeomorphSphere k s₀ (0 : Fin k → ℝ)} = σ ⁻¹' range f :=
    ext fun _ ↦ h.pontryaginThomSphereMap_eq_iff s₀
  rw [o.degree_eq_sum_localIndex o' hE finrank_euclideanSpace_fin (map_continuous _).isProperMap
    (hpre ▸ hσ : (_ ⁻¹' {onePointHomeomorphSphere k s₀ (0 : Fin k → ℝ)}).Finite)]
  exact Finset.sum_congr (Finite.toFinset_inj.2 hpre) fun _ _ ↦ rfl

/-- **A map meeting the core once has collapse of degree `±1`.** Let `σ : M → Q` be a map from a
compact oriented `k`-manifold, `k ≥ 1`, meeting the core of a framed tube with fibre `ℝᵏ` in the
single point `x`. If the composite of `σ` with the Pontryagin–Thom collapse onto `Sᵏ` is a local
homeomorphism at `x`, then this composite has degree `1` or `-1`. -/
theorem degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (hk : 1 ≤ k) (σ : C(M, Q)) {x : M}
    (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x}) :
    o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) = 1 ∨
      o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ) = -1 := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
    connectedSpace_euclideanSphere (by omega)
  have hσx : σ x ∈ range f := hx.symm.subset (mem_singleton x)
  -- The fibre of the composite over the image of the origin is `σ⁻¹(range f) = {x}`.
  have hfib : (pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ ⁻¹'
      {(pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ x} = {x} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, ContinuousMap.comp_apply,
      (h.pontryaginThomSphereMap_eq_iff s₀).2 hσx, h.pontryaginThomSphereMap_eq_iff s₀]
    rw [← mem_preimage, hx, mem_singleton_iff]
  exact o.degree_eq_one_or_eq_neg_one_of_isLocalHomeomorphOn o' hE finrank_euclideanSpace_fin
    (map_continuous _).isProperMap hfib hσ (mem_singleton x)

include o o' hE in
/-- **A map meeting the core once is detected on homology.** Let `σ : M → Q` be a map from a
compact connected oriented `k`-manifold, `k ≥ 1`, meeting the core of a framed tube with fibre `ℝᵏ`
in the single point `x`. If the composite of `σ` with the Pontryagin–Thom collapse onto `Sᵏ` is a
local homeomorphism at `x`, then this composite induces a bijection `Hₖ(M; ℤ) → Hₖ(Sᵏ; ℤ)`. -/
theorem bijective_singularHomologyMap_pontryaginThomSphereMap_comp [ConnectedSpace M]
    (h : IsFramedTube f τ) (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (hk : 1 ≤ k)
    (σ : C(M, Q)) {x : M} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x}) :
    Function.Bijective (ContinuousMap.singularHomologyMap ℤ k
      ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ)) := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
    connectedSpace_euclideanSphere (by omega)
  exact (o.bijective_singularHomologyMap_iff o' hE finrank_euclideanSpace_fin _).2
    (h.degree_pontryaginThomSphereMap_comp_eq_one_or_eq_neg_one o o' hE s₀ hk σ hx hσ)

/-- **The collapse of a sphere meeting the core once is bijective on `Hₖ(Sᵏ; ℤ)`.** For
`k ≥ 2`, let `σ : Sᵏ → Q` meet the core of a framed tube with fibre `ℝᵏ` in the single point `x`.
If the composite of `σ` with the Pontryagin–Thom collapse onto `Sᵏ` is a local homeomorphism at
`x`, then this composite induces a bijection on `Hₖ(Sᵏ; ℤ)`. -/
theorem bijective_singularHomologyMap_pontryaginThomSphereMap_comp_sphere (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (hk : 2 ≤ k)
    (σ : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, Q)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (k + 1))) 1} (hx : σ ⁻¹' range f = {x})
    (hσ : IsLocalHomeomorphOn (pontryaginThomSphereMap h.isOpenEmbedding s₀ ∘ σ) {x}) :
    Function.Bijective (ContinuousMap.singularHomologyMap ℤ k
      ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp σ)) := by
  -- The sphere `Sᵏ` is simply connected, hence connected and orientable.
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :=
    simplyConnectedSpace_sphere_euclideanSpace hk
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) (E := EuclideanSpace ℝ (Fin k))
    finrank_euclideanSpace_fin
  exact h.bijective_singularHomologyMap_pontryaginThomSphereMap_comp o o finrank_euclideanSpace_fin
    s₀ (by omega) σ hx hσ

end IsFramedTube

end TauCeti
