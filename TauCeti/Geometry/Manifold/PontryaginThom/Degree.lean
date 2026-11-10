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

/-!
# The degree of a Pontryagin–Thom collapse along a map

Let `τ : S × ℝᵏ → M` be a framed tube around `f : S → M`, with `S` compact and `M` Hausdorff, and
let `c : M → Sᵏ` be its Pontryagin–Thom collapse onto the sphere
(`TauCeti.pontryaginThomSphereMap`). The collapse sends exactly the core `f(S)` to the image `p₀`
of the origin of `ℝᵏ` (`TauCeti.IsFramedTube.pontryaginThomSphereMap_eq_iff`). So for a map
`g : P → M` from a compact oriented `k`-manifold `P`, the fibre of `c ∘ g : P → Sᵏ` over `p₀` is the
set `g⁻¹(f(S))` of points where `g` meets the core. When it is finite, the degree of `c ∘ g` is the
sum of the local indices of `c ∘ g` over these points
(`TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_sum_localIndex`). This is the
intersection number of `g` with the framed submanifold `f(S)`: by the identity
`(c ∘ g)_*[P] = deg (c ∘ g) • [Sᵏ]` it computes the effect of the collapse on the fundamental class
carried by `g`.

Near a point `x` of `g⁻¹(f(S))` the map `c ∘ g` is the normal coordinate of `g` in the tube,
`z ↦ pr₂ (τ⁻¹ (g z))`, read in `Sᵏ`. The map `g` meets the core *transversely* at `x` when this
normal coordinate restricts to an open embedding on a neighbourhood of `x`; for smooth `g` meeting a
smooth framed submanifold transversely in the differential sense, the normal coordinate has
invertible derivative at `x`, and the inverse function theorem gives this. At such a point the
local index is `±1` (`TauCeti.HomologicalOrientation.isUnit_localIndex_of_isOpenEmbedding`).
Hence when `g` meets the core in a single point, transversely, the degree of `c ∘ g` is `±1`
(`TauCeti.IsFramedTube.isUnit_degree_pontryaginThomSphereMap_comp`). For a map `g : Sᵏ → M` from
the sphere itself, `k ≥ 2`, this says that `c ∘ g` induces a bijection on `Hₖ(Sᵏ; ℤ)`
(`TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp`). The proof of
Lemma 7.6 of Barraud–Damian–Humilière–Oancea uses this for a sphere meeting a framed submanifold
transversely in one point; the sign of the degree depends on the orientations.

Only the topology of the tube is used: `M` is an arbitrary Hausdorff space.

## Main results

* `TauCeti.IsFramedTube.pontryaginThomSphereMap_eq_iff`: the collapse sends exactly the core to the
  image of the origin.
* `TauCeti.IsFramedTube.degree_pontryaginThomSphereMap_comp_eq_sum_localIndex`: the degree of
  `c ∘ g` is the sum of the local indices over the points where `g` meets the core.
* `TauCeti.IsFramedTube.isUnit_degree_pontryaginThomSphereMap_comp`: if `g` meets the core in a
  single point, transversely, then `c ∘ g` has degree `±1`.
* `TauCeti.IsFramedTube.bijective_singularHomologyMap_pontryaginThomSphereMap_comp`: for
  `g : Sᵏ → M`, `k ≥ 2`, meeting the core once, transversely, `c ∘ g` is bijective on
  `Hₖ(Sᵏ; ℤ)`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia,
  1965, §§5 and 7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 7.6.
-/

public section

noncomputable section

open Function Module Set Topology OnePoint Metric

namespace TauCeti

namespace IsFramedTube

variable {S M : Type} [TopologicalSpace S] [CompactSpace S] [TopologicalSpace M] [T2Space M]

/-- **The core is the preimage of the image of the origin.** The Pontryagin–Thom collapse of a
framed tube onto the sphere sends a point to the image of the origin exactly when it lies on the
core. -/
theorem pontryaginThomSphereMap_eq_iff {k : ℕ} {f : S → M} {τ : S × (Fin k → ℝ) → M}
    (h : IsFramedTube f τ) (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) {m : M} :
    pontryaginThomSphereMap h.isOpenEmbedding s₀ m =
        onePointHomeomorphSphere k s₀ ((0 : Fin k → ℝ) : OnePoint (Fin k → ℝ)) ↔
      m ∈ range f := by
  rw [coe_pontryaginThomSphereMap, comp_apply, (onePointHomeomorphSphere k s₀).injective.eq_iff,
    h.pontryaginThomCollapse_eq_zero_iff]

variable {P E : Type} [TopologicalSpace P] [T2Space P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E P] {k : ℕ}
  (o : HomologicalOrientation P E (k + 1))
  (o' : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)
    (EuclideanSpace ℝ (Fin (k + 1))) (k + 1))
  (hE : finrank ℝ E = k + 1)

/-- The sphere `Sᵏ⁺¹`, `k + 1 ≥ 1`, is connected. -/
private theorem connectedSpace_sphere :
    ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
  isConnected_iff_connectedSpace.1 <| isConnected_sphere (by
    rw [← finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < k + 2)) 0 zero_le_one

/-- **The degree of a collapse along a map is an intersection number.** Let `c` be the
Pontryagin–Thom collapse onto `Sᵏ⁺¹` of a framed tube around `f : S → M`, and `g : P → M` a map from
a compact oriented manifold of dimension `k + 1` meeting the core `f(S)` in finitely many points.
Then the degree of `c ∘ g` is the sum of the local indices of `c ∘ g` at these points. -/
theorem degree_pontryaginThomSphereMap_comp_eq_sum_localIndex {f : S → M}
    {τ : S × (Fin (k + 1) → ℝ) → M} (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) (g : C(P, M))
    (hg : (g ⁻¹' range f).Finite) :
    o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g) = ∑ x ∈ hg.toFinset,
      o.localIndex o' ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g) x := by
  have := connectedSpace_sphere (k := k)
  have hpre : (pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g ⁻¹'
      {onePointHomeomorphSphere (k + 1) s₀ ((0 : Fin (k + 1) → ℝ) : OnePoint _)} = g ⁻¹' range f :=
    ext fun x ↦ h.pontryaginThomSphereMap_eq_iff s₀
  rw [o.degree_eq_sum_localIndex o' hE finrank_euclideanSpace_fin
    ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g).continuous.isProperMap
    (hpre ▸ hg : (_ ⁻¹' {onePointHomeomorphSphere (k + 1) s₀ ((0 : Fin (k + 1) → ℝ) :
      OnePoint _)}).Finite)]
  exact Finset.sum_congr (Finite.toFinset_inj.2 hpre) fun _ _ ↦ rfl

/-- **A map meeting the core once, transversely, is detected by the collapse.** Let `c` be the
Pontryagin–Thom collapse onto `Sᵏ⁺¹` of a framed tube `τ` around `f : S → M`, and `g : P → M` a map
from a compact oriented manifold of dimension `k + 1` meeting the core `f(S)` only at `x`. If `g`
meets the core transversely at `x`, in the sense that its normal coordinate `pontryaginThomCollapse
τ ∘ g` restricts to an open embedding on an open neighbourhood `U` of `x`, then `c ∘ g` has degree
`±1`. -/
theorem isUnit_degree_pontryaginThomSphereMap_comp {f : S → M}
    {τ : S × (Fin (k + 1) → ℝ) → M} (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) (g : C(P, M)) {x : P}
    (hx : g ⁻¹' range f = {x}) {U : Set P} (hUo : IsOpen U) (hxU : x ∈ U)
    (hgU : IsOpenEmbedding fun z : U ↦ pontryaginThomCollapse τ (g z)) :
    IsUnit (o.degree o' hE ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g)) := by
  have := connectedSpace_sphere (k := k)
  have hgx : g x ∈ range f := hx.symm.subset (mem_singleton x)
  -- On `U`, the collapse along `g` is the normal coordinate of `g` read in the sphere.
  have hcU :
      IsOpenEmbedding (((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g).restrict U) := by
    rw [ContinuousMap.coe_restrict, ContinuousMap.coe_comp, coe_pontryaginThomSphereMap]
    exact (onePointHomeomorphSphere (k + 1) s₀).isOpenEmbedding.comp hgU
  refine o.isUnit_degree_of_isOpenEmbedding o' hE finrank_euclideanSpace_fin
    ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g).continuous.isProperMap
    (ext fun z ↦ ?_) hUo hxU hcU
  rw [mem_preimage, mem_singleton_iff, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
    (h.pontryaginThomSphereMap_eq_iff s₀).2 hgx, h.pontryaginThomSphereMap_eq_iff s₀,
    ← mem_preimage, hx, mem_singleton_iff]

/-- **A sphere meeting the core once, transversely, maps with degree `±1`.** Let `c` be the
Pontryagin–Thom collapse onto `Sⁿ⁺²` of a framed tube `τ` around `f : S → M`, and `g : Sⁿ⁺² → M` a
map meeting the core `f(S)` only at `x`, transversely: its normal coordinate
`pontryaginThomCollapse τ ∘ g` restricts to an open embedding on an open neighbourhood `U` of `x`.
Then `c ∘ g : Sⁿ⁺² → Sⁿ⁺²` induces a bijection on `Hₙ₊₂(Sⁿ⁺²; ℤ)`. -/
theorem bijective_singularHomologyMap_pontryaginThomSphereMap_comp {n : ℕ} {f : S → M}
    {τ : S × (Fin (n + 2) → ℝ) → M} (h : IsFramedTube f τ)
    (s₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)
    (g : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, M)) {x : sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1} (hx : g ⁻¹' range f = {x}) {U : Set (sphere (0 : EuclideanSpace ℝ
      (Fin (n + 3))) 1)} (hUo : IsOpen U) (hxU : x ∈ U)
    (hgU : IsOpenEmbedding fun z : U ↦ pontryaginThomCollapse τ (g z)) :
    Function.Bijective (ContinuousMap.singularHomologyMap ℤ (n + 2)
      ((pontryaginThomSphereMap h.isOpenEmbedding s₀).comp g)) := by
  -- The sphere `Sⁿ⁺²` is simply connected, hence connected and orientable.
  have := simplyConnectedSpace_sphere_euclideanSpace (n := n + 2) (by omega)
  obtain ⟨o⟩ := HomologicalOrientation.nonempty_of_simplyConnectedSpace
    (M := sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (d := n + 2)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n + 2))
  exact (o.bijective_singularHomologyMap_iff_isUnit_degree o finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin _).2
    (h.isUnit_degree_pontryaginThomSphereMap_comp o o finrank_euclideanSpace_fin s₀ g hx hUo hxU
      hgU)

end IsFramedTube

end TauCeti
