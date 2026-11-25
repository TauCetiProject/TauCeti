/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.Analysis.Complex.Conformal.LocalIndex
public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The homological degree of a holomorphic map between Riemann surfaces

A map `f : X → Y` between Riemann surfaces has two kinds of multiplicities. The analytic ones
count preimages with their orders of vanishing: the local multiplicity
`TauCeti.RiemannSurface.localMultiplicity f x` is the order of vanishing of `f - f x` read in
holomorphic charts, and the fibre sum `TauCeti.RiemannSurface.fiberMultiplicitySum f y` adds them
over the fibre of `y`. For a map from a compact surface to a connected one which is holomorphic
everywhere and constant near no point, every fibre sum is the degree
`TauCeti.RiemannSurface.degree f`. The topological ones come from local homology, for the
canonical homological orientations `TauCeti.complexHomologicalOrientation` of the complex
structures: the local index `TauCeti.HomologicalOrientation.localIndex` of `f` at an isolated
point of its fibre, the local degree `TauCeti.HomologicalOrientation.localDegree` at a point with
compact fibre, and the degree `TauCeti.HomologicalOrientation.degree` of a proper map to a
connected surface. The degree is characterized by `f_*[X]_{f⁻¹(K)} = deg f • [Y]_K`, for the
fundamental classes relative to compact subsets `K ⊆ Y` and their preimages
(`TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_preimage`); for compact `X`
and `Y` it gives `f_*[X] = deg f • [Y]` in ordinary homology
(`TauCeti.HomologicalOrientation.mapFundamentalClass_eq_degree_smul`). This file shows that the
analytic and topological multiplicities agree.

* At a point near which `f` is holomorphic, the local index of `f` is its local multiplicity
  (`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation`). So the local index of a
  holomorphic map is never negative, and it is positive exactly when `f` is not constant near the
  point (`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_pos_iff`).
* Over a point with finite fibre, near each point of which `f` is holomorphic, the local degree of
  `f` is the fibre sum (`TauCeti.RiemannSurface.localDegree_complexHomologicalOrientation`).
* A proper map to a connected Riemann surface has homological degree equal to the fibre sum
  over any point `y` near whose preimages it is holomorphic and not constant
  (`TauCeti.RiemannSurface.degree_complexHomologicalOrientation`). That fibre is compact, hence
  finite (`TauCeti.RiemannSurface.finite_preimage_singleton_of_isCompact`). The source need not be
  compact, as for a proper projection of an open curve onto a disc.
* For compact `X`, the comparison of the homological degree with the degree of a finite
  holomorphic map
  (`TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_complexHomologicalOrientation`, in
  `TauCeti.Analysis.Complex.RiemannSurface.FundamentalClass`) is derived from this.

The local statement reduces to the plane. In the charts at `x` and `f x`, restricted to open
subsets on which `f` maps the first into the second, the canonical orientations are pulled back
from that of `ℂ` (`TauCeti.comap_complexHomologicalOrientation_of_mem_maximalAtlas`), the local
index is natural under these open embeddings (`TauCeti.HomologicalOrientation.localIndex_comap`),
and in the plane the local index of a holomorphic map is its order of vanishing
(`TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub`). The degree
statements then follow by summing local indices over a fibre
(`TauCeti.HomologicalOrientation.localDegree_eq_sum_localIndex`).

The topological degree is defined for continuous maps and is invariant under proper homotopies,
so these identities let a count of holomorphic preimages with multiplicities be computed from
homology, and conversely let the homological degree of a proper map to a connected surface be read
off from a single fibre near whose points the map is holomorphic and not constant.

## Main results

* `TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation`: the local index of a
  holomorphic map is its local multiplicity.
* `TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_pos_iff`: it is positive
  exactly when the map is not constant near the point.
* `TauCeti.RiemannSurface.localDegree_complexHomologicalOrientation`: the local degree over a
  finite fibre is the fibre sum of local multiplicities.
* `TauCeti.RiemannSurface.degree_complexHomologicalOrientation`: the degree of a proper map is
  the fibre sum over a point near whose preimages it is holomorphic and not constant.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (the degree of a holomorphic map).
-/

public section

open Filter IsManifold Set Topology TopologicalSpace

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]

/-- **The local index of a holomorphic map is its local multiplicity.** If `f : X → Y` is
holomorphic near `x`, its local index at `x`, for the canonical homological orientations of `X`
and `Y`, is the local multiplicity of `f` at `x`. Both are `0` when `f` is constant near `x`. -/
theorem localIndex_complexHomologicalOrientation (f : C(X, Y)) {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    (complexHomologicalOrientation X).localIndex (complexHomologicalOrientation Y) f x =
      localMultiplicity f x := by
  rw [localMultiplicity_def]
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  -- The open sets `U = c.source ∩ f⁻¹ c'.source` and `V = c'.source`, with `f` restricted to a map
  -- `g : U → V`, embedded into `ℂ` by the charts.
  let U : Opens X :=
    ⟨c.source ∩ f ⁻¹' c'.source, c.open_source.inter (c'.open_source.preimage f.continuous)⟩
  let V : Opens Y := ⟨c'.source, c'.open_source⟩
  let g : C(U, V) := ⟨fun u ↦ ⟨f u, u.property.2⟩, by fun_prop⟩
  let x' : U := ⟨x, mem_chart_source ℂ x, mem_chart_source ℂ (f x)⟩
  have hU : (U : Set X) ⊆ c.source := inter_subset_left
  have hj : IsOpenEmbedding (c ∘ Subtype.val : U → ℂ) :=
    c.isOpenEmbedding_comp U.isOpenEmbedding' (by simpa using hU)
  have hk : IsOpenEmbedding (c' ∘ Subtype.val : V → ℂ) :=
    c'.isOpenEmbedding_comp V.isOpenEmbedding' (by simp [V])
  -- The local index of `f` at `x` is that of `g` at `x'`, for the restricted orientations, which
  -- are the orientations pulled back from `ℂ` along the charts.
  have h := (complexHomologicalOrientation X).localIndex_comap
    (complexHomologicalOrientation Y) Complex.finrank_real_complex U.isOpenEmbedding'
    V.isOpenEmbedding' (f := g) (g := f) (x := x') (.of_forall fun _ ↦ rfl)
  rw [comap_subtypeVal_complexHomologicalOrientation,
    comap_subtypeVal_complexHomologicalOrientation,
    ← comap_complexHomologicalOrientation_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hU,
    ← comap_complexHomologicalOrientation_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x))
      (U := V) subset_rfl,
    (complexHomologicalOrientation ℂ).localIndex_comap_eq_analyticOrderNatAt_sub hj hk
      (φ := fun z ↦ c' (f (c.symm z))) ?_ ?_] at h
  · simpa [x', c.left_inv (mem_chart_source ℂ x)] using h.symm
  · exact .of_forall fun z ↦ by simp [g, c.left_inv (hU z.property)]
  · simpa [x'] using analyticAt_chartAt_comp_comp_chartAt_symm hf

/-- **Positivity of the local index of a holomorphic map.** If `f : X → Y` is holomorphic near `x`,
its local index at `x`, for the canonical homological orientations, is positive exactly when `f` is
not constant near `x`. -/
theorem localIndex_complexHomologicalOrientation_pos_iff (f : C(X, Y)) {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    0 < (complexHomologicalOrientation X).localIndex (complexHomologicalOrientation Y) f x ↔
      ¬ EventuallyConst f (𝓝 x) := by
  rw [localIndex_complexHomologicalOrientation f hf, Nat.cast_pos, localMultiplicity_pos_iff hf]

/-- **The local degree of a holomorphic map is its fibre sum.** If the fibre of `f : X → Y` over
`y` is finite and `f` is holomorphic near each of its points, the local degree of `f` at `y`, for
the canonical homological orientations, is the number of preimages of `y` counted with local
multiplicities. -/
theorem localDegree_complexHomologicalOrientation (f : C(X, Y)) {y : Y}
    (hy : (f ⁻¹' {y}).Finite)
    (hf : ∀ x ∈ f ⁻¹' {y}, ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z) :
    (complexHomologicalOrientation X).localDegree (complexHomologicalOrientation Y)
      Complex.finrank_real_complex f y = fiberMultiplicitySum f y := by
  rw [HomologicalOrientation.localDegree_eq_sum_localIndex _ _ Complex.finrank_real_complex
    Complex.finrank_real_complex f hy, fiberMultiplicitySum_eq_sum hy, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x hx ↦
    localIndex_complexHomologicalOrientation f (hf x (hy.mem_toFinset.1 hx))

/-- **The degree of a proper holomorphic map is its fibre sum.** Let `f : X → Y` be a proper map
to a connected Riemann surface which, near each point of the fibre over `y`, is holomorphic and
not constant. Then the degree of `f`, for the canonical homological orientations, is the number of
preimages of `y` counted with local multiplicities. -/
theorem degree_complexHomologicalOrientation [PreconnectedSpace Y] {f : C(X, Y)}
    (hp : IsProperMap f) {y : Y}
    (hf : ∀ x ∈ f ⁻¹' {y}, ∀ᶠ z in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f z)
    (hne : ∀ x ∈ f ⁻¹' {y}, ¬ EventuallyConst f (𝓝 x)) :
    (complexHomologicalOrientation X).degree (complexHomologicalOrientation Y)
      Complex.finrank_real_complex f = fiberMultiplicitySum f y := by
  rw [← HomologicalOrientation.localDegree_eq_degree _ _ _ Complex.finrank_real_complex hp y]
  exact localDegree_complexHomologicalOrientation f
    (finite_preimage_singleton_of_isCompact (hp.isCompact_preimage isCompact_singleton) hf hne) hf

end TauCeti.RiemannSurface
