/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
over the fibre of `y`, which for a map from a compact surface onto a connected one is the degree
`TauCeti.RiemannSurface.degree f`. The topological ones come from local homology, for the
canonical homological orientations `TauCeti.complexHomologicalOrientation` of the complex
structures: the local index `TauCeti.HomologicalOrientation.localIndex` of `f` at an isolated
point of its fibre, the local degree `TauCeti.HomologicalOrientation.localDegree` at a point with
compact fibre, and the degree `TauCeti.HomologicalOrientation.degree` of a proper map, which
computes the image `f_*[X]` of the fundamental class. This file shows that they agree.

* At a point near which `f` is holomorphic, the local index of `f` is its local multiplicity
  (`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation`). So the local index of a
  holomorphic map is never negative, and it is positive exactly when `f` is not constant near the
  point (`TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_pos_iff`).
* Over a point with finite fibre, near each point of which `f` is holomorphic, the local degree of
  `f` is the fibre sum (`TauCeti.RiemannSurface.localDegree_complexHomologicalOrientation`).
* A proper map onto a connected Riemann surface has homological degree equal to the fibre sum
  over any point `y` near whose preimages it is holomorphic and not constant
  (`TauCeti.RiemannSurface.degree_complexHomologicalOrientation`). That fibre is compact, hence
  finite (`TauCeti.RiemannSurface.finite_preimage_singleton_of_isCompact`). The source need not be
  compact, as for a proper projection of an open curve onto a disc.
* For compact `X` the homological degree is the degree of `f`
  (`TauCeti.RiemannSurface.degree_complexHomologicalOrientation_eq_degree`), so
  `f_*[X] = deg f • [Y]` in `H₂(Y; ℤ)` when `Y` is compact too
  (`TauCeti.RiemannSurface.mapFundamentalClass_complexHomologicalOrientation`). Since the degree is
  a natural number, `f_* : H₂(X; ℤ) → H₂(Y; ℤ)` is bijective exactly when `deg f = 1`
  (`TauCeti.RiemannSurface.bijective_singularHomologyMap_iff_degree_eq_one`); a finite holomorphic
  map of degree one is a biholomorphism (`TauCeti.RiemannSurface.biholomorphOfDegreeEqOne`).

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
homology, and conversely let the homological degree of a holomorphic map be read off from a single
fibre.

## Main results

* `TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation`: the local index of a
  holomorphic map is its local multiplicity.
* `TauCeti.RiemannSurface.localIndex_complexHomologicalOrientation_pos_iff`: it is positive
  exactly when the map is not constant near the point.
* `TauCeti.RiemannSurface.localDegree_complexHomologicalOrientation`: the local degree over a
  finite fibre is the fibre sum of local multiplicities.
* `TauCeti.RiemannSurface.degree_complexHomologicalOrientation`: the degree of a proper map is
  the fibre sum over a point near whose preimages it is holomorphic and not constant.
* `TauCeti.RiemannSurface.degree_complexHomologicalOrientation_eq_degree`: for a compact source
  the homological degree is the degree.
* `TauCeti.RiemannSurface.mapFundamentalClass_complexHomologicalOrientation`:
  `f_*[X] = deg f • [Y]` for compact Riemann surfaces.
* `TauCeti.RiemannSurface.bijective_singularHomologyMap_iff_degree_eq_one`: `f_*` is bijective on
  `H₂(-; ℤ)` exactly when `deg f = 1`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (the degree of a holomorphic map).
-/

public section

open Filter Function IsManifold Set Topology TopologicalSpace

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
  let g : C(U, V) := ⟨fun u ↦ ⟨f u, u.2.2⟩, by fun_prop⟩
  let x' : U := ⟨x, mem_chart_source ℂ x, mem_chart_source ℂ (f x)⟩
  have hU : (U : Set X) ⊆ c.source := inter_subset_left
  have hj : IsOpenEmbedding (c ∘ Subtype.val : U → ℂ) :=
    c.isOpenEmbedding_comp U.isOpenEmbedding' (by simpa using hU)
  have hk : IsOpenEmbedding (c' ∘ Subtype.val : V → ℂ) :=
    c'.isOpenEmbedding_comp V.isOpenEmbedding' (by simp [V])
  -- The local index of `f` at `x` is that of `g` at `x'`, for the restricted orientations, which
  -- are the orientations pulled back from `ℂ` along the charts.
  have h := HomologicalOrientation.localIndex_comap Complex.finrank_real_complex
    (complexHomologicalOrientation X) (complexHomologicalOrientation Y) U.isOpenEmbedding'
    V.isOpenEmbedding' (f := g) (g := f) (x := x') (.of_forall fun _ ↦ rfl)
  rw [comap_subtypeVal_complexHomologicalOrientation,
    comap_subtypeVal_complexHomologicalOrientation,
    ← comap_complexHomologicalOrientation_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hU hj,
    ← comap_complexHomologicalOrientation_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x))
      subset_rfl hk,
    (complexHomologicalOrientation ℂ).localIndex_comap_eq_analyticOrderNatAt_sub hj hk
      (φ := fun z ↦ c' (f (c.symm z))) ?_ ?_] at h
  · simpa [x', c.left_inv (mem_chart_source ℂ x)] using h.symm
  · exact .of_forall fun z ↦ by simp [g, c.left_inv (hU z.2)]
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
onto a connected Riemann surface which, near each point of the fibre over `y`, is holomorphic and
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

/-- **The homological degree of a holomorphic map is its degree.** For a holomorphic map `f` from
a compact Riemann surface onto a connected one which is constant near no point, the degree of `f`
for the canonical homological orientations is `TauCeti.RiemannSurface.degree f`. -/
theorem degree_complexHomologicalOrientation_eq_degree [CompactSpace X] [PreconnectedSpace Y]
    {f : C(X, Y)} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    (complexHomologicalOrientation X).degree (complexHomologicalOrientation Y)
      Complex.finrank_real_complex f = degree f := by
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · have : IsEmpty X := f.toFun.isEmpty
    rw [HomologicalOrientation.degree_of_isEmpty, degree_eq_zero_of_isEmpty, Nat.cast_zero]
  · rw [degree_complexHomologicalOrientation f.continuous.isProperMap (y := y)
      (fun _ _ ↦ .of_forall hf) fun x _ ↦ hne x, fiberMultiplicitySum_eq_degree hf hne y]

/-- **A holomorphic map multiplies the fundamental class by its degree.** For a holomorphic map
`f : X → Y` between compact Riemann surfaces, with `Y` connected, which is constant near no point,
`f_*[X] = deg f • [Y]` in `H₂(Y; ℤ)`. -/
theorem mapFundamentalClass_complexHomologicalOrientation [CompactSpace X] [CompactSpace Y]
    [PreconnectedSpace Y] {f : C(X, Y)} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    (complexHomologicalOrientation X).mapFundamentalClass Complex.finrank_real_complex f =
      (degree f : ℤ) • complexFundamentalClass Y := by
  rw [HomologicalOrientation.mapFundamentalClass_eq_degree_smul _ (complexHomologicalOrientation Y)
    _ Complex.finrank_real_complex, degree_complexHomologicalOrientation_eq_degree hf hne,
    complexFundamentalClass_def]

/-- **A holomorphic map is an isomorphism on top homology exactly in degree one.** For a
holomorphic map `f : X → Y` between compact connected Riemann surfaces which is constant near no
point, `f_* : H₂(X; ℤ) → H₂(Y; ℤ)` is bijective exactly when `deg f = 1`. -/
theorem bijective_singularHomologyMap_iff_degree_eq_one [CompactSpace X] [CompactSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y] {f : C(X, Y)} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    Bijective (ContinuousMap.singularHomologyMap ℤ 2 f) ↔ degree f = 1 := by
  rw [HomologicalOrientation.bijective_singularHomologyMap_iff _ (complexHomologicalOrientation Y)
    Complex.finrank_real_complex Complex.finrank_real_complex,
    degree_complexHomologicalOrientation_eq_degree hf hne]
  omega

end TauCeti.RiemannSurface
