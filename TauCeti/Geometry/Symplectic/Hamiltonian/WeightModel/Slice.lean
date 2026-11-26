/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Convexity
import TauCeti.Topology.OpenPartialHomeomorph.Germ

/-!
# Local convexity of the slice model of a torus moment map

Let a torus `T` with Lie algebra `𝔱` act on a symplectic manifold with moment map `μ`, and let `x`
be a point whose isotropy algebra `𝔥 ⊆ 𝔱` is not necessarily zero. Choose a complement `𝔪` of
`𝔥` in `𝔱`. In the local normal form of Marle and Guillemin–Sternberg, a neighbourhood of the
orbit of `x` is modelled on `T ×_H (𝔥⁰ × V)`, where `𝔥⁰ ⊆ 𝔱*` is the annihilator of `𝔥` and `V`
is the symplectic slice, a unitary representation of the stabilizer `H` with weights
`βₖ ∈ 𝔥*`. Extending the weights by zero on `𝔪` gives covectors `αₖ ∈ 𝔪⁰ ⊆ 𝔱*`, and the moment
map reads

`μ(θ, a, z) = μ(x) + a - ½ Σₖ |zₖ|² αₖ`,

with `θ` a coordinate along the orbit, on which `μ` does not depend, `a ∈ 𝔥⁰`, and the slice
coordinates `z ∈ ℂ^ι`. The last term is the weight model moment map
`TauCeti.weightMomentMap α`. Since `𝔥⁰ ∩ 𝔪⁰ = 0`, the subspace `A = 𝔥⁰` meets the span of the
weights trivially. At a fixed point `A = 0` and this is the weight model itself; at a point with
trivial isotropy algebra `A = 𝔱*`, the weights vanish and `μ` is a submersion.

This file proves that this model, for any subspace `A` of `𝔱*` meeting the span of the weights
trivially, has the local convexity properties consumed by the local-to-global principle of
Condevaux–Dazord–Molino and Hilgert–Neeb–Plank (`TauCeti.IsConvexChart`). Write
`g(a, z) = a + μ_α(z)` on `A × ℂ^ι`, with `μ_α = TauCeti.weightMomentMap α`.

* **Local openness onto the local cone.** `g` sends every neighbourhood of a point `(a, z)` onto a
  neighbourhood of `g(a, z)` within its image `A + cone{-αₖ}`
  (`TauCeti.image_mem_nhdsWithin_add_range_weightMomentMap`). A continuous linear projection
  `π : 𝔱* → A` vanishing on the span of the weights recovers `a = π(g(a, z))`, so near `g(a, z)`
  the `A`-component of a value moves little, and the remaining weight component is reached from
  near `z` because the weight model is open onto its cone
  (`TauCeti.image_mem_nhdsWithin_range_weightMomentMap`). With an orbit coordinate `θ` and a
  translation by `ν`, the model `(θ, a, z) ↦ ν + a + μ_α(z)` is likewise open onto the local cone
  `ν + A + cone{-αₖ}` (`TauCeti.image_mem_nhdsWithin_vadd_add_range_weightMomentMap`).
* **Convexity charts.** For a preconnected open set `B` of a parameter space, an open convex set
  `U ⊆ 𝔱*` and an invariant ball `R = {‖q‖² + ‖p‖² < r}` of `ℂ^ι`, the product
  `B × (A ∩ U) × R` is a convexity chart of `(θ, a, z) ↦ ν + a + μ_α(z)`
  (`TauCeti.isConvexChart_prod_prod_add_weightMomentMap`). Its image is the convex set
  `ν + (U ∩ A) + μ_α(R)` (`TauCeti.convex_image_add_weightMomentMap_prod`), and its fibre over `v`
  is the product of `B` with a set which, read in `𝔱* × ℂ^ι`, is the image of the preconnected
  set `R ∩ μ_α⁻¹{s | v - ν - s ∈ U ∩ A}` (`TauCeti.isPreconnected_preimage_weightMomentMap_inter`)
  under `z ↦ (v - ν - μ_α(z), z)`
  (`TauCeti.isPreconnected_prod_inter_preimage_add_weightMomentMap`).
* **Transport through a chart.** A map `f` reading as this model in a chart
  `e : X → P × (A × ℂ^ι)` has, when `P` is locally connected, a convexity chart around every point
  of the source of `e` on the zero section `z = 0`, that is, on the orbit
  (`TauCeti.exists_isConvexChart_of_eqOn_add_weightMomentMap`), and the germ of the image of `f`
  at every point of the source is that of the local cone `ν + A + cone{-αₖ}`
  (`TauCeti.map_nhds_eq_nhdsWithin_vadd_add_range_weightMomentMap`). At a point `x` of the zero
  section this is the cone `μ(x) + A + cone{-αₖ}` with vertex `μ(x)`
  (`TauCeti.map_nhds_eq_nhdsWithin_apply_vadd_add_range_weightMomentMap`), the local cone of
  Hilgert, Neeb and Plank.

The disjointness of `A` from the span of the weights is what makes the `A`-component of a value
well defined; it holds in the slice model since `𝔥⁰ ∩ 𝔪⁰ = (𝔥 + 𝔪)⁰ = 0`. Constructing such
charts on a Hamiltonian torus manifold is the local normal form near an orbit; these statements
are its convexity input, as `TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Chart` is for
the weight normal form at a fixed point.

## Main results

* `TauCeti.image_mem_nhdsWithin_add_range_weightMomentMap`: `(a, z) ↦ a + μ_α(z)` is open onto its
  image.
* `TauCeti.image_mem_nhdsWithin_vadd_add_range_weightMomentMap`: so is
  `(θ, a, z) ↦ ν + a + μ_α(z)`, onto the local cone.
* `TauCeti.convex_image_add_weightMomentMap_prod`,
  `TauCeti.isPreconnected_prod_inter_preimage_add_weightMomentMap`: its images of the products of
  convex sets with invariant balls are convex, and its fibres in them are preconnected.
* `TauCeti.isConvexChart_prod_prod_add_weightMomentMap`: products of preconnected open sets, the
  intersections of `A` with open convex sets and invariant balls are convexity charts of the slice
  model.
* `TauCeti.exists_isConvexChart_of_eqOn_add_weightMomentMap`: a map reading as the slice model in
  a chart has convexity charts at the points of the zero section.
* `TauCeti.map_nhds_eq_nhdsWithin_vadd_add_range_weightMomentMap`,
  `TauCeti.map_nhds_eq_nhdsWithin_apply_vadd_add_range_weightMomentMap`: the germ of its image is
  the germ of the local cone, which at a point of the zero section has its vertex there.

## References

* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Theorem 4.1 (the local cones of a moment map, from the
  local normal form near an orbit) and Theorem 3.10 (the local-to-global principle).
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984,
  161–175.
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
-/

public section

open Filter Function Metric Set Topology
open scoped Pointwise

namespace TauCeti

variable {ι : Type*} [Fintype ι] {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

variable {A : Submodule ℝ (StrongDual ℝ 𝔱)} {α : ι → StrongDual ℝ 𝔱}

/-- **The image of a slice chart is convex.** For a convex set `U ⊆ 𝔱*` and every `r`, the map
`(a, z) ↦ a + μ_α(z)` sends the product of `A ∩ U` with the ball `‖q‖² + ‖p‖² < r` onto the convex
set `(U ∩ A) + μ_α({‖q‖² + ‖p‖² < r})`. -/
theorem convex_image_add_weightMomentMap_prod {U : Set (StrongDual ℝ 𝔱)} (hU : Convex ℝ U)
    (r : ℝ) :
    Convex ℝ ((fun y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2) ''
      ((((↑) : A → StrongDual ℝ 𝔱) ⁻¹' U) ×ˢ {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r})) := by
  have h : (fun y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2) ''
      ((((↑) : A → StrongDual ℝ 𝔱) ⁻¹' U) ×ˢ {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r}) =
      (U ∩ A) + weightMomentMap α '' {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r} := by
    ext v
    simp only [mem_image, mem_prod, mem_preimage, Set.mem_add, mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨a, x⟩, ⟨haU, hx⟩, rfl⟩
      exact ⟨a, ⟨haU, a.property⟩, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨haU, ha⟩, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨(⟨a, ha⟩, x), ⟨haU, hx⟩, rfl⟩
  rw [h]
  exact (hU.inter A.convex).add (convex_image_weightMomentMap_setOf_lt α r)

/-- **The fibres of a slice chart are preconnected.** For a convex set `U ⊆ 𝔱*`, every `r` and every
`v`, the points `(a, z)` with `a ∈ A ∩ U` and `‖q‖² + ‖p‖² < r` at which `a + μ_α(z) = v` form a
preconnected set: in `𝔱* × ℂ^ι` it is the image under `z ↦ (v - μ_α(z), z)` of the preconnected
set of points of the ball at which `v - μ_α(z)` lies in the convex set `U ∩ A`. -/
theorem isPreconnected_prod_inter_preimage_add_weightMomentMap {U : Set (StrongDual ℝ 𝔱)}
    (hU : Convex ℝ U) (r : ℝ) (v : StrongDual ℝ 𝔱) :
    IsPreconnected (((((↑) : A → StrongDual ℝ 𝔱) ⁻¹' U) ×ˢ {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r}) ∩
      (fun y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2) ⁻¹' {v}) := by
  set T := (v - ·) ⁻¹' (U ∩ (A : Set (StrongDual ℝ 𝔱)))
  have hT : Convex ℝ T :=
    (hU.inter A.convex).affine_preimage (AffineMap.const ℝ _ v - AffineMap.id ℝ _)
  -- Read the fibre in `𝔱* × ℂ^ι`, where its `𝔱*`-component is `v - μ_α(z)`.
  have hι : IsInducing (Prod.map ((↑) : A → StrongDual ℝ 𝔱)
      (id : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    IsInducing.subtypeVal.prodMap IsInducing.id
  rw [← hι.isPreconnected_image]
  convert (isPreconnected_preimage_weightMomentMap_inter α hT r).image
    (fun x ↦ (v - weightMomentMap α x, x)) (by fun_prop) using 1
  ext ⟨s, x⟩
  simp only [mem_image, mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff, Prod.mk.injEq, T,
    SetLike.mem_coe]
  constructor
  · rintro ⟨⟨a, x⟩, ⟨⟨ha, hx⟩, hv⟩, rfl, rfl⟩
    have hax : v - weightMomentMap α x = a := by rw [← hv, add_sub_cancel_right]
    exact ⟨x, ⟨⟨by rwa [hax], by rw [hax]; exact a.property⟩, hx⟩, hax, rfl⟩
  · rintro ⟨x, ⟨⟨hxU, hxA⟩, hx⟩, rfl, rfl⟩
    exact ⟨(⟨_, hxA⟩, x), ⟨⟨hxU, hx⟩, sub_add_cancel _ _⟩, rfl⟩

variable [FiniteDimensional ℝ 𝔱]

/-- A subspace `A` of `𝔱*` meeting the span of the weights trivially is the range of a continuous
linear projection of `𝔱*` vanishing on that span. -/
private theorem exists_projection (hA : Disjoint A (Submodule.span ℝ (range α))) :
    ∃ π : StrongDual ℝ 𝔱 →L[ℝ] A, (∀ a : A, π a = a) ∧
      ∀ x, π (weightMomentMap α x) = 0 := by
  -- Enlarge the span of the weights to a complement of `A`.
  obtain ⟨C, hsC, hC⟩ := hA.symm.exists_isCompl
  have h : IsCompl A C := hC.symm
  let π₀ : StrongDual ℝ 𝔱 →L[ℝ] StrongDual ℝ 𝔱 :=
    ⟨A.projection _ h, (A.projection _ h).continuous_of_finiteDimensional⟩
  refine ⟨π₀.codRestrict A fun v ↦ Submodule.projection_apply_mem h v, fun a ↦ ?_, fun x ↦ ?_⟩
  · exact Subtype.ext (Submodule.projection_apply_left h a)
  · exact Subtype.ext ((Submodule.projection_apply_eq_zero_iff h).2
      (hsC (weightMomentMap_mem_span α x)))

/-- **The slice model is open onto its image.** If `A` meets the span of the weights trivially,
the map `(a, z) ↦ a + μ_α(z)` on `A × ℂ^ι` sends every neighbourhood of a point `y` onto a
neighbourhood of its value at `y` within its image `A + cone{-αₖ}`. -/
theorem image_mem_nhdsWithin_add_range_weightMomentMap
    (hA : Disjoint A (Submodule.span ℝ (range α)))
    (y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
    {N : Set (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))} (hN : N ∈ 𝓝 y) :
    (fun y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
        (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2) '' N ∈
      𝓝[(A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α)]
        ((y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2) := by
  obtain ⟨π, hπA, hπw⟩ := exists_projection hA
  obtain ⟨u, hu, n, hn, hun⟩ := mem_nhds_prod_iff.1 hN
  set v₀ := (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2
  have hπv (a : A) (x) : π ((a : StrongDual ℝ 𝔱) + weightMomentMap α x) = a := by
    rw [map_add, hπA, hπw, add_zero]
  -- Near `v₀`, the `A`-component `π v` of a value `v` is near `y.1`, and on the image the rest
  -- `v - π v` is a value of the weight model near `μ_α(y.2)`.
  have h₁ : Tendsto π (𝓝[(A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α)] v₀)
      (𝓝 y.1) := by
    rw [← hπv y.1 y.2]
    exact π.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h₂ : Tendsto (fun v ↦ v - (π v : StrongDual ℝ 𝔱))
      (𝓝[(A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α)] v₀)
      (𝓝[range (weightMomentMap α)] (weightMomentMap α y.2)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono ?_⟩
    · have hc : Continuous fun v ↦ v - (π v : StrongDual ℝ 𝔱) := by fun_prop
      have h := hc.continuousAt (x := v₀)
      rw [ContinuousAt, hπv, add_sub_cancel_left] at h
      exact h.mono_left nhdsWithin_le_nhds
    · rintro _ ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      rw [hπv ⟨a, ha⟩ x, add_sub_cancel_left]
  filter_upwards [h₁ hu, h₂ (image_mem_nhdsWithin_range_weightMomentMap α y.2 hn)]
    with v hv₁ hv₂
  obtain ⟨x, hx, hxv⟩ := hv₂
  refine ⟨(π v, x), hun ⟨hv₁, hx⟩, ?_⟩
  dsimp only at hxv ⊢
  rw [hxv, add_sub_cancel]

/-- **The slice model with a parameter is open onto the local cone.** If `A` meets the span of the
weights trivially, the map `(θ, a, z) ↦ ν + a + μ_α(z)` on `P × A × ℂ^ι` sends every neighbourhood
of a point `y` onto a neighbourhood of its value at `y` within the local cone
`ν + A + cone{-αₖ}`. -/
theorem image_mem_nhdsWithin_vadd_add_range_weightMomentMap {P : Type*} [TopologicalSpace P]
    (hA : Disjoint A (Submodule.span ℝ (range α))) (ν : StrongDual ℝ 𝔱)
    (y : P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)))
    {N : Set (P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)))} (hN : N ∈ 𝓝 y) :
    (fun y : P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) ↦
        ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) '' N ∈
      𝓝[ν +ᵥ ((A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α))]
        (ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) := by
  -- The slice of `N` through `y` is a neighbourhood of `y.2`, and translation by `ν` is an
  -- embedding.
  have hN' : (fun x ↦ (y.1, x)) ⁻¹' N ∈ 𝓝 y.2 :=
    (Continuous.prodMk_right y.1).continuousAt.preimage_mem_nhds hN
  have h := image_mem_map (m := Homeomorph.addLeft ν)
    (image_mem_nhdsWithin_add_range_weightMomentMap hA y.2 hN')
  rw [(Homeomorph.addLeft ν).isEmbedding.map_nhdsWithin_eq, Homeomorph.coe_addLeft] at h
  rw [← image_vadd]
  refine mem_of_superset h ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨(y.1, x), hx, rfl⟩

/-- **Convexity charts of the slice model.** Let `A` be a subspace of `𝔱*` meeting the span of the
weights `αₖ` trivially. For a preconnected open set `B` of a topological space `P`, an open convex
set `U ⊆ 𝔱*` and every `r`, the product of `B`, `A ∩ U` and the ball `‖q‖² + ‖p‖² < r` is a
convexity chart of `(θ, a, z) ↦ ν + a - ½ Σₖ |zₖ|² αₖ`. -/
theorem isConvexChart_prod_prod_add_weightMomentMap {P : Type*} [TopologicalSpace P]
    (hA : Disjoint A (Submodule.span ℝ (range α))) (ν : StrongDual ℝ 𝔱) {B : Set P}
    (hBo : IsOpen B) (hB : IsPreconnected B) {U : Set (StrongDual ℝ 𝔱)} (hUo : IsOpen U)
    (hU : Convex ℝ U) (r : ℝ) :
    IsConvexChart
      (fun y : P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) ↦
        ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2))
      (B ×ˢ ((((↑) : A → StrongDual ℝ 𝔱) ⁻¹' U) ×ˢ {x | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 < r})) := by
  set g := fun y : A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ↦
    (y.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2
  refine ⟨hBo.prod ((hUo.preimage continuous_subtypeVal).prod
    (isOpen_lt (by fun_prop) continuous_const)), ?_, fun W _ hWo y hy ↦ ?_, fun v ↦ ?_⟩
  · -- The model ignores the parameter in `P`: the image is a translate of a convex set, or empty.
    rw [show (fun y ↦ ν + g y.2) = (ν + ·) ∘ g ∘ Prod.snd from rfl, image_comp, image_comp]
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · simp only [hBe, empty_prod, image_empty]
      exact convex_empty
    · rw [snd_image_prod hBne]
      exact (convex_image_add_weightMomentMap_prod hU r).translate ν
  · refine nhdsWithin_mono _ ?_
      (image_mem_nhdsWithin_vadd_add_range_weightMomentMap hA ν y (hWo.mem_nhds hy))
    rintro _ ⟨w, -, rfl⟩
    exact vadd_mem_vadd_set ⟨_, w.2.1.property, _, mem_range_self _, rfl⟩
  · -- The fibre of `v` is the product of `B` with the fibre of `v - ν` in the slice chart.
    convert hB.prod (isPreconnected_prod_inter_preimage_add_weightMomentMap (A := A) (α := α) hU r
      (v - ν))
      using 1
    ext ⟨p, y⟩
    simp only [mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hp, hy⟩, hv⟩
      exact ⟨hp, hy, by rw [← hv, add_sub_cancel_left]⟩
    · rintro ⟨hp, hy, hv⟩
      exact ⟨⟨hp, hy⟩, by rw [hv, add_sub_cancel]⟩

variable {X P : Type*} [TopologicalSpace X]

/-- **Convexity charts of a map reading as the slice model.** Let `A` be a subspace of `𝔱*`
meeting the span of the weights `αₖ` trivially. If, in a chart `e : X → P × (A × ℂ^ι)`, a map `f`
reads `(θ, a, z) ↦ ν + a - ½ Σₖ |zₖ|² αₖ` with `P` locally connected, then every point of the
source of `e` sent to the zero section `z = 0` lies in a convexity chart of `f`. -/
theorem exists_isConvexChart_of_eqOn_add_weightMomentMap [TopologicalSpace P]
    [LocallyConnectedSpace P]
    {e : OpenPartialHomeomorph X (P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)))}
    {f : X → StrongDual ℝ 𝔱} {ν : StrongDual ℝ 𝔱} (hA : Disjoint A (Submodule.span ℝ (range α)))
    (hf : EqOn f ((fun y ↦ ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) ∘ e)
      e.source) {x : X} (hx : x ∈ e.source) (hx0 : (e x).2.2 = 0) :
    ∃ U, x ∈ U ∧ IsConvexChart f U := by
  -- A product of a connected open set of `P`, a ball of `A` and a ball `‖q‖² + ‖p‖² < ε²` inside
  -- the target of `e`.
  have hex : e x = ((e x).1, ((e x).2.1, 0)) := Prod.ext rfl (Prod.ext rfl hx0)
  have ht : e.target ∈ 𝓝 ((e x).1, ((e x).2.1, (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))) := by
    rw [← hex]
    exact e.open_target.mem_nhds (e.map_source hx)
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.1 ht
  obtain ⟨a, ha, w', hw', haw⟩ := mem_nhds_prod_iff.1 hw
  obtain ⟨B, ⟨hBo, hxB, hB⟩, hBu⟩ :=
    (LocallyConnectedSpace.open_connected_basis _).mem_iff.1 hu
  obtain ⟨η, hη, hηa⟩ := Metric.mem_nhds_iff.1 ha
  obtain ⟨ε, hε, hεw⟩ := Metric.mem_nhds_iff.1 hw'
  have hRw : {y : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < ε ^ 2} ⊆ w' :=
    fun y hy ↦ by
      refine hεw ?_
      rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
      constructor <;> refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_ <;>
        nlinarith [hy.out, sq_nonneg ‖y.1‖, sq_nonneg ‖y.2‖]
  set D : Set (P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))) := B ×ˢ
    ((((↑) : A → StrongDual ℝ 𝔱) ⁻¹' ball ((e x).2.1 : StrongDual ℝ 𝔱) η) ×ˢ
      {y | ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 < ε ^ 2})
  have hD : IsConvexChart
      (fun y : P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) ↦
        ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) D :=
    isConvexChart_prod_prod_add_weightMomentMap hA ν hBo hB.isPreconnected isOpen_ball
      (convex_ball _ _) (ε ^ 2)
  -- Points of `A` within `η` of `(e x).2.1` in `𝔱*` lie in the ball of `A`.
  have hηa' : ((↑) : A → StrongDual ℝ 𝔱) ⁻¹' ball ((e x).2.1 : StrongDual ℝ 𝔱) η ⊆ a :=
    fun b hb ↦ hηa (by rwa [mem_preimage, mem_ball, ← Subtype.dist_eq] at hb)
  have hDt : D ⊆ e.target := (prod_mono hBu ((prod_mono hηa' hRw).trans haw)).trans huw
  refine ⟨e.source ∩ e ⁻¹' D, ⟨hx, ?_⟩, hD.source_inter_preimage hDt hf⟩
  rw [mem_preimage, hex]
  exact ⟨hxB, mem_ball_self hη, by simpa using pow_pos hε 2⟩

/-- **The germ of the image is the local cone.** Let `A` be a subspace of `𝔱*` meeting the span
of the weights `αₖ` trivially. If, in a chart `e : X → P × (A × ℂ^ι)`, a map `f` reads
`(θ, a, z) ↦ ν + a - ½ Σₖ |zₖ|² αₖ`, then `f` maps the neighbourhood filter of every point `x` of
the source of `e` onto the neighbourhood filter of `f x` within the local cone
`ν + A + cone{-αₖ}`. -/
theorem map_nhds_eq_nhdsWithin_vadd_add_range_weightMomentMap [TopologicalSpace P]
    {e : OpenPartialHomeomorph X (P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)))}
    {f : X → StrongDual ℝ 𝔱} {ν : StrongDual ℝ 𝔱} (hA : Disjoint A (Submodule.span ℝ (range α)))
    (hf : EqOn f ((fun y ↦ ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) ∘ e)
      e.source) {x : X} (hx : x ∈ e.source) :
    map f (𝓝 x) = 𝓝[ν +ᵥ ((A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α))] (f x) :=
  e.map_nhds_eq_nhdsWithin_of_eqOn hf hx (by fun_prop)
    (Eventually.of_forall fun y ↦
      vadd_mem_vadd_set ⟨_, y.2.1.property, _, mem_range_self _, rfl⟩)
    fun _ ↦ image_mem_nhdsWithin_vadd_add_range_weightMomentMap hA ν (e x)

/-- **The local cone at a point of the orbit.** Let `A` be a subspace of `𝔱*` meeting the span of
the weights `αₖ` trivially. If, in a chart `e : X → P × (A × ℂ^ι)`, a map `f` reads
`(θ, a, z) ↦ ν + a - ½ Σₖ |zₖ|² αₖ`, then at every point `x` of the source of `e` on the zero
section `z = 0`, `f` maps the neighbourhood filter of `x` onto the neighbourhood filter of `f x`
within the local cone `f x + A + cone{-αₖ}` with vertex `f x`. -/
theorem map_nhds_eq_nhdsWithin_apply_vadd_add_range_weightMomentMap [TopologicalSpace P]
    {e : OpenPartialHomeomorph X (P × (A × (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)))}
    {f : X → StrongDual ℝ 𝔱} {ν : StrongDual ℝ 𝔱} (hA : Disjoint A (Submodule.span ℝ (range α)))
    (hf : EqOn f ((fun y ↦ ν + ((y.2.1 : StrongDual ℝ 𝔱) + weightMomentMap α y.2.2)) ∘ e)
      e.source) {x : X} (hx : x ∈ e.source) (hx0 : (e x).2.2 = 0) :
    map f (𝓝 x) =
      𝓝[f x +ᵥ ((A : Set (StrongDual ℝ 𝔱)) + range (weightMomentMap α))] (f x) := by
  set a₀ : StrongDual ℝ 𝔱 := ((e x).2.1 : StrongDual ℝ 𝔱)
  have hfx : f x = ν + a₀ := by
    rw [hf hx, comp_apply, hx0, weightMomentMap_zero, add_zero]
  -- Translating by `a₀ ∈ A` does not move `A + cone{-αₖ}`.
  rw [map_nhds_eq_nhdsWithin_vadd_add_range_weightMomentMap hA hf hx, hfx, add_vadd,
    ← vadd_add_assoc a₀, vadd_coe_set (show a₀ ∈ A from (e x).2.1.property)]

end TauCeti
