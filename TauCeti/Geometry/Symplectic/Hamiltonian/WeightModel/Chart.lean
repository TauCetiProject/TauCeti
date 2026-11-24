/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.LocalToGlobal
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import TauCeti.Analysis.Normed.Group.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Convexity

/-!
# The moment map near a fixed point, read through a weight chart

Let a compact commutative Lie group `G`, such as a torus, act on a symplectic manifold `(M, σ)`
with moment map `μ`, and let `p` be a fixed point. The weight normal form
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`) gives a chart `z = (q, p)` of `M` at
`p` onto a round ball `‖q‖² + ‖p‖² < r` of `ℂⁿ`, in which `g` acts by `zₖ ↦ χₖ(g) zₖ`, the
fundamental vector fields are those of the weight model, and

`μ = μ(p) - ½ Σₖ (qₖ² + pₖ²) αₖ`

for the weights `αₖ` of the characters `χₖ`. This file reads the local properties of the weight
model (`TauCeti.weightMomentMap`) on `M` through such a chart.

* **The local moment cone.** On the chart, `μ` takes values in `μ(p) - cone{αₖ}`, and it sends
  every neighbourhood of a point `x` of the chart onto a neighbourhood of `μ(x)` in this cone. So
  the germ of `μ` at `x` is the germ of the cone at `μ(x)`: `μ` maps the neighbourhood filter of
  `x` onto that of `μ(x)` within the cone
  (`TauCeti.map_nhds_eq_nhdsWithin_vadd_range_weightMomentMap`).
* **Local convexity.** The part of the chart over each smaller ball `‖q‖² + ‖p‖² < r'` is a
  convexity chart of `μ` (`TauCeti.isConvexChart_source_inter_preimage_setOf_lt`, in the sense of
  `TauCeti.IsConvexChart`): `μ` maps it onto a convex set, it is open onto that image, and the
  points of the ball mapped into a convex set form a preconnected set
  (`TauCeti.isPreconnected_source_inter_preimage_setOf_lt_inter_preimage`).
* **Stabilizers.** `g` fixes a point `x` of the chart exactly when `χₖ(g) = 1` for every
  coordinate `zₖ(x)` that is nonzero (`TauCeti.smul_eq_self_iff_of_weightRotation`).
* **Isotropy algebras and orbit rank.** `ξ` generates a vector field vanishing at `x` exactly
  when `αₖ(ξ) = 0` for every such coordinate, and the orbit tangent space `𝔤·x` has dimension the
  rank of those weights (`TauCeti.mem_isotropy_fundamental_iff_of_mfderiv_eq`,
  `TauCeti.finrank_orbitTangent_fundamental_of_mfderiv_eq`).

These hold for any chart with the stated properties, and the corresponding properties of the
model are `TauCeti.image_mem_nhdsWithin_range_weightMomentMap`,
`TauCeti.isPreconnected_preimage_weightMomentMap_inter`,
`TauCeti.weightRotation_arg_apply_eq_self_iff`, `TauCeti.mem_ker_weightInfinitesimalAction_iff`
and `TauCeti.finrank_range_weightInfinitesimalAction`.

Applied to the weight normal form, they give, at every fixed point `p`, arbitrarily small
`G`-invariant convexity charts of `μ` containing `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_isConvexChart_subset`), and the germ of the image of
`μ` at `p` is that of the cone `μ(p) - cone{αₖ}`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_map_nhds_eq_nhdsWithin_vadd_hull`). These are the local
data that the local-to-global principle (`IsProperMap.convex_range_of_isConvexChart`) consumes at
fixed points in the convexity theorem of Atiyah and Guillemin–Sternberg. Since `μ` takes values in
the algebraic dual `𝔤*` while convexity charts are stated for maps to normed spaces, these
statements read `μ` in the continuous dual, through `LinearMap.toContinuousLinearMap`.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2 (the local form of the moment map at a fixed point).
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Lemmas 2.1–2.2 and Theorem 4.1 (the local convexity data
  of moment maps).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 27.
-/

public section

open Filter Set Topology
open scoped Pointwise Manifold ContDiff

namespace TauCeti

/-! ### Transport through a chart onto a ball -/

section Chart

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
  {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱] {α : ι → StrongDual ℝ 𝔱}
  {e : OpenPartialHomeomorph X (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)}
  {f : X → StrongDual ℝ 𝔱} {ν : StrongDual ℝ 𝔱}

/-- A map that is the weight model moment map read through a chart `e`, up to the constant `ν`,
takes values in the cone `ν - cone{α_i}` on the source of `e`. -/
theorem mapsTo_source_vadd_range_weightMomentMap
    (hf : ∀ x ∈ e.source, f x = ν + weightMomentMap α (e x)) :
    MapsTo f e.source (ν +ᵥ range (weightMomentMap α)) := fun x hx ↦ by
  rw [hf x hx]
  exact vadd_mem_vadd_set (mem_range_self _)

/-- **Local openness onto the moment cone.** A map that is the weight model moment map read through
a chart `e`, up to the constant `ν`, sends every neighbourhood of a point `x` of the source of `e`
onto a neighbourhood of its value at `x` in the cone `ν - cone{α_i}`. -/
theorem image_mem_nhdsWithin_vadd_range_weightMomentMap
    (hf : ∀ x ∈ e.source, f x = ν + weightMomentMap α (e x)) {x : X} (hx : x ∈ e.source)
    {N : Set X} (hN : N ∈ 𝓝 x) :
    f '' N ∈ 𝓝[ν +ᵥ range (weightMomentMap α)] (f x) := by
  -- The model is open onto its image, and `e` is open on its source.
  have h := image_mem_nhdsWithin_range_weightMomentMap α (e x)
    (e.image_mem_nhds hx (inter_mem hN (e.open_source.mem_nhds hx)))
  -- Translate by `ν`.
  have ht := (Homeomorph.addLeft ν).isEmbedding.map_nhdsWithin_eq (range (weightMomentMap α))
    (weightMomentMap α (e x))
  have h' := image_mem_map (m := Homeomorph.addLeft ν) h
  rw [ht] at h'
  simp only [Homeomorph.coe_addLeft, ← hf x hx] at h'
  rw [← image_vadd]
  refine mem_of_superset h' ?_
  rintro _ ⟨_, ⟨_, ⟨y, ⟨hyN, hy⟩, rfl⟩, rfl⟩, rfl⟩
  exact ⟨y, hyN, hf y hy⟩

/-- **The germ of the image is the moment cone.** A map that is the weight model moment map read
through a chart `e`, up to the constant `ν`, maps the neighbourhood filter of a point `x` of the
source of `e` onto the neighbourhood filter of its value at `x` within the cone `ν - cone{α_i}`.
-/
theorem map_nhds_eq_nhdsWithin_vadd_range_weightMomentMap
    (hf : ∀ x ∈ e.source, f x = ν + weightMomentMap α (e x)) {x : X} (hx : x ∈ e.source) :
    map f (𝓝 x) = 𝓝[ν +ᵥ range (weightMomentMap α)] (f x) := by
  -- Near `x`, `f` is the continuous map `ν + μ_model ∘ e`.
  have hcont : ContinuousAt f x := by
    have hd : ContinuousAt (fun y ↦ ν + weightMomentMap α (e y)) x :=
      continuousAt_const.add ((hasFDerivAt_weightMomentMap α (e x)).continuousAt.comp
        (e.continuousAt hx))
    exact hd.congr (eventually_of_mem (e.open_source.mem_nhds hx) fun y hy ↦ (hf y hy).symm)
  refine le_antisymm (fun T hT ↦ ?_) fun T hT ↦
    mem_of_superset (image_mem_nhdsWithin_vadd_range_weightMomentMap hf hx hT)
      (image_preimage_subset f T)
  obtain ⟨V, hV, hVT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hT
  exact mem_map.2 (mem_of_superset
    (inter_mem (hcont.preimage_mem_nhds hV) (e.open_source.mem_nhds hx))
    fun y ⟨hyV, hy⟩ ↦ hVT ⟨hyV, mapsTo_source_vadd_range_weightMomentMap hf hy⟩)

/-- For a chart `e` onto the ball `‖q‖² + ‖p‖² < r`, the ball of radius `min r r'` lies in the
target of `e`. -/
private theorem setOf_lt_min_subset_target {r : ℝ}
    (htarget : e.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) (r' : ℝ) :
    {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < min r r'} ⊆ e.target := fun _ hz ↦ by
  rw [htarget]
  exact lt_of_lt_of_le hz (min_le_left r r')

/-- The points of the source of a chart `e` onto the ball `‖q‖² + ‖p‖² < r` lying over the ball
`‖q‖² + ‖p‖² < r'` and over a set `T` are the image under `e⁻¹` of the points of the smaller of the
two balls lying over `T`. -/
private theorem source_inter_preimage_setOf_lt_eq_symm_image {r : ℝ}
    (htarget : e.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) (r' : ℝ)
    (T : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    e.source ∩ e ⁻¹' ({z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r'} ∩ T) =
      e.symm '' ({z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < min r r'} ∩ T) := by
  rw [e.symm_image_eq_source_inter_preimage
    (inter_subset_left.trans (setOf_lt_min_subset_target htarget r'))]
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, lt_min_iff]
  refine and_congr_right fun hx ↦ ?_
  have hxr : ‖(e x).1‖ ^ 2 + ‖(e x).2‖ ^ 2 < r := by
    simpa only [htarget, mem_ofPred_eq] using e.map_source hx
  tauto

/-- **Preconnected preimages of convex sets.** Let `f` be the weight model moment map read through a
chart `e` onto the ball `‖q‖² + ‖p‖² < r`, up to a constant. Inside the part of the chart over
every ball `‖q‖² + ‖p‖² < r'`, the points mapped into a convex set `S` form a preconnected set. -/
theorem isPreconnected_source_inter_preimage_setOf_lt_inter_preimage
    (hf : ∀ x ∈ e.source, f x = ν + weightMomentMap α (e x)) {r : ℝ}
    (htarget : e.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) (r' : ℝ) {S : Set (StrongDual ℝ 𝔱)}
    (hS : Convex ℝ S) :
    IsPreconnected (e.source ∩ e ⁻¹' {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r'} ∩ f ⁻¹' S) := by
  -- In coordinates, these are the points of a ball mapped by the model into `-ν + S`.
  have hset : e.source ∩ e ⁻¹' {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r'} ∩ f ⁻¹' S =
      e.source ∩ e ⁻¹' ({z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r'} ∩
        weightMomentMap α ⁻¹' ((ν + ·) ⁻¹' S)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨hx, hxr⟩, hxS⟩
      exact ⟨hx, hxr, hf x hx ▸ hxS⟩
    · rintro ⟨hx, hxr, hxS⟩
      exact ⟨⟨hx, hxr⟩, (hf x hx).symm ▸ hxS⟩
  rw [hset, source_inter_preimage_setOf_lt_eq_symm_image htarget, inter_comm]
  refine (isPreconnected_preimage_weightMomentMap_inter α (hS.translate_preimage_right ν)
    (min r r')).image _
    (e.continuousOn_symm.mono (inter_subset_right.trans (setOf_lt_min_subset_target htarget r')))

/-- **Convexity charts from a weight chart.** Let `f` be the weight model moment map read through a
chart `e` onto the ball `‖q‖² + ‖p‖² < r`, up to a constant. Then the part of the chart over every
ball `‖q‖² + ‖p‖² < r'` is a convexity chart of `f`: `f` maps it onto a convex set, it is open
onto this image, and its fibres are preconnected. -/
theorem isConvexChart_source_inter_preimage_setOf_lt
    (hf : ∀ x ∈ e.source, f x = ν + weightMomentMap α (e x)) {r : ℝ}
    (htarget : e.target = {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r}) (r' : ℝ) :
    IsConvexChart f (e.source ∩ e ⁻¹' {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r'}) where
  isOpen := e.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  convex_image := by
    -- The image is the translate by `ν` of the image of the smaller ball under the model.
    have hU := source_inter_preimage_setOf_lt_eq_symm_image htarget r' univ
    simp only [inter_univ] at hU
    rw [hU, image_image, EqOn.image_eq (f₂ := fun z ↦ ν + weightMomentMap α z) fun z hz ↦ ?_,
      ← image_image (ν + ·)]
    · exact (convex_image_weightMomentMap_setOf_lt α (min r r')).translate ν
    have hzt : z ∈ e.target := setOf_lt_min_subset_target htarget r' hz
    simp only [hf _ (e.map_target hzt), e.right_inv hzt]
  image_mem_nhdsWithin W hW hWo x hx :=
    nhdsWithin_mono _ (((mapsTo_source_vadd_range_weightMomentMap hf).mono_left
      inter_subset_left).image_subset)
      (image_mem_nhdsWithin_vadd_range_weightMomentMap hf (hW hx).1 (hWo.mem_nhds hx))
  isPreconnected_inter_preimage_singleton v :=
    isPreconnected_source_inter_preimage_setOf_lt_inter_preimage hf htarget r'
      (convex_singleton v)

/-- **Stabilizers in a weight chart.** If `g` acts at a point `x` of the source of a chart `e` by
the rotation `zₖ ↦ uₖ zₖ` by unit complex numbers, then `g` fixes `x` exactly when `uₖ = 1` for
every coordinate `zₖ(x)` that is nonzero. -/
theorem smul_eq_self_iff_of_weightRotation {G : Type*} [SMul G X] {g : G} {u : ι → Circle}
    {x : X} (hx : x ∈ e.source) (hgx : g • x ∈ e.source)
    (he : e (g • x) = weightRotation (fun k ↦ Complex.arg (u k : ℂ)) (e x)) :
    g • x = x ↔ ∀ k, ((e x).1 k ≠ 0 ∨ (e x).2 k ≠ 0) → u k = 1 := by
  rw [← weightRotation_arg_apply_eq_self_iff, ← he]
  exact ⟨fun h ↦ by rw [h], fun h ↦ e.injOn hgx hx h⟩

end Chart

/-! ### Isotropy algebras and orbit rank in a weight chart -/

section Infinitesimal

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {ι : Type*} [Fintype ι] {α : ι → StrongDual ℝ E}
  {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    M (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞}
  {x : M}

/-- **Isotropy algebras in a weight chart.** If the differential of a chart at a point `x` of its
source carries the fundamental vector field of `ξ` to that of the weight model, then `ξ` generates
a vector field vanishing at `x` exactly when `αₖ(ξ) = 0` for every coordinate `zₖ(x)` that is
nonzero. -/
theorem mem_isotropy_fundamental_iff_of_mfderiv_eq (hx : x ∈ chart.source)
    {ξ : GroupLieAlgebra I G}
    (hgen : mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) chart x
      (fundamentalVectorField I' ξ x) = weightInfinitesimalAction α (chart x) ξ) :
    ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x ↔
      ∀ k, ((chart x).1 k ≠ 0 ∨ (chart x).2 k ≠ 0) → α k ξ = 0 := by
  rw [InfinitesimalAction.mem_isotropy_iff, InfinitesimalAction.fundamental_apply,
    ← (chart.bijective_mvfderiv (by simp) hx).1.eq_iff' (map_zero _),
    mvfderiv_apply_eq_mfderiv_apply, hgen]
  exact LinearMap.mem_ker.symm.trans (mem_ker_weightInfinitesimalAction_iff α (chart x) ξ)

/-- **Orbit rank in a weight chart.** In a chart whose differential carries the fundamental vector
fields of the action to those of the weight model, the orbit tangent space `𝔤·x` at a point `x` of
the source has dimension the rank of the weights `αₖ` for which the coordinate `zₖ(x)` is
nonzero. -/
theorem finrank_orbitTangent_fundamental_of_mfderiv_eq (hx : x ∈ chart.source)
    (hgen : ∀ ξ : GroupLieAlgebra I G,
      mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) chart x
        (fundamentalVectorField I' ξ x) = weightInfinitesimalAction α (chart x) ξ) :
    Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) =
      Module.finrank ℝ
        (Submodule.span ℝ (α '' {k | (chart x).1 k ≠ 0 ∨ (chart x).2 k ≠ 0})) := by
  -- The differential of the chart carries the orbit tangent space isomorphically onto the range
  -- of the infinitesimal action of the model.
  have hcomp : (mvfderiv I' chart x).toLinearMap ∘ₗ
      (InfinitesimalAction.fundamental I G I' M).eval x = weightInfinitesimalAction α (chart x) :=
    LinearMap.ext fun ξ ↦ by
      rw [LinearMap.comp_apply, InfinitesimalAction.eval_apply,
        InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe,
        mvfderiv_apply_eq_mfderiv_apply]
      exact hgen ξ
  rw [InfinitesimalAction.orbitTangent_eq_range,
    (Submodule.equivMapOfInjective _ (chart.bijective_mvfderiv (by simp) hx).1
      (LinearMap.range ((InfinitesimalAction.fundamental I G I' M).eval x))).finrank_eq,
    ← LinearMap.range_comp, hcomp]
  exact finrank_range_weightInfinitesimalAction α (chart x)

end Infinitesimal

/-! ### Convexity charts at a fixed point -/

/-- The moment map identity `μ(x) = μ(p) + μ_model(chart x)` of a weight chart, read in the
continuous dual. -/
private theorem toContinuousLinearMap_eq_add_weightMomentMap
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {α : ι → StrongDual ℝ E}
    {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      M (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞}
    {μ : M → Module.Dual ℝ E} {p : M}
    (hμ : ∀ x ∈ chart.source, ∀ ξ, μ x ξ = μ p ξ + weightMomentMap α (chart x) ξ) :
    ∀ x ∈ chart.toOpenPartialHomeomorph.source,
      (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E) =
        LinearMap.toContinuousLinearMap (μ p) +
          weightMomentMap α (chart.toOpenPartialHomeomorph x) := fun x hx ↦ by
  ext ξ
  simp [LinearMap.coe_toContinuousLinearMap', PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    hμ x hx]

namespace SmoothTwoForm.IsMomentMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] {σ : SmoothTwoForm I' M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Small invariant convexity charts at a fixed point.** Let a compact commutative Lie group `G`
act smoothly on a finite-dimensional symplectic manifold `(M, σ)` without boundary, preserving
`σ`, with moment map `μ`, and let `p` be a fixed point. Then every neighbourhood of `p` contains a
`G`-invariant convexity chart of `μ`, read in the continuous dual `𝔤*`, containing `p`. -/
theorem exists_isConvexChart_subset
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ U ⊆ N, p ∈ U ∧ (∀ g : G, ∀ x ∈ U, g • x ∈ U) ∧
      IsConvexChart (fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) U := by
  obtain ⟨n, χ, α, chart, r, -, -, hpchart, hchartp, -, htarget, hequiv, -, -, hμchart⟩ :=
    hμ.exists_weightModelChart hσ hG hp
  have hf := toContinuousLinearMap_eq_add_weightMomentMap (E := E) hμchart
  set e := chart.toOpenPartialHomeomorph
  -- Shrink the chart to a ball whose preimage lies in `N`.
  have he0 : e p = 0 := by simp [e, hchartp]
  obtain ⟨r', hr', hr'N⟩ := exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset
    (he0 ▸ e.image_mem_nhds hpchart (inter_mem hN (e.open_source.mem_nhds hpchart)))
  refine ⟨e.source ∩ e ⁻¹' {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r' ^ 2}, fun x ⟨hx, hxr⟩ ↦ ?_,
    ⟨hpchart, by simp [he0, hr']⟩, fun g x ⟨hx, hxr⟩ ↦ ?_,
    isConvexChart_source_inter_preimage_setOf_lt hf htarget _⟩
  · obtain ⟨y, ⟨hyN, hy⟩, hyx⟩ := hr'N hxr
    rwa [← e.injOn hy hx hyx]
  · -- The rotations of the coordinates preserve the balls.
    refine ⟨(hequiv g x hx).1, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, e, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
      (hequiv g x hx).2, norm_fst_sq_add_norm_snd_sq_weightRotation]
    exact hxr

/-- **The local moment cone at a fixed point.** Let a compact commutative Lie group `G` act
smoothly on a finite-dimensional symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ`, and let `p` be a fixed point. Then there are continuous characters
`χₖ : G → S¹`, with real weights `αₖ ∈ 𝔤*` determined by `χₖ (exp ξ) = e^{i αₖ(ξ)}`, such that `μ`,
read in the continuous dual `𝔤*`, maps the neighbourhood filter of `p` onto the neighbourhood
filter of `μ(p)` within the cone `μ(p) - cone{αₖ}`. In other words, near `p` the image of `μ` lies
in this cone, and `μ` maps every neighbourhood of `p` onto a neighbourhood of `μ(p)` in it. -/
theorem exists_map_nhds_eq_nhdsWithin_vadd_hull
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E),
      (∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ)) ∧
      map (fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) (𝓝 p) =
        𝓝[(LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E) +ᵥ
          (PointedCone.hull ℝ (range (-α)) : Set (StrongDual ℝ E))]
          ((LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E)) := by
  obtain ⟨n, χ, α, chart, r, hα, -, hpchart, -, -, -, -, -, -, hμchart⟩ :=
    hμ.exists_weightModelChart hσ hG hp
  refine ⟨n, χ, α, hα, ?_⟩
  have h := map_nhds_eq_nhdsWithin_vadd_range_weightMomentMap
    (e := chart.toOpenPartialHomeomorph)
    (f := fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E))
    (ν := (LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E))
    (toContinuousLinearMap_eq_add_weightMomentMap (E := E) hμchart) hpchart
  rwa [range_weightMomentMap] at h

end SmoothTwoForm.IsMomentMap

end TauCeti
