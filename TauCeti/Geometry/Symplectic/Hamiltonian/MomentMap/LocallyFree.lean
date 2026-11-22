/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
public import TauCeti.Geometry.Manifold.Submersion.ConvexChart
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConvexHull
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Chart

/-!
# Convexity of moment maps of actions that are locally free off their fixed points

Let a Lie group `G` act smoothly on a finite-dimensional boundaryless manifold `M` with a two-form
`σ`, with moment map `μ : M → 𝔤*`. Read in the continuous dual `𝔤*`, `μ` is a smooth map whose
differential at `x` is the moment-map differential `dμ_x`, `⟨dμ_x(v), ξ⟩ = σ(ξ_M x, v)`. Where `σ`
is nondegenerate, `dμ_x` is surjective exactly when the isotropy algebra `𝔤_x` is trivial, that
is, when the action is locally free at `x`
(`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff`). At such a point `μ` is a
submersion, so the submersion normal form gives arbitrarily small convexity charts of `μ` around
`x` (`ContMDiffOn.exists_isConvexChart_subset_of_surjective_mfderiv`).

At a fixed point of a compact commutative Lie group, the weight normal form gives convexity charts
too (`TauCeti.SmoothTwoForm.IsMomentMap.exists_isConvexChart_subset`). So when every point of `M`
is either fixed by `G` or has trivial isotropy algebra, every point lies in a convexity chart of
`μ`, and the local-to-global principle (`IsProperMap.convex_range_of_isConvexChart`) applies to the
proper map `μ` of a compact connected `M`: **the image of `μ` is convex and its fibres are
connected**. For a compact connected commutative `G`, the image of `μ` lies in the convex hull of
the images of the fixed points
(`TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`), so it is that
convex hull.

The hypothesis always holds for a circle, a compact connected commutative Lie group of dimension
one: its isotropy algebras are `0` or all of `𝔤`, and a point whose isotropy algebra is `𝔤` is a
critical point of every component of `μ`, hence fixed. This gives **Atiyah's connectedness
theorem for Hamiltonian circle actions**: on a compact connected symplectic manifold the fibres
of the moment map of a circle action are connected, and its image is the interval spanned by the
values at the fixed points. For a torus of higher dimension the points whose isotropy algebra is
neither `0` nor `𝔤` need the local normal form of the action at points with nontrivial
stabilizers.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `contMDiff_toContinuousLinearMap`, `mfderiv_toContinuousLinearMap_apply`: a moment map read
  in the continuous dual is smooth, with differential `dμ_x`.
* `exists_isConvexChart_subset_of_isotropy_eq_bot`: a moment map has arbitrarily small convexity
  charts around every point where the action is locally free and `σ` is nondegenerate.
* `convex_range_of_forall_mem_fixedPoints_or_isotropy_eq_bot`,
  `isPreconnected_preimage_singleton_of_forall_mem_fixedPoints_or_isotropy_eq_bot`: if every
  point is fixed or locally free, the moment map of a compact commutative group on a compact
  connected symplectic manifold has convex image and connected fibres.
* `range_eq_convexHull_image_fixedPoints_of_forall_mem_fixedPoints_or_isotropy_eq_bot`: for
  connected `G`, the image is the convex hull of the images of the fixed points.
* `mem_fixedPoints_or_isotropy_eq_bot_of_finrank_eq_one`: a circle action is locally free off its
  fixed points.
* `isPreconnected_preimage_singleton_of_finrank_eq_one`,
  `range_eq_convexHull_image_fixedPoints_of_finrank_eq_one`: Atiyah's theorem for circle actions.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (connectedness of the fibres of the moment map of a circle action).
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Sections 3–4 (local convexity data of moment maps).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27.
-/

public section

noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### Regular points of a moment map -/

section Regular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- A moment map, read in the continuous dual `𝔤*`, is smooth. -/
theorem contMDiff_toContinuousLinearMap
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) :
    ContMDiff I' 𝓘(ℝ, StrongDual ℝ E) ∞
      fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E) :=
  -- The evaluations of `LinearMap.toContinuousLinearMap (μ x)` are the components `μ_ξ`.
  fun _ ↦ contMDiffAt_clm_apply.2 fun ξ ↦ (h.contMDiff ξ).contMDiffAt

/-- The differential of a moment map, read in the continuous dual `𝔤*`, is the moment-map
differential `dμ_x`. -/
theorem mfderiv_toContinuousLinearMap_apply
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (x : M)
    (v : TangentSpace I' x) :
    mfderiv I' 𝓘(ℝ, StrongDual ℝ E)
        (fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)) x v =
      LinearMap.toContinuousLinearMap (h.differential x v) := by
  have hf := (h.contMDiff_toContinuousLinearMap.mdifferentiableAt (by simp) : MDifferentiableAt _ _
    (fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)) x)
  refine ContinuousLinearMap.ext fun ξ ↦ ?_
  -- Evaluation at `ξ` is continuous linear, so it commutes with the differential.
  have hcomp : (fun y ↦ μ y ξ) =
      ContinuousLinearMap.apply ℝ ℝ ξ ∘
        fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E) := by
    ext y
    simp only [comp_apply, ContinuousLinearMap.apply_apply]
    -- `LinearMap.toContinuousLinearMap` keeps the underlying function.
    exact (LinearMap.coe_toContinuousLinearMap' (μ y)).symm ▸ rfl
  have h' := mfderiv_comp_apply x (ContinuousLinearMap.apply ℝ ℝ ξ).mdifferentiableAt hf v
  rw [← hcomp, (ContinuousLinearMap.apply ℝ ℝ ξ).mfderiv_eq] at h'
  -- Both sides are `dμ_ξ (v)`, up to the evaluation of `LinearMap.toContinuousLinearMap`.
  exact h'.symm.trans ((mvfderiv_apply_eq_mfderiv_apply (fun y ↦ μ y ξ) x v).symm.trans
    (h.differential_apply x v ξ).symm)

end Regular

section RegularChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Convexity charts at locally free points.** Let a Lie group `G` act smoothly on a
finite-dimensional boundaryless manifold `M` with a two-form `σ`, with moment map `μ`. At a point
`x` where `σ` is nondegenerate and the isotropy algebra `𝔤_x` is trivial, `μ` is a submersion, and
every neighbourhood of `x` contains a convexity chart of `μ`, read in the continuous dual `𝔤*`,
containing `x`. -/
theorem exists_isConvexChart_subset_of_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) {x : M}
    (hσ : (σ.bilinFormAt x).Nondegenerate)
    (hx : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) {N : Set M} (hN : N ∈ 𝓝 x) :
    ∃ U ⊆ N, x ∈ U ∧
      IsConvexChart (fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)) U := by
  refine h.contMDiff_toContinuousLinearMap.contMDiffOn
    |>.exists_isConvexChart_subset_of_surjective_mfderiv isOpen_univ (mem_univ x) (by simp)
      (fun (φ : StrongDual ℝ E) ↦ ?_) hN
  obtain ⟨v, hv⟩ := (h.differential_surjective_iff hσ).2 hx (φ : E →ₗ[ℝ] ℝ)
  refine ⟨v, ?_⟩
  rw [h.mfderiv_toContinuousLinearMap_apply, hv]
  -- `LinearMap.toContinuousLinearMap` keeps the underlying function.
  exact ContinuousLinearMap.ext fun _ ↦ rfl

end RegularChart

/-! ### Actions that are locally free off their fixed points -/

section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

omit [CompactSpace M] [ConnectedSpace M] [T2Space M] in
/-- If every point is fixed or locally free, every point lies in a convexity chart of `μ`. -/
private theorem exists_isConvexChart_of_forall_mem_fixedPoints_or_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hfree : ∀ x, x ∈ MulAction.fixedPoints G M ∨
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) (x : M) :
    ∃ U, x ∈ U ∧
      IsConvexChart (fun y ↦ (LinearMap.toContinuousLinearMap (μ y) : StrongDual ℝ E)) U := by
  rcases hfree x with hx | hx
  · obtain ⟨U, -, hxU, -, hU⟩ := h.exists_isConvexChart_subset hσ hG hx Filter.univ_mem
    exact ⟨U, hxU, hU⟩
  · obtain ⟨U, -, hxU, hU⟩ := h.exists_isConvexChart_subset_of_isotropy_eq_bot
      (hσ.isNondegenerate.nondegenerate_bilinFormAt x) hx Filter.univ_mem
    exact ⟨U, hxU, hU⟩

/-- **Convexity for actions that are locally free off their fixed points.** Let a compact
commutative Lie group `G` act smoothly on a compact connected boundaryless symplectic manifold
`(M, σ)`, preserving `σ`, with moment map `μ`. If every point of `M` is fixed by `G` or has trivial
isotropy algebra, then the image of `μ` is convex. -/
theorem convex_range_of_forall_mem_fixedPoints_or_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hfree : ∀ x, x ∈ MulAction.fixedPoints G M ∨
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) :
    Convex ℝ (range μ) := by
  have hc := h.contMDiff_toContinuousLinearMap.continuous.isProperMap
    |>.convex_range_of_isConvexChart
      (h.exists_isConvexChart_of_forall_mem_fixedPoints_or_isotropy_eq_bot hσ hG hfree)
  -- Transport back along the linear equivalence `𝔤* ≃ StrongDual ℝ 𝔤`, stated for families of
  -- functionals on the model space `E` of `𝔤`.
  have key : ∀ ν : M → Module.Dual ℝ E,
      Convex ℝ (range fun x ↦ (LinearMap.toContinuousLinearMap (ν x) : StrongDual ℝ E)) →
        Convex ℝ (range ν) := fun ν hν ↦ by
    have hν' := hν.linear_image (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E)
      (F' := ℝ)).symm.toLinearMap
    simpa [← range_comp, Function.comp_def] using hν'
  exact key μ hc

/-- **Connected fibres for actions that are locally free off their fixed points.** Let a compact
commutative Lie group `G` act smoothly on a compact connected boundaryless symplectic manifold
`(M, σ)`, preserving `σ`, with moment map `μ`. If every point of `M` is fixed by `G` or has trivial
isotropy algebra, then every fibre of `μ` is preconnected, so connected when nonempty. -/
theorem isPreconnected_preimage_singleton_of_forall_mem_fixedPoints_or_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hfree : ∀ x, x ∈ MulAction.fixedPoints G M ∨
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥)
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    IsPreconnected (μ ⁻¹' {ν}) := by
  have hc := (h.contMDiff_toContinuousLinearMap.continuous.isProperMap)
    |>.isPreconnected_preimage_singleton_of_isConvexChart
      (h.exists_isConvexChart_of_forall_mem_fixedPoints_or_isotropy_eq_bot hσ hG hfree)
      (LinearMap.toContinuousLinearMap ν)
  convert hc using 1
  ext x
  exact (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).injective.eq_iff.symm

variable [PreconnectedSpace G]

/-- **The image is the convex hull of the fixed-point images.** Let a compact connected
commutative Lie group `G` act smoothly on a compact connected boundaryless symplectic manifold
`(M, σ)`, preserving `σ`, with moment map `μ`. If every point of `M` is fixed by `G` or has
trivial isotropy algebra, then `μ(M) = conv μ(M^G)`. -/
theorem range_eq_convexHull_image_fixedPoints_of_forall_mem_fixedPoints_or_isotropy_eq_bot
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hfree : ∀ x, x ∈ MulAction.fixedPoints G M ∨
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥) :
    range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  exact (h.range_subset_convexHull_image_fixedPoints hσ.isNondegenerate).antisymm
    (convexHull_min (image_subset_range μ _)
      (h.convex_range_of_forall_mem_fixedPoints_or_isotropy_eq_bot hσ hG hfree))

omit [I.Boundaryless] [CompactSpace M] [ConnectedSpace M] in
/-- **A circle action is locally free off its fixed points.** Let a compact connected commutative
Lie group `G` of dimension one act smoothly on a boundaryless manifold `M` with a nondegenerate
two-form `σ`, with moment map `μ`. Then every point of `M` is fixed by `G` or has trivial isotropy
algebra. -/
theorem mem_fixedPoints_or_isotropy_eq_bot_of_finrank_eq_one
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (hE : Module.finrank ℝ E = 1) (x : M) :
    x ∈ MulAction.fixedPoints G M ∨ (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  refine or_iff_not_imp_right.2 fun hx ↦ ?_
  -- A nonzero subspace of the line `𝔤` is all of `𝔤`.
  have htop : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊤ := by
    rw [← LieSubalgebra.toSubmodule_inj, LieSubalgebra.top_toSubmodule]
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    rw [show Module.finrank ℝ (GroupLieAlgebra I G) = 1 from hE, Nat.one_le_iff_ne_zero,
      Ne, Submodule.finrank_eq_zero, LieSubalgebra.toSubmodule_eq_bot]
    exact hx
  -- So `x` is critical for every component, in particular for a generic one, whose critical
  -- set is the fixed-point set.
  obtain ⟨ξ, hξ⟩ := (dense_setOf_criticalPoints_eq_fixedPoints G h hσ).nonempty
  rw [← mem_ofPred_eq.mp hξ, h.mem_criticalPoints_iff_mem_isotropy (hσ.nondegenerate_bilinFormAt x),
    htop]
  exact LieSubalgebra.mem_top ξ

/-- **Atiyah's connectedness theorem for circle actions.** Let a compact connected commutative Lie
group `G` of dimension one, a circle, act smoothly on a compact connected boundaryless symplectic
manifold `(M, σ)`, preserving `σ`, with moment map `μ`. Then every fibre of `μ` is preconnected,
so connected when nonempty. -/
theorem isPreconnected_preimage_singleton_of_finrank_eq_one
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hE : Module.finrank ℝ E = 1) (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    IsPreconnected (μ ⁻¹' {ν}) :=
  h.isPreconnected_preimage_singleton_of_forall_mem_fixedPoints_or_isotropy_eq_bot hσ hG
    (h.mem_fixedPoints_or_isotropy_eq_bot_of_finrank_eq_one hσ.isNondegenerate hE) ν

/-- **The image of a circle moment map.** Let a compact connected commutative Lie group `G` of
dimension one, a circle, act smoothly on a compact connected boundaryless symplectic manifold
`(M, σ)`, preserving `σ`, with moment map `μ`. Then `μ(M) = conv μ(M^G)`: the image is the
interval spanned by the values of `μ` at the fixed points. -/
theorem range_eq_convexHull_image_fixedPoints_of_finrank_eq_one
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hE : Module.finrank ℝ E = 1) :
    range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) :=
  h.range_eq_convexHull_image_fixedPoints_of_forall_mem_fixedPoints_or_isotropy_eq_bot hσ hG
    (h.mem_fixedPoints_or_isotropy_eq_bot_of_finrank_eq_one hσ.isNondegenerate hE)

end Global

end TauCeti.SmoothTwoForm.IsMomentMap
