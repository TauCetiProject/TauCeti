/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical

/-!
# The affine span of the image of a moment map

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
preconnected manifold `M` with a nondegenerate two-form `σ`, so that `dμ_Z = ι_{Z_M} σ` for every
`Z ∈ 𝔤`. Write `𝔨 = {Z ∈ 𝔤 | Z_M = 0}` for the kernel of the infinitesimal action, the
intersection of all isotropy algebras `𝔤_x`. This file computes the affine span of the image
`μ(M)`, its *affine support*:

`affineSpan ℝ (μ(M)) = μ(x) + 𝔨⁰` for every `x ∈ M`,

where `𝔨⁰ ⊆ 𝔤*` is the annihilator of `𝔨`
(`TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range`). The reason is that a component
`μ_Z = ⟨μ, Z⟩` is constant on the preconnected manifold `M` exactly when its differential
`ι_{Z_M} σ` vanishes, that is, by nondegeneracy, exactly when `Z_M = 0`
(`TauCeti.SmoothTwoForm.IsMomentMap.eq_zero_iff_forall_apply_eq`). So the vectors `Z` killing every
difference `μ(x) - μ(y)` are exactly the elements of `𝔨`, and when `𝔤` is finite-dimensional the
direction of the affine span is the annihilator of `𝔨`. In particular the affine span of `μ(M)`
has dimension `dim 𝔤 - dim 𝔨`, it is all of `𝔤*` exactly when the infinitesimal action is
injective, and `μ` is constant exactly when the action is trivial.

For a smooth action of a Lie group `G`, an element `ξ` of the Lie algebra lies in `𝔨` exactly when
every `exp (t ξ)` acts trivially on `M`, so `𝔨` is the Lie algebra of the kernel `⋂ₓ G_x` of the
action. If the action is effective (`FaithfulSMul G M`), then `𝔨 = 0`, so **the image of the moment
map has full affine dimension `dim G`**: its affine span is all of `𝔤*`
(`TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range_eq_top_of_faithfulSMul`). For a torus acting
on a compact connected symplectic manifold, `μ(M)` is a convex polytope by the convexity theorem
of Atiyah and Guillemin–Sternberg, and a convex set with full affine span has nonempty interior.
So this is the statement that the moment polytope of an effective torus action is full-dimensional.

Neither closedness of `σ` nor equivariance of `μ` is used, and `M` need not be compact.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.eq_zero_iff_forall_apply_eq`: a component `μ_Z` is constant
  exactly when `Z_M = 0`.
* `TauCeti.SmoothTwoForm.IsMomentMap.dualCoannihilator_vectorSpan_range`: the vectors annihilating
  the direction of the affine span of `μ(M)` form the kernel `𝔨` of the infinitesimal action.
* `TauCeti.SmoothTwoForm.IsMomentMap.vectorSpan_range`: the direction of the affine span of `μ(M)`
  is the annihilator `𝔨⁰`.
* `TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range`: the affine span of `μ(M)` is `μ(x) + 𝔨⁰`.
* `TauCeti.SmoothTwoForm.IsMomentMap.finrank_vectorSpan_range_add_finrank_ker`: the affine span of
  `μ(M)` has dimension `dim 𝔤 - dim 𝔨`.
* `TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range_eq_top_iff`: the affine span of `μ(M)` is
  all of `𝔤*` exactly when `𝔨 = 0`.
* `TauCeti.SmoothTwoForm.IsMomentMap.range_subsingleton_iff`: `μ` is constant exactly when the
  infinitesimal action is trivial.
* `TauCeti.SmoothTwoForm.IsMomentMap.mem_dualCoannihilator_vectorSpan_range_iff`: for a group
  action, `ξ` annihilates the direction of the affine span of `μ(M)` exactly when every
  `exp (t ξ)` acts trivially.
* `TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range_eq_top_of_faithfulSMul`,
  `TauCeti.SmoothTwoForm.IsMomentMap.finrank_vectorSpan_range_of_faithfulSMul`: for an effective
  group action, the image of the moment map has full affine dimension `dim G`.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lectures 22 and 27 (moment maps, and torus convexity for effective actions).
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

section Infinitesimal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}

/-- On a preconnected manifold, the component `μ_Z` of a moment map is constant when the generated
vector field `Z_M` vanishes, since its differential is `ι_{Z_M} σ = 0`. -/
theorem apply_eq_apply_of_eq_zero [PreconnectedSpace M] (h : σ.IsMomentMap a μ) {Z : 𝔤}
    (hZ : a Z = 0) (x y : M) : μ x Z = μ y Z := by
  refine MDifferentiable.apply_eq_of_mfderiv_eq_zero (fun y ↦ h.mdifferentiableAt Z y)
    (fun z ↦ ?_) x y
  rw [← mvfderiv_eq_zero_iff]
  ext v
  rw [← h.eval₂_apply, hZ, Pi.zero_apply, SmoothBundleForm.eval₂_zero_left, zero_apply]

/-- For a nondegenerate form, the vector field `Z_M` vanishes when the component `μ_Z` of a moment
map is constant: every point is then a critical point of `μ_Z`. -/
theorem eq_zero_of_forall_apply_eq (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) {Z : 𝔤}
    (hZ : ∀ x y, μ x Z = μ y Z) : a Z = 0 := by
  funext x
  refine (h.mem_criticalPoints_iff (hσ.nondegenerate_bilinFormAt x) Z).1 ?_
  rw [mem_criticalPoints, show (fun y ↦ μ y Z) = fun _ ↦ μ x Z from funext fun y ↦ hZ y x]
  exact mfderiv_const

/-- **Constant components of a moment map.** For a nondegenerate form on a preconnected manifold,
the component `μ_Z = ⟨μ, Z⟩` of a moment map is constant exactly when the generated vector field
`Z_M` vanishes identically. -/
theorem eq_zero_iff_forall_apply_eq [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (hσ : σ.IsNondegenerate) {Z : 𝔤} : a Z = 0 ↔ ∀ x y, μ x Z = μ y Z :=
  ⟨h.apply_eq_apply_of_eq_zero, h.eq_zero_of_forall_apply_eq hσ⟩

/-- On a preconnected manifold, the direction of the affine span of the image of a moment map lies
in the annihilator of the kernel `𝔨 = {Z | Z_M = 0}` of the infinitesimal action. -/
theorem vectorSpan_range_le [PreconnectedSpace M] (h : σ.IsMomentMap a μ) :
    vectorSpan ℝ (range μ) ≤ (LinearMap.ker a.toLinearMap).dualAnnihilator := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
  intro Z hZ
  rw [LinearMap.mem_ker, InfinitesimalAction.coe_toLinearMap] at hZ
  simp only [vsub_eq_sub, LinearMap.sub_apply, h.apply_eq_apply_of_eq_zero hZ x y, sub_self]

/-- **The annihilator of the affine support.** For a nondegenerate form on a preconnected
manifold, the vectors `Z ∈ 𝔤` annihilating the direction of the affine span of the image of a
moment map are exactly the elements of the kernel `𝔨 = {Z | Z_M = 0}` of the infinitesimal
action. -/
theorem dualCoannihilator_vectorSpan_range [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (hσ : σ.IsNondegenerate) :
    (vectorSpan ℝ (range μ)).dualCoannihilator = LinearMap.ker a.toLinearMap := by
  refine le_antisymm (fun Z hZ ↦ ?_)
    (Submodule.le_dualAnnihilator_iff_le_dualCoannihilator.1 h.vectorSpan_range_le)
  rw [Submodule.mem_dualCoannihilator] at hZ
  rw [LinearMap.mem_ker, InfinitesimalAction.coe_toLinearMap]
  refine h.eq_zero_of_forall_apply_eq hσ fun x y ↦ ?_
  rw [← sub_eq_zero, ← LinearMap.sub_apply, ← vsub_eq_sub]
  exact hZ _ (vsub_mem_vectorSpan ℝ (mem_range_self x) (mem_range_self y))

variable [FiniteDimensional ℝ 𝔤]

/-- **The direction of the affine support.** For a nondegenerate form on a preconnected manifold
and a finite-dimensional Lie algebra, the direction of the affine span of the image of a moment map
is the annihilator `𝔨⁰` of the kernel `𝔨 = {Z | Z_M = 0}` of the infinitesimal action. -/
theorem vectorSpan_range [PreconnectedSpace M] (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) :
    vectorSpan ℝ (range μ) = (LinearMap.ker a.toLinearMap).dualAnnihilator := by
  rw [← h.dualCoannihilator_vectorSpan_range hσ, Subspace.dualCoannihilator_dualAnnihilator_eq]

/-- **The affine support of a moment map.** For a nondegenerate form on a preconnected manifold
and a finite-dimensional Lie algebra, the affine span of the image of a moment map is the affine
subspace `μ(x) + 𝔨⁰` through any of its values, where `𝔨 = {Z | Z_M = 0}` is the kernel of the
infinitesimal action. -/
theorem affineSpan_range [PreconnectedSpace M] (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate)
    (x : M) :
    affineSpan ℝ (range μ) =
      AffineSubspace.mk' (μ x) (LinearMap.ker a.toLinearMap).dualAnnihilator :=
  AffineSubspace.ext_of_direction_eq
    (by rw [direction_affineSpan, AffineSubspace.direction_mk', h.vectorSpan_range hσ])
    ⟨μ x, mem_affineSpan ℝ (mem_range_self x), AffineSubspace.self_mem_mk' _ _⟩

/-- **The dimension of the affine support.** For a nondegenerate form on a preconnected manifold
and a finite-dimensional Lie algebra, the affine span of the image of a moment map has dimension
`dim 𝔤 - dim 𝔨`, where `𝔨 = {Z | Z_M = 0}` is the kernel of the infinitesimal action. -/
theorem finrank_vectorSpan_range_add_finrank_ker [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (hσ : σ.IsNondegenerate) :
    Module.finrank ℝ (vectorSpan ℝ (range μ)) + Module.finrank ℝ (LinearMap.ker a.toLinearMap) =
      Module.finrank ℝ 𝔤 := by
  rw [h.vectorSpan_range hσ, add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq]

/-- **Full affine support.** For a nondegenerate form on a nonempty preconnected manifold and a
finite-dimensional Lie algebra, the image of a moment map affinely spans `𝔤*` exactly when the
infinitesimal action `Z ↦ Z_M` is injective. -/
theorem affineSpan_range_eq_top_iff [Nonempty M] [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (hσ : σ.IsNondegenerate) :
    affineSpan ℝ (range μ) = ⊤ ↔ LinearMap.ker a.toLinearMap = ⊥ := by
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ (range_nonempty μ),
    h.vectorSpan_range hσ, Submodule.dualAnnihilator_eq_top_iff]

omit [FiniteDimensional ℝ 𝔤] in
/-- **Constant moment maps.** For a nondegenerate form on a preconnected manifold, a moment map is
constant exactly when the infinitesimal action is trivial. -/
theorem range_subsingleton_iff [PreconnectedSpace M] (h : σ.IsMomentMap a μ)
    (hσ : σ.IsNondegenerate) : (range μ).Subsingleton ↔ ∀ Z, a Z = 0 := by
  refine ⟨fun hμ Z ↦ h.eq_zero_of_forall_apply_eq hσ fun x y ↦ ?_, ?_⟩
  · rw [hμ (mem_range_self x) (mem_range_self y)]
  · rintro ha _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact LinearMap.ext fun Z ↦ h.apply_eq_apply_of_eq_zero (ha Z) x y

end Infinitesimal

section Group

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [BoundarylessManifold I' M] [MulAction G M] [ContMDiffSMul I I' ∞ G M] [PreconnectedSpace M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The affine support of a group moment map.** For a moment map of a smooth action of a Lie
group `G` on a preconnected manifold with a nondegenerate form, `ξ` annihilates the direction of
the affine span of `μ(M)` exactly when every `exp (t ξ)` acts trivially on `M`. So that direction
is the annihilator of the Lie algebra of the kernel `⋂ₓ G_x` of the action. -/
theorem mem_dualCoannihilator_vectorSpan_range_iff
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    {ξ : GroupLieAlgebra I G} :
    ξ ∈ (vectorSpan ℝ (range μ)).dualCoannihilator ↔
      ∀ (t : ℝ) (x : M), mulInvariantExp (I := I) (t • ξ) • x = x := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  rw [h.dualCoannihilator_vectorSpan_range hσ,
    InfinitesimalAction.mem_ker_toLinearMap_fundamental_iff]

variable [FaithfulSMul G M]

/-- **Effective actions have moment images of full affine dimension.** For a moment map of an
effective smooth action of a Lie group `G` on a preconnected manifold with a nondegenerate form,
the affine span of the image of the moment map has dimension `dim G`. -/
theorem finrank_vectorSpan_range_of_faithfulSMul
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    Module.finrank ℝ (vectorSpan ℝ (range μ)) = Module.finrank ℝ (GroupLieAlgebra I G) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := ‹FiniteDimensional ℝ E›
  rw [← h.finrank_vectorSpan_range_add_finrank_ker hσ,
    InfinitesimalAction.ker_toLinearMap_fundamental_eq_bot, finrank_bot, add_zero]

/-- **Effective actions have moment images of full affine dimension.** For a moment map of an
effective smooth action of a Lie group `G` on a nonempty preconnected manifold with a
nondegenerate form, the image of the moment map affinely spans `𝔤*`. -/
theorem affineSpan_range_eq_top_of_faithfulSMul [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    affineSpan ℝ (range μ) = ⊤ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : FiniteDimensional ℝ (GroupLieAlgebra I G) := ‹FiniteDimensional ℝ E›
  rw [h.affineSpan_range_eq_top_iff hσ]
  exact InfinitesimalAction.ker_toLinearMap_fundamental_eq_bot

end Group

end TauCeti.SmoothTwoForm.IsMomentMap
