/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.NormalQuotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Torus
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.AffineSpan
import TauCeti.Topology.Algebra.GroupAction.Effective

/-!
# Hamiltonian torus actions on the effective quotient

Let a commutative Lie group `G`, such as a torus, act smoothly on a manifold `M` with a two-form
`σ`, with Hamiltonian torus data and moment map `μ : M → 𝔤*`
(`TauCeti.SmoothTwoForm.HamiltonianTorusData`). The action need not be effective: its kernel
`K = {g | ∀ x, g • x = x}` may be nontrivial. This file passes to the **effective quotient**
`G ⧸ K`, which acts faithfully on `M`, and describes the moment map and the image of `μ` through it.

* **Descent along a surjective homomorphism.** Suppose `G` acts through a surjective homomorphism
  `π : G →* Q` onto a commutative Lie group `Q` acting on `M`, differentiable at the identity with
  surjective differential `dπ : 𝔤 → 𝔮`. For `ξ ∈ ker dπ` the fundamental vector field `ξ_M` is
  that of `dπ ξ = 0`, so the component `μ_ξ` is locally constant. On a preconnected manifold each
  difference `μ x - μ x₀` therefore vanishes on `ker dπ` and factors uniquely through `dπ`. This
  gives a unique moment map `ν : M → 𝔮*` of Hamiltonian torus data for `Q` with
  `ν x ∘ dπ = μ x - μ x₀` (`TauCeti.SmoothTwoForm.HamiltonianTorusData.existsUnique_comp_eq_sub`).
  This is the converse of restriction along a homomorphism
  (`TauCeti.SmoothTwoForm.HamiltonianTorusData.comp_monoidHom`).
* **The effective quotient.** The kernel `K` of a smooth action on a Hausdorff manifold is a closed
  subgroup, so `G ⧸ K` is a Lie group, acting smoothly and faithfully on `M`
  (`Subgroup.contMDiffSMul_quotientKerToPermHom`). The projection `G → G ⧸ K` is a surjective
  submersion, so the descent applies: the effective quotient carries Hamiltonian torus data,
  with moment map `ν` determined by `ν x ∘ dπ = μ x - μ x₀`
  (`TauCeti.SmoothTwoForm.HamiltonianTorusData.existsUnique_quotientKerToPermHom`).
* **The dimension of the moment image.** For a nondegenerate `σ` on a nonempty preconnected
  manifold, the image of `ν` affinely spans `Lie(G ⧸ K)*`, since `G ⧸ K` acts effectively
  (`TauCeti.SmoothTwoForm.IsMomentMap.affineSpan_range_eq_top_of_faithfulSMul`). As
  `μ = μ x₀ + dπ^* ν` with `dπ^*` injective, the affine span of `μ(M)` has dimension
  `dim (G ⧸ K) = dim G - dim K`
  (`HamiltonianTorusData.finrank_vectorSpan_range_add_finrank_lieSubalgebraOfSubgroup_ker`). For a
  compact connected `M` the image `μ(M)` is the moment polytope of the convexity theorem of Atiyah
  and Guillemin–Sternberg, and this identifies it, through the injective affine map
  `ν' ↦ μ x₀ + dπ^* ν'`, with the full-dimensional moment polytope `ν(M)` of the effective quotient.
  For instance a trivial action has kernel the whole group, and its moment image is a point.

## Main results

* `TauCeti.SmoothTwoForm.HamiltonianTorusData.existsUnique_comp_eq_sub`: Hamiltonian torus data
  descend along a surjective homomorphism with surjective differential.
* `TauCeti.SmoothTwoForm.HamiltonianTorusData.existsUnique_quotientKerToPermHom`: Hamiltonian
  torus data descend to the effective quotient.
* `HamiltonianTorusData.finrank_vectorSpan_range_add_finrank_lieSubalgebraOfSubgroup_ker`, in the
  namespace `TauCeti.SmoothTwoForm`: the affine span of the moment image has dimension
  `dim G - dim K`.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lectures 22 and 27 (Hamiltonian torus actions and effective actions).
-/

public section

open Function Set MulAction
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.HamiltonianTorusData

section Descent

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G]
  [LieGroup I (minSmoothness ℝ 3) G]
  {F HQ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace HQ] {J : ModelWithCorners ℝ F HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q] [CommGroup Q]
  [LieGroup J (minSmoothness ℝ 3) Q]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [MulAction Q M] [ContMDiffSMul J I' ∞ Q M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

/-- For an action through `π : G →* Q`, the differences of a moment map of Hamiltonian torus data
on a preconnected manifold vanish on the kernel of `dπ`: the fundamental vector field of
`ξ ∈ ker dπ` is that of `dπ ξ = 0`. -/
private theorem sub_mem_range_dualMap [PreconnectedSpace M] (h : σ.HamiltonianTorusData μ)
    (π : G →* Q) (hπ : MDifferentiableAt I J π 1) (hsmul : ∀ (g : G) (x : M), g • x = π g • x)
    (hdπ : Surjective (π.groupLieAlgebraMap I J)) (x₀ x : M) :
    μ x - μ x₀ ∈ LinearMap.range (π.groupLieAlgebraMap I J).toLinearMap.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ hdπ,
    Submodule.mem_dualAnnihilator]
  intro ξ hξ
  have h0 : InfinitesimalAction.fundamental I G I' M ξ = 0 := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hξ
    rw [InfinitesimalAction.fundamental_apply,
      ← π.fundamentalVectorField_groupLieAlgebraMap hπ hsmul, hξ,
      ← InfinitesimalAction.fundamental_apply, map_zero]
  rw [LinearMap.sub_apply, h.toIsMomentMap.apply_eq_apply_of_eq_zero h0 x x₀, sub_self]

/-- **Descent of Hamiltonian torus data along a surjective homomorphism.** Let a commutative Lie
group `G` act on a preconnected manifold `(M, σ)` through a surjective homomorphism `π : G →* Q`
onto a commutative Lie group `Q` acting on `M`, with `π` differentiable at the identity and with
surjective differential `dπ`. If the action of `G` has Hamiltonian torus data with moment map `μ`,
then for every base point `x₀` there is a unique moment map `ν` of Hamiltonian torus data for `Q`
with `ν x ∘ dπ = μ x - μ x₀` for all `x`. Conversely `x ↦ ν x ∘ dπ` is a moment map of
Hamiltonian torus data for `G` for every such `ν`
(`TauCeti.SmoothTwoForm.HamiltonianTorusData.comp_monoidHom`). -/
theorem existsUnique_comp_eq_sub [PreconnectedSpace M] (h : σ.HamiltonianTorusData μ)
    (π : G →* Q) (hπ : MDifferentiableAt I J π 1) (hsmul : ∀ (g : G) (x : M), g • x = π g • x)
    (hπs : Surjective π) (hdπ : Surjective (π.groupLieAlgebraMap I J)) (x₀ : M) :
    ∃! ν : M → Module.Dual ℝ (GroupLieAlgebra J Q), σ.HamiltonianTorusData ν ∧
      ∀ x, (ν x).comp (π.groupLieAlgebraMap I J).toLinearMap = μ x - μ x₀ := by
  choose ν hν using sub_mem_range_dualMap h π hπ hsmul hdπ x₀
  simp only [LinearMap.dualMap_apply'] at hν
  have hνμ : (fun x ↦ (ν x).comp (π.groupLieAlgebraMap I J).toLinearMap) =
      fun x ↦ μ x + -μ x₀ := funext fun x ↦ by rw [hν, sub_eq_add_neg]
  refine ⟨ν, ⟨⟨IsEquivariantMomentMap.of_comp_monoidHom π hπ hsmul hπs hdπ ?_, fun q ↦ ?_⟩, hν⟩,
    fun ν' hν' ↦ funext fun x ↦ (LinearMap.cancel_right hdπ).1 ((hν'.2 x).trans (hν x).symm)⟩
  · rw [hνμ]
    exact (h.add_const (-μ x₀)).toIsEquivariantMomentMap
  · obtain ⟨g, rfl⟩ := hπs q
    simpa only [hsmul] using h.mpullback_smul g

end Descent

section EffectiveQuotient

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Hamiltonian torus data descend to the effective quotient.** Let a commutative Lie group `G`
act on a preconnected manifold `(M, σ)` with Hamiltonian torus data and moment map `μ`, and let
`K` be the kernel of the action, a closed subgroup when `M` is Hausdorff
(`TauCeti.isClosed_ker_toPermHom`). The quotient Lie group `G ⧸ K` acts smoothly and faithfully
on `M`, and for every base point `x₀` there is a unique moment map `ν` of Hamiltonian torus data
for `G ⧸ K` with `ν x ∘ dπ = μ x - μ x₀` for all `x`, where `dπ` is the differential at the
identity of the projection `π : G → G ⧸ K`. -/
theorem existsUnique_quotientKerToPermHom [PreconnectedSpace M] (h : σ.HamiltonianTorusData μ)
    (hK : IsClosed ((toPermHom G M).ker : Set G)) (x₀ : M) :
    letI := Subgroup.quotientChartedSpaceOfIsClosed I hK
    haveI := Subgroup.lieGroup_quotientOfIsClosed (I := I) hK
    haveI := Subgroup.contMDiffSMul_quotientKerToPermHom (I := I) (I' := I') (M := M) hK
    ∃! ν : M → Module.Dual ℝ (GroupLieAlgebra 𝓘(ℝ, Subgroup.QuotientModelSpace I
        (toPermHom G M).ker) (G ⧸ (toPermHom G M).ker)),
      σ.HamiltonianTorusData ν ∧ ∀ x, (ν x).comp ((QuotientGroup.mk' (toPermHom G M).ker)
        |>.groupLieAlgebraMap I 𝓘(ℝ, Subgroup.QuotientModelSpace I (toPermHom G M).ker)
        |>.toLinearMap) = μ x - μ x₀ := by
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hK
  have := Subgroup.lieGroup_quotientOfIsClosed (I := I) hK
  have := Subgroup.contMDiffSMul_quotientKerToPermHom (I := I) (I' := I') (M := M) hK
  exact h.existsUnique_comp_eq_sub _
    ((Subgroup.contMDiff_quotientMk (I := I) hK).mdifferentiableAt (by simp))
    (fun g x ↦ (quotientKerToPermHom_mk_smul G M g x).symm) (QuotientGroup.mk'_surjective _)
    (Subgroup.surjective_groupLieAlgebraMap_mk' hK) x₀

/-- **The dimension of the moment image of a Hamiltonian torus action.** For Hamiltonian torus data
of a commutative Lie group `G` on a nonempty preconnected Hausdorff boundaryless manifold with a
nondegenerate form, the affine span of the image of the moment map has dimension
`dim G - dim K`, where `K` is the kernel of the action: the dimension of the effective quotient
`G ⧸ K`. -/
theorem finrank_vectorSpan_range_add_finrank_lieSubalgebraOfSubgroup_ker [T2Space M]
    [BoundarylessManifold I' M] [Nonempty M] [PreconnectedSpace M] (h : σ.HamiltonianTorusData μ)
    (hσ : σ.IsNondegenerate) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    Module.finrank ℝ (vectorSpan ℝ (range μ)) +
      Module.finrank ℝ (Lie.lieSubalgebraOfSubgroup (I := I) (toPermHom G M).ker).toSubmodule =
        Module.finrank ℝ E := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  have hK : IsClosed ((toPermHom G M).ker : Set G) := isClosed_ker_toPermHom G M fun x ↦
    (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := I') (n := ∞) x).continuous
  let _ := Subgroup.quotientChartedSpaceOfIsClosed I hK
  have := Subgroup.lieGroup_quotientOfIsClosed (I := I) hK
  have := Subgroup.contMDiffSMul_quotientKerToPermHom (I := I) (I' := I') (M := M) hK
  let _ : T2Space (G ⧸ (toPermHom G M).ker) :=
    𝓘(ℝ, Subgroup.QuotientModelSpace I (toPermHom G M).ker).t2Space_of_lieGroup ∞
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨ν, hν, hνμ⟩ := (h.existsUnique_quotientKerToPermHom hK x₀).exists
  set dπ := ((QuotientGroup.mk' (toPermHom G M).ker).groupLieAlgebraMap I
    𝓘(ℝ, Subgroup.QuotientModelSpace I (toPermHom G M).ker)).toLinearMap
  -- The image of `μ` is the image of `ν` under the affine map `f : ν' ↦ dπ^* ν' + μ x₀`, whose
  -- linear part `dπ^*` is injective, and the image of `ν` affinely spans `Lie(G ⧸ K)*`, as
  -- `G ⧸ K` acts effectively.
  let f := dπ.dualMap.toAffineMap + AffineMap.const ℝ _ (μ x₀)
  have hrange : range μ = f '' range ν := by
    rw [← range_comp]
    refine congrArg range (funext fun x ↦ ?_)
    simp [f, LinearMap.dualMap_apply', dπ, hνμ]
  have htop : vectorSpan ℝ (range ν) = ⊤ := by
    rw [← direction_affineSpan, hν.toIsMomentMap.affineSpan_range_eq_top_of_faithfulSMul hσ,
      AffineSubspace.direction_top]
  have hinj : Injective dπ.dualMap :=
    LinearMap.dualMap_injective_of_surjective (Subgroup.surjective_groupLieAlgebraMap_mk' hK)
  rw [hrange, ← AffineMap.map_vectorSpan, htop, Submodule.map_top]
  have hf : f.linear = dπ.dualMap := by simp [f]
  rw [hf, LinearMap.finrank_range_of_inj hinj, Subspace.dual_finrank_eq]
  exact Subgroup.finrank_quotientModelSpace_add_finrank_lieSubalgebraOfSubgroup I _ hK

end EffectiveQuotient

end TauCeti.SmoothTwoForm.HamiltonianTorusData
