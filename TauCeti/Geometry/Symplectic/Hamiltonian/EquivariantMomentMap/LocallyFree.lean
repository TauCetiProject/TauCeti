/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.LocallyFree
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Orbit

/-!
# Moment maps of effective actions of compact commutative Lie groups

Let a compact commutative Lie group `G`, such as a torus, act smoothly and effectively on a
connected Hausdorff manifold `M` without boundary, carrying a nondegenerate two-form `σ`. The
action is locally free on a dense open set of points
(`TauCeti.Lie.exists_isOpen_dense_forall_isotropy_eq_bot`). Where the form is nondegenerate, a
moment map `μ : M → 𝔤*` has surjective differential exactly at the points where the action is
locally free (`TauCeti.SmoothTwoForm.IsMomentMap.differential_surjective_iff`). Hence:

* the regular points of `μ` contain a dense open set
  (`TauCeti.SmoothTwoForm.IsMomentMap.exists_isOpen_dense_forall_differential_surjective`);
* if `M` is nonempty and `μ` is a group-level moment map, then the orbits are isotropic and some
  orbit has the dimension of `G`, so `2 dim G ≤ dim M`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.two_mul_finrank_le_of_faithfulSMul`). This is the
  bound `dim T ≤ ½ dim M` for effective Hamiltonian torus actions, with equality for symplectic
  toric manifolds.

Neither closedness of `σ` nor compactness of `M` is used.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27 (effective torus actions and the bound `dim T ≤ ½ dim M`).
* V. Guillemin, S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [IsMulCommutative G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M] [FaithfulSMul G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The regular points of a moment map of an effective torus action are dense.** For a moment
map of an effective smooth action of a compact commutative Lie group on a connected manifold with
a nondegenerate two-form, the differential of `μ` is surjective on a dense open set of points. -/
theorem IsMomentMap.exists_isOpen_dense_forall_differential_surjective
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate) :
    ∃ U : Set M, IsOpen U ∧ Dense U ∧ ∀ x ∈ U, Function.Surjective (h.differential x) := by
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  obtain ⟨U, hUo, hUd, hU⟩ := Lie.exists_isOpen_dense_forall_isotropy_eq_bot (I := I) (I' := I')
    (G := G) (M := M)
  exact ⟨U, hUo, hUd, fun x hx ↦
    (h.differential_surjective_iff (hσ.nondegenerate_bilinFormAt x)).2 (hU x hx)⟩

/-- **The dimension bound for effective torus actions.** If a compact commutative Lie group, such
as a torus, acts effectively on a nonempty connected manifold with a nondegenerate two-form and has
a group-level moment map, then it has at most half the dimension of `M`. -/
theorem IsEquivariantMomentMap.two_mul_finrank_le_of_faithfulSMul [Nonempty M]
    (h : σ.IsEquivariantMomentMap μ) (hσ : σ.IsNondegenerate) :
    2 * finrank ℝ (GroupLieAlgebra I G) ≤ finrank ℝ E' := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  have : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨x, hx⟩ := Lie.exists_isotropy_eq_bot (I := I) (I' := I') (G := G) (M := M)
  exact h.two_mul_finrank_le (hσ.nondegenerate_bilinFormAt x) hx

end TauCeti.SmoothTwoForm
