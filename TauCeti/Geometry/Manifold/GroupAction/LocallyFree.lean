/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Geometry.Manifold.GroupAction.GermKernel

/-!
# Effective actions of compact commutative Lie groups are generically locally free

Let a compact commutative Lie group `G`, such as a torus, act smoothly and effectively on a
connected Hausdorff manifold `M` without boundary. This file proves that the action is locally
free on a dense open set of points: there is a dense open `U ⊆ M` such that the isotropy algebra
`𝔤_x = {ξ | ξ_M(x) = 0}` is trivial, equivalently the stabilizer `G_x` is discrete, at every
`x ∈ U` (`TauCeti.Lie.exists_isOpen_dense_forall_isotropy_eq_bot`). In particular a nonempty such
`M` has a point at which the action is locally free.

The proof uses the elements of order two. In a compact commutative Lie group the elements `g` with
`g ^ n = 1`, for `n ≠ 0`, form a closed subgroup whose Lie algebra is trivial, since
`exp (t ξ / n) ^ n = exp (t ξ)`; so it is discrete and compact, hence finite
(`TauCeti.Lie.finite_setOf_pow_eq_one`). If `ξ ∈ 𝔤_x` is nonzero, the closed
one-parameter subgroup `T_ξ`, the closure of `{exp (t ξ) | t ∈ ℝ}`, fixes `x`; it is a torus of
positive dimension, a product of at least one circle, so it contains an element `g ≠ 1` with
`g ^ 2 = 1` (`TauCeti.Lie.exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot`). So every point
that is not locally free lies in the fixed set of one of the finitely many involutions of `G`. By
the identity principle for elements of finite order (`TauCeti.isClopen_interior_fixedBy`), the
fixed set of an involution has clopen interior, which on the connected manifold `M` is empty
unless the involution acts trivially, that is, unless it is `1`, by effectiveness. The fixed sets
are closed, so their finite union is a closed nowhere dense set, and its complement is the dense
open set `U`.

Commutativity cannot be dropped: `SO(3)` acts effectively on the sphere `S²`, and every
stabilizer is a circle.

## Main results

* `TauCeti.Lie.finite_setOf_pow_eq_one`: a compact commutative Lie group has finitely many
  elements `g` with `g ^ n = 1`, for `n ≠ 0`.
* `TauCeti.Lie.exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot`: for a smooth action of a
  compact Lie group, a point with nontrivial isotropy algebra is fixed by an element `g ≠ 1` with
  `g ^ 2 = 1`.
* `TauCeti.Lie.exists_isOpen_dense_forall_isotropy_eq_bot`: an effective smooth action of a
  compact commutative Lie group on a connected manifold is locally free on a dense open set.
* `TauCeti.Lie.dense_setOf_isotropy_eq_bot`, `TauCeti.Lie.exists_isotropy_eq_bot`: the locally
  free points are dense, and there is one when `M` is nonempty.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press, 1972, Chapter IV,
  § 3 (principal orbits), whose principal orbit theorem implies this statement.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27 (effective torus actions and the bound `dim T ≤ ½ dim M`).
-/

public section

noncomputable section

open MulAction Set
open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [FiniteDimensional ℝ E]

section TwoTorsion

variable [IsMulCommutative G]

variable (I) in
include I in
/-- **A compact commutative Lie group has finitely many elements of order dividing `n`**, for
`n ≠ 0`. They form a closed subgroup with trivial Lie algebra, since
`exp (t ξ / n) ^ n = exp (t ξ)`, so it is discrete and compact, hence finite. -/
theorem finite_setOf_pow_eq_one [CompactSpace G] {n : ℕ} (hn : n ≠ 0) :
    {g : G | g ^ n = 1}.Finite := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- The elements of order dividing `n` form the kernel of the `n`-th power homomorphism.
  let K : Subgroup G := open IsMulCommutative in (powMonoidHom n : G →* G).ker
  have hK : IsClosed (K : Set G) := isClosed_eq (continuous_pow n) continuous_const
  -- The Lie algebra of `K` is trivial: a one-parameter subgroup of exponent `n` is constant.
  have hbot : lieSubalgebraOfSubgroup (I := I) K = ⊥ := by
    refine (LieSubalgebra.eq_bot_iff _).2 fun X hX ↦ ?_
    rw [mem_lieSubalgebraOfSubgroup hK] at hX
    let e := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint
    have hexp (t : ℝ) : mulInvariantExp (I := I) (t • e X) = 1 := by
      -- Membership in the kernel of the power homomorphism is `g ^ n = 1` by definition.
      have h : lieExp (I := I) (((n : ℝ)⁻¹ * t) • X) ^ n = 1 := hX ((n : ℝ)⁻¹ * t)
      rw [mul_smul, lieExp_inv_natCast_smul_pow _ hn, lieExp_eq_mulInvariantExp, map_smul] at h
      exact h
    exact e.injective ((forall_mulInvariantExp_smul_eq_one_iff.1 hexp).trans (map_zero e).symm)
  have : DiscreteTopology K := (discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot hK).2 hbot
  -- As a set, `K` is `{g | g ^ n = 1}` by definition.
  exact hK.isCompact.finite (isDiscrete_iff_discreteTopology.2 this)

end TwoTorsion

section Action

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]

/-- **A point with nontrivial isotropy is fixed by an involution.** For a smooth action of a
compact Lie group, if `ξ_M(x) = 0` for some `ξ ≠ 0`, then the closed one-parameter subgroup
`T_ξ` fixes `x`. It is a torus of positive dimension, so it contains an element `g ≠ 1` with
`g ^ 2 = 1`, and this element fixes `x`. -/
theorem exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot [CompactSpace G] {x : M}
    (hx : (InfinitesimalAction.fundamental I G I' M).isotropy x ≠ ⊥) :
    ∃ g : G, g ^ 2 = 1 ∧ g ≠ 1 ∧ g • x = x := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x, ξ ≠ 0 := by
    by_contra! h
    exact hx ((LieSubalgebra.eq_bot_iff _).2 h)
  have hle : closedOneParameterSubgroup ξ ≤ stabilizer G x :=
    (mem_isotropy_fundamental_iff_closedOneParameterSubgroup_le (I' := I')).1 hξ
  -- `T_ξ` is a torus, a product of `d` circles.
  obtain ⟨φ⟩ :=
    (isTorus_closedOneParameterSubgroup ξ).nonempty_continuousMulEquiv_pi_circle (I := I)
  set d := Module.finrank ℝ (lieSubalgebraOfSubgroup (I := I) (closedOneParameterSubgroup ξ))
  -- It is nontrivial, since `exp (t ξ) ≠ 1` for some `t`, so `d ≠ 0`.
  obtain ⟨t, ht⟩ : ∃ t : ℝ, mulInvariantExp (I := I) (t • ξ) ≠ 1 := by
    by_contra! h
    exact hξ0 (forall_mulInvariantExp_smul_eq_one_iff.1 h)
  have hd : 0 < d := by
    refine Nat.pos_of_ne_zero fun hd ↦ ht ?_
    have : IsEmpty (Fin d) := by
      rw [hd]
      infer_instance
    have : Subsingleton (closedOneParameterSubgroup ξ) := φ.toEquiv.subsingleton
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨_, mulInvariantExp_smul_mem_closedOneParameterSubgroup ξ t⟩ :
        closedOneParameterSubgroup ξ) 1)
  -- The element `-1` of the first circle factor is an involution of `T_ξ`.
  let c : Fin d → Circle := Pi.mulSingle ⟨0, hd⟩ (-1)
  have hc2 : c ^ 2 = 1 := by
    rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  have hc1 : c ≠ 1 := fun h ↦ Circle.neg_ne_self 1 (by
    simpa [c] using congrFun h ⟨0, hd⟩)
  refine ⟨φ.symm c, ?_, fun h ↦ hc1 ?_, hle (φ.symm c).2⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hc2, map_one, Subgroup.coe_one]
  · rw [← φ.apply_symm_apply c, show φ.symm c = 1 from Subtype.ext h, map_one]

/-- **Effective actions of compact commutative Lie groups are generically locally free.** For an
effective smooth action of a compact commutative Lie group, such as a torus, on a connected
Hausdorff manifold without boundary, the isotropy algebra `𝔤_x` is trivial on a dense open set of
points `x`. The complement of the union of the fixed sets of the finitely many involutions `g ≠ 1`
is such a set. -/
theorem exists_isOpen_dense_forall_isotropy_eq_bot [CompactSpace G] [IsMulCommutative G]
    [FaithfulSMul G M] [PreconnectedSpace M] :
    ∃ U : Set M, IsOpen U ∧ Dense U ∧
      ∀ x ∈ U, (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  let S := {g : G | g ^ 2 = 1 ∧ g ≠ 1}
  have : Finite S :=
    ((finite_setOf_pow_eq_one I two_ne_zero).subset fun g (hg : g ∈ S) ↦ hg.1).to_subtype
  have hsmooth (g : G) : ContMDiff I' I' 1 fun x : M ↦ g • x :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) g).of_le ENat.LEInfty.out
  have hclosed (g : S) : IsClosed (fixedBy M (g : G)) :=
    isClosed_fixedPoints (hsmooth g).continuous
  -- The fixed set of an involution `g ≠ 1` has empty interior, by the identity principle.
  have hnd (g : S) : IsNowhereDense (fixedBy M (g : G)) := by
    rw [(hclosed g).isNowhereDense_iff]
    by_contra hne
    have hfin : IsOfFinOrder (g : G) := isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, g.2.1⟩
    have huniv := (isClopen_interior_fixedBy (g : G) hfin (hsmooth g)).eq_univ
      (nonempty_iff_ne_empty.2 hne)
    refine g.2.2 (FaithfulSMul.eq_of_smul_eq_smul (α := M) fun x ↦ ?_)
    rw [one_smul]
    exact interior_subset (huniv ▸ mem_univ x : x ∈ interior (fixedBy M (g : G)))
  refine ⟨(⋃ g : S, fixedBy M (g : G))ᶜ, (isClosed_iUnion_of_finite hclosed).isOpen_compl, ?_,
    fun x hx ↦ ?_⟩
  · rw [← interior_eq_empty_iff_dense_compl]
    exact (isClosed_iUnion_of_finite hclosed).isNowhereDense_iff.1 (IsNowhereDense.iUnion hnd)
  · by_contra h
    obtain ⟨g, hg2, hg1, hgx⟩ := exists_sq_eq_one_ne_one_smul_eq_of_isotropy_ne_bot h
    exact hx (mem_iUnion.2 ⟨⟨g, hg2, hg1⟩, hgx⟩)

/-- **The locally free points of an effective action of a compact commutative Lie group are
dense.** -/
theorem dense_setOf_isotropy_eq_bot [CompactSpace G] [IsMulCommutative G] [FaithfulSMul G M]
    [PreconnectedSpace M] :
    Dense {x : M | (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥} := by
  obtain ⟨U, -, hU, hUx⟩ := exists_isOpen_dense_forall_isotropy_eq_bot (I := I) (I' := I')
    (G := G) (M := M)
  exact hU.mono hUx

/-- **An effective action of a compact commutative Lie group has a locally free point.** -/
theorem exists_isotropy_eq_bot [CompactSpace G] [IsMulCommutative G] [FaithfulSMul G M]
    [PreconnectedSpace M] [Nonempty M] :
    ∃ x : M, (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ :=
  (dense_setOf_isotropy_eq_bot (I := I)).nonempty

end Action

end TauCeti.Lie
