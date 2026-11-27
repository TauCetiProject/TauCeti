/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic

/-!
# Torsion in compact commutative Lie groups

In a compact commutative Lie group `G`, the elements `g` with `g ^ n = 1`, for `n ≠ 0`, form a
closed subgroup, the kernel of the `n`-th power homomorphism. Its Lie algebra is trivial, since
`exp (t ξ / n) ^ n = exp (t ξ)`, so it is discrete; being compact, it is finite
(`TauCeti.Lie.finite_setOf_pow_eq_one`). Hence `G` has countably many elements of finite order
(`TauCeti.Lie.countable_setOf_isOfFinOrder`).

## Main results

* `TauCeti.Lie.finite_setOf_pow_eq_one`: a compact commutative Lie group has finitely many
  elements `g` with `g ^ n = 1`, for `n ≠ 0`.
* `TauCeti.Lie.countable_setOf_isOfFinOrder`: a compact commutative Lie group has countably many
  elements of finite order.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [FiniteDimensional ℝ E] [IsMulCommutative G]

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
  have hKset : (K : Set G) = {g | g ^ n = 1} := by
    ext g
    simp [K, MonoidHom.mem_ker]
  have hK : IsClosed (K : Set G) := hKset ▸ isClosed_eq (continuous_pow n) continuous_const
  -- The Lie algebra of `K` is trivial: a one-parameter subgroup of exponent `n` is constant.
  have hbot : lieSubalgebraOfSubgroup (I := I) K = ⊥ := by
    refine (LieSubalgebra.eq_bot_iff _).2 fun X hX ↦ ?_
    rw [mem_lieSubalgebraOfSubgroup hK] at hX
    let e := leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint
    have hexp (t : ℝ) : mulInvariantExp (I := I) (t • e X) = 1 := by
      have h : lieExp (I := I) (((n : ℝ)⁻¹ * t) • X) ^ n = 1 :=
        (Set.ext_iff.1 hKset _).1 (hX ((n : ℝ)⁻¹ * t))
      rw [mul_smul, lieExp_inv_natCast_smul_pow _ hn, lieExp_eq_mulInvariantExp, map_smul] at h
      exact h
    exact e.injective ((forall_mulInvariantExp_smul_eq_one_iff.1 hexp).trans (map_zero e).symm)
  have : DiscreteTopology K := (discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot hK).2 hbot
  rw [← hKset]
  exact hK.isCompact.finite (isDiscrete_iff_discreteTopology.2 this)

variable (I) in
include I in
/-- **A compact commutative Lie group has countably many elements of finite order**, finitely many
of each order. -/
theorem countable_setOf_isOfFinOrder [CompactSpace G] : {g : G | IsOfFinOrder g}.Countable := by
  refine (Set.countable_iUnion fun n : ℕ ↦
    (finite_setOf_pow_eq_one I (Nat.add_one_ne_zero n)).countable).mono fun g hg ↦ ?_
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hg
  exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Set.mem_ofPred_eq, Nat.sub_add_cancel hn]⟩

end TauCeti.Lie
