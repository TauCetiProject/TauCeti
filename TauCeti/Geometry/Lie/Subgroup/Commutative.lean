/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.LieAlgebra
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.GroupTheory.Subgroup.Centralizer
import TauCeti.Geometry.Lie.Exponential.Classification

/-!
# The Lie algebra of a commutative subgroup

For a subgroup `K` of a finite-dimensional real Lie group `G`, the adjoint action of the
centralizer of `K` fixes the Lie algebra `Lie(K)` pointwise, and the Lie algebra of the
centralizer brackets to zero with `Lie(K)`. A commutative subgroup lies in its own centralizer, so
the adjoint action of a commutative `K` fixes `Lie(K)` pointwise and `Lie(K)` is an abelian Lie
subalgebra of `𝔤`; in particular the Lie algebra of a commutative Lie group is abelian. This
applies to the Lie algebra `𝔱` of a torus `T ≤ G`, which is abelian and fixed pointwise by
`Ad(T)`.

Conjugation by `g` carries the one-parameter subgroup of `X ∈ Lie(K)` to the one-parameter
subgroup of `Ad g X`; when `g` commutes with the former, uniqueness of the generator of a
one-parameter subgroup gives `Ad g X = X`. The bracket `⁅X, Y⁆` is the derivative at `0` of the
adjoint orbit `s ↦ Ad (lieExp (s • X)) Y`, which is then constant, so the bracket vanishes. Both
statements pass from the derivations whose one-parameter subgroups lie in a subgroup to the Lie
subalgebra they generate by `TauCeti.Lie.lieSubalgebraOfSubgroup_induction`.

## Main results

* `TauCeti.Lie.Ad_apply_eq_self_of_forall_commute`: `Ad g` fixes a derivation whose one-parameter
  subgroup commutes with `g`.
* `TauCeti.Lie.Ad_apply_eq_self_of_mem_centralizer`: the adjoint action of the centralizer of `K`
  fixes `Lie(K)` pointwise.
* `TauCeti.Lie.lie_eq_zero_of_mem_lieSubalgebraOfSubgroup_centralizer`: the Lie algebra of the
  centralizer of `K` brackets to zero with `Lie(K)`.
* `TauCeti.Lie.Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup` and
  `TauCeti.Lie.lie_eq_zero_of_mem_lieSubalgebraOfSubgroup`: for a commutative subgroup, the
  adjoint action of `K` fixes `Lie(K)` pointwise and `Lie(K)` is abelian elementwise.
* `TauCeti.Lie.isLieAbelian_lieSubalgebraOfSubgroup`: the Lie algebra of a commutative subgroup
  is abelian.
* `TauCeti.Lie.isLieAbelian_of_isMulCommutative`: the Lie algebra of a commutative Lie group is
  abelian.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 8
  (Vector Fields), § The Lie Algebra of a Lie Group, and Chapter 20 (The Exponential Map),
  § One-Parameter Subgroups and the Exponential Map.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The adjoint action fixes the generator of a commuting one-parameter subgroup**: if `g`
commutes with `lieExp (t • X)` for every `t`, then `Ad g X = X`. -/
theorem Ad_apply_eq_self_of_forall_commute {g : G} {X : LeftInvariantDerivation I G}
    (h : ∀ t : ℝ, Commute g (lieExp (I := I) (t • X))) : Ad (I := I) g X = X := by
  apply oneParameterSubgroup_injective (I := I) (G := G)
  ext t
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective t
  have hconj : lieExp (I := I) (t • Ad (I := I) g X) = g * lieExp (I := I) (t • X) * g⁻¹ := by
    rw [← map_smul, conj_lieExp (I := I) g (t • X)]
  rw [oneParameterSubgroup_apply, oneParameterSubgroup_apply, hconj, (h t).eq,
    mul_inv_cancel_right]

/-- **The adjoint action of the centralizer of `K` fixes `Lie(K)` pointwise.** -/
theorem Ad_apply_eq_self_of_mem_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K) : Ad (I := I) g X = X := by
  induction hX using lieSubalgebraOfSubgroup_induction with
  | mem Y hY =>
    exact Ad_apply_eq_self_of_forall_commute fun t =>
      (Subgroup.mem_centralizer_iff.mp hg _ (hY t)).symm
  | zero => exact map_zero _
  | add Y Z _ _ hY hZ => rw [map_add, hY, hZ]
  | smul c Y _ hY => rw [map_smul, hY]
  | lie Y Z _ _ hY hZ => rw [LieEquiv.map_lie, hY, hZ]

/-- **The Lie algebra of the centralizer of `K` brackets to zero with `Lie(K)`**: for
`X ∈ Lie(centralizer K)` and `Y ∈ Lie(K)`, `⁅X, Y⁆ = 0`. -/
theorem lie_eq_zero_of_mem_lieSubalgebraOfSubgroup_centralizer {K : Subgroup G}
    {X Y : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) (Subgroup.centralizer (K : Set G)))
    (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) K) : ⁅X, Y⁆ = 0 := by
  induction hX using lieSubalgebraOfSubgroup_induction with
  | mem Z hZ =>
    -- The bracket is the derivative at `0` of the adjoint orbit `s ↦ Ad (lieExp (s • Z)) Y`,
    -- which is constant because `lieExp (s • Z)` centralizes `K`.
    have horbit : (fun s : ℝ => Ad (I := I) (lieExp (I := I) (s • Z)) Y) = fun _ => Y :=
      funext fun s => Ad_apply_eq_self_of_mem_centralizer (hZ s) hY
    have hderiv := hasDerivAt_Ad_lieExp_smul_apply_zero (I := I) Z Y
    rw [horbit] at hderiv
    exact hderiv.unique (hasDerivAt_const 0 Y)
  | zero => exact zero_lie Y
  | add Z W _ _ hZ hW => rw [add_lie, hZ, hW, add_zero]
  | smul c Z _ hZ => rw [smul_lie, hZ, smul_zero]
  | lie Z W _ _ hZ hW => rw [lie_lie, hZ, hW, lie_zero, lie_zero, sub_zero]

/-- **The adjoint action of a commutative subgroup fixes its Lie algebra pointwise.** -/
theorem Ad_apply_eq_self_of_mem_lieSubalgebraOfSubgroup {K : Subgroup G} [IsMulCommutative K]
    {g : G} (hg : g ∈ K) {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K) : Ad (I := I) g X = X :=
  Ad_apply_eq_self_of_mem_centralizer (Subgroup.le_centralizer K hg) hX

/-- **The Lie algebra of a commutative subgroup is abelian**, elementwise. -/
theorem lie_eq_zero_of_mem_lieSubalgebraOfSubgroup {K : Subgroup G} [IsMulCommutative K]
    {X Y : LeftInvariantDerivation I G} (hX : X ∈ lieSubalgebraOfSubgroup (I := I) K)
    (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) K) : ⁅X, Y⁆ = 0 :=
  lie_eq_zero_of_mem_lieSubalgebraOfSubgroup_centralizer
    (lieSubalgebraOfSubgroup_mono (Subgroup.le_centralizer K) hX) hY

/-- **The Lie algebra of a commutative subgroup is abelian.** -/
instance isLieAbelian_lieSubalgebraOfSubgroup (K : Subgroup G) [IsMulCommutative K] :
    IsLieAbelian (lieSubalgebraOfSubgroup (I := I) K) where
  trivial X Y := Subtype.ext (lie_eq_zero_of_mem_lieSubalgebraOfSubgroup X.2 Y.2)

/-- **The Lie algebra of a commutative Lie group is abelian.** -/
instance isLieAbelian_of_isMulCommutative [IsMulCommutative G] :
    IsLieAbelian (LeftInvariantDerivation I G) where
  trivial _ _ :=
    lie_eq_zero_of_mem_lieSubalgebraOfSubgroup (K := ⊤)
      (mem_lieSubalgebraOfSubgroup_of_forall fun _ => Subgroup.mem_top _)
      (mem_lieSubalgebraOfSubgroup_of_forall fun _ => Subgroup.mem_top _)

end TauCeti.Lie
