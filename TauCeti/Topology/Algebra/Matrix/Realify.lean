/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Realification of matrices is a closed embedding

Realification `Matrix.realify` is an injective `ℝ`-linear map between finite-dimensional real
vector spaces, hence a closed embedding for the entrywise topologies. On invertible matrices it
induces a closed embedding `Matrix.GeneralLinearGroup.realify n 𝕜 : GL n 𝕜 → GL (n ⊕ n) ℝ` of
topological groups, and `Matrix.GeneralLinearGroup.realifyEquivRange` is the resulting isomorphism
of topological groups onto its image. For `𝕜 = ℂ` this image is the closed subgroup of invertible
real matrices commuting with `J` (`Matrix.GeneralLinearGroup.mem_range_realify_iff`).

The unitary group `Matrix.unitaryGroup n 𝕜` is compact, so its realification is a closed embedding
into `GL (n ⊕ n) ℝ` as well. For `𝕜 = ℂ` its image is the intersection of the symplectic and
orthogonal subgroups (`Matrix.GeneralLinearGroup.range_realify_comp_toUnits`), and
`Matrix.unitaryGroupEquivSymplecticInfOrthogonal` is the resulting isomorphism of topological
groups `U(n) ≃ₜ* Sp(2n, ℝ) ∩ O(2n)`. By `TauCeti.GLSymplectic.inf_range_realify` and
`Matrix.GeneralLinearGroup.unitarySubgroup_inf_range_realify`, the same subgroup is the
intersection of either of these groups with the realified `GL(n, ℂ)`.

## Main results

* `Matrix.isClosedEmbedding_realify`: realification of matrices is a closed embedding.
* `Matrix.GeneralLinearGroup.isClosedEmbedding_realify`: realification of invertible matrices is a
  closed embedding.
* `Matrix.GeneralLinearGroup.realifyEquivRange`: realification is an isomorphism of topological
  groups from `GL n 𝕜` onto its image in `GL (n ⊕ n) ℝ`.
* `Matrix.GeneralLinearGroup.isClosedEmbedding_realify_comp_toUnits`: realification of unitary
  matrices is a closed embedding into `GL (n ⊕ n) ℝ`.
* `Matrix.unitaryGroupEquivSymplecticInfOrthogonal`: the realification isomorphism of topological
  groups from `U(n)` onto the orthogonal symplectic matrices.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 2.2.
-/

public section

open Topology

namespace Matrix

variable {m n : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- Realification of matrices is a closed embedding for the entrywise topologies. -/
theorem isClosedEmbedding_realify [Finite m] [Finite n] :
    IsClosedEmbedding (realify : Matrix m n 𝕜 → Matrix (m ⊕ m) (n ⊕ n) ℝ) := by
  have h : ⇑(realifyLinearMap m n 𝕜) = realify := funext realifyLinearMap_apply
  rw [← h]
  exact LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 (h ▸ realify_injective))

variable [Fintype n] [DecidableEq n]

namespace GeneralLinearGroup

variable (n 𝕜) in
/-- Realification of invertible matrices is a closed embedding of topological groups. -/
theorem isClosedEmbedding_realify : IsClosedEmbedding (realify n 𝕜) := by
  rw [realify_def]
  refine IsClosedEmbedding.units_map ?_
  convert Matrix.isClosedEmbedding_realify (m := n) (n := n) (𝕜 := 𝕜)
  exact funext realifyAlgHom_apply

variable (n 𝕜) in
/-- **`GL(n, 𝕜)` is isomorphic to its realification**: realification is an isomorphism of
topological groups from `GL n 𝕜` onto its image in `GL (n ⊕ n) ℝ`. For `𝕜 = ℂ` the image is the
subgroup of invertible real matrices commuting with `J`
(`Matrix.GeneralLinearGroup.mem_range_realify_iff`). -/
noncomputable def realifyEquivRange : GL n 𝕜 ≃ₜ* (realify n 𝕜).range :=
  let e := MonoidHom.ofInjective (realify_injective (ι := n) (𝕜 := 𝕜))
  ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfIsInducing
      ((isClosedEmbedding_realify n 𝕜).isInducing.codRestrict (s := (realify n 𝕜).range)
        fun A ↦ ⟨A, rfl⟩))
    e.map_mul

@[simp]
theorem realifyEquivRange_apply (A : GL n 𝕜) :
    (realifyEquivRange n 𝕜 A : GL (n ⊕ n) ℝ) = realify n 𝕜 A :=
  (rfl)

@[simp]
theorem realify_realifyEquivRange_symm_apply (M : (realify n 𝕜).range) :
    realify n 𝕜 ((realifyEquivRange n 𝕜).symm M) = M := by
  rw [← realifyEquivRange_apply, ContinuousMulEquiv.apply_symm_apply]

variable (n 𝕜) in
/-- Realification of unitary matrices is a closed embedding into `GL (n ⊕ n) ℝ`. -/
theorem isClosedEmbedding_realify_comp_toUnits :
    IsClosedEmbedding ((realify n 𝕜).comp Unitary.toUnits : unitaryGroup n 𝕜 → GL (n ⊕ n) ℝ) := by
  -- The unitary group is compact, so a continuous injection into a Hausdorff space suffices.
  refine Continuous.isClosedEmbedding ?_
    ((realify_injective).comp Unitary.toUnits_injective)
  refine (isClosedEmbedding_realify n 𝕜).continuous.comp (Units.continuous_iff.2
    ⟨continuous_subtype_val, ?_⟩)
  -- The inverse of the unit of a unitary matrix is its conjugate transpose, again unitary.
  simp only [Unitary.val_inv_toUnits_apply, UnitaryGroup.inv_val, continuous_fun_star_iff]
  exact continuous_subtype_val

end GeneralLinearGroup

open TauCeti

/-- **`U(n) ≃ₜ* Sp(2n, ℝ) ∩ O(2n)`**: realification is an isomorphism of topological groups from
the complex unitary group onto the orthogonal elements of the real symplectic group. -/
noncomputable def unitaryGroupEquivSymplecticInfOrthogonal :
    unitaryGroup n ℂ ≃ₜ* ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :=
  let e := (MonoidHom.ofInjective
    (GeneralLinearGroup.isClosedEmbedding_realify_comp_toUnits n ℂ).injective).trans
    (MulEquiv.subgroupCongr GeneralLinearGroup.range_realify_comp_toUnits)
  ContinuousMulEquiv.mk'
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
      ((GeneralLinearGroup.isClosedEmbedding_realify_comp_toUnits n ℂ).continuous.subtype_mk _))
    e.map_mul

@[simp]
theorem unitaryGroupEquivSymplecticInfOrthogonal_apply (U : unitaryGroup n ℂ) :
    (unitaryGroupEquivSymplecticInfOrthogonal U : GL (n ⊕ n) ℝ) =
      GeneralLinearGroup.realify n ℂ (Unitary.toUnits U) := by
  simp [unitaryGroupEquivSymplecticInfOrthogonal, ContinuousMulEquiv.coe_mk',
    ← Homeomorph.coe_toEquiv, MonoidHom.ofInjective_apply]

@[simp]
theorem realify_toUnits_unitaryGroupEquivSymplecticInfOrthogonal_symm_apply
    (M : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    GeneralLinearGroup.realify n ℂ
      (Unitary.toUnits (unitaryGroupEquivSymplecticInfOrthogonal.symm M)) = M := by
  rw [← unitaryGroupEquivSymplecticInfOrthogonal_apply, ContinuousMulEquiv.apply_symm_apply]

end Matrix
