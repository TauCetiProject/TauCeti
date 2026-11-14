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
import TauCeti.Topology.Algebra.Star.Unitary

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
* `Matrix.GeneralLinearGroup.realifyUnitaryHomeomorph`: realification is a homeomorphism from
  `U(n)` onto the orthogonal matrices of any subgroup of `GL (n ⊕ n) ℝ` whose orthogonal elements
  are the realified unitary matrices, such as the symplectic group and the realified `GL(n, ℂ)`.
* `TauCeti.GLSymplectic.ofUnitary`: the realification `U(n) →* Sp(2n, ℝ)`, a continuous group
  morphism (`TauCeti.GLSymplectic.continuous_ofUnitary`).

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
  exact (isClosedEmbedding_realify n 𝕜).continuous.comp Unitary.continuous_toUnits

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

namespace GeneralLinearGroup

variable {G : Subgroup (GL (n ⊕ n) ℝ)}

/-- If the orthogonal elements of a subgroup `G` of `GL (n ⊕ n) ℝ` are the realified unitary
matrices, then realification is a homeomorphism from `U(n)` onto the orthogonal matrices whose
units lie in `G`. This applies to the symplectic group (`TauCeti.GLSymplectic.inf_unitarySubgroup`)
and to the realified `GL(n, ℂ)` (`Matrix.GeneralLinearGroup.unitarySubgroup_inf_range_realify`). -/
noncomputable def realifyUnitaryHomeomorph
    (hG : G ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) = (unitarySubgroup (GL n ℂ)).map (realify n ℂ)) :
    unitaryGroup n ℂ ≃ₜ {u : unitaryGroup (n ⊕ n) ℝ // Unitary.toUnits u ∈ G} :=
  have hmem (U : unitaryGroup n ℂ) : (U : Matrix n n ℂ).realify ∈ unitaryGroup (n ⊕ n) ℝ :=
    realify_mem_orthogonalGroup_iff.2 U.2
  have hG' (U : unitaryGroup n ℂ) : Unitary.toUnits ⟨_, hmem U⟩ ∈ G := by
    have hU : realify n ℂ (Unitary.toUnits U) ∈ G ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) :=
      hG ▸ Subgroup.mem_map_of_mem _ (by simp [mem_unitarySubgroup_iff, Units.unitary_eq])
    have hUnits : Unitary.toUnits ⟨_, hmem U⟩ = realify n ℂ (Unitary.toUnits U) :=
      Units.ext (by simp [coe_realify])
    exact hUnits ▸ (Subgroup.mem_inf.1 hU).1
  let f : unitaryGroup n ℂ → {u : unitaryGroup (n ⊕ n) ℝ // Unitary.toUnits u ∈ G} :=
    fun U ↦ ⟨⟨_, hmem U⟩, hG' U⟩
  have hf : Function.Bijective f := by
    refine ⟨fun U V h ↦ Subtype.ext (Matrix.realify_injective ?_), fun u ↦ ?_⟩
    · exact congrArg (fun u : {u : unitaryGroup (n ⊕ n) ℝ // Unitary.toUnits u ∈ G} ↦
        ((u : unitaryGroup (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ)) h
    have hu : Unitary.toUnits (u : unitaryGroup (n ⊕ n) ℝ) ∈
        G ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) :=
      Subgroup.mem_inf.2 ⟨u.2, by simp [mem_unitarySubgroup_iff, Units.unitary_eq]⟩
    rw [hG] at hu
    obtain ⟨A, hA, hAu⟩ := hu
    refine ⟨⟨A, by simpa [mem_unitarySubgroup_iff, Units.unitary_eq] using hA⟩, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    simpa [f, coe_realify] using congrArg Units.val hAu
  -- `U(n)` is compact, so a continuous bijection onto a Hausdorff space is a homeomorphism.
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)
    (((Matrix.isClosedEmbedding_realify (m := n) (n := n) (𝕜 := ℂ)).continuous.comp
      continuous_subtype_val).subtype_mk _ |>.subtype_mk _)

/-- Realification identifies `U(n)` with the orthogonal matrices of `G`, as matrices. -/
@[simp]
theorem coe_realifyUnitaryHomeomorph_apply
    (hG : G ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) = (unitarySubgroup (GL n ℂ)).map (realify n ℂ))
    (U : unitaryGroup n ℂ) :
    ((realifyUnitaryHomeomorph hG U : unitaryGroup (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) =
      (U : Matrix n n ℂ).realify :=
  (rfl)

/-- The unitary matrix corresponding to an orthogonal matrix of `G` realifies to it. -/
@[simp]
theorem realify_realifyUnitaryHomeomorph_symm_apply
    (hG : G ⊓ unitarySubgroup (GL (n ⊕ n) ℝ) = (unitarySubgroup (GL n ℂ)).map (realify n ℂ))
    (u : {u : unitaryGroup (n ⊕ n) ℝ // Unitary.toUnits u ∈ G}) :
    (((realifyUnitaryHomeomorph hG).symm u : unitaryGroup n ℂ) : Matrix n n ℂ).realify =
      ((u : unitaryGroup (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  rw [← coe_realifyUnitaryHomeomorph_apply hG, Homeomorph.apply_symm_apply]

end GeneralLinearGroup

end Matrix

open Matrix

namespace TauCeti.GLSymplectic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Realification `U(n) → Sp(2n, ℝ)`, identifying complex unitary matrices with the orthogonal
symplectic matrices. -/
noncomputable def ofUnitary : unitaryGroup n ℂ →* GLSymplectic n ℝ :=
  (Subgroup.inclusion inf_le_left).comp
    (unitaryGroupEquivSymplecticInfOrthogonal (n := n)).toMulEquiv.toMonoidHom

/-- `ofUnitary U` is the orthogonal symplectic matrix realifying `U`. -/
theorem ofUnitary_apply (U : unitaryGroup n ℂ) :
    ofUnitary U = Subgroup.inclusion inf_le_left (unitaryGroupEquivSymplecticInfOrthogonal U) :=
  (rfl)

/-- The underlying matrix of `ofUnitary U` is the realification of `U`. -/
@[simp]
theorem coe_ofUnitary (U : unitaryGroup n ℂ) :
    ((ofUnitary U : GL (n ⊕ n) ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ) = (U : Matrix n n ℂ).realify := by
  rw [ofUnitary_apply, Subgroup.coe_inclusion, unitaryGroupEquivSymplecticInfOrthogonal_apply]
  simp

/-- Realification of unitary matrices is continuous. -/
theorem continuous_ofUnitary : Continuous (ofUnitary : unitaryGroup n ℂ → GLSymplectic n ℝ) := by
  refine continuous_induced_rng.2 ((continuous_subtype_val.comp
    (map_continuous (unitaryGroupEquivSymplecticInfOrthogonal (n := n)))).congr fun U ↦ ?_)
  rw [Function.comp_apply, Function.comp_apply, ofUnitary_apply, Subgroup.coe_inclusion]

end TauCeti.GLSymplectic
