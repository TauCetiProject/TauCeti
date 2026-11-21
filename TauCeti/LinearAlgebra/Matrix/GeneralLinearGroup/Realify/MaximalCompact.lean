/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Realify
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# Maximal compact subgroups of the realified general linear group

Realification `Matrix.GeneralLinearGroup.realify n 𝕜 : GL n 𝕜 →* GL (n ⊕ n) ℝ` is an isomorphism of
topological groups onto its image `C = (realify n 𝕜).range`
(`Matrix.GeneralLinearGroup.realifyEquivRange`). For `𝕜 = ℂ` this image is the group `C_ℝ` of
invertible real `2n × 2n` matrices commuting with `J`
(`Matrix.GeneralLinearGroup.mem_range_realify_iff`), the realification of `GL(n, ℂ)`. For every
`𝕜` the realified unitary group is the orthogonal part `C ∩ O(2n)`
(`Matrix.GeneralLinearGroup.unitarySubgroup_inf_range_realify`).

This file shows that the realified unitary group `realify (U(n))` is a maximal compact subgroup of
`C`, and that every compact subgroup of `C` is conjugate into it by an element of `C`. So the
maximal compact subgroups of `C` are exactly the `C`-conjugates of `realify (U(n))`. Maximality is
the theorem for closed subgroups of `GL (n ⊕ n) ℝ` stable under the polar decomposition
(`Matrix.GeneralLinearGroup.maximal_isCompact_unitarySubgroup_subgroupOf`), applied to `C`, which
contains the orthogonal polar factors of its elements
(`Matrix.GeneralLinearGroup.toUnits_polarUnitary_mem_range_realify`). Conjugacy is the statement
for `GL n 𝕜` (`Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`), transported along
the closed embedding `realify n 𝕜`: a compact subgroup of `GL (n ⊕ n) ℝ` contained in `C` has
compact preimage in `GL n 𝕜`, and is the image of that preimage.

## Main results

* `Matrix.GeneralLinearGroup.isCompact_map_realify_unitarySubgroup`: the realified unitary group is
  compact.
* `Matrix.GeneralLinearGroup.eq_map_realify_unitarySubgroup_of_isCompact_of_le`: a compact subgroup
  of the realified group containing the realified unitary group is the realified unitary group.
* `Matrix.GeneralLinearGroup.maximal_isCompact_map_realify_unitarySubgroup_subgroupOf`: the
  realified unitary group is a maximal compact subgroup of the realified group.
* `Matrix.GeneralLinearGroup.exists_conj_realify_smul_le_map_realify_unitarySubgroup`: every
  compact subgroup of the realified group is conjugate into the realified unitary group by a
  realified matrix.
* `Matrix.GeneralLinearGroup.maximal_isCompact_range_realify_iff`: the maximal compact
  subgroups of the realified group are exactly the conjugates of the realified unitary group.

## References

* Anthony W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 2 (`U(n)` is a maximal compact subgroup of
  `GL(n, ℂ)`, viewed as a closed linear group stable under transpose).
* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

open Pointwise

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The realified unitary group is compact. -/
theorem isCompact_map_realify_unitarySubgroup :
    IsCompact (((unitarySubgroup (GL n 𝕜)).map (realify n 𝕜) : Subgroup (GL (n ⊕ n) ℝ)) :
      Set (GL (n ⊕ n) ℝ)) := by
  rw [Subgroup.coe_map]
  exact isCompact_unitarySubgroup.image (isClosedEmbedding_realify n 𝕜).continuous

/-- **The realified unitary group is maximal compact in the realified group.** A compact subgroup
of `GL (n ⊕ n) ℝ` contained in the realification of `GL n 𝕜` and containing the realified unitary
group is the realified unitary group. -/
theorem eq_map_realify_unitarySubgroup_of_isCompact_of_le {K : Subgroup (GL (n ⊕ n) ℝ)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) ℝ))) (hKR : K ≤ (realify n 𝕜).range)
    (hUK : (unitarySubgroup (GL n 𝕜)).map (realify n 𝕜) ≤ K) :
    K = (unitarySubgroup (GL n 𝕜)).map (realify n 𝕜) := by
  rw [← unitarySubgroup_inf_range_realify, inf_comm] at hUK ⊢
  exact eq_inf_unitarySubgroup_of_isCompact_of_le_of_polarUnitary_mem
    (fun _ ↦ toUnits_polarUnitary_mem_range_realify) hK hKR hUK

/-- **The realified unitary group is a maximal compact subgroup of the realified group**, viewed in
the subgroup lattice of `(realify n 𝕜).range` with the inherited topology. For `𝕜 = ℂ` this says
that `U(n)` is a maximal compact subgroup of the realified `GL(n, ℂ)` in `GL(2n, ℝ)`. -/
theorem maximal_isCompact_map_realify_unitarySubgroup_subgroupOf :
    Maximal (fun K : Subgroup (realify n 𝕜).range ↦ IsCompact (K : Set (realify n 𝕜).range))
      (((unitarySubgroup (GL n 𝕜)).map (realify n 𝕜)).subgroupOf (realify n 𝕜).range) := by
  rw [← unitarySubgroup_inf_range_realify, Subgroup.inf_subgroupOf_right]
  exact maximal_isCompact_unitarySubgroup_subgroupOf
    (fun _ ↦ toUnits_polarUnitary_mem_range_realify) (isClosedEmbedding_realify n 𝕜).isClosed_range

/-- **Every compact subgroup of the realified group is conjugate into the realified unitary
group** by a realified matrix. This is Weyl's unitarian trick for `GL n 𝕜`
(`Matrix.GeneralLinearGroup.exists_conj_smul_le_unitarySubgroup`), applied to the preimage of the
subgroup. -/
theorem exists_conj_realify_smul_le_map_realify_unitarySubgroup {K : Subgroup (GL (n ⊕ n) ℝ)}
    (hK : IsCompact (K : Set (GL (n ⊕ n) ℝ))) (hKR : K ≤ (realify n 𝕜).range) :
    ∃ g : GL n 𝕜,
      MulAut.conj (realify n 𝕜 g) • K ≤ (unitarySubgroup (GL n 𝕜)).map (realify n 𝕜) := by
  obtain ⟨g, hg⟩ := exists_conj_smul_le_unitarySubgroup (K := K.comap (realify n 𝕜))
    ((isClosedEmbedding_realify n 𝕜).isCompact_preimage hK)
  refine ⟨g, fun x hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  obtain ⟨a, rfl⟩ := hKR hk
  refine ⟨MulAut.conj g • a, hg ((Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨a, hk, rfl⟩),
    ?_⟩
  simp [MulAut.smul_def]

/-- **The maximal compact subgroups of the realified group are the conjugates of the realified
unitary group.** For `𝕜 = ℂ`, the maximal compact subgroups of the realified `GL(n, ℂ)` are the
conjugates of the realified `U(n)` by realified invertible complex matrices. -/
theorem maximal_isCompact_range_realify_iff {K : Subgroup (realify n 𝕜).range} :
    Maximal (fun H : Subgroup (realify n 𝕜).range ↦ IsCompact (H : Set (realify n 𝕜).range)) K ↔
      ∃ g : (realify n 𝕜).range, K = MulAut.conj g •
        ((unitarySubgroup (GL n 𝕜)).map (realify n 𝕜)).subgroupOf (realify n 𝕜).range := by
  refine Subgroup.maximal_isCompact_iff_exists_eq_conj_smul
    maximal_isCompact_map_realify_unitarySubgroup_subgroupOf fun K hK ↦ ?_
  obtain ⟨g, hg⟩ := exists_conj_realify_smul_le_map_realify_unitarySubgroup
    (hK.image continuous_subtype_val) (Subgroup.map_subtype_le K)
  refine ⟨⟨realify n 𝕜 g, g, rfl⟩, fun x hx ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  refine Subgroup.mem_subgroupOf.2 (hg ((Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨k, ⟨k, hk, rfl⟩, ?_⟩))
  simp [MulAut.smul_def]

end Matrix.GeneralLinearGroup
