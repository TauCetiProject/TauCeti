/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.Category.ProfiniteGrp.Basic
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Examples of compact open subgroups

The `2`-adic numbers are locally profinite, and the translation stabilizer of `ℤ₂` is `ℤ₂`. In
the discrete symmetric group on three letters, the compact clopen set `{1, (0 1), (0 2)}` is not a
subgroup and has trivial left translation stabilizer. The real line is locally compact but not
locally profinite: the interval `(-1, 1)` contains no open subgroup.
-/

open Set Filter
open scoped Pointwise Topology

namespace TauCeti

example : (𝓝 (0 : ℚ_[2])).HasBasis
    (fun H : OpenAddSubgroup ℚ_[2] ↦ IsCompact (H : Set ℚ_[2])) (↑) :=
  NonarchimedeanAddGroup.nhds_zero_hasBasis_isCompact_openAddSubgroup

example : AddAction.stabilizer ℚ_[2] ((PadicInt.subring 2).toAddSubgroup : Set ℚ_[2]) =
    (PadicInt.subring 2).toAddSubgroup :=
  AddAction.stabilizer_addSubgroup _

example : ∀ U ∈ 𝓝 (0 : ℚ_[2]),
    ∃ H : OpenAddSubgroup ℚ_[2], IsCompact (H : Set ℚ_[2]) ∧ (H : Set ℚ_[2]) ⊆ U :=
  ((IsTopologicalAddGroup.locallyCompact_totallyDisconnected_tfae (G := ℚ_[2])).out 1 3).1
    (⟨inferInstance, inferInstance⟩ :
      LocallyCompactSpace ℚ_[2] ∧ TotallyDisconnectedSpace ℚ_[2])

/-- The `2`-adic integers, as a compact subgroup of `ℚ₂`, form a profinite additive group. -/
noncomputable example : ProfiniteAddGrp :=
  ProfiniteAddGrp.ofCompactAddSubgroup (PadicInt.subring 2).toAddSubgroup
    (isCompact_iff_compactSpace.2 (PadicInt.compactSpace 2))

example : Equiv.swap 0 1 * Equiv.swap 0 2 ∉
    ({1, Equiv.swap 0 1, Equiv.swap 0 2} : Finset (Equiv.Perm (Fin 3))) := by
  decide

example : MulAction.stabilizer (Equiv.Perm (Fin 3))
    (({1, Equiv.swap 0 1, Equiv.swap 0 2} : Finset (Equiv.Perm (Fin 3))) :
      Set (Equiv.Perm (Fin 3))) = ⊥ := by
  ext g
  simp only [MulAction.mem_stabilizer_set, smul_eq_mul, Finset.mem_coe, Subgroup.mem_bot]
  revert g
  decide

example (H : OpenAddSubgroup ℝ) : ¬ (H : Set ℝ) ⊆ Ioo (-1) 1 := fun h ↦ by
  have hH : (H : Set ℝ) = univ := (isClopen_iff.1 ⟨H.isClosed, H.isOpen⟩).resolve_left
    (Set.ne_empty_iff_nonempty.2 ⟨0, H.zero_mem⟩)
  exact (h (hH ▸ mem_univ (1 : ℝ))).2.false

end TauCeti
