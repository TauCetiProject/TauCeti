/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.CompositionSeries.Basic
import TauCeti.GroupTheory.GroupExtension.DihedralSixteen
import Mathlib.GroupTheory.IndexNormal

/-!
# A composition series need not be a chief series

In the dihedral group of order eight, written as `C₂ ≀ C₂`, the kernel of the first-coordinate
character of the base group is normal in the base group but is not normal in the whole group:
conjugation by the swap exchanges the two coordinates. Refining this subnormal chain gives a
composition series with a term that is not normal in the ambient group.
-/

namespace TauCeti

open WreathC2

example : ∃ s : GroupCompositionSeries WreathC2, ∃ i, ¬ (s i).Normal := by
  let H := wreathTautological.ker.map wreathBase.subtype
  have hHB : H ≤ wreathBase := Subgroup.map_subtype_le _
  have hH : (H.subgroupOf wreathBase).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      wreathBase.subtype_injective]
    infer_instance
  have hnot : ¬ H.Normal := by
    intro hN
    have hx : mk 0 1 0 ∈ H := by
      refine Subgroup.mem_map.mpr ⟨⟨mk 0 1 0, mem_wreathBase_iff.mpr (by simp)⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      apply toAdd_eq_zero.mp
      simp
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp (hN.conj_mem _ hx wreathSwap)
    have hz : coordA (y : WreathC2) = 0 := by
      rw [MonoidHom.mem_ker] at hy
      simpa using congrArg Multiplicative.toAdd hy
    have : (1 : ZMod 2) = 0 := by
      simpa using (congrArg coordA he).symm.trans hz
    exact one_ne_zero this
  obtain ⟨s, hs0, hsH⟩ := exists_groupCompositionSeries_between
    (G := WreathC2) (B := H) bot_le (by infer_instance)
  obtain ⟨t, htH, htB⟩ := exists_groupCompositionSeries_between hHB hH
  have : wreathBase.Normal := Subgroup.normal_of_index_eq_two index_wreathBase
  obtain ⟨u, huB, hu1⟩ := exists_groupCompositionSeries_between
    (A := wreathBase) (B := ⊤) le_top (by infer_instance)
  let v := s.smash t (hsH.trans htH.symm)
  let w := v.smash u (by simp [v, htB, huB])
  let i : Fin (v.length + 1) := (Fin.last s.length).castLE (by simp [v])
  let j : Fin (w.length + 1) := i.castLE (by simp [w])
  refine ⟨⟨w, by simpa [w, v] using hs0, by simpa [w] using hu1⟩, j, ?_⟩
  have hi : w j = H := by
    rw [RelSeries.smash_castLE, RelSeries.smash_castLE, RelSeries.apply_last, hsH]
  exact fun h ↦ hnot (hi ▸ h)

end TauCeti
