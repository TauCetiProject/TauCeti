/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.CompositionSeries.Refinement
import TauCeti.Algebra.Group.Subgroup.ZPowers
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# A composition series need not be a chief series

In the dihedral group of order eight, a reflection subgroup is normal in the Klein four subgroup
of elements with even rotation index, but is not normal in the whole group. Refining this chain
of normal inclusions gives a composition series with a term that is not normal in the ambient
group.

We use Mathlib's `DihedralGroup 4` model from `Mathlib.GroupTheory.SpecificGroups.Dihedral`.
The parity character reads the index modulo two on both constructors. The counterexample is
proved directly from this model.
-/

public section

namespace TauCeti

open DihedralGroup Multiplicative

example : ∃ s : GroupCompositionSeries (DihedralGroup 4), ∃ i, ¬ (s i).Normal := by
  let parity : DihedralGroup 4 →* Multiplicative (ZMod 2) := {
    toFun := fun | .r i => ofAdd (i.val : ZMod 2) | .sr i => ofAdd (i.val : ZMod 2)
    map_one' := by decide +kernel
    map_mul' := by
      intro x y
      cases x <;> cases y <;> decide +revert +kernel }
  let K := parity.ker
  let H := Subgroup.zpowers (sr (0 : ZMod 4))
  have hHK : H ≤ K := by
    apply Subgroup.zpowers_le.mpr
    exact MonoidHom.mem_ker.mpr (by decide +kernel)
  have hcomm : ∀ x y : DihedralGroup 4,
      parity x = 1 → parity y = 1 → x * y = y * x := by decide +kernel
  have hH : (H.subgroupOf K).Normal := by
    have : IsMulCommutative K := IsMulCommutative.of_comm fun x y ↦
      Subtype.ext (hcomm x y x.property y.property)
    infer_instance
  have hnot : ¬ H.Normal := by
    intro hN
    have hs := hN.conj_mem (sr 0) (Subgroup.mem_zpowers (sr 0)) (r 1)
    have heq : (r 1 : DihedralGroup 4) * sr 0 * (r 1)⁻¹ = sr 2 := by decide +kernel
    have hs2 : sr 2 ∈ Subgroup.zpowers (sr (0 : ZMod 4)) := heq ▸ hs
    rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_sr 0)] at hs2
    exact (by decide +kernel : ¬ ((sr 2 : DihedralGroup 4) = 1 ∨ sr 2 = sr 0)) hs2
  let c : RelSeries {p : Subgroup (DihedralGroup 4) × Subgroup (DihedralGroup 4) |
      p.1 ≤ p.2 ∧ (p.1.subgroupOf p.2).Normal} :=
    (((RelSeries.singleton _ ⊥).snoc H (by
      simp only [Set.mem_ofPred_eq, RelSeries.last_singleton]
      exact ⟨bot_le, inferInstance⟩)).snoc K (by
      simpa only [Set.mem_ofPred_eq, RelSeries.last_snoc] using ⟨hHK, hH⟩)) |>.snoc ⊤ (by
        simp only [Set.mem_ofPred_eq, RelSeries.last_snoc]
        exact ⟨le_top, inferInstance⟩)
  obtain ⟨s, hs0, hs1, hsMem⟩ := c.exists_relSeries_isCompositionStep_refinement
  have hHmem : H ∈ c := by
    apply RelSeries.mem_snoc.mpr ∘ Or.inl
    apply RelSeries.mem_snoc.mpr ∘ Or.inl
    exact RelSeries.mem_snoc.mpr (Or.inr rfl)
  obtain ⟨i, hi⟩ := hsMem H hHmem
  refine ⟨⟨s, by simpa [c] using hs0, by simpa [c] using hs1⟩, i, ?_⟩
  simpa only [GroupCompositionSeries.coe_mk, hi] using hnot

end TauCeti
