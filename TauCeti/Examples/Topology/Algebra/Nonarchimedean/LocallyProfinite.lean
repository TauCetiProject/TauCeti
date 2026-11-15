/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.NumberTheory.Padics.OpenAddSubgroup
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Profinite
import TauCeti.Topology.Algebra.Group.Perm
import TauCeti.Topology.Algebra.Group.Preconnected
import TauCeti.Topology.Algebra.Nonarchimedean.LocallyProfinite

/-!
# Examples and counterexamples for Van Dantzig's theorem

Concrete positive and negative examples illustrating Van Dantzig's theorem, compact open subgroup
bases, and left translation stabilizers:

* In the noncompact locally profinite additive group `ℚ_[2]`, the subsets `ℤ_[2]` and `2 • ℤ_[2]`
  have translation stabilizers `ℤ_[2]` and `2 • ℤ_[2]` respectively, and the fractional lattices
  `(2 : ℚ_[2]) ^ m • ℤ_[2]` (`m : ℤ`) form a neighbourhood basis of `0 : ℚ_[2]`.
* In the discrete symmetric group `Equiv.Perm (Fin 3)`, the subset `C = {1, swap 0 1, swap 0 2}` is
  compact, clopen, and contains `1`, yet is not a subgroup because `(swap 0 1) * (swap 0 2)` is a
  `3`-cycle outside `C`; its left translation stabilizer is the trivial subgroup `⊥` (`{1}`).
* The trivial group `Unit` has `{⊤}` as its singleton compact open subgroup basis at `1`.
* In the locally compact Hausdorff connected additive group `ℝ`, the interval `(-1, 1)` contains no
  open additive subgroup, so local compactness alone does not produce open subgroups.
-/

open Filter Set
open scoped Pointwise Topology

namespace TauCeti

/-! ### Noncompact locally profinite `ℚ_[2]` -/

section PadicTwo

example : NoncompactSpace ℚ_[2] := inferInstance

example : LocallyCompactSpace ℚ_[2] ∧ TotallyDisconnectedSpace ℚ_[2] :=
  ⟨inferInstance, inferInstance⟩

example : NonarchimedeanAddGroup ℚ_[2] := inferInstance

noncomputable example : ProfiniteAddGrp :=
  (Padic.zpowOpenAddSubgroup 2 0).toProfiniteAddGrp (Padic.isCompact_zpowOpenAddSubgroup 0)

example :
    AddAction.stabilizer ℚ_[2] (PadicInt.subring 2 : Set ℚ_[2]) =
      (PadicInt.subring 2).toAddSubgroup :=
  Padic.stabilizer_padicInt_subring

example :
    AddAction.stabilizer ℚ_[2] ((2 : ℚ_[2]) • (PadicInt.subring 2 : Set ℚ_[2])) =
      (Padic.zpowOpenAddSubgroup 2 1).toAddSubgroup ∧
    ((Padic.zpowOpenAddSubgroup 2 1 : OpenAddSubgroup ℚ_[2]) : Set ℚ_[2]) =
      (2 : ℚ_[2]) • (PadicInt.subring 2 : Set ℚ_[2]) :=
  ⟨Padic.stabilizer_smul_padicInt_subring, Padic.coe_zpowOpenAddSubgroup_one⟩

example :
    (𝓝 (0 : ℚ_[2])).HasBasis (fun _ : ℤ ↦ True)
      fun m ↦ (2 : ℚ_[2]) ^ m • (PadicInt.subring 2 : Set ℚ_[2]) :=
  Padic.nhds_zero_hasBasis_zpow_smul_subring 2

end PadicTwo

/-! ### Discrete `S₃`: a compact clopen identity neighbourhood that is not a subgroup -/

section PermFin3

example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    IsCompact C ∧ IsClopen C ∧ (1 : Equiv.Perm (Fin 3)) ∈ C := by
  dsimp only
  exact ⟨Set.toFinite _ |>.isCompact, isClopen_discrete _, by simp⟩

example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    Equiv.swap 0 1 ∈ C ∧ Equiv.swap 0 2 ∈ C ∧ Equiv.swap 0 1 * Equiv.swap 0 2 ∉ C ∧
      ¬∃ H : Subgroup (Equiv.Perm (Fin 3)), (H : Set (Equiv.Perm (Fin 3))) = C := by
  dsimp only
  have hnotMem : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉
      ({1, Equiv.swap 0 1, Equiv.swap 0 2} : Set (Equiv.Perm (Fin 3))) := by decide
  refine ⟨by simp, by simp, hnotMem, ?_⟩
  rintro ⟨H, hH⟩
  have h01 : Equiv.swap (0 : Fin 3) 1 ∈ H := SetLike.mem_coe.mp (hH.symm ▸ by simp)
  have h02 : Equiv.swap (0 : Fin 3) 2 ∈ H := SetLike.mem_coe.mp (hH.symm ▸ by simp)
  exact hnotMem (hH ▸ SetLike.mem_coe.mpr (H.mul_mem h01 h02))

example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    MulAction.stabilizer (Equiv.Perm (Fin 3)) C = ⊥ ∧
      (MulAction.stabilizer (Equiv.Perm (Fin 3)) C : Set (Equiv.Perm (Fin 3))) = {1} := by
  dsimp only
  have hbot : MulAction.stabilizer (Equiv.Perm (Fin 3))
      ({1, Equiv.swap 0 1, Equiv.swap 0 2} : Set (Equiv.Perm (Fin 3))) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases MulAction.stabilizer_subset_of_one_mem (by simp) hg with rfl | rfl | rfl
    · exact Subgroup.one_mem ⊥
    · exact False.elim <|
        (by decide : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 2 ∉
          ({1, Equiv.swap 0 1, Equiv.swap 0 2} : Set (Equiv.Perm (Fin 3))))
          ((MulAction.mem_stabilizer_iff.mp hg) ▸ smul_mem_smul_set (by simp))
    · exact False.elim <|
        (by decide : Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 ∉
          ({1, Equiv.swap 0 1, Equiv.swap 0 2} : Set (Equiv.Perm (Fin 3))))
          ((MulAction.mem_stabilizer_iff.mp hg) ▸ smul_mem_smul_set (by simp))
  exact ⟨hbot, by simp [hbot]⟩

example :
    let C : Set (Equiv.Perm (Fin 3)) := {1, Equiv.swap 0 1, Equiv.swap 0 2}
    (MulAction.stabilizerOpenSubgroup (Set.toFinite C).isCompact (isOpen_discrete C)).toSubgroup =
        MulAction.stabilizer (Equiv.Perm (Fin 3)) C ∧
      ((MulAction.stabilizerOpenSubgroup (Set.toFinite C).isCompact (isOpen_discrete C) :
        OpenSubgroup (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3))) =
          MulAction.stabilizer (Equiv.Perm (Fin 3)) C ∧
      ((1 : Equiv.Perm (Fin 3)) ∈
        MulAction.stabilizerOpenSubgroup (Set.toFinite C).isCompact (isOpen_discrete C)) := by
  simp

end PermFin3

/-! ### The trivial group `Unit` -/

section TrivialGroup

example : Unique (OpenSubgroup Unit) := inferInstance

example : IsCompact ((⊤ : OpenSubgroup Unit) : Set Unit) :=
  OpenSubgroup.isCompact_top_of_subsingleton

example : ((⊤ : OpenSubgroup Unit).toProfiniteGrp
    OpenSubgroup.isCompact_top_of_subsingleton : Type) = (⊤ : OpenSubgroup Unit) ∧
    MulAction.stabilizerOpenSubgroup
      (OpenSubgroup.isCompact_top_of_subsingleton (G := Unit)) (⊤ : OpenSubgroup Unit).isOpen =
        (⊤ : OpenSubgroup Unit) := by
  simp

example :
    (𝓝 (1 : Unit)).HasBasis (fun K : OpenSubgroup Unit ↦ K = ⊤) fun K ↦ (K : Set Unit) :=
  OpenSubgroup.nhds_one_hasBasis_eq_top Unit

end TrivialGroup

/-! ### Connected locally compact `ℝ`: no open additive subgroup inside `(-1, 1)` -/

section RealLine

example : LocallyCompactSpace ℝ ∧ T2Space ℝ ∧ IsTopologicalAddGroup ℝ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

example : ¬∃ U : OpenAddSubgroup ℝ, (U : Set ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 :=
  fun ⟨U, hU⟩ ↦ U.not_subset_of_ne_univ ((ne_univ_iff_exists_notMem _).mpr ⟨1, by simp⟩) hU

example : ¬∃ U : OpenAddSubgroup ℝ, IsCompact (U : Set ℝ) := fun ⟨U, hU⟩ ↦
  U.not_isCompact hU

example : ¬NonarchimedeanAddGroup ℝ := fun h ↦ by
  obtain ⟨U, hU⟩ :=
    @NonarchimedeanAddGroup.is_nonarchimedean ℝ _ _ h (Set.Ioo (-1 : ℝ) 1)
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  exact U.not_subset_of_ne_univ ((ne_univ_iff_exists_notMem _).mpr ⟨1, by simp⟩) hU

end RealLine

end TauCeti
