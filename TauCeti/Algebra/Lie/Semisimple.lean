/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
import TauCeti.Algebra.Lie.Basic

/-!
# Semisimplicity from an atomistic ideal lattice

If a Lie algebra is spanned by its minimal nonzero ideals, its abelian minimal ideals are
central. When the centre is zero, all minimal ideals are therefore nonabelian, and they form
an internal direct sum: each such ideal commutes with the supremum of the other minimal ideals.
-/

public section

namespace TauCeti

open LieAlgebra LieSubmodule

/-- A centreless Lie algebra whose minimal nonzero ideals span it is semisimple. -/
theorem isSemisimple_of_sSup_atoms_eq_top_of_center_eq_bot {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] (hspan : sSup {I : LieIdeal R L | IsAtom I} = ⊤)
    (hZ : center R L = ⊥) : IsSemisimple R L := by
  have hother (I : LieIdeal R L) (hI : IsAtom I) :
      ⁅I, sSup ({J | IsAtom J} \ {I})⁆ = ⊥ := by
    rw [sSup_eq_iSup', lie_iSup, iSup_eq_bot]
    rintro ⟨J, hJ, hne⟩
    have hJI : J ≠ I := by simpa only [Set.mem_singleton_iff] using hne
    exact le_bot_iff.mp ((lie_le_inf I J).trans (hI.disjoint_of_ne hJ hJI.symm).le_bot)
  have hnonab (I : LieIdeal R L) (hI : IsAtom I) : ¬ IsLieAbelian I := by
    intro hab
    have hsum : I ⊔ sSup ({J | IsAtom J} \ {I}) = ⊤ := by
      rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hI, hspan]
    have hzero : ⁅(⊤ : LieIdeal R L), I⁆ = ⊥ := by
      rw [lie_comm, ← hsum, lie_sup, hother I hI, sup_bot_eq]
      exact (lie_abelian_iff_lie_self_eq_bot I).mp hab
    apply hI.1
    rw [← le_bot_iff, ← hZ]
    intro x hx
    apply (LieModule.mem_maxTrivSubmodule R L L x).mpr
    exact fun y ↦ (lie_eq_bot_iff I ⊤).mp hzero y (mem_top y) x hx
  refine ⟨hspan, ?_, hnonab⟩
  intro I hI
  rw [disjoint_iff, ← hI.lt_iff, lt_iff_le_and_ne]
  refine ⟨inf_le_left, fun heq ↦ hnonab I hI ?_⟩
  apply (lie_abelian_iff_lie_self_eq_bot I).mpr
  exact le_bot_iff.mp ((mono_lie_right I (heq.symm.le.trans inf_le_right)).trans (hother I hI).le)

end TauCeti
