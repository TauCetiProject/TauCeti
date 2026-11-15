/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic

/-!
# Comparing roots through their simple-root coefficients

The column of simple-root coefficients of a root (`RootPairing.Base.rootCoefficients`) determines
the root, and its entries sum to the height. So one root lies above another in the positive root
cone exactly when its column dominates the column of the other, and a root whose column
dominates that of `RootPairing.Base.highestRoot` is the highest root itself.

These criteria need neither reducedness nor irreducibility, so they identify the highest root of
a concrete datum from coefficient bounds alone, even over `ℤ`.

## Main results

* `RootPairing.Base.root_sub_root_mem_posRootCone_iff`: the difference of two roots lies in the
  positive root cone exactly when their columns compare coefficientwise.
* `RootPairing.Base.highestRoot_eq_of_rootCoefficients_le`: a root whose column dominates that of
  the highest root is the highest root.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base)

/-- **One root lies above another in the positive root cone exactly when its column dominates the
column of the other.** -/
theorem root_sub_root_mem_posRootCone_iff {i j : ι} :
    P.root i - P.root j ∈ TauCeti.posRootCone P b ↔
      b.rootCoefficients j ≤ b.rootCoefficients i := by
  refine ⟨fun h k ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf⟩ := (TauCeti.mem_posRootCone P b).mp h
    have hi : b.rootCoefficients i = fun k ↦ b.rootCoefficients j k + f k := by
      rw [rootCoefficients_eq_iff]
      simp only [add_smul, Finset.sum_add_distrib, sum_rootCoefficients_smul_root, natCast_zsmul,
        Finset.sum_coe_sort b.support fun l ↦ f l • P.root l, ← hf, add_sub_cancel]
    simp [hi]
  · rw [← b.sum_rootCoefficients_smul_root i, ← b.sum_rootCoefficients_smul_root j,
      ← Finset.sum_sub_distrib]
    refine AddSubmonoid.sum_mem _ fun k _ ↦ ?_
    rw [← sub_smul, ← Int.toNat_of_nonneg (sub_nonneg.mpr (h k)), natCast_zsmul]
    exact (TauCeti.posRootCone P b).nsmul_mem (TauCeti.root_mem_posRootCone_of_mem_posRoots P b
      ((TauCeti.mem_posRoots P b _).mpr (b.isPos_of_mem_support k.2))) _

/-- A root whose simple-root coefficients dominate those of `RootPairing.Base.highestRoot` is the
highest root. -/
theorem highestRoot_eq_of_rootCoefficients_le [Finite ι] [Nonempty ι] {i : ι}
    (h : b.rootCoefficients b.highestRoot ≤ b.rootCoefficients i) : b.highestRoot = i := by
  refine b.rootCoefficients_injective (funext fun k ↦ ?_)
  have hsum := b.height_le_height_highestRoot i
  rw [← b.sum_rootCoefficients_eq_height, ← b.sum_rootCoefficients_eq_height] at hsum
  exact (Finset.sum_eq_sum_iff_of_le fun k _ ↦ h k).mp
    (le_antisymm (Finset.sum_le_sum fun k _ ↦ h k) hsum) k (Finset.mem_univ k)

end RootPairing.Base
