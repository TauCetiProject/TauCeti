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
the root, and its entries sum to the height. So a coefficientwise inequality between two root
columns places the difference of the roots in the positive root cone, and a root whose column
dominates that of `RootPairing.Base.highestRoot` is the highest root itself.

These criteria need neither reducedness nor irreducibility, so they identify the highest root of
a concrete datum from coefficient bounds alone, even over `ℤ`.

## Main results

* `RootPairing.Base.root_sub_mem_posRootCone_of_rootCoefficients_le`: coefficient dominance places
  the difference of two roots in the positive root cone.
* `RootPairing.Base.highestRoot_eq_of_rootCoefficients_le`: a root whose column dominates that of
  the highest root is the highest root.
-/

public section

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} (b : P.Base)

/-- If every simple-root coefficient of the root `j` is at most the corresponding coefficient of
the root `i`, then `P.root i - P.root j` lies in the positive root cone. -/
theorem root_sub_mem_posRootCone_of_rootCoefficients_le {i j : ι}
    (h : b.rootCoefficients j ≤ b.rootCoefficients i) :
    P.root i - P.root j ∈ TauCeti.posRootCone P b := by
  rw [← b.sum_rootCoefficients_smul_root i, ← b.sum_rootCoefficients_smul_root j,
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
