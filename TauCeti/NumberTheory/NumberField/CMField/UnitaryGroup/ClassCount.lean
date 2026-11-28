/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.GroupTheory.DoubleCoset.LevelCount
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Class counts at adelic unitary levels

Passing from the integral unitary group to a smaller level increases the number of classes by
at most the index of the level. If the level contains a principal congruence subgroup, the
absolute norm of the level ideal gives an explicit bound for this index. This is the
change-of-level step of `New.Data.card_stdClasses_le_exp_mul_log` in
`grh/src/New/UpperBound/Size/Estimates.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open NumberField
open scoped NumberField

namespace TauCeti

variable {E ι : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype ι] [DecidableEq ι]

/-- The class count at a subgroup of the integral unitary level containing the principal level
of `N` is at most the integral-level class count times `N(N)^(|ι|²)`, where `N(N)` is the ideal's
absolute norm. The left-hand subgroup can be any subgroup of the finite adelic unitary group,
including the image of the rational points. If the integral-level class set is infinite,
`Nat.card` is zero at both levels. -/
theorem natCard_unitary_classes_le_of_principal_level (Γ : Subgroup (finiteAdelicUnitaryGroup E ι))
    {K : Subgroup (finiteAdelicUnitaryGroup E ι)} {N : Ideal (𝓞 E)} (hN : N ≠ ⊥)
    (hprincipal : principalUnitaryLevel E ι N ≤ K)
    (hK : K ≤ integralAdelicUnitaryGroup E ι) :
    Nat.card (DoubleCoset.Quotient (Γ : Set (finiteAdelicUnitaryGroup E ι)) K) ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set (finiteAdelicUnitaryGroup E ι))
        (integralAdelicUnitaryGroup E ι)) * N.absNorm ^ (Fintype.card ι ^ 2) := by
  have hfinite : (principalUnitaryLevel E ι N).IsFiniteRelIndex (integralAdelicUnitaryGroup E ι) :=
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact (isOpen_principalUnitaryLevel hN)
      (isCompact_integralAdelicUnitaryGroup E ι)
  have : K.IsFiniteRelIndex (integralAdelicUnitaryGroup E ι) :=
    Subgroup.isFiniteRelIndex_of_le_left _ hprincipal
  have hindex := Subgroup.relIndex_le_of_le_left hprincipal hfinite.relIndex_ne_zero
  exact (DoubleCoset.natCard_quotient_le_mul_relIndex Γ hK).trans
    (Nat.mul_le_mul_left _ (hindex.trans (relIndex_principalUnitaryLevel_le hN)))

end TauCeti
