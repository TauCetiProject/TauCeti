/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RealModel
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Discriminant
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Basic

/-!
# Discriminant forms of real models: rank one and type A

The discriminant group of a real model is identified with the original rational discriminant
group. These examples check both its action on representatives and preservation of the
half-norm discriminant quadratic map. In particular, the generator values are `1 / (2a)` for
a positive even rank-one lattice of norm `a`, and `n / (2(n + 1))` for `Aₙ`.

The quadratic map is the existing one on the rational model of the real lattice, not a new
real-valued quadratic form. The examples reuse the rational calculations in
`IntegralLattice.RankOne.Discriminant` and `IntegralLattice.RootLattice.TypeA.Basic`.
-/

public section

namespace TauCeti.IntegralLattice

section RankOne

variable (a : ℤ) [NeZero a] (ha : 0 < a)

-- The generator is carried to the class of its actual real dual representative.
example :
    (rankOne a).realModelDiscriminantGroupEquiv (isPosDef_rankOne ha) (rankOneClass a) =
      Submodule.Quotient.mk
        ((rankOne a).realModelDualEquiv (isPosDef_rankOne ha) (rankOneDualGen a)) := by
  have hg : rankOneClass a = Submodule.Quotient.mk (rankOneDualGen a) := by
    simpa using zsmul_rankOneClass a 1
  rw [hg, realModelDiscriminantGroupEquiv_mk]

-- This includes every positive even rank-one lattice ⟨2m⟩.
example (he : Even a) :
    (ZLattice.ratModel
      ((rankOne a).isIntegral_realModel (isPosDef_rankOne ha))).discriminantQuadraticMap
        ((ZLattice.isEven_ratModel_iff _).mpr
          (((rankOne a).isEven_realModel_iff (isPosDef_rankOne ha)).mpr
            ((isEven_rankOne_iff a).mpr he)))
        (ZLattice.ratModelDiscriminantGroupEquiv _
          ((rankOne a).realModelDiscriminantGroupEquiv (isPosDef_rankOne ha) (rankOneClass a))) =
      ((1 / (2 * a) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_realModelDiscriminantGroupEquiv _ _
    ((isEven_rankOne_iff a).mpr he), discriminantQuadraticMap_rankOneClass a he]

-- The bilinear value is twice the half-norm value.
example :
    (ZLattice.ratModel
      ((rankOne a).isIntegral_realModel (isPosDef_rankOne ha))).discriminantPairing
        (ZLattice.ratModelDiscriminantGroupEquiv _
          ((rankOne a).realModelDiscriminantGroupEquiv (isPosDef_rankOne ha) (rankOneClass a)))
        (ZLattice.ratModelDiscriminantGroupEquiv _
          ((rankOne a).realModelDiscriminantGroupEquiv (isPosDef_rankOne ha) (rankOneClass a))) =
      ((1 / a : ℚ) : AddCircle (1 : ℚ)) := by
  simp

end RankOne

section TypeA

variable (n : ℕ)

-- This works also for n = 0: the generator and its value are both zero.
example :
    (typeARootLattice n).realModelDiscriminantGroupEquiv (isPosDef_typeARootLattice n)
        (typeAFundamentalWeightClass n) =
      Submodule.Quotient.mk
        ((typeARootLattice n).realModelDualEquiv (isPosDef_typeARootLattice n)
          (typeAFundamentalWeightDual n)) := by
  rw [← mk_typeAFundamentalWeightDual, realModelDiscriminantGroupEquiv_mk]

example :
    (ZLattice.ratModel ((typeARootLattice n).isIntegral_realModel
      (isPosDef_typeARootLattice n))).discriminantQuadraticMap
        ((ZLattice.isEven_ratModel_iff _).mpr
          (((typeARootLattice n).isEven_realModel_iff (isPosDef_typeARootLattice n)).mpr
            (isEven_typeARootLattice n)))
        (ZLattice.ratModelDiscriminantGroupEquiv _
          ((typeARootLattice n).realModelDiscriminantGroupEquiv (isPosDef_typeARootLattice n)
            (typeAFundamentalWeightClass n))) =
      (((n : ℚ) / (2 * ((n : ℚ) + 1))) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap_realModelDiscriminantGroupEquiv _ _
    (isEven_typeARootLattice n), discriminantQuadraticMap_typeAFundamentalWeightClass]

end TypeA

end TauCeti.IntegralLattice
