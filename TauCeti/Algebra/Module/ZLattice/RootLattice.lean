/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.FrickePartner
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Level
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Level
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic

/-!
# Real models of the root lattices `A₂`, `D₄` and `E₈`

The root lattices `A₂ = typeARootLattice 2`, `D₄ = checkerboardLattice 4` and
`E₈ = typeE₈RootLattice` are positive definite even rational lattices, so they have real models
(`TauCeti.IntegralLattice.realModel`), even full lattices in Euclidean spaces of dimension `2`,
`4` and `8`. This file computes the level and the order of the discriminant group of these real
models from the rational lattices, through the comparison of the two models
(`TauCeti.IntegralLattice.level_realModel`,
`TauCeti.IntegralLattice.natCard_discriminantGroup_realModel`). The order of the discriminant
group is the determinant `det L = covolume L ^ 2`
(`ZLattice.IsIntegral.det_eq_card_discriminantGroup`), and it gives the signed discriminant
`D_L = (-1)^k det L` of a lattice of rank `2k`:

* `A₂` has level `3` and determinant `3`, so `D = -3`;
* `D₄` has level `2` and determinant `4`, so `D = 4`;
* `E₈` has level `1` and determinant `1`; these values are direct `simp` consequences of
  `TauCeti.IntegralLattice.level_typeE₈RootLattice` and of the unimodularity of `E₈`.

The scaled lattice `√2 • E₈` is even of level `2`, and its Fricke partner `√2 • (√2 • E₈)^∨` is
`E₈` again, of level `1`. So the level of the Fricke partner of an even lattice of level `N` can
be a proper divisor of `N`. These are instances of the general statements for a scaled even
unimodular lattice (`ZLattice.IsEven.level_sqrt_smul_of_isUnimodular`,
`ZLattice.IsEven.sqrt_level_smul_dual_sqrt_smul_of_isUnimodular`).

## Main statements

* `TauCeti.IntegralLattice.level_realModel_typeARootLattice_two`,
  `TauCeti.IntegralLattice.natCard_discriminantGroup_realModel_typeARootLattice_two`: the real
  model of `A₂` has level `3` and discriminant group of order `3`.
* `TauCeti.IntegralLattice.level_realModel_checkerboardLattice_four`,
  `TauCeti.IntegralLattice.natCard_discriminantGroup_realModel_checkerboardLattice_four`: the real
  model of `D₄` has level `2` and discriminant group of order `4`.
* `TauCeti.IntegralLattice.level_sqrt_two_smul_realModel_typeE₈RootLattice`,
  `TauCeti.IntegralLattice.level_sqrt_level_smul_dual_sqrt_two_smul_realModel_typeE₈RootLattice`:
  `√2 • E₈` has level `2`, and its Fricke partner has level `1`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer,
  1999, Chapter 4.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
-/

public section

open scoped Pointwise

namespace TauCeti.IntegralLattice

/-! ### `A₂` -/

/-- The real model of the root lattice `A₂` has level `3`. -/
theorem level_realModel_typeARootLattice_two :
    ZLattice.level ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) = 3 := by
  rw [level_realModel, level_typeARootLattice_of_even even_two]

/-- The discriminant group of the real model of the root lattice `A₂` has order `3`, which is its
determinant. -/
theorem natCard_discriminantGroup_realModel_typeARootLattice_two :
    Nat.card (ZLattice.DiscriminantGroup
      ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2))) = 3 := by
  rw [natCard_discriminantGroup_realModel, natCard_discriminantGroup_typeARootLattice]

/-! ### `D₄` -/

/-- The real model of the root lattice `D₄` has level `2`. -/
theorem level_realModel_checkerboardLattice_four :
    ZLattice.level ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) = 2 := by
  rw [level_realModel, level_checkerboardLattice_of_four_dvd dvd_rfl]

/-- The discriminant group of the real model of the root lattice `D₄` has order `4`, which is its
determinant. -/
theorem natCard_discriminantGroup_realModel_checkerboardLattice_four :
    Nat.card (ZLattice.DiscriminantGroup
      ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4))) = 4 := by
  rw [natCard_discriminantGroup_realModel, natCard_discriminantGroup_checkerboardLattice]

/-! ### `E₈` and `√2 • E₈` -/

/-- The real model space of `E₈` is nontrivial, of dimension `8`. -/
private theorem nontrivial_realModelSpace_typeE₈RootLattice :
    Nontrivial (typeE₈RootLattice.RealModelSpace isPosDef_typeE₈RootLattice) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [finrank_carrier])

/-- The real model of the root lattice `E₈`, scaled by `√2`, has level `2`. -/
theorem level_sqrt_two_smul_realModel_typeE₈RootLattice :
    ZLattice.level (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) = 2 := by
  have := nontrivial_realModelSpace_typeE₈RootLattice
  exact_mod_cast ((isEven_realModel_iff _ _).mpr
    isEven_typeE₈RootLattice).level_sqrt_smul_of_isUnimodular
    ((isUnimodular_realModel_iff _ _).mpr isUnimodular_typeE₈RootLattice) two_ne_zero

/-- The Fricke partner `√2 • (√2 • E₈)^∨` of the even lattice `√2 • E₈` of level `2` has level `1`,
a proper divisor of `2`: it is `E₈` itself. -/
theorem level_sqrt_level_smul_dual_sqrt_two_smul_realModel_typeE₈RootLattice :
    ZLattice.level
      (√(ZLattice.level (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) : ℝ) •
        ZLattice.dual (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice)) = 1 := by
  have := nontrivial_realModelSpace_typeE₈RootLattice
  have h := ((isEven_realModel_iff _ _).mpr
    isEven_typeE₈RootLattice).sqrt_level_smul_dual_sqrt_smul_of_isUnimodular
    ((isUnimodular_realModel_iff _ _).mpr isUnimodular_typeE₈RootLattice) (m := 2) two_ne_zero
  push_cast at h
  rw [h, level_realModel, level_typeE₈RootLattice]

end TauCeti.IntegralLattice
