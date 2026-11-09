/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.SignedDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Level
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Level
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic

/-!
# Real models of the root lattices `A₂`, `D₄` and `E₈`

The root lattices `A₂ = typeARootLattice 2`, `D₄ = checkerboardLattice 4` and
`E₈ = typeE₈RootLattice` are positive definite even rational lattices, so they have real models
(`TauCeti.IntegralLattice.realModel`), even full lattices in Euclidean spaces of dimension `2`,
`4` and `8`. This file computes the level, the order of the discriminant group, the signed
discriminant `ZLattice.signedDiscr`, and the conductor of the Kronecker character `(D_L / ·)` of
these real models from the rational lattices, through the comparison of the two models
(`TauCeti.IntegralLattice.level_realModel`,
`TauCeti.IntegralLattice.natCard_discriminantGroup_realModel`,
`TauCeti.IntegralLattice.signedDiscr_realModel`):

* `A₂` has level `3`, determinant `3` and signed discriminant `D = -3`, whose Kronecker character
  `(-3 / ·)` is primitive of conductor `3`;
* `D₄` has level `2`, determinant `4` and signed discriminant `D = 4 = 2²`, so its Kronecker
  character `(4 / ·)` is trivial of conductor `1`;
* `E₈` has level `1`, determinant `1` and signed discriminant `D = 1`.

The scaled lattice `√2 • E₈` is even of level `2` and signed discriminant `256 = 16²`, and its
Fricke partner `√2 • (√2 • E₈)^∨` is `E₈` again, of level `1` and signed discriminant `1`. So the
level of the Fricke partner of an even lattice of level `N` can be a proper divisor of `N`, while
both `√2 • E₈` and `E₈` have trivial Kronecker character of conductor `1`.

## Main statements

* `TauCeti.IntegralLattice.level_realModel_typeARootLattice_two`,
  `TauCeti.IntegralLattice.natCard_discriminantGroup_realModel_typeARootLattice_two`,
  `TauCeti.IntegralLattice.signedDiscr_realModel_typeARootLattice_two`,
  `TauCeti.IntegralLattice.conductor_kroneckerChar_signedDiscr_realModel_typeARootLattice_two`:
  the real model of `A₂` has level `3`, discriminant group of order `3`, signed discriminant `-3`,
  and Kronecker conductor `3`.
* `TauCeti.IntegralLattice.level_realModel_checkerboardLattice_four`,
  `TauCeti.IntegralLattice.natCard_discriminantGroup_realModel_checkerboardLattice_four`,
  `TauCeti.IntegralLattice.signedDiscr_realModel_checkerboardLattice_four`,
  `TauCeti.IntegralLattice.kroneckerChar_signedDiscr_realModel_checkerboardLattice_four`:
  the real model of `D₄` has level `2`, discriminant group of order `4`, signed discriminant `4`,
  and trivial Kronecker character (conductor `1`).
* `TauCeti.IntegralLattice.signedDiscr_realModel_typeE₈RootLattice`,
  `TauCeti.IntegralLattice.level_sqrt_two_smul_realModel_typeE₈RootLattice`,
  `TauCeti.IntegralLattice.signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice`,
  `TauCeti.IntegralLattice.level_sqrt_level_smul_dual_sqrt_two_smul_realModel_typeE₈RootLattice`:
  `E₈` has signed discriminant `1`, `√2 • E₈` has level `2`, signed discriminant `256` and trivial
  Kronecker character, and its Fricke partner has level `1`.

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

/-- The real model of the root lattice `A₂` has signed discriminant `-3`. -/
theorem signedDiscr_realModel_typeARootLattice_two :
    ZLattice.signedDiscr
      ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)) = -3 := by
  rw [signedDiscr_realModel, finrank_carrier, Module.finrank_fin_fun, determinant_typeARootLattice]
  norm_num

/-- Over any commutative ring with `2 ≠ 0`, the Kronecker character `(-3 / ·)` of the real model of
`A₂` is primitive of conductor `3`. -/
theorem conductor_kroneckerChar_signedDiscr_realModel_typeARootLattice_two
    (R : Type*) [CommRing R] [NeZero (2 : R)] :
    (TauCeti.kroneckerChar R
      (ZLattice.signedDiscr ((typeARootLattice 2).realModel (isPosDef_typeARootLattice 2)))
      (((isEven_realModel_iff _ _).mpr (isEven_typeARootLattice 2)).signedDiscr_modEq_zero_or_one
        (by simp [finrank_carrier]))
      ((isIntegral_realModel _ _).signedDiscr_ne_zero)).conductor = 3 := by
  refine (TauCeti.conductor_kroneckerChar_eq_natAbs_of_neg_of_prime _ _ ?_ ?_).trans ?_
  · rw [signedDiscr_realModel_typeARootLattice_two]
    norm_num
  · rw [signedDiscr_realModel_typeARootLattice_two]
    exact Nat.prime_three
  · rw [signedDiscr_realModel_typeARootLattice_two]
    rfl

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

/-- The real model of the root lattice `D₄` has signed discriminant `4`. -/
theorem signedDiscr_realModel_checkerboardLattice_four :
    ZLattice.signedDiscr
      ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)) = 4 := by
  rw [ZLattice.signedDiscr_def, RealModelSpace.finrank_eq, finrank_carrier, Module.finrank_fin_fun,
    natCard_discriminantGroup_realModel_checkerboardLattice_four]
  norm_num

/-- Because `D_{D₄} = 4 = 2²` is a square, the Kronecker character of the real model of `D₄` is the
trivial character modulo `4`. -/
theorem kroneckerChar_signedDiscr_realModel_checkerboardLattice_four
    (R : Type*) [CommRing R] :
    TauCeti.kroneckerChar R
      (ZLattice.signedDiscr ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)))
      (((isEven_realModel_iff _ _).mpr
        (isEven_checkerboardLattice 4)).signedDiscr_modEq_zero_or_one
        ⟨2, by simp [finrank_carrier]⟩)
      ((isIntegral_realModel _ _).signedDiscr_ne_zero) = 1 :=
  TauCeti.kroneckerChar_eq_one_of_isSquare _ _
    ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩

/-- The Kronecker character of the real model of `D₄` has conductor `1`. -/
theorem conductor_kroneckerChar_signedDiscr_realModel_checkerboardLattice_four
    (R : Type*) [CommRing R] :
    (TauCeti.kroneckerChar R
      (ZLattice.signedDiscr ((checkerboardLattice 4).realModel (isPosDef_checkerboardLattice 4)))
      (((isEven_realModel_iff _ _).mpr
        (isEven_checkerboardLattice 4)).signedDiscr_modEq_zero_or_one
        ⟨2, by simp [finrank_carrier]⟩)
      ((isIntegral_realModel _ _).signedDiscr_ne_zero)).conductor = 1 :=
  TauCeti.conductor_kroneckerChar_eq_one_of_isSquare _ _
    ⟨2, by rw [signedDiscr_realModel_checkerboardLattice_four]; norm_num⟩

/-! ### `E₈` and `√2 • E₈` -/

/-- The real model space of `E₈` is nontrivial, of dimension `8`. -/
private theorem nontrivial_realModelSpace_typeE₈RootLattice :
    Nontrivial (typeE₈RootLattice.RealModelSpace isPosDef_typeE₈RootLattice) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [finrank_carrier])

/-- The real model of the even unimodular root lattice `E₈` has signed discriminant `1`. -/
theorem signedDiscr_realModel_typeE₈RootLattice :
    ZLattice.signedDiscr (typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) = 1 :=
  ((isEven_realModel_iff _ _).mpr isEven_typeE₈RootLattice).signedDiscr_eq_one_of_isUnimodular
    ((isUnimodular_realModel_iff _ _).mpr isUnimodular_typeE₈RootLattice)

/-- The real model of the root lattice `E₈`, scaled by `√2`, has level `2`. -/
theorem level_sqrt_two_smul_realModel_typeE₈RootLattice :
    ZLattice.level (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) = 2 := by
  have := nontrivial_realModelSpace_typeE₈RootLattice
  exact_mod_cast ((isEven_realModel_iff _ _).mpr
    isEven_typeE₈RootLattice).level_sqrt_smul_of_isUnimodular
    ((isUnimodular_realModel_iff _ _).mpr isUnimodular_typeE₈RootLattice) two_ne_zero

/-- The real model of `E₈` scaled by `√2` has signed discriminant `256 = 16²`. -/
theorem signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice :
    ZLattice.signedDiscr
      (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) = 256 := by
  have := (isIntegral_realModel typeE₈RootLattice isPosDef_typeE₈RootLattice).signedDiscr_sqrt_smul
    (m := 2) two_ne_zero
  push_cast at this
  rw [this, signedDiscr_realModel_typeE₈RootLattice, RealModelSpace.finrank_eq, finrank_carrier,
    Module.finrank_fin_fun]
  norm_num

/-- Because `D_{√2 • E₈} = 256 = 16²` is a square, the Kronecker character of `√2 • E₈` is the
trivial character modulo `256`. -/
theorem kroneckerChar_signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice
    (R : Type*) [CommRing R] :
    TauCeti.kroneckerChar R
      (ZLattice.signedDiscr (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice))
      (((isEven_realModel_iff _ _).mpr
        isEven_typeE₈RootLattice).signedDiscr_sqrt_smul_modEq_zero_or_one
        ⟨4, by simp [finrank_carrier]⟩ two_ne_zero)
      ((isIntegral_realModel _ _).signedDiscr_sqrt_smul_ne_zero two_ne_zero) = 1 := by
  refine TauCeti.kroneckerChar_eq_one_of_isSquare _ _ ⟨16, ?_⟩
  have h := signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice
  norm_num [h]

/-- The Kronecker character of `√2 • E₈` has conductor `1`. -/
theorem conductor_kroneckerChar_signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice
    (R : Type*) [CommRing R] :
    (TauCeti.kroneckerChar R
      (ZLattice.signedDiscr (√(2 : ℝ) • typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice))
      (((isEven_realModel_iff _ _).mpr
        isEven_typeE₈RootLattice).signedDiscr_sqrt_smul_modEq_zero_or_one
        ⟨4, by simp [finrank_carrier]⟩ two_ne_zero)
      ((isIntegral_realModel _ _).signedDiscr_sqrt_smul_ne_zero two_ne_zero)).conductor = 1 := by
  refine TauCeti.conductor_kroneckerChar_eq_one_of_isSquare _ _ ⟨16, ?_⟩
  have h := signedDiscr_sqrt_two_smul_realModel_typeE₈RootLattice
  norm_num [h]

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
