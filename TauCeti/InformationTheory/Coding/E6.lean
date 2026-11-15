/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Tetracode
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic

import Mathlib.Algebra.BigOperators.Field

/-!
# Ternary codes in the `E₆` discriminant alphabet

The discriminant quadratic module of the `E₆` root lattice is cyclic of order three. Under
`TauCeti.IntegralLattice.typeE₆DiscriminantGroupEquiv`, which sends `1 : ZMod 3` to the
minuscule fundamental-weight class `ϖ₁`, its half-norm quadratic value and polar pairing are

```text
q(a) = 2a² / 3,    b(a, b) = ab / 3    in ℚ/ℤ.
```

Consequently, the quadratic value of a ternary word in a coordinate power of the `E₆`
discriminant alphabet is twice its Hamming weight divided by three, and an additive ternary
code is quadratic-isotropic if and only if all of its Hamming weights are divisible by three.
This file places ternary additive codes into coordinate powers of the `E₆` discriminant group
and into the discriminant groups of orthogonal powers of `typeE₆RootLattice`, and specializes
both constructions to the ternary tetracode `TauCeti.tetracode`.

The coordinate-power transport mirrors the `A₂` and `D₄` constructions in
`TauCeti.InformationTheory.Coding.A2` and `TauCeti.InformationTheory.Coding.RootDiscriminant`
by the Tau Ceti contributors.

## Main declarations

* `TauCeti.IntegralLattice.typeE₆StandardQuadraticModule_quadratic`: the `E₆` quadratic value
  of a ternary symbol is `0` at zero and `2/3` at either nonzero symbol.
* `TauCeti.IntegralLattice.isNondegenerate_typeE₆StandardQuadraticModule`: the standard cyclic
  `E₆` discriminant model is nondegenerate.
* `TauCeti.coordinatePower_typeE₆StandardQuadraticModule_quadratic`: the `E₆` quadratic value
  of a ternary word is twice its Hamming weight divided by three.
* `TauCeti.isIsotropic_coordinatePower_typeE₆StandardQuadraticModule_iff`: a ternary additive
  code is quadratic-isotropic in the `E₆` coordinate alphabet iff every codeword weight is a
  multiple of three.
* `TauCeti.codeInTypeE6Discriminant` and `TauCeti.codeInTypeE6CoordinatePowerDiscriminant`:
  transport a ternary additive code to coordinate powers of the `E₆` discriminant group and to
  the discriminant group of `typeE₆RootLattice.coordinatePower ι`.
* `TauCeti.Tetracode.isLagrangian_typeE6`,
  `TauCeti.Tetracode.isLagrangian_codeInTypeE6Discriminant`, and
  `TauCeti.Tetracode.isLagrangian_codeInTypeE6CoordinatePowerDiscriminant`: the ternary
  tetracode gives a quadratic Lagrangian in four copies of the `E₆` discriminant alphabet and
  in the discriminant group of `(E₆)⁴`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §3 and §8.3, and Chapter 16, §1.
* W. Ebeling, *Lattices and Codes*, 3rd ed., §§1.3 and 3.3.
-/

public section

namespace TauCeti

namespace IntegralLattice

/-- In the standard `E₆` discriminant module, the quadratic value of a symbol is `0` at zero
and `2/3` at either nonzero symbol. -/
-- Not `@[simp]`: `typeE₆StandardQuadraticModule_quadratic_one` is already `@[simp]` at `1`.
theorem typeE₆StandardQuadraticModule_quadratic (a : ZMod 3) :
    typeE₆StandardQuadraticModule.quadratic a =
      (((if a ≠ 0 then 2 else 0 : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ)) := by
  rcases (by decide : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2) a with rfl | rfl | rfl
  · exact (QuadraticMap.map_zero _).trans (by simp)
  · simp [one_ne_zero]
  · have h2 : typeE₆StandardQuadraticModule.quadratic (2 : ZMod 3) =
        typeE₆StandardQuadraticModule.quadratic (1 : ZMod 3) := by
      rw [show (2 : ZMod 3) = -1 by decide]
      exact QuadraticMap.map_neg _ _
    rw [h2, typeE₆StandardQuadraticModule_quadratic_one]
    simp [show (2 : ZMod 3) ≠ 0 by decide]

/-- **The standard cyclic `E₆` discriminant model is nondegenerate.** -/
theorem isNondegenerate_typeE₆StandardQuadraticModule :
    typeE₆StandardQuadraticModule.IsNondegenerate :=
  typeE₆DiscriminantQuadraticIsometry.isNondegenerate_iff.mpr
    (isNondegenerate_discriminantQuadraticModule _ _)

end IntegralLattice

open IntegralLattice

variable {ι : Type*} [Fintype ι]

/-! ## The `E₆` coordinate quadratic form -/

/-- The quadratic value of a ternary word in the `E₆` coordinate alphabet is twice its Hamming
weight divided by three. -/
@[simp↓]
theorem coordinatePower_typeE₆StandardQuadraticModule_quadratic (x : ι → ZMod 3) :
    (typeE₆StandardQuadraticModule.coordinatePower ι).quadratic x =
      (((2 * (hammingNorm x : ℚ) / 3 : ℚ)) : AddCircle (1 : ℚ)) := by
  calc
    _ = ∑ i, typeE₆StandardQuadraticModule.quadratic (x i) :=
      FiniteQuadraticModule.coordinatePower_quadratic typeE₆StandardQuadraticModule ι x
    _ = ∑ i, ((((if x i ≠ 0 then 2 else 0 : ℚ)) / 3 : ℚ) : AddCircle (1 : ℚ)) :=
      Finset.sum_congr rfl fun i _ ↦ typeE₆StandardQuadraticModule_quadratic (x i)
    _ = (((∑ i, (if x i ≠ 0 then 2 else 0 : ℚ) / 3 : ℚ)) : AddCircle (1 : ℚ)) :=
      (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        (fun i ↦ (if x i ≠ 0 then 2 else 0 : ℚ) / 3) Finset.univ).symm
    _ = _ := by
      have hsum : ∑ i, (if x i ≠ 0 then 2 else 0 : ℚ) = 2 * (hammingNorm x : ℚ) := by
        simp only [hammingNorm, Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
          nsmul_eq_mul, add_zero, mul_comm]
      congr 1
      rw [← Finset.sum_div, hsum]

/-- A ternary additive code is quadratic-isotropic in the `E₆` coordinate alphabet exactly
when all of its Hamming weights are divisible by three. -/
@[simp]
theorem isIsotropic_coordinatePower_typeE₆StandardQuadraticModule_iff
    (C : AdditiveCode (ZMod 3) ι) :
    (typeE₆StandardQuadraticModule.coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, 3 ∣ hammingNorm x := by
  have hpoint (x : ι → ZMod 3) :
      (typeE₆StandardQuadraticModule.coordinatePower ι).quadratic x = 0 ↔
        3 ∣ hammingNorm x := by
    have hnum : (2 : ℚ) * (hammingNorm x : ℚ) = ((2 * (hammingNorm x : ℤ) : ℤ) : ℚ) := by
      push_cast; rfl
    have hden : (3 : ℚ) = ((3 : ℕ) : ℚ) := by norm_num
    rw [coordinatePower_typeE₆StandardQuadraticModule_quadratic, hnum, hden,
      AddCircle.coe_intCast_div_natCast_eq_zero_iff (by norm_num : 3 ≠ 0)]
    omega
  constructor
  · intro h x hx
    exact (hpoint x).mp
      ((typeE₆StandardQuadraticModule.coordinatePower ι).isIsotropic_def.mp h x hx)
  · intro h
    exact (typeE₆StandardQuadraticModule.coordinatePower ι).isIsotropic_def.mpr
      fun x hx ↦ (hpoint x).mpr (h x hx)

/-! ## Transport to the discriminant groups of `E₆` -/

/-- Coordinatewise identification of ternary symbols with the corresponding minuscule-weight
classes in the `E₆` discriminant groups. -/
noncomputable def typeE6CoordinateDiscriminantEquiv :
    (ι → ZMod 3) ≃+ (ι → typeE₆RootLattice.DiscriminantGroup) :=
  AddEquiv.piCongrRight fun _ ↦ typeE₆DiscriminantGroupEquiv

omit [Fintype ι] in
/-- The coordinatewise `E₆` discriminant equivalence applies the scalar equivalence in each
coordinate. -/
@[simp]
theorem typeE6CoordinateDiscriminantEquiv_apply (x : ι → ZMod 3) (i : ι) :
    typeE6CoordinateDiscriminantEquiv x i = typeE₆DiscriminantGroupEquiv (x i) := by
  rw [typeE6CoordinateDiscriminantEquiv, AddEquiv.piCongrRight_apply]

omit [Fintype ι] in
/-- The inverse coordinatewise `E₆` discriminant equivalence applies the inverse scalar
equivalence in each coordinate. -/
@[simp]
theorem typeE6CoordinateDiscriminantEquiv_symm_apply
    (x : ι → typeE₆RootLattice.DiscriminantGroup) (i : ι) :
    (typeE6CoordinateDiscriminantEquiv (ι := ι)).symm x i =
      typeE₆DiscriminantGroupEquiv.symm (x i) :=
  (rfl)

omit [Fintype ι] in
/-- The constant word with symbol `1` maps coordinatewise to the minuscule-weight class `ϖ₁`. -/
@[simp]
theorem typeE6CoordinateDiscriminantEquiv_one :
    typeE6CoordinateDiscriminantEquiv (fun _ : ι ↦ 1) =
      fun _ ↦ typeE₆MinusculeWeightClass := by
  ext i
  simp

/-- The additive equivalence underlying the canonical coordinatewise `E₆` quadratic isometry
is `typeE6CoordinateDiscriminantEquiv`. -/
@[simp]
theorem typeE6CoordinateDiscriminantQuadraticIsometry_toAddEquiv :
    (typeE₆DiscriminantQuadraticIsometry.coordinatePower ι).toAddEquiv =
      typeE6CoordinateDiscriminantEquiv (ι := ι) := by
  rw [FiniteQuadraticModule.Isometry.coordinatePower_toAddEquiv,
    typeE₆DiscriminantQuadraticIsometry_toAddEquiv]
  rfl

/-- A ternary additive code transported coordinatewise to the discriminant groups of copies of
the `E₆` root lattice. The symbol `1` is sent to the minuscule-weight class `ϖ₁` in every
coordinate. -/
noncomputable def codeInTypeE6Discriminant (C : AdditiveCode (ZMod 3) ι) :
    AddSubgroup (ι → typeE₆RootLattice.DiscriminantGroup) :=
  C.map (typeE6CoordinateDiscriminantEquiv (ι := ι))

/-- Membership in the transported `E₆` discriminant subgroup is detected by applying the
inverse coordinate equivalence. -/
@[simp]
theorem mem_codeInTypeE6Discriminant_iff {κ : Type*} (C : AdditiveCode (ZMod 3) κ)
    (x : κ → typeE₆RootLattice.DiscriminantGroup) :
    x ∈ codeInTypeE6Discriminant C ↔
      (typeE6CoordinateDiscriminantEquiv (ι := κ)).symm x ∈ C :=
  AddSubgroup.mem_map_equiv (f := typeE6CoordinateDiscriminantEquiv (ι := κ)) (K := C) (x := x)

/-- Transport to the `E₆` discriminant groups preserves and reflects quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeE6Discriminant_iff (C : AdditiveCode (ZMod 3) ι) :
    ((typeE₆RootLattice.discriminantQuadraticModule
        isEven_typeE₆RootLattice).coordinatePower ι).IsIsotropic
      (codeInTypeE6Discriminant C) ↔
    (typeE₆StandardQuadraticModule.coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeE6Discriminant, ← typeE6CoordinateDiscriminantQuadraticIsometry_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff
    (typeE₆StandardQuadraticModule.coordinatePower ι)
    (typeE₆DiscriminantQuadraticIsometry.coordinatePower ι) C

/-- Transport to the `E₆` discriminant groups preserves and reflects the quadratic
Lagrangian condition. -/
@[simp]
theorem isLagrangian_codeInTypeE6Discriminant_iff (C : AdditiveCode (ZMod 3) ι) :
    ((typeE₆RootLattice.discriminantQuadraticModule
        isEven_typeE₆RootLattice).coordinatePower ι).IsLagrangian
      (codeInTypeE6Discriminant C) ↔
    (typeE₆StandardQuadraticModule.coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeE6Discriminant, ← typeE6CoordinateDiscriminantQuadraticIsometry_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff
    (typeE₆StandardQuadraticModule.coordinatePower ι)
    (typeE₆DiscriminantQuadraticIsometry.coordinatePower ι) C

/-- Transport a ternary additive code into the discriminant group of the orthogonal power
of `typeE₆RootLattice`. -/
noncomputable def codeInTypeE6CoordinatePowerDiscriminant (C : AdditiveCode (ZMod 3) ι) :
    AddSubgroup (typeE₆RootLattice.coordinatePower ι).DiscriminantGroup :=
  C.map
    (typeE₆DiscriminantQuadraticIsometry.coordinatePowerDiscriminant ι).toAddEquiv.toAddMonoidHom

/-- Membership in the transported `E₆` coordinate-power code is detected by the inverse
coordinate-power isometry. -/
@[simp]
theorem mem_codeInTypeE6CoordinatePowerDiscriminant_iff (C : AdditiveCode (ZMod 3) ι)
    (x : (typeE₆RootLattice.coordinatePower ι).DiscriminantGroup) :
    x ∈ codeInTypeE6CoordinatePowerDiscriminant C ↔
      (typeE₆DiscriminantQuadraticIsometry.coordinatePowerDiscriminant ι).toAddEquiv.symm x ∈ C :=
  AddSubgroup.mem_map_equiv
    (f := (typeE₆DiscriminantQuadraticIsometry.coordinatePowerDiscriminant ι).toAddEquiv)

/-- Transport to the `E₆` coordinate-power discriminant group preserves and reflects
quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeE6CoordinatePowerDiscriminant_iff
    (C : AdditiveCode (ZMod 3) ι) :
    ((typeE₆RootLattice.coordinatePower ι).discriminantQuadraticModule
      (isEven_typeE₆RootLattice.coordinatePower ι)).IsIsotropic
        (codeInTypeE6CoordinatePowerDiscriminant C) ↔
      (typeE₆StandardQuadraticModule.coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeE6CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff _
    (typeE₆DiscriminantQuadraticIsometry.coordinatePowerDiscriminant ι) C

/-- A ternary code is a quadratic Lagrangian in the actual `E₆` coordinate-power discriminant
group exactly when it is one in the ternary `E₆` coordinate alphabet. -/
@[simp]
theorem isLagrangian_codeInTypeE6CoordinatePowerDiscriminant_iff
    (C : AdditiveCode (ZMod 3) ι) :
    ((typeE₆RootLattice.coordinatePower ι).discriminantQuadraticModule
      (isEven_typeE₆RootLattice.coordinatePower ι)).IsLagrangian
        (codeInTypeE6CoordinatePowerDiscriminant C) ↔
      (typeE₆StandardQuadraticModule.coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeE6CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff _
    (typeE₆DiscriminantQuadraticIsometry.coordinatePowerDiscriminant ι) C

namespace Tetracode

/-- The ternary tetracode is quadratic-isotropic in the `E₆` coordinate alphabet. -/
theorem isIsotropic_typeE6 :
    (typeE₆StandardQuadraticModule.coordinatePower (Fin 4)).IsIsotropic
      tetracode.toAddSubgroup := by
  rw [isIsotropic_coordinatePower_typeE₆StandardQuadraticModule_iff]
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [hammingNorm_eq_three_of_mem_tetracode_of_ne_zero hx hx0]

/-- The ternary tetracode is a quadratic Lagrangian in the `E₆` coordinate alphabet. -/
theorem isLagrangian_typeE6 :
    (typeE₆StandardQuadraticModule.coordinatePower (Fin 4)).IsLagrangian
      tetracode.toAddSubgroup := by
  have hcard :
      Nat.card tetracode.toAddSubgroup ^ 2 =
        Nat.card (typeE₆StandardQuadraticModule.coordinatePower (Fin 4)) := by
    have ht : Nat.card tetracode.toAddSubgroup = 9 := natCard_tetracode
    have hm : Nat.card (typeE₆StandardQuadraticModule.coordinatePower (Fin 4)) =
        Nat.card (Fin 4 → ZMod 3) := rfl
    rw [ht, hm]
    norm_num [Nat.card_pi]
  exact FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq
    (typeE₆StandardQuadraticModule.coordinatePower (Fin 4)) isIsotropic_typeE6
    (FiniteQuadraticModule.IsNondegenerate.coordinatePower
      isNondegenerate_typeE₆StandardQuadraticModule (Fin 4)) hcard

/-- The ternary tetracode, transported to four copies of the `E₆` discriminant group, is a
quadratic Lagrangian subgroup. -/
theorem isLagrangian_codeInTypeE6Discriminant :
    ((typeE₆RootLattice.discriminantQuadraticModule
        isEven_typeE₆RootLattice).coordinatePower (Fin 4)).IsLagrangian
      (codeInTypeE6Discriminant tetracode.toAddSubgroup) :=
  (isLagrangian_codeInTypeE6Discriminant_iff _).mpr isLagrangian_typeE6

/-- The ternary tetracode gives a quadratic Lagrangian in the discriminant group of four
orthogonal copies of the `E₆` root lattice. -/
theorem isLagrangian_codeInTypeE6CoordinatePowerDiscriminant :
    ((typeE₆RootLattice.coordinatePower (Fin 4)).discriminantQuadraticModule
      (isEven_typeE₆RootLattice.coordinatePower (Fin 4))).IsLagrangian
        (codeInTypeE6CoordinatePowerDiscriminant tetracode.toAddSubgroup) :=
  (isLagrangian_codeInTypeE6CoordinatePowerDiscriminant_iff _).mpr isLagrangian_typeE6

end Tetracode

end TauCeti
