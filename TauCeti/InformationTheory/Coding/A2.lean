/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.TernaryGolay
public import TauCeti.InformationTheory.Coding.Tetracode
public import TauCeti.LinearAlgebra.FiniteBilinearModule.CoordinatePower
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA

/-!
# Ternary codes in the `A₂` discriminant alphabet

The discriminant quadratic module of the `A₂` root lattice is cyclic of order three. Under
the canonical identification which sends `1 : ZMod 3` to the first fundamental-weight class, its
half-norm quadratic value and polar pairing are

```text
q(a) = a² / 3,    b(a, b) = 2ab / 3    in ℚ/ℤ.
```

Consequently, the quadratic value of a ternary word is its Hamming weight divided by three.
This file uses that formula to place the tetracode and the extended ternary Golay code as
quadratic-isotropic Lagrangian subgroups in coordinate powers of the actual `A₂` discriminant
module. These are the glue subgroups used by lattice constructions based on orthogonal sums of
`A₂` root lattices.

## Main declarations

* `TauCeti.coordinatePower_typeAStandardQuadraticModule_two_quadratic`: the `A₂` quadratic
  value of a ternary word is its Hamming weight divided by three.
* `TauCeti.codeInTypeA2Discriminant`: transport a ternary additive code to a coordinate power of
  the `A₂` discriminant group.
* `TauCeti.Tetracode.isLagrangian_codeInTypeA2Discriminant` and
  `TauCeti.TernaryGolay.isLagrangian_codeInTypeA2Discriminant`: the two named ternary codes give
  quadratic Lagrangians.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3 and
  Chapter 7, §8.
* W. Ebeling, *Lattices and Codes*, §§3.3 and 5.4.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ## The `A₂` coordinate quadratic form -/

/-- The quadratic value of a ternary word in the `A₂` coordinate alphabet is its Hamming
weight divided by three. -/
theorem coordinatePower_typeAStandardQuadraticModule_two_quadratic (x : ι → ZMod 3) :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).quadratic x =
      (((hammingNorm x : ℚ) / 3 : ℚ) : AddCircle (1 : ℚ)) := by
  calc
    _ = ∑ i, (IntegralLattice.typeAStandardQuadraticModule 2).quadratic (x i) :=
      FiniteQuadraticModule.coordinatePower_quadratic
        (IntegralLattice.typeAStandardQuadraticModule 2) ι x
    _ = ∑ i, ((((if x i ≠ 0 then 1 else 0 : ℚ)) / 3 : ℚ) :
          AddCircle (1 : ℚ)) :=
      Finset.sum_congr rfl fun i _ ↦
        IntegralLattice.typeAStandardQuadraticModule_two_quadratic (x i)
    _ = (((∑ i, (if x i ≠ 0 then 1 else 0 : ℚ) / 3 : ℚ)) :
          AddCircle (1 : ℚ)) :=
      (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))
        (fun i ↦ (if x i ≠ 0 then 1 else 0 : ℚ) / 3) Finset.univ).symm
    _ = _ := by
      have hsum : ∑ i, (if x i ≠ 0 then 1 else 0 : ℚ) = (hammingNorm x : ℚ) := by
        simp only [Finset.sum_boole, hammingNorm]
      congr 1
      rw [← Finset.sum_div, hsum]

/-- A ternary additive code is quadratic-isotropic in the `A₂` coordinate alphabet exactly
when all of its Hamming weights are divisible by three. -/
@[simp]
theorem isIsotropic_coordinatePower_typeAStandardQuadraticModule_two_iff
    (C : AdditiveCode (ZMod 3) ι) :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).IsIsotropic C ↔
      ∀ x ∈ C, 3 ∣ hammingNorm x := by
  have hpoint (x : ι → ZMod 3) :
      ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).quadratic x = 0 ↔
        3 ∣ hammingNorm x := by
    have hden : ((3 : ℕ) : ℚ) = 3 := by norm_num
    rw [coordinatePower_typeAStandardQuadraticModule_two_quadratic, ← hden,
      ← Int.cast_natCast (hammingNorm x),
      AddCircle.coe_intCast_div_natCast_eq_zero_iff (by norm_num : 3 ≠ 0)]
    exact Int.natCast_dvd_natCast
  constructor
  · intro h x hx
    exact (hpoint x).mp
      (((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).isIsotropic_def.mp
        h x hx)
  · intro h
    apply ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).isIsotropic_def.mpr
    exact fun x hx ↦ (hpoint x).mpr (h x hx)

/-! ## Transport to the discriminant groups of `A₂` -/

/-- Coordinatewise reduction from ternary symbols to the corresponding fundamental-weight
classes in the `A₂` discriminant groups. -/
noncomputable def typeA2CoordinateDiscriminantEquiv :
    (ι → ZMod 3) ≃+ (ι → (IntegralLattice.typeARootLattice 2).DiscriminantGroup) :=
  AddEquiv.piCongrRight fun _ ↦ IntegralLattice.typeADiscriminantGroupEquiv 2

omit [Fintype ι] in
/-- The coordinatewise `A₂` discriminant equivalence applies the scalar equivalence in each
coordinate. -/
@[simp]
theorem typeA2CoordinateDiscriminantEquiv_apply (x : ι → ZMod 3) (i : ι) :
    typeA2CoordinateDiscriminantEquiv x i =
      IntegralLattice.typeADiscriminantGroupEquiv 2 (x i) := by
  rw [typeA2CoordinateDiscriminantEquiv, AddEquiv.piCongrRight_apply]

omit [Fintype ι] in
/-- The constant word with symbol `1` maps coordinatewise to the first fundamental-weight
class. -/
@[simp]
theorem typeA2CoordinateDiscriminantEquiv_one :
    typeA2CoordinateDiscriminantEquiv (fun _ : ι ↦ 1) =
      fun _ ↦ IntegralLattice.typeAFundamentalWeightClass 2 := by
  ext i
  simp

/-- The additive equivalence underlying the canonical coordinatewise `A₂` quadratic isometry
is the explicit coordinatewise discriminant-group equivalence. -/
@[simp]
theorem typeA2CoordinateDiscriminantQuadraticIsometry_toAddEquiv :
    ((IntegralLattice.typeADiscriminantQuadraticIsometry 2).coordinatePower ι).toAddEquiv =
      typeA2CoordinateDiscriminantEquiv (ι := ι) := by
  rw [FiniteQuadraticModule.Isometry.coordinatePower_toAddEquiv,
    IntegralLattice.typeADiscriminantQuadraticIsometry_toAddEquiv]
  rfl

/-- A ternary additive code transported coordinatewise to the discriminant groups of copies of
the `A₂` root lattice. The symbol `1` is sent to the first fundamental-weight class in every
coordinate. -/
noncomputable def codeInTypeA2Discriminant (C : AdditiveCode (ZMod 3) ι) :
    AddSubgroup (ι → (IntegralLattice.typeARootLattice 2).DiscriminantGroup) :=
  C.map (typeA2CoordinateDiscriminantEquiv (ι := ι))

/-- Membership in the transported `A₂` discriminant subgroup is detected by applying the
inverse coordinate isometry. -/
@[simp] theorem mem_codeInTypeA2Discriminant_iff {κ : Type*} (C : AdditiveCode (ZMod 3) κ)
    (x : κ → (IntegralLattice.typeARootLattice 2).DiscriminantGroup) :
    x ∈ codeInTypeA2Discriminant C ↔
      (typeA2CoordinateDiscriminantEquiv (ι := κ)).symm x ∈ C := by
  exact AddSubgroup.mem_map_equiv
    (f := typeA2CoordinateDiscriminantEquiv (ι := κ)) (K := C) (x := x)

/-- Transport to the `A₂` discriminant groups preserves and reflects quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeA2Discriminant_iff (C : AdditiveCode (ZMod 3) ι) :
    (((IntegralLattice.typeARootLattice 2).discriminantQuadraticModule
        (IntegralLattice.isEven_typeARootLattice 2)).coordinatePower ι).IsIsotropic
      (codeInTypeA2Discriminant C) ↔
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeA2Discriminant, ← typeA2CoordinateDiscriminantQuadraticIsometry_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι)
    ((IntegralLattice.typeADiscriminantQuadraticIsometry 2).coordinatePower ι) C

/-- Transport to the `A₂` discriminant groups preserves and reflects the quadratic
Lagrangian condition. -/
@[simp]
theorem isLagrangian_codeInTypeA2Discriminant_iff (C : AdditiveCode (ZMod 3) ι) :
    (((IntegralLattice.typeARootLattice 2).discriminantQuadraticModule
        (IntegralLattice.isEven_typeARootLattice 2)).coordinatePower ι).IsLagrangian
      (codeInTypeA2Discriminant C) ↔
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeA2Discriminant, ← typeA2CoordinateDiscriminantQuadraticIsometry_toAddEquiv]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower ι)
    ((IntegralLattice.typeADiscriminantQuadraticIsometry 2).coordinatePower ι) C

namespace Tetracode

/-- The tetracode is quadratic-isotropic in the `A₂` coordinate alphabet. -/
theorem isIsotropic_typeA2 :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 4)).IsIsotropic
      tetracode.toAddSubgroup := by
  rw [isIsotropic_coordinatePower_typeAStandardQuadraticModule_two_iff]
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [hammingNorm_eq_three_of_mem_tetracode_of_ne_zero hx hx0]

/-- The tetracode is a quadratic Lagrangian in the `A₂` coordinate alphabet. -/
theorem isLagrangian_typeA2 :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 4)).IsLagrangian
      tetracode.toAddSubgroup := by
  apply FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 4)) isIsotropic_typeA2
    (FiniteQuadraticModule.IsNondegenerate.coordinatePower
      (IntegralLattice.isNondegenerate_typeAStandardQuadraticModule 2) (Fin 4))
  -- Unfolding the specialized type-`A` carrier exposes the concrete ternary word space.
  change Nat.card tetracode.toAddSubgroup ^ 2 = Nat.card (Fin 4 → ZMod 3)
  have hcard : Nat.card tetracode.toAddSubgroup = 9 := by
    exact natCard_tetracode
  rw [hcard]
  norm_num [Nat.card_pi]

/-- The tetracode, transported to four copies of the actual `A₂` discriminant group, is a
quadratic-isotropic Lagrangian subgroup. -/
theorem isLagrangian_codeInTypeA2Discriminant :
    (((IntegralLattice.typeARootLattice 2).discriminantQuadraticModule
        (IntegralLattice.isEven_typeARootLattice 2)).coordinatePower (Fin 4)).IsLagrangian
      (codeInTypeA2Discriminant tetracode.toAddSubgroup) := by
  rw [isLagrangian_codeInTypeA2Discriminant_iff]
  exact isLagrangian_typeA2

end Tetracode

namespace TernaryGolay

/-- The extended ternary Golay code is quadratic-isotropic in the `A₂` coordinate alphabet. -/
theorem isIsotropic_typeA2 :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 12)).IsIsotropic
      code.toAddSubgroup := by
  rw [isIsotropic_coordinatePower_typeAStandardQuadraticModule_two_iff]
  exact fun _ hx => three_dvd_hammingNorm hx

/-- The extended ternary Golay code is a quadratic Lagrangian in the `A₂` coordinate
alphabet. -/
theorem isLagrangian_typeA2 :
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 12)).IsLagrangian
      code.toAddSubgroup := by
  apply FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq
    ((IntegralLattice.typeAStandardQuadraticModule 2).coordinatePower (Fin 12)) isIsotropic_typeA2
    (FiniteQuadraticModule.IsNondegenerate.coordinatePower
      (IntegralLattice.isNondegenerate_typeAStandardQuadraticModule 2) (Fin 12))
  -- Unfolding the specialized type-`A` carrier exposes the concrete ternary word space.
  change Nat.card code.toAddSubgroup ^ 2 = Nat.card (Fin 12 → ZMod 3)
  have hcard : Nat.card code.toAddSubgroup = 729 := by
    exact natCard_code
  rw [hcard]
  norm_num [Nat.card_pi]

/-- The extended ternary Golay code, transported to twelve copies of the actual `A₂`
discriminant group, is a quadratic-isotropic Lagrangian subgroup. -/
theorem isLagrangian_codeInTypeA2Discriminant :
    (((IntegralLattice.typeARootLattice 2).discriminantQuadraticModule
        (IntegralLattice.isEven_typeARootLattice 2)).coordinatePower (Fin 12)).IsLagrangian
      (codeInTypeA2Discriminant code.toAddSubgroup) := by
  rw [isLagrangian_codeInTypeA2Discriminant_iff]
  exact isLagrangian_typeA2

end TernaryGolay

end TauCeti
