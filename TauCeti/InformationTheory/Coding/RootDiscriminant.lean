/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.A2
public import TauCeti.InformationTheory.Coding.Hexacode.D4
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.CoordinatePower

/-!
# Named codes in root-lattice discriminant groups

The tetracode and ternary Golay code give quadratic Lagrangians in the discriminant groups of
four and twelve orthogonal copies of the `A₂` root lattice. The hexacode gives one in the
discriminant group of six orthogonal copies of the `D₄` root lattice. These subgroups live in
the actual discriminant groups of the lattice powers.

The coordinate isometries are the composites of the root-alphabet identifications with the
canonical discriminant isometry for a coordinate power. Thus ternary `1` maps to the
fundamental-weight class, while quaternary `1`, `ω`, and `ω²` map to the vector, spinor, and
cospinor classes respectively.

The coordinate conventions follow Conway and Sloane, *Sphere Packings, Lattices and Groups*,
Chapter 4, §3 and Chapter 7, §§8–9.
-/

public section

namespace TauCeti

open IntegralLattice

variable {ι : Type*} [Fintype ι]

/-- Transport a ternary additive code into the discriminant group of the orthogonal power
of `A₂`. -/
noncomputable def codeInTypeA2CoordinatePowerDiscriminant (C : AdditiveCode (ZMod 3) ι) :
    AddSubgroup ((typeARootLattice 2).coordinatePower ι).DiscriminantGroup :=
  C.map
    ((typeADiscriminantQuadraticIsometry 2).coordinatePowerDiscriminant ι).toAddEquiv.toAddMonoidHom

/-- Membership in the transported code is detected by the inverse coordinate-power isometry. -/
@[simp]
theorem mem_codeInTypeA2CoordinatePowerDiscriminant_iff
    (C : AdditiveCode (ZMod 3) ι)
    (x : ((typeARootLattice 2).coordinatePower ι).DiscriminantGroup) :
    x ∈ codeInTypeA2CoordinatePowerDiscriminant C ↔
      ((typeADiscriminantQuadraticIsometry 2).coordinatePowerDiscriminant ι).toAddEquiv.symm x ∈
        C :=
  AddSubgroup.mem_map_equiv
    (f := ((typeADiscriminantQuadraticIsometry 2).coordinatePowerDiscriminant ι).toAddEquiv)

/-- Transport to the `A₂` coordinate-power discriminant group preserves and reflects
quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeA2CoordinatePowerDiscriminant_iff
    (C : AdditiveCode (ZMod 3) ι) :
    (((typeARootLattice 2).coordinatePower ι).discriminantQuadraticModule
      ((isEven_typeARootLattice 2).coordinatePower ι)).IsIsotropic
        (codeInTypeA2CoordinatePowerDiscriminant C) ↔
      ((typeAStandardQuadraticModule 2).coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeA2CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff _
    ((typeADiscriminantQuadraticIsometry 2).coordinatePowerDiscriminant ι) C

/-- A ternary code is a quadratic Lagrangian in the actual coordinate-power discriminant group
exactly when it is one in the ternary coordinate alphabet. -/
@[simp]
theorem isLagrangian_codeInTypeA2CoordinatePowerDiscriminant_iff
    (C : AdditiveCode (ZMod 3) ι) :
    (((typeARootLattice 2).coordinatePower ι).discriminantQuadraticModule
      ((isEven_typeARootLattice 2).coordinatePower ι)).IsLagrangian
        (codeInTypeA2CoordinatePowerDiscriminant C) ↔
      ((typeAStandardQuadraticModule 2).coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeA2CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff _
    ((typeADiscriminantQuadraticIsometry 2).coordinatePowerDiscriminant ι) C

namespace Tetracode

/-- The tetracode gives a quadratic Lagrangian in the discriminant group of four
orthogonal copies of the `A₂` root lattice. -/
theorem isLagrangian_codeInTypeA2CoordinatePowerDiscriminant :
    (((typeARootLattice 2).coordinatePower (Fin 4)).discriminantQuadraticModule
      ((isEven_typeARootLattice 2).coordinatePower (Fin 4))).IsLagrangian
        (codeInTypeA2CoordinatePowerDiscriminant tetracode.toAddSubgroup) := by
  rw [isLagrangian_codeInTypeA2CoordinatePowerDiscriminant_iff]
  exact isLagrangian_typeA2

end Tetracode

namespace TernaryGolay

/-- The extended ternary Golay code gives a quadratic Lagrangian in the discriminant
group of twelve orthogonal copies of the `A₂` root lattice. -/
theorem isLagrangian_codeInTypeA2CoordinatePowerDiscriminant :
    (((typeARootLattice 2).coordinatePower (Fin 12)).discriminantQuadraticModule
      ((isEven_typeARootLattice 2).coordinatePower (Fin 12))).IsLagrangian
        (codeInTypeA2CoordinatePowerDiscriminant code.toAddSubgroup) := by
  rw [isLagrangian_codeInTypeA2CoordinatePowerDiscriminant_iff]
  exact isLagrangian_typeA2

end TernaryGolay

variable {F : Type*} [Field F] [Finite F]

/-- Transport a quaternary additive code into the discriminant group of an orthogonal
power of the `D₄` root lattice. -/
noncomputable def codeInTypeD4CoordinatePowerDiscriminant (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    AddSubgroup ((checkerboardLattice 4).coordinatePower ι).DiscriminantGroup :=
  C.map
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant
      ι).toAddEquiv.toAddMonoidHom

/-- Membership in the transported quaternary code is detected by the inverse
coordinate-power isometry. -/
@[simp]
theorem mem_codeInTypeD4CoordinatePowerDiscriminant_iff (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι)
    (x : ((checkerboardLattice 4).coordinatePower ι).DiscriminantGroup) :
    x ∈ codeInTypeD4CoordinatePowerDiscriminant hF hω C ↔
      ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant
        ι).toAddEquiv.symm x ∈ C :=
  AddSubgroup.mem_map_equiv
    (f := ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant
      ι).toAddEquiv)

/-- Transport to the `D₄` coordinate-power discriminant group preserves and reflects
quadratic isotropy. -/
@[simp]
theorem isIsotropic_codeInTypeD4CoordinatePowerDiscriminant_iff
    (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    (((checkerboardLattice 4).coordinatePower ι).discriminantQuadraticModule
      ((isEven_checkerboardLattice 4).coordinatePower ι)).IsIsotropic
        (codeInTypeD4CoordinatePowerDiscriminant hF hω C) ↔
      ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).IsIsotropic C := by
  rw [codeInTypeD4CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isIsotropic_map_iff _
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant ι) C

/-- A quaternary code is a quadratic Lagrangian in the actual `D₄` coordinate-power discriminant
group exactly when it is one in the quaternary coordinate alphabet. -/
@[simp]
theorem isLagrangian_codeInTypeD4CoordinatePowerDiscriminant_iff
    (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (C : AdditiveCode F ι) :
    (((checkerboardLattice 4).coordinatePower ι).discriminantQuadraticModule
      ((isEven_checkerboardLattice 4).coordinatePower ι)).IsLagrangian
        (codeInTypeD4CoordinatePowerDiscriminant hF hω C) ↔
      ((typeD4QuaternaryQuadraticModule hF).coordinatePower ι).IsLagrangian C := by
  rw [codeInTypeD4CoordinatePowerDiscriminant]
  exact FiniteQuadraticModule.Isometry.isLagrangian_map_iff _
    ((typeD4QuaternaryDiscriminantQuadraticIsometry hF hω).coordinatePowerDiscriminant ι) C

namespace Hexacode

/-- The hexacode gives a quadratic Lagrangian in the discriminant group of six
orthogonal copies of the `D₄` root lattice. The root used for the coordinate isometry
may differ from the root used to define the code. -/
theorem isLagrangian_codeInTypeD4CoordinatePowerDiscriminant (hF : Nat.card F = 4) {ω ω' : F}
    (hω : ω ^ 2 + ω + 1 = 0) (hω' : ω' ^ 2 + ω' + 1 = 0) :
    (((checkerboardLattice 4).coordinatePower (Fin 6)).discriminantQuadraticModule
      ((isEven_checkerboardLattice 4).coordinatePower (Fin 6))).IsLagrangian
        (codeInTypeD4CoordinatePowerDiscriminant hF hω' (code ω).toAddSubgroup) := by
  rw [isLagrangian_codeInTypeD4CoordinatePowerDiscriminant_iff]
  exact isLagrangian_typeD4 hF hω

end Hexacode

end TauCeti
