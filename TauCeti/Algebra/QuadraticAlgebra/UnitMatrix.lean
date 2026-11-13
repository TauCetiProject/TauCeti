/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.PeriodMatrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The group of quadratic multiplication matrices

For `ω² = a + bω`, multiplication by `t + sω` on row coordinates in `(ω, 1)` is the matrix
`!![t + b*s, a*s; s, t]`. Its determinant is the norm, so the matrices of this shape in `GL₂(R)`
form a group canonically isomorphic to `(QuadraticAlgebra R a b)ˣ`. The bottom row supplies the
inverse of this isomorphism. No field or reducedness hypothesis is needed: residue algebras at
ramified primes are included.

For the monic polynomial `X² + BX + C`, take `a = -C` and `b = -B`. Over `R = ZMod N`, this is
the finite matrix group used to act on quadratic division points. The coefficient-change law
for `periodUnitMatrix` identifies reduction of actual integral units inside this group; it does
not replace their image by the scalar signs.

## References

* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §2.
-/

public section

noncomputable section

open Matrix

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The period representation on units. Its value is an invertible multiplication matrix. -/
def periodUnitMatrix : (QuadraticAlgebra R a b)ˣ →* GL (Fin 2) R :=
  Units.map periodMulMatrixHom

/-- The matrix underlying the representation of a unit is its multiplication matrix. -/
@[simp]
theorem coe_periodUnitMatrix (u : (QuadraticAlgebra R a b)ˣ) :
    (periodUnitMatrix u : Matrix (Fin 2) (Fin 2) R) =
      (u : QuadraticAlgebra R a b).periodMulMatrix :=
  periodMulMatrixHom_apply _

/-- The unit representation is faithful, including over rings with zero divisors. -/
theorem periodUnitMatrix_injective :
    Function.Injective (periodUnitMatrix : (QuadraticAlgebra R a b)ˣ → GL (Fin 2) R) :=
  Units.map_injective (by
    simpa only [Function.Injective, periodMulMatrixHom_apply] using
      (periodMulMatrix_injective (a := a) (b := b)))

/-- The group of invertible quadratic multiplication matrices. -/
def periodMatrixGroup (a b : R) : Subgroup (GL (Fin 2) R) :=
  (periodUnitMatrix : (QuadraticAlgebra R a b)ˣ →* GL (Fin 2) R).range

/-- Quadratic multiplication matrices commute, so subgroups of unit images admit group
quotients without a separate normality hypothesis. -/
instance : IsMulCommutative (periodMatrixGroup a b) :=
  inferInstanceAs (IsMulCommutative
    (periodUnitMatrix : (QuadraticAlgebra R a b)ˣ →* GL (Fin 2) R).range)

/-- An invertible matrix is a quadratic multiplication matrix exactly when its entries satisfy
the two linear equations imposed by its bottom row. -/
@[simp]
theorem mem_periodMatrixGroup_iff {M : GL (Fin 2) R} :
    M ∈ periodMatrixGroup a b ↔
      M 0 0 = M 1 1 + b * M 1 0 ∧ M 0 1 = a * M 1 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    simp [coe_periodUnitMatrix, periodMulMatrix_eq]
  · intro h
    let z : QuadraticAlgebra R a b := ⟨M 1 1, M 1 0⟩
    have hz : z.periodMulMatrix = (M : Matrix (Fin 2) (Fin 2) R) := by
      rw [periodMulMatrix_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [z, h.1, h.2]
    have hu : IsUnit z := isUnit_periodMulMatrix_iff z |>.mp (hz ▸ M.isUnit)
    exact ⟨hu.unit, Units.ext (by simpa using hz)⟩

/-- The units of the quadratic algebra are exactly the invertible period matrices. -/
def periodUnitMatrixEquiv : (QuadraticAlgebra R a b)ˣ ≃* periodMatrixGroup a b :=
  MonoidHom.ofInjective periodUnitMatrix_injective

/-- The equivalence uses the specified period representation, not an arbitrary identification. -/
@[simp]
theorem coe_periodUnitMatrixEquiv (u : (QuadraticAlgebra R a b)ˣ) :
    (periodUnitMatrixEquiv u : GL (Fin 2) R) = periodUnitMatrix u :=
  (by rfl)

/-- The bottom row gives the algebra element underlying the inverse equivalence. -/
@[simp]
theorem coe_periodUnitMatrixEquiv_symm (M : periodMatrixGroup a b) :
    ((periodUnitMatrixEquiv.symm M : (QuadraticAlgebra R a b)ˣ) : QuadraticAlgebra R a b) =
      ⟨(M : GL (Fin 2) R) 1 1, (M : GL (Fin 2) R) 1 0⟩ := by
  obtain ⟨u, rfl⟩ := periodUnitMatrixEquiv.surjective M
  simp [periodMulMatrix_eq]

/-- Coefficient change on the algebra's units is the entrywise coefficient change on matrices. -/
@[simp]
theorem periodUnitMatrix_mapRingHom {S : Type*} [CommRing S] (f : R →+* S)
    (u : (QuadraticAlgebra R a b)ˣ) :
    periodUnitMatrix (Units.map (mapRingHom f a b :
      QuadraticAlgebra R a b →* QuadraticAlgebra S (f a) (f b)) u) =
      GeneralLinearGroup.map f (periodUnitMatrix u) := by
  apply Units.ext
  simpa only [coe_periodUnitMatrix, GeneralLinearGroup.map, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.mapMatrix_apply] using
    (periodMulMatrix_mapRingHom f (u : QuadraticAlgebra R a b))

/-- Counting the matrix group is the same as counting units in the actual quadratic algebra. -/
theorem card_periodMatrixGroup :
    Nat.card (periodMatrixGroup a b) = Nat.card (QuadraticAlgebra R a b)ˣ :=
  Nat.card_congr periodUnitMatrixEquiv.toEquiv.symm

/-- A coordinate formula for the order of the group, suitable for finite residue-ring
computations. It counts exactly the pairs whose norm is a unit. -/
theorem card_periodMatrixGroup_eq_card_norm_units :
    Nat.card (periodMatrixGroup a b) =
      Nat.card {p : R × R // IsUnit (p.1 ^ 2 + b * p.1 * p.2 - a * p.2 ^ 2)} := by
  rw [card_periodMatrixGroup]
  refine Nat.card_congr (Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans
    (Equiv.subtypeEquiv (equivProd a b) ?_))
  intro z
  exact isUnit_iff_norm_isUnit.trans (by simp [norm_def, equivProd, sq, mul_assoc])

end QuadraticAlgebra
