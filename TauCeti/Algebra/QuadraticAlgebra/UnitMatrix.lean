/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.PeriodMatrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.QuadraticAlgebra.Discriminant
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
not replace their image by the scalar signs. Over `(a, b) = (0, 0)`, `unipotentPeriodMatrixHom`
embeds `Multiplicative R` as the lower-triangular unipotent matrices `!![1, 0; s, 1]`.

Over `ℤ` with `discr a b ≤ 0`, every unit has norm `1`, so the representation takes values in
`SL(2, ℤ)` (`periodUnitSLMatrix`). These are the integral matrices that act on the upper
half-plane by Möbius transformations fixing a quadratic point.

## References

* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §2.
-/

public section

noncomputable section

open Matrix
open scoped MatrixGroups

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

/-- The unit representation preserves negation. -/
@[simp]
theorem periodUnitMatrix_neg (u : (QuadraticAlgebra R a b)ˣ) :
    periodUnitMatrix (-u) = -periodUnitMatrix u := by
  apply Units.ext
  simp only [coe_periodUnitMatrix, Units.val_neg, periodMulMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- The group of invertible quadratic multiplication matrices. -/
def periodMatrixGroup (a b : R) : Subgroup (GL (Fin 2) R) :=
  (periodUnitMatrix : (QuadraticAlgebra R a b)ˣ →* GL (Fin 2) R).range

/-- Quadratic multiplication matrices commute, so subgroups of unit images admit group
quotients without a separate normality hypothesis. -/
instance : IsMulCommutative (periodMatrixGroup a b) :=
  inferInstanceAs (IsMulCommutative
    (periodUnitMatrix : (QuadraticAlgebra R a b)ˣ →* GL (Fin 2) R).range)

/-- Entrywise negation preserves invertible quadratic multiplication matrices. -/
instance : Neg (periodMatrixGroup a b) where
  neg g := ⟨-g.val, by
    rcases g.property with ⟨u, hu⟩
    exact ⟨-u, by rw [periodUnitMatrix_neg, hu]⟩⟩

/-- Coercing `-g` from `periodMatrixGroup a b` to `GL (Fin 2) R` negates in `GL (Fin 2) R`. -/
@[simp]
theorem coe_neg_periodMatrixGroup (g : periodMatrixGroup a b) :
    ((-g : periodMatrixGroup a b) : GL (Fin 2) R) = -(g : GL (Fin 2) R) :=
  (by rfl)

/-- Distributive negation on invertible quadratic multiplication matrices. -/
instance : HasDistribNeg (periodMatrixGroup a b) :=
  Subtype.coe_injective.hasDistribNeg _ coe_neg_periodMatrixGroup (periodMatrixGroup a b).coe_mul

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

/-- `periodUnitMatrixEquiv` commutes with negation. -/
@[simp]
theorem periodUnitMatrixEquiv_neg (u : (QuadraticAlgebra R a b)ˣ) :
    periodUnitMatrixEquiv (-u) = -periodUnitMatrixEquiv u := by
  apply Subtype.ext
  simp

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

variable (R) in
/-- Over `(a, b) = (0, 0)` (where `ω² = 0`), the unipotent unit `1 + sω` has multiplication
matrix `!![1, 0; s, 1]`, giving `Multiplicative R →* periodMatrixGroup (0 : R) (0 : R)`. -/
def unipotentPeriodMatrixHom : Multiplicative R →* periodMatrixGroup (0 : R) (0 : R) where
  toFun s := periodUnitMatrixEquiv
    { val := ⟨1, s.toAdd⟩
      inv := ⟨1, -s.toAdd⟩
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  map_one' := by rw [← map_one periodUnitMatrixEquiv]; congr 1; apply Units.ext; ext <;> simp
  map_mul' s t := by
    rw [← map_mul periodUnitMatrixEquiv]; congr 1; apply Units.ext; ext <;> simp [add_comm]

/-- Underlying `2 × 2` matrix of `unipotentPeriodMatrixHom R s`. -/
@[simp]
theorem coe_unipotentPeriodMatrixHom (s : Multiplicative R) :
    (((unipotentPeriodMatrixHom R s :
        periodMatrixGroup (0 : R) (0 : R)) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![1, 0; s.toAdd, 1] := by
  simp [unipotentPeriodMatrixHom, periodMulMatrix_eq]

/-- `periodUnitMatrixEquiv.symm` sends `unipotentPeriodMatrixHom R s` to the unit `1 + sω`. -/
theorem val_periodUnitMatrixEquiv_symm_unipotentPeriodMatrixHom (s : Multiplicative R) :
    ((periodUnitMatrixEquiv.symm (unipotentPeriodMatrixHom R s) :
      (QuadraticAlgebra R 0 0)ˣ) : QuadraticAlgebra R 0 0) = ⟨1, s.toAdd⟩ := by
  simp

/-! ### Integral units of nonpositive discriminant -/

section SpecialLinear

variable {a b : ℤ}

/-- When `discr a b ≤ 0`, every integral unit has norm `1`
(`QuadraticAlgebra.norm_eq_one_of_discr_nonpos`), so its multiplication matrix lies in
`SL(2, ℤ)`. -/
def periodUnitSLMatrix (hd : discr a b ≤ 0) : (QuadraticAlgebra ℤ a b)ˣ →* SL(2, ℤ) where
  toFun u := ⟨(u : QuadraticAlgebra ℤ a b).periodMulMatrix, by
    rw [det_periodMulMatrix, norm_eq_one_of_discr_nonpos hd]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext <| by simp only [Units.val_mul, periodMulMatrix_mul]; rfl

/-- The matrix underlying `periodUnitSLMatrix hd u` is the multiplication matrix of `u`. -/
@[simp]
theorem coe_periodUnitSLMatrix (hd : discr a b ≤ 0) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    ((periodUnitSLMatrix hd u : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (u : QuadraticAlgebra ℤ a b).periodMulMatrix :=
  (rfl)

/-- In `GL(2, ℤ)`, `periodUnitSLMatrix` is the period representation `periodUnitMatrix`. -/
@[simp]
theorem toGL_periodUnitSLMatrix (hd : discr a b ≤ 0) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    SpecialLinearGroup.toGL (periodUnitSLMatrix hd u) = periodUnitMatrix u :=
  Units.ext (by simp)

/-- The representation of integral units in `SL(2, ℤ)` is faithful. -/
theorem periodUnitSLMatrix_injective (hd : discr a b ≤ 0) :
    Function.Injective (periodUnitSLMatrix hd) := fun u v h ↦
  periodUnitMatrix_injective (by rw [← toGL_periodUnitSLMatrix hd, h, toGL_periodUnitSLMatrix])

/-- `periodUnitSLMatrix` commutes with negation. -/
@[simp]
theorem periodUnitSLMatrix_neg (hd : discr a b ≤ 0) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    periodUnitSLMatrix hd (-u) = -periodUnitSLMatrix hd u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [periodMulMatrix_eq, add_comm]

end SpecialLinear

end QuadraticAlgebra
