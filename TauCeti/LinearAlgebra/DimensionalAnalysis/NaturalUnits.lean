/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The mass dimension in natural units

A dimension is represented by its mass, length, and time exponents. The speed of
light and the reduced Planck constant have dimensions `(0, 1, -1)` and `(1, 2, -1)`.
Setting both constants equal to one identifies exponent vectors modulo the span
of these two dimensions. This quotient is measured by the mass dimension
`(a, b, c) ↦ a - b - c`.

The basis ordered as speed, action, and mass also expresses dimensions in terms
of powers of the speed of light, the reduced Planck constant, and mass. The
rational quotient allows fractional exponents and agrees with the integer quotient
under coordinate casting. The quotient identification uses the first isomorphism
theorem, `LinearMap.quotKerEquivOfSurjective`.
-/

public section

namespace TauCeti.NaturalUnits

open Module

variable (R : Type*) [CommRing R]

/-- The mass, length, and time exponents of speed. -/
def speed : Fin 3 → R := ![0, 1, -1]

/-- The mass, length, and time exponents of action. -/
def action : Fin 3 → R := ![1, 2, -1]

/-- The mass, length, and time exponents of mass. -/
def mass : Fin 3 → R := ![1, 0, 0]

/-- The coordinates of the speed exponent vector. -/
theorem speed_def : speed R = ![0, 1, -1] := (rfl)

/-- The coordinates of the action exponent vector. -/
theorem action_def : action R = ![1, 2, -1] := (rfl)

/-- The coordinates of the mass exponent vector. -/
theorem mass_def : mass R = ![1, 0, 0] := (rfl)

/-- The basis of exponent vectors ordered as speed, action, and mass. -/
noncomputable def unitBasis : Basis (Fin 3) R (Fin 3 → R) :=
  Basis.ofEquivFun
    { toFun := fun x ↦ ![-x 1 - 2 * x 2, x 1 + x 2, x 0 - x 1 - x 2]
      invFun := fun u ↦ ![u 1 + u 2, u 0 + 2 * u 1, -u 0 - u 1]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro a x
        ext i
        fin_cases i <;> simp <;> ring
      left_inv := by
        intro x
        ext i
        fin_cases i <;> simp <;> ring
      right_inv := by
        intro u
        ext i
        fin_cases i <;> simp <;> ring }

variable {R}

/-- The exponents of speed, action, and mass representing an exponent vector `x`. -/
theorem unitBasis_equivFun (x : Fin 3 → R) :
    (unitBasis R).equivFun x = ![-x 1 - 2 * x 2, x 1 + x 2, x 0 - x 1 - x 2] := by
  simp only [unitBasis, Basis.equivFun_ofEquivFun]
  rfl

/-- The first basis vector is the dimension of speed. -/
@[simp] theorem unitBasis_zero : unitBasis R 0 = speed R := by
  apply (unitBasis R).equivFun.injective
  ext i
  simp only [Basis.equivFun_self, unitBasis_equivFun]
  fin_cases i <;> norm_num [speed]

/-- The second basis vector is the dimension of action. -/
@[simp] theorem unitBasis_one : unitBasis R 1 = action R := by
  apply (unitBasis R).equivFun.injective
  ext i
  simp only [Basis.equivFun_self, unitBasis_equivFun]
  fin_cases i <;> norm_num [action]

/-- The third basis vector is the dimension of mass. -/
@[simp] theorem unitBasis_two : unitBasis R 2 = mass R := by
  apply (unitBasis R).equivFun.injective
  ext i
  simp only [Basis.equivFun_self, unitBasis_equivFun]
  fin_cases i <;> simp [mass]

/-- The ordered speed, action, and mass rows have determinant one. -/
theorem det_unitBasis : (Matrix.of (unitBasis R : Fin 3 → Fin 3 → R)).det = 1 := by
  rw [Matrix.det_fin_three]
  norm_num [speed, action, mass]

/-- The unique exponents of speed, action, and mass that give a length dimension. -/
theorem sum_smul_unitBasis_eq_length_iff (u : Fin 3 → ℤ) :
    (∑ i, u i • unitBasis ℤ i) = ![0, 1, 0] ↔ u = ![-1, 1, -1] := by
  have h : (unitBasis ℤ).equivFun ![0, 1, 0] = ![-1, 1, -1] := by
    rw [unitBasis_equivFun]
    decide
  rw [← Basis.equivFun_symm_apply, LinearEquiv.symm_apply_eq, h]

/-- A monomial in the reduced Planck constant `ℏ`, mass `m`, and speed `c` with length
dimension is the reduced Compton wavelength `ℏ / (m * c)`. -/
theorem zpow_eq_comptonWavelength_of_dimension {G : Type*} [DivisionCommMonoid G]
    {ℏ m c : G} {a b d : ℤ}
    (h : d • speed ℤ + a • action ℤ + b • mass ℤ = ![0, 1, 0]) :
    ℏ ^ a * m ^ b * c ^ d = ℏ / (m * c) := by
  have hu := (sum_smul_unitBasis_eq_length_iff ![d, a, b]).mp (by
    simpa [Fin.sum_univ_three] using h)
  have hd : d = -1 := congrFun hu 0
  have ha : a = 1 := congrFun hu 1
  have hb : b = -1 := congrFun hu 2
  simp [hd, ha, hb, div_eq_mul_inv, mul_assoc, mul_comm m⁻¹ c⁻¹]

variable (R)

/-- The mass dimension is the mass coordinate in the speed, action, and mass basis. -/
noncomputable def massDimension : (Fin 3 → R) →ₗ[R] R :=
  (unitBasis R).coord 2

variable {R}

/-- In mass, length, and time coordinates the mass dimension is `a - b - c`. -/
@[simp] theorem massDimension_apply (x : Fin 3 → R) :
    massDimension R x = x 0 - x 1 - x 2 := by
  rw [massDimension, Basis.coord_apply, ← Basis.equivFun_apply, unitBasis_equivFun]
  rfl

/-- The exponent vectors identified with zero by setting `c = ℏ = 1`. -/
def unitRelations (R : Type*) [CommRing R] : Submodule R (Fin 3 → R) :=
  Submodule.span R {speed R, action R}

/-- The relations are generated by the speed and action exponent vectors. -/
theorem unitRelations_eq_span : unitRelations R = Submodule.span R {speed R, action R} := (rfl)

/-- A vector has mass dimension zero exactly when it is in the span of speed and action. -/
theorem ker_massDimension : LinearMap.ker (massDimension R) = unitRelations R := by
  have hspan : unitRelations R = Submodule.span R (unitBasis R '' ({0, 1} : Set (Fin 3))) := by
    simp [unitRelations]
  ext x
  rw [hspan, (unitBasis R).mem_span_image, Finsupp.support_subset_iff, LinearMap.mem_ker,
    massDimension, Basis.coord_apply]
  constructor
  · intro hx i hi
    fin_cases i <;> simp_all
  · exact fun hx ↦ hx 2 (by decide)

/-- An exponent vector represents zero in natural units exactly when its mass dimension is zero. -/
@[simp] theorem mem_unitRelations_iff (x : Fin 3 → R) :
    x ∈ unitRelations R ↔ massDimension R x = 0 := by
  rw [← ker_massDimension, LinearMap.mem_ker]

/-- Every mass dimension is represented by a multiple of the mass vector. -/
theorem massDimension_surjective : Function.Surjective (massDimension R) := by
  intro a
  use a • mass R
  simp [mass]

/-- The quotient by the dimensions of speed and action is identified with the coefficient
ring by the mass dimension. Take `R = ℤ` for integral exponents and `R = ℚ` for rational
exponents. -/
noncomputable def quotientEquiv (R : Type*) [CommRing R] :
    ((Fin 3 → R) ⧸ unitRelations R) ≃ₗ[R] R :=
  (Submodule.quotEquivOfEq _ _ ker_massDimension.symm).trans
    ((massDimension R).quotKerEquivOfSurjective massDimension_surjective)

/-- The quotient equivalence evaluates on a representative by its mass dimension. -/
@[simp] theorem quotientEquiv_mk (x : Fin 3 → R) :
    quotientEquiv R (Submodule.Quotient.mk x) = massDimension R x := by
  simp [quotientEquiv, Submodule.quotEquivOfEq_mk]

/-- The inverse quotient equivalence represents a degree by the corresponding power of mass. -/
@[simp] theorem quotientEquiv_symm_apply (a : R) :
    (quotientEquiv R).symm a = Submodule.Quotient.mk (p := unitRelations R) (a • mass R) := by
  apply (quotientEquiv R).injective
  simp [mass]

/-- Coordinatewise casting from integral to rational physical exponents. -/
def castExponents : (Fin 3 → ℤ) →ₛₗ[Int.castRingHom ℚ] (Fin 3 → ℚ) where
  toFun x i := x i
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp [Pi.smul_apply, smul_eq_mul]

/-- Casting a vector of exponents casts each coordinate. -/
@[simp] theorem castExponents_apply (x : Fin 3 → ℤ) (i : Fin 3) :
    castExponents x i = (x i : ℚ) := (rfl)

/-- The map from the integer unit quotient to the rational unit quotient, induced by casting
mass, length, and time exponents. -/
noncomputable def quotientIntToRat :
    ((Fin 3 → ℤ) ⧸ unitRelations ℤ) →ₛₗ[Int.castRingHom ℚ]
      ((Fin 3 → ℚ) ⧸ unitRelations ℚ) :=
  (unitRelations ℤ).mapQ (unitRelations ℚ) castExponents (by
    intro x hx
    have h : x 0 - x 1 - x 2 = 0 := by simpa using hx
    simp only [Submodule.mem_comap, mem_unitRelations_iff, massDimension_apply, castExponents_apply]
    exact_mod_cast h)

/-- The quotient map casts the components of a representative. -/
@[simp] theorem quotientIntToRat_mk (x : Fin 3 → ℤ) :
    quotientIntToRat (Submodule.Quotient.mk x) = Submodule.Quotient.mk (castExponents x) :=
  Submodule.mapQ_apply _ _ _ _

/-- Under the quotient equivalences the induced map is the usual inclusion of integers
into rationals. -/
@[simp] theorem quotientEquiv_quotientIntToRat (x : (Fin 3 → ℤ) ⧸ unitRelations ℤ) :
    quotientEquiv ℚ (quotientIntToRat x) = (quotientEquiv ℤ x : ℚ) := by
  induction x using Submodule.Quotient.induction_on
  simp

end TauCeti.NaturalUnits
