/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Multiplicative
public import TauCeti.RingTheory.PolynomialLaw.Power

/-!
# Determinants in the sense of Chenevier

For a commutative ring `A` and an associative unital `A`-algebra `R`, not necessarily
commutative, a `d`-dimensional `A`-valued *determinant* on `R` is a polynomial law `R →ₚₗ[A] A`
which is homogeneous of degree `d` and multiplicative after every commutative scalar extension
`S` of `A`. The motivating example is `det ∘ ρ` for a representation `ρ : R →ₐ[A] Mₙ(A)`.
Determinants replace traces of representations over coefficient rings in which `d!` need not be
invertible, such as the nonreduced Hecke algebras acting on cohomology with torsion
coefficients.

A determinant is recorded through its whole polynomial law, not through its values on `R`: over a
finite ring `A` two different laws can have the same ground map. Its ground map `D : R → A` is a
monoid homomorphism, homogeneous of degree `d` for the scalar action, and hence sends units to
units. The structure is stated for commutative semirings `A` and semirings `R`, where none of
this needs subtraction.

In the degenerate dimensions the definition is pinned down completely: the only determinant of
dimension `0` is the constant law `1`, and determinants of dimension `1` are exactly the
`A`-algebra maps `R →ₐ[A] A`.

## Main declarations

* `TauCeti.Determinant A R d`: the `d`-dimensional `A`-valued determinants on `R`.
* `TauCeti.Determinant.map_one`, `TauCeti.Determinant.map_mul`, `TauCeti.Determinant.map_smul`:
  the ground map preserves `1` and products and is homogeneous of degree `d`.
* `TauCeti.Determinant.toMonoidHom`: the ground map as a monoid homomorphism `R →* A`.
* `TauCeti.Determinant.isUnit_apply`: a determinant sends units to units.
* `TauCeti.Determinant.toLaw_toFun_eq_one`: a determinant of dimension `0` is the constant
  law `1`; `Determinant A R 0` has exactly one element.
* `TauCeti.Determinant.algHomEquiv`: determinants of dimension `1` are the `A`-algebra maps
  `R →ₐ[A] A`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.5](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

namespace TauCeti

/-- A `d`-dimensional `A`-valued determinant on an `A`-algebra `R`, in the sense of Chenevier: a
polynomial law `R →ₚₗ[A] A` which is homogeneous of degree `d` and multiplicative after every
commutative scalar extension of `A`. -/
structure Determinant (A : Type u) [CommSemiring A] (R : Type*) [Semiring R] [Algebra A R]
    (d : ℕ) where
  /-- The underlying polynomial law. -/
  toLaw : R →ₚₗ[A] A
  /-- The law is homogeneous of degree `d` after every scalar extension. -/
  isHomogeneousOfDegree : toLaw.IsHomogeneousOfDegree d
  /-- The law preserves `1` and products after every scalar extension. -/
  isMultiplicative : toLaw.IsMultiplicative

namespace Determinant

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d : ℕ}

theorem toLaw_injective : Function.Injective (toLaw : Determinant A R d → R →ₚₗ[A] A) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ rfl
  rfl

/-- Two determinants are equal when their polynomial laws are. -/
@[ext]
theorem ext {D E : Determinant A R d} (h : D.toLaw = E.toLaw) : D = E :=
  toLaw_injective h

/-- The value `D x ∈ A` of a determinant at an element `x ∈ R` is the ground value of its law. -/
instance : CoeFun (Determinant A R d) fun _ ↦ R → A where
  coe D := D.toLaw.ground

variable (D : Determinant A R d)

@[simp]
protected theorem map_one : D 1 = 1 :=
  D.isMultiplicative.ground_one

@[simp]
protected theorem map_mul (x y : R) : D (x * y) = D x * D y :=
  D.isMultiplicative.ground_mul x y

/-- A determinant of dimension `d` is homogeneous of degree `d`: `D (a • x) = a ^ d * D x`. -/
@[simp]
protected theorem map_smul (a : A) (x : R) : D (a • x) = a ^ d * D x :=
  D.isHomogeneousOfDegree.ground_smul a x

/-- A determinant sends `a • 1` to `a ^ d`. -/
protected theorem map_algebraMap (a : A) : D (algebraMap A R a) = a ^ d := by
  rw [Algebra.algebraMap_eq_smul_one, D.map_smul, D.map_one, mul_one]

/-- The ground map of a determinant, as a monoid homomorphism `R →* A`. -/
def toMonoidHom : R →* A where
  toFun := D
  map_one' := D.map_one
  map_mul' := D.map_mul

@[simp]
theorem coe_toMonoidHom : ⇑D.toMonoidHom = D :=
  (rfl)

/-- A determinant sends units to units. -/
theorem isUnit_apply {x : R} (hx : IsUnit x) : IsUnit (D x) :=
  hx.map D.toMonoidHom

/-! ### Dimension zero -/

/-- A determinant of dimension `0` is the constant law `1`, after scalar extension to every
commutative `A`-algebra. -/
@[simp]
theorem toLaw_toFun_eq_one (D : Determinant A R 0) (S : Type*) [CommSemiring S] [Algebra A S]
    (x : S ⊗[A] R) : D.toLaw.toFun S x = 1 := by
  -- homogeneity of degree `0` gives `D (0 • y) = D y`, so `D` is constant
  have h (y : S ⊗[A] R) : D.toLaw.toFun S y = D.toLaw.toFun S 0 := by
    simpa using (D.isHomogeneousOfDegree.toFun_smul (0 : S) y).symm
  rw [h, ← h 1, D.isMultiplicative.toFun_one]

/-- The constant law `1`, a determinant of dimension `0`. Its polynomial law is the power law
`y ↦ y ^ 0` precomposed with the zero law. -/
instance : Inhabited (Determinant A R 0) where
  default :=
    { toLaw := (PolynomialLaw.power A A 0).comp 0
      isHomogeneousOfDegree :=
        (PolynomialLaw.isHomogeneousOfDegree_power 0).comp
          (PolynomialLaw.isHomogeneousOfDegree_zero 0)
      isMultiplicative :=
        { toFun'_one S _ _ := by simp
          toFun'_mul x y := by simp } }

/-- The determinants of dimension `0` are all equal to the constant law `1`. -/
instance : Unique (Determinant A R 0) where
  uniq D := ext <| by
    ext S _ _ x
    rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun, toLaw_toFun_eq_one,
      toLaw_toFun_eq_one]

/-! ### Dimension one -/

variable (A R) in
/-- The `A`-algebra maps `R →ₐ[A] A` are identified with the determinants of dimension `1`, by
`φ ↦ φ.toLinearMap.toPolynomialLaw`: a law homogeneous of degree `1` and multiplicative is the
polynomial law of its ground map. -/
def algHomEquiv : (R →ₐ[A] A) ≃ Determinant A R 1 where
  toFun φ :=
    { toLaw := PolynomialLaw.algHomEquiv A R A φ
      isHomogeneousOfDegree := (PolynomialLaw.algHomEquiv A R A φ).property.1
      isMultiplicative := (PolynomialLaw.algHomEquiv A R A φ).property.2 }
  invFun D := (PolynomialLaw.algHomEquiv A R A).symm
    ⟨D.toLaw, D.isHomogeneousOfDegree, D.isMultiplicative⟩
  left_inv φ := by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
  right_inv D := ext <| by
    simp only [Equiv.apply_symm_apply]

/-- The determinant of dimension `1` attached to an algebra map `φ` has the polynomial law of
`φ`. -/
@[simp]
theorem toLaw_algHomEquiv (φ : R →ₐ[A] A) :
    (algHomEquiv A R φ).toLaw = φ.toLinearMap.toPolynomialLaw :=
  PolynomialLaw.coe_algHomEquiv_apply φ

/-- The determinant of dimension `1` attached to an algebra map `φ` takes the values of `φ`. -/
theorem coe_algHomEquiv (φ : R →ₐ[A] A) : ⇑(algHomEquiv A R φ) = ⇑φ := by
  simp

/-- The algebra map attached to a determinant of dimension `1` is its ground map. -/
@[simp]
theorem coe_algHomEquiv_symm (D : Determinant A R 1) : ⇑((algHomEquiv A R).symm D) = ⇑D := by
  simp [algHomEquiv]

end Determinant

end TauCeti
