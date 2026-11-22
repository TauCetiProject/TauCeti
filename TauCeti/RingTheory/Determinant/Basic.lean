/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Multiplicative

/-!
# Determinants as multiplicative polynomial laws

A degree-`d` determinant on an associative `A`-algebra `R` is a multiplicative polynomial
law `R → A`, homogeneous of degree `d` after every commutative scalar extension.
The coefficient semiring need not be a field or reduced, and the source need not be
commutative, finite or flat. In particular, the ground function alone does not determine
a determinant.

This file bundles the two predicates on Mathlib's polynomial-law carrier. It provides
extensionality on the underlying law, the ground monoid homomorphism, restriction along
algebra maps, the unique degree-zero determinant, and the equivalence between degree-one
determinants and algebra maps. The constructions work over commutative semirings; over
commutative rings they give Chenevier's determinants.

## References

* G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, arXiv:0809.0415v2, §1.5, pp. 9–10.
-/

public noncomputable section

open TensorProduct

universe u v

namespace TauCeti

/-- A degree-`d` determinant is a homogeneous multiplicative polynomial law, with both
conditions imposed after every commutative scalar extension. Degree zero is allowed. -/
structure Determinant (A : Type u) [CommSemiring A] (R : Type v) [Semiring R]
    [Algebra A R] (d : ℕ) where
  /-- The full polynomial law, not just its ground function. -/
  toLaw : R →ₚₗ[A] A
  /-- Homogeneity after every commutative scalar extension. -/
  isHomogeneous : toLaw.IsHomogeneousOfDegree d
  /-- Preservation of the unit and products after every commutative scalar extension. -/
  isMultiplicative : toLaw.IsMultiplicative

namespace Determinant

variable {A : Type u} [CommSemiring A] {R : Type v} [Semiring R] [Algebra A R]
  {d : ℕ}

/-- Determinants are equal when their entire polynomial laws are equal. -/
@[ext]
theorem ext {D E : Determinant A R d} (h : D.toLaw = E.toLaw) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Evaluation of a determinant on its source algebra is evaluation of its ground law. -/
instance : CoeFun (Determinant A R d) (fun _ ↦ R → A) := ⟨fun D ↦ D.toLaw.ground⟩

/-- The ground map of a determinant preserves the unit. -/
@[simp]
theorem map_one (D : Determinant A R d) : D 1 = 1 :=
  D.isMultiplicative.ground_one

/-- The ground map of a determinant preserves multiplication. -/
@[simp]
theorem map_mul (D : Determinant A R d) (x y : R) : D (x * y) = D x * D y :=
  D.isMultiplicative.ground_mul x y

/-- The ground multiplicative map of a determinant. -/
def toMonoidHom (D : Determinant A R d) : R →* A where
  toFun := D
  map_one' := D.map_one
  map_mul' := D.map_mul

@[simp]
theorem toMonoidHom_apply (D : Determinant A R d) (x : R) : D.toMonoidHom x = D x :=
  (rfl)

/-- A determinant sends units to units. -/
theorem isUnit_map (D : Determinant A R d) {x : R} (hx : IsUnit x) : IsUnit (D x) :=
  hx.map D.toMonoidHom

/-- Scalar multiplication on the source has weight `d`. -/
@[simp]
theorem map_smul (D : Determinant A R d) (a : A) (x : R) :
    D (a • x) = a ^ d * D x :=
  D.isHomogeneous.ground_smul a x

/-- In positive degree the determinant vanishes at zero. -/
@[simp]
theorem map_zero (D : Determinant A R d) (hd : d ≠ 0) : D 0 = 0 := by
  have h := D.map_smul 0 (0 : R)
  simpa [zero_pow hd] using h

/-- Restriction along an algebra map, on the entire polynomial law. -/
def comap {R' : Type*} [Semiring R'] [Algebra A R'] (D : Determinant A R d)
    (φ : R' →ₐ[A] R) : Determinant A R' d where
  toLaw := D.toLaw.comp φ.toLinearMap.toPolynomialLaw
  isHomogeneous := by
    simpa using D.isHomogeneous.comp φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw
  isMultiplicative := D.isMultiplicative.comp φ.isMultiplicative_toPolynomialLaw

/-- The full polynomial law of a restricted determinant is composition with the linear law. -/
theorem toLaw_comap {R' : Type*} [Semiring R'] [Algebra A R']
    (D : Determinant A R d) (φ : R' →ₐ[A] R) :
    (D.comap φ).toLaw = D.toLaw.comp φ.toLinearMap.toPolynomialLaw :=
  (rfl)

/-- Restriction evaluates by applying the algebra map first. -/
@[simp]
theorem comap_apply {R' : Type*} [Semiring R'] [Algebra A R']
    (D : Determinant A R d) (φ : R' →ₐ[A] R) (x : R') : (D.comap φ) x = D (φ x) := by
  simp [toLaw_comap, PolynomialLaw.ground_apply]

@[simp]
theorem comap_id (D : Determinant A R d) : D.comap (AlgHom.id A R) = D := by
  apply ext
  simp [toLaw_comap, PolynomialLaw.comp_id]

/-- Successive restrictions equal restriction along the composite. -/
theorem comap_comp {R' R'' : Type*} [Semiring R'] [Algebra A R']
    [Semiring R''] [Algebra A R''] (D : Determinant A R d)
    (φ : R' →ₐ[A] R) (ψ : R'' →ₐ[A] R') :
    D.comap (φ.comp ψ) = (D.comap φ).comap ψ := by
  apply ext
  simp [toLaw_comap, PolynomialLaw.comp_assoc]

/-- The degree-zero determinant: its value is one after every scalar extension. -/
def degreeZero (A : Type u) [CommSemiring A] (R : Type v) [Semiring R] [Algebra A R] :
    Determinant A R 0 where
  toLaw :=
    { toFun' _ _ _ _ := 1
      isCompat' φ := by
        funext _
        simp [Algebra.TensorProduct.one_def] }
  isHomogeneous := PolynomialLaw.isHomogeneousOfDegree_iff.mpr fun S _ _ s x ↦ by simp
  isMultiplicative :=
    { toFun'_one _ := rfl
      toFun'_mul _ _ := (one_mul 1).symm }

/-- The constant-one formula for the degree-zero law. -/
@[simp]
theorem degreeZero_toFun' (S : Type u) [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    (degreeZero A R).toLaw.toFun' S x = 1 :=
  (rfl)

/-- The degree-zero law is constant one over coefficient algebras in any universe. -/
@[simp]
theorem degreeZero_toFun (S : Type*) [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    (degreeZero A R).toLaw.toFun S x = 1 := by
  obtain ⟨n, φ, y, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun, degreeZero_toFun']
  simp [Algebra.TensorProduct.one_def]

/-- Every degree-zero determinant is the constant-one law. -/
theorem eq_degreeZero (D : Determinant A R 0) : D = degreeZero A R := by
  apply ext
  ext S _ _ x
  have hx := D.isHomogeneous.toFun'_smul (0 : S) x
  have h1 := D.isHomogeneous.toFun'_smul (0 : S) (1 : S ⊗[A] R)
  simp only [zero_smul, pow_zero, one_smul] at hx h1
  simpa using hx.symm.trans (h1.trans (D.isMultiplicative.toFun'_one S))

instance : Unique (Determinant A R 0) where
  default := degreeZero A R
  uniq := eq_degreeZero

/-- Ground evaluation of the degree-zero determinant is one, including at zero. -/
@[simp]
theorem degreeZero_apply (x : R) : degreeZero A R x = 1 := by
  simp [PolynomialLaw.ground_apply, ← Algebra.TensorProduct.lid_toLinearEquiv]

end Determinant

end TauCeti

/-- An algebra map, regarded as a degree-one determinant. -/
def AlgHom.toDeterminant {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (φ : R →ₐ[A] A) : TauCeti.Determinant A R 1 where
  toLaw := φ.toLinearMap.toPolynomialLaw
  isHomogeneous := φ.toLinearMap.isHomogeneousOfDegree_toPolynomialLaw
  isMultiplicative := φ.isMultiplicative_toPolynomialLaw

@[simp]
theorem AlgHom.toLaw_toDeterminant {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (φ : R →ₐ[A] A) :
    φ.toDeterminant.toLaw = φ.toLinearMap.toPolynomialLaw :=
  (rfl)

namespace TauCeti.Determinant

/-- Degree-one determinants are exactly algebra maps. This repackages
`PolynomialLaw.algHomEquiv` on the bundled determinant carrier. -/
def algHomEquiv (A : Type u) [CommSemiring A] (R : Type v) [Semiring R] [Algebra A R] :
    (R →ₐ[A] A) ≃ Determinant A R 1 where
  toFun := AlgHom.toDeterminant
  invFun D := D.isHomogeneous.toAlgHom D.isMultiplicative
  left_inv := AlgHom.toAlgHom_isHomogeneousOfDegree_toPolynomialLaw
  right_inv D := ext (D.isHomogeneous.toPolynomialLaw_toAlgHom D.isMultiplicative)

@[simp]
theorem algHomEquiv_apply {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (φ : R →ₐ[A] A) : algHomEquiv A R φ = φ.toDeterminant :=
  (rfl)

/-- Recovering the algebra map of a determinant built from `φ` gives back `φ`. -/
@[simp]
theorem algHomEquiv_symm_toDeterminant {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (φ : R →ₐ[A] A) : (algHomEquiv A R).symm φ.toDeterminant = φ := by
  simpa only [algHomEquiv_apply] using (algHomEquiv A R).symm_apply_apply φ

/-- Bundling the algebra map recovered from a degree-one determinant gives back that determinant. -/
@[simp]
theorem toDeterminant_algHomEquiv_symm {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (D : Determinant A R 1) : ((algHomEquiv A R).symm D).toDeterminant = D := by
  simpa only [algHomEquiv_apply] using (algHomEquiv A R).apply_symm_apply D

/-- The algebra map recovered from a degree-one determinant has the same ground values. -/
@[simp]
theorem algHomEquiv_symm_apply {A : Type u} [CommSemiring A] {R : Type v} [Semiring R]
    [Algebra A R] (D : Determinant A R 1) (x : R) : (algHomEquiv A R).symm D x = D x := by
  exact congrFun (D.isHomogeneous.coe_toAlgHom D.isMultiplicative) x

end TauCeti.Determinant
