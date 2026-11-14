/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BinaryForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The differentiated representation of `SL₂` on binary forms

The contragredient action `(g • f)(x, y) = f(d x - b y, a y - c x)` of `SL₂` on polynomial
functions in `x = X 0` and `y = X 1` differentiates at the identity to first-order differential
operators: a tangent vector `x` with trace-zero tangent matrix `A` acts as the derivation sending
`X 0` to `-A₀₀ X 0 - A₀₁ X 1` and `X 1` to `-A₁₀ X 0 + A₀₀ X 1`.

On the homogeneous component `TauCeti.SpecialLinear.binaryForms R d` of degree `d`, the standard
basis `(E₀₁, E₁₀, H)` of `sl (Fin 2) R` acts on the signed monomial basis
`wᵢ = (-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` (`0 ≤ i ≤ d`) by the integral ladder

`E₀₁ · wᵢ = i · wᵢ₋₁`, `E₁₀ · wᵢ = (d - i) · wᵢ₊₁`, `H · wᵢ = (d - 2i) · wᵢ`,

matching the coordinate basis of the standard `sl₂`-module `TauCeti.Sl2Std R d`. Over every
commutative ring `R` — without field, characteristic, or factorial-invertibility assumptions —
`TauCeti.SpecialLinear.binaryFormsEquivSl2Std` therefore identifies `binaryForms R d` with
`Sl2Std R d` linearly and equivariantly for the differentiated `sl (Fin 2) R`-action, carrying the
highest-weight monomial `yᵈ` to `Sl2Std.basis R d 0`. Over a field of characteristic zero, this
exhibits `binaryForms k d` as an `O(SL₂)`-comodule realization of the unique `(d + 1)`-dimensional
irreducible representation of `sl (Fin 2) k`.

## Main declarations

* `TauCeti.SpecialLinear.differential_polynomialComodule_mul` and
  `TauCeti.SpecialLinear.differential_polynomialComodule_pow`: the Leibniz and power rules for the
  differentiated `SLₙ`-action on polynomial functions.
* `TauCeti.SpecialLinear.differential_polynomialComodule_X_zero` and
  `TauCeti.SpecialLinear.differential_polynomialComodule_X_one`: the infinitesimal `SL₂`-action on
  the two coordinates.
* `TauCeti.SpecialLinear.binaryFormsSignedBasis`: the signed monomial basis
  `(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` of `binaryForms R d`.
* `TauCeti.SpecialLinear.binaryFormsEquivSl2Std`: the `R`-linear equivalence
  `binaryForms R d ≃ₗ[R] Sl2Std R d` sending `(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` to
  `Sl2Std.basis R d i`.
* `TauCeti.SpecialLinear.binaryFormsEquivSl2Std_differential` and
  `TauCeti.SpecialLinear.differential_binaryFormsEquivSl2Std_symm`: equivariance of
  `binaryFormsEquivSl2Std` with respect to `Comodule.differential` and `tangentLieEquivSl 2`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.7 and II.2.16.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §7.2.
-/

public section

open LieAlgebra Module MvPolynomial
open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] GeneralLinear.standardComodule standardComodule

section PolynomialDifferential

variable {R : Type u} [CommRing R]

/-- **Leibniz rule on polynomial functions.** Every tangent vector of `SLₙ` acts on the polynomial
comodule `R[X₀, …, Xₙ₋₁]` as a derivation. -/
theorem differential_polynomialComodule_mul {n : ℕ}
    (x : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) R))
    (p q : MvPolynomial (Fin n) R) :
    letI := polynomialComodule R n
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x (p * q) =
      Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x p * q +
        p * Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x q := by
  let _ := polynomialComodule R n
  have hcoact (f : MvPolynomial (Fin n) R) :
      Comodule.coact (R := R) (C := coordinateHopfAlgebra R n) f =
        Comodule.polynomialCoact (coordinateHopfAlgebra R n) (Pi.basisFun R (Fin n)) f := by
    rw [polynomialComodule_coact, AlgHom.toLinearMap_apply]
  rw [Comodule.differential_apply, Comodule.differential_apply, Comodule.differential_apply,
    hcoact (p * q), map_mul, ← hcoact p, ← hcoact q,
    LinearMap.tensorComponent_mul (Bialgebra.CounitAlgebra.algEquivSelf_comp_apply_mul x)]
  simp only [← Comodule.coactComponent_apply, Comodule.coactComponent_counit, LinearMap.id_apply]

/-- Bundling the differentiated `SLₙ`-action on `MvPolynomial (Fin n) R` as an `R`-derivation. -/
private noncomputable def polynomialComoduleDerivation {n : ℕ}
    (x : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) R)) :
    Derivation R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
  letI := polynomialComodule R n
  Derivation.mk' (Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x) fun p q ↦ by
    rw [differential_polynomialComodule_mul, smul_eq_mul, smul_eq_mul]
    ring

/-- **Power rule on polynomial functions.** A tangent vector of `SLₙ` differentiates `p ^ m` to
`m • p ^ (m - 1) * (x • p)`. -/
theorem differential_polynomialComodule_pow {n : ℕ}
    (x : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) R))
    (p : MvPolynomial (Fin n) R) (m : ℕ) :
    letI := polynomialComodule R n
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x (p ^ m) =
      m • p ^ (m - 1) *
        Comodule.differential (R := R) (H := coordinateHopfAlgebra R n) x p := by
  let _ := polynomialComodule R n
  simpa only [polynomialComoduleDerivation, Derivation.coe_mk', smul_eq_mul, smul_mul_assoc] using
    (polynomialComoduleDerivation x).leibniz_pow p m

private theorem algEquivSelf_apply_coefficientMatrix_two
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) (i j : Fin 2) :
    Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R 2) R
        (x (Comodule.coefficientMatrix (C := coordinateHopfAlgebra R 2)
          (Pi.basisFun R (Fin 2)) i j)) =
      (tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) i j := by
  rw [coefficientMatrix_basisFun, Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    tangentMatrix_apply]

private theorem tangentMatrix_two_one_one
    (A : SpecialLinear.sl (Fin 2) R) :
    (A : Matrix (Fin 2) (Fin 2) R) 1 1 = -(A : Matrix (Fin 2) (Fin 2) R) 0 0 := by
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) R) = 0 := A.property
  rw [Matrix.trace_fin_two] at htr
  exact eq_neg_of_add_eq_zero_right htr

/-- **Infinitesimal action of `SL₂` on `X 0`.** A tangent vector `x` with trace-zero matrix `A`
sends `X 0` to `-A₀₀ X 0 - A₀₁ X 1`. -/
theorem differential_polynomialComodule_X_zero
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x
        (X 0 : MvPolynomial (Fin 2) R) =
      -((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 0) • X 0 -
        ((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 1) • X 1 := by
  let _ := polynomialComodule R 2
  rw [Comodule.differential_apply, polynomialComodule_coact, AlgHom.toLinearMap_apply,
    Comodule.polynomialCoact_X, Fin.sum_univ_two]
  simp only [← Comodule.coefficientMatrix_apply, map_add, LinearMap.tensorComponent_tmul,
    LinearMap.comp_apply, Derivation.coeFn_coe, AlgEquiv.toLinearMap_apply]
  rw [antipode_coefficientMatrix_zero_zero, antipode_coefficientMatrix_zero_one, map_neg, map_neg,
    algEquivSelf_apply_coefficientMatrix_two, algEquivSelf_apply_coefficientMatrix_two,
    tangentMatrix_two_one_one (tangentMatrix 2 x), neg_smul, neg_smul, sub_eq_add_neg]

/-- **Infinitesimal action of `SL₂` on `X 1`.** A tangent vector `x` with trace-zero matrix `A`
sends `X 1` to `-A₁₀ X 0 + A₀₀ X 1`. -/
theorem differential_polynomialComodule_X_one
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x
        (X 1 : MvPolynomial (Fin 2) R) =
      -((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 1 0) • X 0 +
        ((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 0) • X 1 := by
  let _ := polynomialComodule R 2
  rw [Comodule.differential_apply, polynomialComodule_coact, AlgHom.toLinearMap_apply,
    Comodule.polynomialCoact_X, Fin.sum_univ_two]
  simp only [← Comodule.coefficientMatrix_apply, map_add, LinearMap.tensorComponent_tmul,
    LinearMap.comp_apply, Derivation.coeFn_coe, AlgEquiv.toLinearMap_apply]
  rw [antipode_coefficientMatrix_one_zero, antipode_coefficientMatrix_one_one, map_neg, map_neg,
    algEquivSelf_apply_coefficientMatrix_two, algEquivSelf_apply_coefficientMatrix_two, neg_smul]

private theorem differential_slFinTwoBasis_zero_monomial (i j : ℕ) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 0))
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) =
      -((i : R) • (X 0 ^ (i - 1) * X 1 ^ (j + 1))) := by
  let _ := polynomialComodule R 2
  have hmat : tangentMatrix (R := R) (B := R) 2
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 0)) = slFinTwoBasis R 0 := by
    rw [← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [differential_polynomialComodule_mul, differential_polynomialComodule_pow,
    differential_polynomialComodule_pow, differential_polynomialComodule_X_zero,
    differential_polynomialComodule_X_one, hmat, slFinTwoBasis_zero]
  simp [SpecialLinear.val_single, smul_eq_C_mul, pow_succ]
  ring

private theorem differential_slFinTwoBasis_one_monomial (i j : ℕ) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) =
      -((j : R) • (X 0 ^ (i + 1) * X 1 ^ (j - 1))) := by
  let _ := polynomialComodule R 2
  have hmat : tangentMatrix (R := R) (B := R) 2
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1)) = slFinTwoBasis R 1 := by
    rw [← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [differential_polynomialComodule_mul, differential_polynomialComodule_pow,
    differential_polynomialComodule_pow, differential_polynomialComodule_X_zero,
    differential_polynomialComodule_X_one, hmat, slFinTwoBasis_one]
  simp [SpecialLinear.val_single, smul_eq_C_mul, pow_succ]
  ring

private theorem differential_slFinTwoBasis_two_monomial (i j : ℕ) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 2))
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) =
      ((j : R) - (i : R)) • (X 0 ^ i * X 1 ^ j) := by
  let _ := polynomialComodule R 2
  have hmat : tangentMatrix (R := R) (B := R) 2
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 2)) = slFinTwoBasis R 2 := by
    rw [← tangentLieEquivSl_apply, LieEquiv.apply_symm_apply]
  rw [differential_polynomialComodule_mul, differential_polynomialComodule_pow,
    differential_polynomialComodule_pow, differential_polynomialComodule_X_zero,
    differential_polynomialComodule_X_one, hmat, slFinTwoBasis_two]
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [SpecialLinear.val_singleSubSingle, smul_eq_C_mul, pow_succ] <;> ring

end PolynomialDifferential

/-! ### The signed monomial basis and equivalence with `Sl2Std` -/

section BinaryFormsEquiv

variable {R : Type u} [CommRing R]

attribute [local instance] polynomialComodule

/-- The monomial `yᵈ` is a binary form of degree `d`. -/
theorem X_one_pow_mem_binaryForms {d : ℕ} :
    (X 1 ^ d : MvPolynomial (Fin 2) R) ∈ binaryForms R d :=
  mem_binaryForms.mpr (isHomogeneous_X_pow 1 d)

/-- The underlying submodule of `binaryForms R d` is the degree-`d` homogeneous submodule. -/
theorem binaryForms_toSubmodule (R : Type u) [CommRing R] (d : ℕ) :
    (binaryForms R d).toSubmodule = homogeneousSubmodule (Fin 2) R d :=
  SetLike.ext fun p ↦ mem_binaryForms.trans (mem_homogeneousSubmodule d p).symm

/-- Linear equivalence between `homogeneousSubmodule (Fin 2) R d` and `binaryForms R d`,
preserving the ambient polynomial. -/
private def homogeneousSubmoduleEquivBinaryForms (R : Type u) [CommRing R] (d : ℕ) :
    homogeneousSubmodule (Fin 2) R d ≃ₗ[R] binaryForms R d where
  toFun p := ⟨p.1, mem_binaryForms.mpr ((mem_homogeneousSubmodule d p.1).mp p.2)⟩
  invFun f := ⟨f.1, (mem_homogeneousSubmodule d f.1).mpr (mem_binaryForms.mp f.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The signed monomial basis `wᵢ = (-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` of `binaryForms R d`, over any
commutative ring. -/
noncomputable def binaryFormsSignedBasis (R : Type u) [CommRing R] (d : ℕ) :
    Basis (Fin (d + 1)) R (binaryForms R d) :=
  (((homogeneousMonomialBasis (σ := Fin 2) (R := R) d).reindex
    (finsuppDegreeFinTwoEquiv d)).map
      (homogeneousSubmoduleEquivBinaryForms R d)).unitsSMul
    fun i ↦ (-1 : Rˣ) ^ (i : ℕ)

/-- The `i`-th vector of `binaryFormsSignedBasis R d` is `(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)`. -/
@[simp]
theorem coe_binaryFormsSignedBasis_apply (d : ℕ) (i : Fin (d + 1)) :
    ((binaryFormsSignedBasis R d i : binaryForms R d) : MvPolynomial (Fin 2) R) =
      (-1 : R) ^ (i : ℕ) • (X 0 ^ (i : ℕ) * X 1 ^ (d - i)) := by
  rw [binaryFormsSignedBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Module.Basis.map_apply, Module.Basis.reindex_apply]
  simp only [homogeneousSubmoduleEquivBinaryForms, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, SetLike.val_smul, coe_homogeneousMonomialBasis,
    coe_finsuppDegreeFinTwoEquiv_symm, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- At `i = 0`, the signed monomial basis vector is the highest-weight monomial `yᵈ`. -/
@[simp]
theorem binaryFormsSignedBasis_zero (d : ℕ) :
    binaryFormsSignedBasis R d 0 = ⟨X 1 ^ d, X_one_pow_mem_binaryForms⟩ := by
  apply Subtype.ext
  rw [coe_binaryFormsSignedBasis_apply]
  simp

/-- **The canonical `R`-linear equivalence `binaryForms R d ≃ₗ[R] Sl2Std R d`** over any
commutative ring, sending `(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` to `Sl2Std.basis R d i`. -/
noncomputable def binaryFormsEquivSl2Std (R : Type u) [CommRing R] (d : ℕ) :
    binaryForms R d ≃ₗ[R] Sl2Std R d :=
  (binaryFormsSignedBasis R d).equiv (Sl2Std.basis R d) (Equiv.refl (Fin (d + 1)))

@[simp]
theorem binaryFormsEquivSl2Std_signedBasis (d : ℕ) (i : Fin (d + 1)) :
    binaryFormsEquivSl2Std R d (binaryFormsSignedBasis R d i) = Sl2Std.basis R d i := by
  simp [binaryFormsEquivSl2Std]

@[simp]
theorem binaryFormsEquivSl2Std_symm_basis (d : ℕ) (i : Fin (d + 1)) :
    (binaryFormsEquivSl2Std R d).symm (Sl2Std.basis R d i) = binaryFormsSignedBasis R d i := by
  simp [binaryFormsEquivSl2Std]

/-- `binaryFormsEquivSl2Std` sends the highest-weight monomial `yᵈ` to `Sl2Std.basis R d 0`. -/
@[simp]
theorem binaryFormsEquivSl2Std_X_one_pow (d : ℕ) :
    binaryFormsEquivSl2Std R d ⟨X 1 ^ d, X_one_pow_mem_binaryForms⟩ = Sl2Std.basis R d 0 := by
  rw [← binaryFormsSignedBasis_zero, binaryFormsEquivSl2Std_signedBasis]

private theorem subtype_differential_binaryForms {d : ℕ}
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R))
    (f : binaryForms R d) :
    ((Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        (M := binaryForms R d) x f : binaryForms R d) : MvPolynomial (Fin 2) R) =
      Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        (M := MvPolynomial (Fin 2) R) x (f : MvPolynomial (Fin 2) R) := by
  simpa only [Subcomodule.subtype_apply] using
    (binaryForms R d).subtype.map_differential x f

private theorem differential_signedBasis_zero (d : ℕ) (i : Fin (d + 1)) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 0))
        (binaryFormsSignedBasis R d i) =
      ((i : ℕ) : R) • binaryFormsSignedBasis R d ⟨(i : ℕ) - 1, by omega⟩ := by
  apply Subtype.ext
  rw [subtype_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_slFinTwoBasis_zero_monomial, SetLike.val_smul,
    coe_binaryFormsSignedBasis_apply]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · simp [hi]
  · dsimp only
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    have hsub : d - (k + 1) + 1 = d - k := by omega
    have hsub2 : k.succ - 1 = k := Nat.succ_sub_one k
    rw [hk, hsub2, hsub]
    simp only [pow_succ, mul_neg, mul_one, smul_neg, smul_smul]
    rw [← neg_smul]
    congr 1
    ring

private theorem differential_signedBasis_one_lt (d : ℕ) (i : Fin (d + 1)) (hi : (i : ℕ) < d) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
        (binaryFormsSignedBasis R d i) =
      ((d : R) - (i : ℕ)) • binaryFormsSignedBasis R d ⟨(i : ℕ) + 1, by omega⟩ := by
  apply Subtype.ext
  rw [subtype_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_slFinTwoBasis_one_monomial, SetLike.val_smul,
    coe_binaryFormsSignedBasis_apply]
  have hsub : d - (i : ℕ) - 1 = d - ((i : ℕ) + 1) := by omega
  have hcast : ((d - (i : ℕ) : ℕ) : R) = (d : R) - (i : ℕ) := Nat.cast_sub hi.le
  simp only [hsub, hcast, pow_succ, mul_neg, mul_one, smul_neg, neg_smul, smul_smul]
  rw [mul_comm ((-1 : R) ^ (i : ℕ))]

private theorem differential_signedBasis_one_last (d : ℕ) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
        (binaryFormsSignedBasis R d (Fin.last d)) = 0 := by
  apply Subtype.ext
  rw [subtype_differential_binaryForms, coe_binaryFormsSignedBasis_apply, Fin.val_last,
    Nat.sub_self, map_smul, differential_slFinTwoBasis_one_monomial]
  simp

private theorem differential_signedBasis_two (d : ℕ) (i : Fin (d + 1)) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 2))
        (binaryFormsSignedBasis R d i) =
      ((d : R) - 2 * (i : ℕ)) • binaryFormsSignedBasis R d i := by
  apply Subtype.ext
  rw [subtype_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_slFinTwoBasis_two_monomial, SetLike.val_smul,
    coe_binaryFormsSignedBasis_apply, smul_smul, smul_smul, Nat.cast_sub (Nat.lt_succ_iff.mp i.2)]
  congr 1
  ring

private theorem binaryFormsEquivSl2Std_differential_basis (d : ℕ) (k : Fin 3) (i : Fin (d + 1)) :
    binaryFormsEquivSl2Std R d
        (Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
          ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R k))
          (binaryFormsSignedBasis R d i)) =
      ⁅slFinTwoBasis R k, Sl2Std.basis R d i⁆ := by
  match k with
  | 0 =>
    rw [differential_signedBasis_zero, (binaryFormsEquivSl2Std R d).map_smul,
      binaryFormsEquivSl2Std_signedBasis, Sl2Std.lie_slFinTwoBasis_zero, Sl2Std.raise_basis]
  | 1 =>
    rw [Sl2Std.lie_slFinTwoBasis_one]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.2) with hi | hi
    · rw [differential_signedBasis_one_lt d i hi, (binaryFormsEquivSl2Std R d).map_smul,
        binaryFormsEquivSl2Std_signedBasis, Sl2Std.lower_basis i hi]
    · have hlast : i = Fin.last d := Fin.ext hi
      rw [hlast, differential_signedBasis_one_last, (binaryFormsEquivSl2Std R d).map_zero,
        Sl2Std.lower_basis_last]
  | 2 =>
    rw [differential_signedBasis_two, (binaryFormsEquivSl2Std R d).map_smul,
      binaryFormsEquivSl2Std_signedBasis, Sl2Std.lie_slFinTwoBasis_two, Sl2Std.diag_basis]

/-- **Equivariance of `binaryFormsEquivSl2Std`.** Over every commutative ring `R`,
`binaryFormsEquivSl2Std R d` intertwines the differentiated representation of `O(SL₂)` on
`binaryForms R d` with the standard `sl (Fin 2) R`-action on `Sl2Std R d`. -/
theorem binaryFormsEquivSl2Std_differential (d : ℕ)
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R))
    (f : binaryForms R d) :
    binaryFormsEquivSl2Std R d
        (Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x f) =
      ⁅tangentLieEquivSl (R := R) (B := R) 2 x, binaryFormsEquivSl2Std R d f⁆ := by
  set A := tangentLieEquivSl (R := R) (B := R) 2 x
  have hx : x = (tangentLieEquivSl (R := R) (B := R) 2).symm A :=
    ((tangentLieEquivSl (R := R) (B := R) 2).symm_apply_apply x).symm
  conv_lhs => rw [hx]
  -- Both sides are `R`-bilinear in `A ∈ sl (Fin 2) R` and `f ∈ binaryForms R d`, so check on bases.
  let lhs : SpecialLinear.sl (Fin 2) R →ₗ[R] binaryForms R d →ₗ[R] Sl2Std R d :=
    { toFun := fun B ↦ (binaryFormsEquivSl2Std R d : binaryForms R d →ₗ[R] Sl2Std R d).comp
        (Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
          ((tangentLieEquivSl (R := R) (B := R) 2).symm.toLinearEquiv B))
      map_add' := fun B₁ B₂ ↦ by
        ext g
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' := fun r B ↦ by
        ext g
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        rw [LinearEquiv.map_smul, map_smul, LinearMap.smul_apply, LinearMap.map_smul] }
  let rhs : SpecialLinear.sl (Fin 2) R →ₗ[R] binaryForms R d →ₗ[R] Sl2Std R d :=
    { toFun := fun B ↦ (LieModule.toEnd R (SpecialLinear.sl (Fin 2) R) (Sl2Std R d) B).comp
        (binaryFormsEquivSl2Std R d : binaryForms R d →ₗ[R] Sl2Std R d)
      map_add' := fun B₁ B₂ ↦ by
        ext g
        simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
      map_smul' := fun r B ↦ by
        ext g
        simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  suffices lhs = rhs from LinearMap.congr_fun (LinearMap.congr_fun this A) f
  refine (slFinTwoBasis R).ext fun k ↦ (binaryFormsSignedBasis R d).ext fun i ↦ ?_
  simp only [lhs, rhs, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, LieModule.toEnd_apply_apply]
  rw [binaryFormsEquivSl2Std_signedBasis]
  exact binaryFormsEquivSl2Std_differential_basis d k i

/-- Inverse form of `binaryFormsEquivSl2Std_differential`: pulling a vector of `Sl2Std R d` back
to `binaryForms R d` intertwines `⁅A, ·⁆` with `Comodule.differential` at
`(tangentLieEquivSl 2).symm A`. -/
theorem differential_binaryFormsEquivSl2Std_symm (d : ℕ)
    (A : SpecialLinear.sl (Fin 2) R) (v : Sl2Std R d) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm A)
        ((binaryFormsEquivSl2Std R d).symm v) =
      (binaryFormsEquivSl2Std R d).symm ⁅A, v⁆ := by
  apply (binaryFormsEquivSl2Std R d).injective
  rw [binaryFormsEquivSl2Std_differential, LieEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end BinaryFormsEquiv

end TauCeti.SpecialLinear
