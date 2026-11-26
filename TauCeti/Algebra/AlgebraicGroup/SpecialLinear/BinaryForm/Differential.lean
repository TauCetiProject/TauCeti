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
import TauCeti.Algebra.AlgebraicGroup.Representation.ComoduleAlgebra

/-!
# The differentiated representation of `SL₂` on binary forms

The homogeneous binary forms `TauCeti.SpecialLinear.binaryForms R d` realize `Sl2Std R d = V(d)` as
an explicit rational `SL₂`-representation, supplying the building blocks used by
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Integration` to integrate finite-dimensional
`sl₂`-modules to `O(SL₂)`-comodules. Differentiating `X 0` and `X 1`
(`differential_polynomialComodule_X_zero`, `differential_polynomialComodule_X_one`), the signed
monomial basis `binaryFormsSignedBasis` gives `binaryFormsEquivSl2Std : binaryForms R d ≃ₗ[R]
Sl2Std R d` over any commutative ring `R`, intertwining `Comodule.differential` with `sl (Fin 2) R`
(`binaryFormsEquivSl2Std_differential`); `polynomialComodule R 2` is supplied locally via `letI`.

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

private theorem coord_differential_standard_two (x : Derivation R (coordinateHopfAlgebra R 2)
    (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) (i j : Fin 2) :
    (Pi.basisFun R (Fin 2)).coord i (Comodule.differential (R := R)
      (H := coordinateHopfAlgebra R 2) x (Pi.basisFun R (Fin 2) j)) =
      (tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) i j := by
  rw [← Derivation.apply_matrixCoefficient, ← Comodule.coefficientMatrix_apply,
    coefficientMatrix_basisFun, Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    tangentMatrix_apply]

/-- **Infinitesimal action of `SL₂` on `X 0`**: `x` with matrix `A` sends `X 0` to
`-A₀₀ X 0 - A₀₁ X 1`. -/
theorem differential_polynomialComodule_X_zero (x : Derivation R (coordinateHopfAlgebra R 2)
    (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x
        (X 0 : MvPolynomial (Fin 2) R) =
      -((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 0) • X 0 -
        ((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 1) • X 1 := by
  let _ := polynomialComodule R 2
  rw [ComoduleAlgebra.differential_polynomial_X (Pi.basisFun R (Fin 2)) x 0, Fin.sum_univ_two,
    coord_differential_standard_two, coord_differential_standard_two, neg_add, neg_smul,
    sub_eq_add_neg]

/-- **Infinitesimal action of `SL₂` on `X 1`**: `x` with matrix `A` sends `X 1` to
`-A₁₀ X 0 + A₀₀ X 1`. -/
theorem differential_polynomialComodule_X_one (x : Derivation R (coordinateHopfAlgebra R 2)
    (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) :
    letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x
        (X 1 : MvPolynomial (Fin 2) R) =
      -((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 1 0) • X 0 +
        ((tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 0) • X 1 := by
  let _ := polynomialComodule R 2
  have htr : Matrix.trace (tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) = 0 :=
    (tangentMatrix 2 x).property
  rw [Matrix.trace_fin_two] at htr
  rw [ComoduleAlgebra.differential_polynomial_X (Pi.basisFun R (Fin 2)) x 1, Fin.sum_univ_two,
    coord_differential_standard_two, coord_differential_standard_two,
    eq_neg_of_add_eq_zero_right htr, neg_add, neg_smul, neg_smul, neg_neg]

end PolynomialDifferential

section BinaryFormsEquiv

variable {R : Type u} [CommRing R]

attribute [local instance] polynomialComodule

/-- The signed monomial basis `wᵢ = (-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` of `binaryForms R d`. -/
noncomputable def binaryFormsSignedBasis (R : Type u) [CommRing R] (d : ℕ) :
    Basis (Fin (d + 1)) R (binaryForms R d) :=
  ((((homogeneousMonomialBasis (σ := Fin 2) (R := R) d).reindex (finsuppDegreeFinTwoEquiv d)).map
    (LinearEquiv.ofEq _ _ (binaryForms_toSubmodule R d).symm)).map
    (binaryForms R d).toSubmoduleEquiv.symm).unitsSMul fun i ↦ (-1 : Rˣ) ^ (i : ℕ)

/-- The `i`-th vector of `binaryFormsSignedBasis R d` is `(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)`. -/
@[simp] theorem coe_binaryFormsSignedBasis_apply (d : ℕ) (i : Fin (d + 1)) :
    ((binaryFormsSignedBasis R d i : binaryForms R d) : MvPolynomial (Fin 2) R) =
      (-1 : R) ^ (i : ℕ) • (X 0 ^ (i : ℕ) * X 1 ^ (d - i)) := by
  simp only [binaryFormsSignedBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Module.Basis.map_apply, Module.Basis.reindex_apply, SetLike.val_smul,
    Subcomodule.coe_toSubmoduleEquiv_symm_apply, LinearEquiv.coe_ofEq_apply,
    coe_homogeneousMonomialBasis, coe_finsuppDegreeFinTwoEquiv_symm, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]

/-- At `i = 0`, the signed monomial basis vector is the highest-weight monomial `yᵈ`. -/
@[simp] theorem binaryFormsSignedBasis_zero (d : ℕ) :
    binaryFormsSignedBasis R d 0 = ⟨X 1 ^ d, X_one_pow_mem_binaryForms⟩ :=
  Subtype.ext <| by rw [coe_binaryFormsSignedBasis_apply]; simp

/-- **The canonical `R`-linear equivalence `binaryForms R d ≃ₗ[R] Sl2Std R d`** sending
`(-1)ⁱ X 0 ^ i * X 1 ^ (d - i)` to `Sl2Std.basis R d i`. -/
noncomputable def binaryFormsEquivSl2Std (R : Type u) [CommRing R] (d : ℕ) :
    binaryForms R d ≃ₗ[R] Sl2Std R d :=
  (binaryFormsSignedBasis R d).equiv (Sl2Std.basis R d) (Equiv.refl (Fin (d + 1)))

@[simp] theorem binaryFormsEquivSl2Std_signedBasis (d : ℕ) (i : Fin (d + 1)) :
    binaryFormsEquivSl2Std R d (binaryFormsSignedBasis R d i) = Sl2Std.basis R d i := by
  simp [binaryFormsEquivSl2Std]

@[simp] theorem binaryFormsEquivSl2Std_symm_basis (d : ℕ) (i : Fin (d + 1)) :
    (binaryFormsEquivSl2Std R d).symm (Sl2Std.basis R d i) = binaryFormsSignedBasis R d i := by
  simp [binaryFormsEquivSl2Std]

/-- `binaryFormsEquivSl2Std` sends the highest-weight monomial `yᵈ` to `Sl2Std.basis R d 0`. -/
@[simp] theorem binaryFormsEquivSl2Std_X_one_pow (d : ℕ) :
    binaryFormsEquivSl2Std R d ⟨X 1 ^ d, X_one_pow_mem_binaryForms⟩ = Sl2Std.basis R d 0 := by
  rw [← binaryFormsSignedBasis_zero, binaryFormsEquivSl2Std_signedBasis]

private theorem coe_differential_binaryForms {d : ℕ} (x : Derivation R (coordinateHopfAlgebra R 2)
    (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) (g : binaryForms R d) :
    ((Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x g :
        binaryForms R d) : MvPolynomial (Fin 2) R) =
      Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x (g : MvPolynomial _ R) := by
  simpa only [Subcomodule.subtype_apply] using (binaryForms R d).subtype.map_differential x g

private theorem differential_polynomialComodule_X_zero_pow_mul_X_one_pow (x : Derivation R
    (coordinateHopfAlgebra R 2) (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R))
    (i j : ℕ) : letI := polynomialComodule R 2
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) =
      (((j : R) - (i : R)) * (tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 0) •
          (X 0 ^ i * X 1 ^ j) - ((i : R) * (tangentMatrix 2 x : Matrix (Fin 2) (Fin 2) R) 0 1) •
          (X 0 ^ (i - 1) * X 1 ^ (j + 1)) - ((j : R) * (tangentMatrix 2 x : Matrix (Fin 2)
          (Fin 2) R) 1 0) • (X 0 ^ (i + 1) * X 1 ^ (j - 1)) := by
  let _ := polynomialComoduleAlgebra R 2
  rw [ComoduleAlgebra.differential_mul, ComoduleAlgebra.differential_pow,
    ComoduleAlgebra.differential_pow, differential_polynomialComodule_X_zero,
    differential_polynomialComodule_X_one]
  rcases i with _ | m <;> rcases j with _ | n <;> simp [smul_eq_C_mul, pow_succ] <;> ring

private theorem differential_slFinTwoBasis_zero_signedBasis (d : ℕ) (i : Fin (d + 1)) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 0))
        (binaryFormsSignedBasis R d i) =
      ((i : ℕ) : R) • binaryFormsSignedBasis R d ⟨(i : ℕ) - 1, by omega⟩ := by
  apply Subtype.ext; rw [coe_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_polynomialComodule_X_zero_pow_mul_X_one_pow, ← tangentLieEquivSl_apply,
    LieEquiv.apply_symm_apply, slFinTwoBasis_zero, SetLike.val_smul,
    coe_binaryFormsSignedBasis_apply]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · simp [hi, SpecialLinear.val_single]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    have hsub : d - (m + 1) + 1 = d - m := by omega
    dsimp only; rw [hm, Nat.succ_sub_one, ← hsub]
    simp [SpecialLinear.val_single, smul_eq_C_mul, pow_succ]; ring

private theorem differential_slFinTwoBasis_one_monomial (i j : ℕ) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
        (X 0 ^ i * X 1 ^ j : MvPolynomial (Fin 2) R) =
      -((j : R) • (X 0 ^ (i + 1) * X 1 ^ (j - 1))) := by
  rw [differential_polynomialComodule_X_zero_pow_mul_X_one_pow, ← tangentLieEquivSl_apply,
    LieEquiv.apply_symm_apply, slFinTwoBasis_one]; simp [SpecialLinear.val_single]

private theorem differential_slFinTwoBasis_one_signedBasis (d : ℕ) {i : Fin (d + 1)}
    (hi : (i : ℕ) < d) : Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
      ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
      (binaryFormsSignedBasis R d i) =
      ((d : R) - (i : ℕ)) • binaryFormsSignedBasis R d ⟨(i : ℕ) + 1, by omega⟩ := by
  apply Subtype.ext; rw [coe_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_slFinTwoBasis_one_monomial, SetLike.val_smul, coe_binaryFormsSignedBasis_apply]
  have hsub : d - (i : ℕ) - 1 = d - ((i : ℕ) + 1) := by omega
  simp only [hsub, Nat.cast_sub hi.le, pow_succ, mul_neg, mul_one, smul_neg, neg_smul, smul_smul]
  rw [mul_comm ((-1 : R) ^ (i : ℕ))]

private theorem differential_slFinTwoBasis_one_signedBasis_last (d : ℕ) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 1))
        (binaryFormsSignedBasis R d (Fin.last d)) = 0 := by
  apply Subtype.ext; rw [coe_differential_binaryForms, coe_binaryFormsSignedBasis_apply,
    Fin.val_last, Nat.sub_self, map_smul, differential_slFinTwoBasis_one_monomial]; simp

private theorem differential_slFinTwoBasis_two_signedBasis (d : ℕ) (i : Fin (d + 1)) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R 2))
        (binaryFormsSignedBasis R d i) =
      ((d : R) - 2 * (i : ℕ)) • binaryFormsSignedBasis R d i := by
  apply Subtype.ext
  have hjd : (d : R) - 2 * (i : ℕ) = ((d - (i : ℕ) : ℕ) : R) - (i : ℕ) := by
    rw [Nat.cast_sub (Nat.lt_succ_iff.mp i.isLt)]; ring
  rw [coe_differential_binaryForms, coe_binaryFormsSignedBasis_apply, map_smul,
    differential_polynomialComodule_X_zero_pow_mul_X_one_pow, ← tangentLieEquivSl_apply,
    LieEquiv.apply_symm_apply, slFinTwoBasis_two, SetLike.val_smul,
    coe_binaryFormsSignedBasis_apply, hjd]
  simp [SpecialLinear.val_singleSubSingle, smul_eq_C_mul]; ring

private theorem binaryFormsEquivSl2Std_differential_basis (d : ℕ) (k : Fin 3) (i : Fin (d + 1)) :
    binaryFormsEquivSl2Std R d (Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm (slFinTwoBasis R k))
        (binaryFormsSignedBasis R d i)) = ⁅slFinTwoBasis R k, Sl2Std.basis R d i⁆ := by
  match k with
  | 0 => rw [differential_slFinTwoBasis_zero_signedBasis, (binaryFormsEquivSl2Std R d).map_smul,
      binaryFormsEquivSl2Std_signedBasis, Sl2Std.lie_slFinTwoBasis_zero, Sl2Std.raise_basis]
  | 1 =>
    rw [Sl2Std.lie_slFinTwoBasis_one]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
    · rw [differential_slFinTwoBasis_one_signedBasis d hi, (binaryFormsEquivSl2Std R d).map_smul,
        binaryFormsEquivSl2Std_signedBasis, Sl2Std.lower_basis i hi]
    · obtain rfl : i = Fin.last d := Fin.ext hi
      rw [differential_slFinTwoBasis_one_signedBasis_last, (binaryFormsEquivSl2Std R d).map_zero,
        Sl2Std.lower_basis_last]
  | 2 => rw [differential_slFinTwoBasis_two_signedBasis, (binaryFormsEquivSl2Std R d).map_smul,
      binaryFormsEquivSl2Std_signedBasis, Sl2Std.lie_slFinTwoBasis_two, Sl2Std.diag_basis]

/-- **Equivariance of `binaryFormsEquivSl2Std`.** Over every commutative ring `R`,
`binaryFormsEquivSl2Std R d` intertwines `Comodule.differential` with `sl (Fin 2) R`. -/
theorem binaryFormsEquivSl2Std_differential (d : ℕ)
    (x : Derivation R (coordinateHopfAlgebra R 2)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R 2) R)) (f : binaryForms R d) :
    binaryFormsEquivSl2Std R d
        (Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2) x f) =
      ⁅tangentLieEquivSl (R := R) (B := R) 2 x, binaryFormsEquivSl2Std R d f⁆ := by
  set A := tangentLieEquivSl (R := R) (B := R) 2 x
  have hx : x = (tangentLieEquivSl (R := R) (B := R) 2).symm.toLinearEquiv A :=
    ((tangentLieEquivSl (R := R) (B := R) 2).symm_apply_apply x).symm
  rw [hx, ← (slFinTwoBasis R).sum_repr A, ← (binaryFormsSignedBasis R d).sum_repr f]
  simp only [map_sum, LinearEquiv.map_smul, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_lie, smul_lie, lie_sum, lie_smul]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg _ (Finset.sum_congr rfl fun k _ ↦ congrArg _ ?_)
  rw [LieEquiv.coe_toLinearEquiv, binaryFormsEquivSl2Std_signedBasis,
    binaryFormsEquivSl2Std_differential_basis]

/-- Inverse form of `binaryFormsEquivSl2Std_differential` on `(binaryFormsEquivSl2Std R d).symm`. -/
theorem differential_binaryFormsEquivSl2Std_symm (d : ℕ)
    (A : SpecialLinear.sl (Fin 2) R) (v : Sl2Std R d) :
    Comodule.differential (R := R) (H := coordinateHopfAlgebra R 2)
        ((tangentLieEquivSl (R := R) (B := R) 2).symm A) ((binaryFormsEquivSl2Std R d).symm v) =
      (binaryFormsEquivSl2Std R d).symm ⁅A, v⁆ := (binaryFormsEquivSl2Std R d).injective <| by
  rw [binaryFormsEquivSl2Std_differential, LieEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end BinaryFormsEquiv

end TauCeti.SpecialLinear
