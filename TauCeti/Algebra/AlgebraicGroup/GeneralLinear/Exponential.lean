/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential.Basic
public import TauCeti.RingTheory.Nilpotent.Exp
import TauCeti.Algebra.Lie.Derivation.LocallyNilpotent
import TauCeti.RingTheory.Derivation.Matrix

/-!
# Exponentials of nilpotent matrices as points of `GLₙ`

Let `X` be an `n × n` matrix over a commutative ring `R`, viewed as a tangent vector at the
identity of `GLₙ` through `TauCeti.GeneralLinear.tangentMatrix`. Its left-invariant vector field
`D` on the coordinate Hopf algebra `O(GLₙ) = R[xᵢⱼ][det⁻¹]` is right multiplication by `X` on
the generic matrix `g = (xᵢⱼ)`, and, by the Leibniz rule applied to `g * g⁻¹ = 1`, left
multiplication by `-X` on its inverse:

```text
D g = g X,    D (g⁻¹) = -X g⁻¹.
```

Hence `Dᵐ g = g Xᵐ` and `Dᵐ (g⁻¹) = (-X)ᵐ g⁻¹`. Since the entries of `g` and `g⁻¹` generate
`O(GLₙ)`, the vector field `D` is locally nilpotent exactly when `X` is nilpotent. When `R` is a
`ℚ`-algebra, the exponential point `ε ∘ exp D` of the tangent vector is then the invertible matrix
`exp X = ∑ Xᵏ / k!`: the exponential of a nilpotent tangent vector of `GLₙ`, defined through its
invariant vector field, is the matrix exponential.

## Main results

* `TauCeti.GeneralLinear.map_iterate_leftInvariantDerivation_genericMatrix`: `Dᵐ g = g Xᵐ`.
* `TauCeti.GeneralLinear.map_iterate_leftInvariantDerivation_genericMatrix_inv`:
  `Dᵐ (g⁻¹) = (-X)ᵐ g⁻¹`.
* `TauCeti.GeneralLinear.isNilpotent_tangentMatrix_iff`: the invariant vector field of a tangent
  vector is locally nilpotent if and only if its matrix is nilpotent.
* `TauCeti.GeneralLinear.pointToGeneralLinear_expPoint`: the exponential point of a nilpotent
  tangent vector is the matrix exponential of its matrix.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* J. E. Humphreys, *Linear Algebraic Groups*, Graduate Texts in Mathematics 21, Springer (1975),
  §15.1.
-/

public section

open WithConv

namespace TauCeti

namespace GeneralLinear

open _root_.TauCeti.Bialgebra (leftInvariantDerivation leftInvariantDerivation_apply)

universe u

variable {R : Type u} [CommRing R] (n : ℕ)

/-- A local abbreviation for the coordinate Hopf algebra of `GLₙ`. -/
local notation "H" => coordinateHopfAlgebra

/-- **The invariant vector field of a tangent vector `X` on the generic matrix**: `D g = g X`. -/
@[simp]
theorem map_leftInvariantDerivation_genericMatrix
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) :
    (genericMatrix R n).map (leftInvariantDerivation d) =
      genericMatrix R n * (tangentMatrix n d).map (algebraMap R (H R n)) := by
  ext i j
  simp only [Matrix.map_apply, genericMatrix_apply, leftInvariantDerivation_apply,
    coordinateHopfAlgebra_comul_X, map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.tensorComponent_tmul, tangentMatrix_apply, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
  rw [Algebra.smul_def, mul_comm]

/-- **Iterated invariant vector fields on the generic matrix**: `Dᵐ g = g Xᵐ`. -/
@[simp]
theorem map_iterate_leftInvariantDerivation_genericMatrix
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) (m : ℕ) :
    (genericMatrix R n).map (leftInvariantDerivation d)^[m] =
      genericMatrix R n * (tangentMatrix n d ^ m).map (algebraMap R (H R n)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ', ← Matrix.map_map, ih, Derivation.matrix_map_mul,
      Derivation.matrix_map_map_algebraMap]
    simp [pow_succ', Matrix.map_mul, Matrix.mul_assoc]

/-- **The invariant vector field of a tangent vector `X` on the inverse generic matrix**:
`D (g⁻¹) = -X g⁻¹`. -/
@[simp]
theorem map_leftInvariantDerivation_genericMatrix_inv
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) :
    (genericMatrix R n)⁻¹.map (leftInvariantDerivation d) =
      -(tangentMatrix n d).map (algebraMap R (H R n)) * (genericMatrix R n)⁻¹ := by
  set g := genericMatrix R n
  set D := leftInvariantDerivation d
  set X := (tangentMatrix n d).map (algebraMap R (H R n))
  have hg := isUnit_det_genericMatrix R n
  -- Differentiate `g * g⁻¹ = 1`.
  have h : g * g⁻¹.map D = -(g * X * g⁻¹) := by
    have h1 := Derivation.matrix_map_mul D g g⁻¹
    rw [Matrix.mul_nonsing_inv _ hg, map_leftInvariantDerivation_genericMatrix] at h1
    have h0 : (1 : Matrix (Fin n) (Fin n) (H R n)).map D = 0 := by
      simpa using Derivation.matrix_map_map_algebraMap D (1 : Matrix (Fin n) (Fin n) R)
    rw [h0] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  calc g⁻¹.map D = g⁻¹ * (g * g⁻¹.map D) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
    _ = -X * g⁻¹ := by
        rw [h, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ hg, Matrix.one_mul, Matrix.neg_mul]

/-- **Iterated invariant vector fields on the inverse generic matrix**:
`Dᵐ (g⁻¹) = (-X)ᵐ g⁻¹`. -/
@[simp]
theorem map_iterate_leftInvariantDerivation_genericMatrix_inv
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) (m : ℕ) :
    (genericMatrix R n)⁻¹.map (leftInvariantDerivation d)^[m] =
      ((-tangentMatrix n d) ^ m).map (algebraMap R (H R n)) * (genericMatrix R n)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ', ← Matrix.map_map, ih, Derivation.matrix_map_mul,
      Derivation.matrix_map_map_algebraMap, Matrix.zero_mul, zero_add,
      map_leftInvariantDerivation_genericMatrix_inv, pow_succ, Matrix.map_mul,
      Matrix.mul_assoc, Matrix.map_neg _ (map_neg _)]

/-- The counit evaluates the iterated invariant vector field on the generic matrix to the power
of the tangent matrix: `ε (Dᵐ g) = Xᵐ`. -/
private theorem map_counit_map_iterate_genericMatrix
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) (m : ℕ) :
    ((genericMatrix R n).map (leftInvariantDerivation d)^[m]).map
        (Bialgebra.counitAlgHom R (H R n)) = tangentMatrix n d ^ m := by
  rw [map_iterate_leftInvariantDerivation_genericMatrix, Matrix.map_mul,
    map_counit_genericMatrix, Matrix.one_mul, Matrix.map_map]
  ext i j
  simp

/-- If the tangent matrix satisfies `Xᴺ = 0`, then `Dᴺ` kills every entry of the generic
matrix. -/
private theorem iterate_leftInvariantDerivation_genericMatrix_eq_zero
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) {N : ℕ}
    (hN : tangentMatrix n d ^ N = 0) (i j : Fin n) :
    (leftInvariantDerivation d)^[N] (genericMatrix R n i j) = 0 := by
  simpa [hN] using
    congrFun (congrFun (map_iterate_leftInvariantDerivation_genericMatrix n d N) i) j

/-- **Local nilpotence of invariant vector fields on `GLₙ`.** The left-invariant vector field of a
tangent vector to `GLₙ` is locally nilpotent if and only if the matrix of the tangent vector is
nilpotent. -/
theorem isNilpotent_tangentMatrix_iff
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R)) :
    IsNilpotent (tangentMatrix n d) ↔ ∀ h, ∃ m, (leftInvariantDerivation d)^[m] h = 0 := by
  set D := leftInvariantDerivation d
  constructor
  · rintro ⟨N, hN⟩ h
    -- The entries of `g` and of `g⁻¹ = S g` generate `O(GLₙ)`, and `D^N` kills both.
    have hD : ⇑(derivationEquivDerivationLieAlgebra D : Module.End R (H R n)) = D :=
      funext (derivationEquivDerivationLieAlgebra_apply D)
    refine (derivationLieAlgebra.exists_pow_apply_eq_zero_of_mem_adjoin
      (derivationEquivDerivationLieAlgebra D) (fun x hx => ?_)
      ((adjoin_coordinateHopfAlgebra_X_union_antipode_X R n).symm ▸ Algebra.mem_top)).imp
      fun m hm => by simpa only [Module.End.pow_apply, hD] using hm
    simp only [Module.End.pow_apply, hD]
    rcases hx with ⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩
    · dsimp only
      rw [← genericMatrix_apply]
      exact ⟨N, iterate_leftInvariantDerivation_genericMatrix_eq_zero n d hN i j⟩
    · refine ⟨N, ?_⟩
      have := congrFun (congrFun (map_iterate_leftInvariantDerivation_genericMatrix_inv n d N) i) j
      rw [neg_pow, hN, mul_zero, Matrix.map_zero _ (map_zero _), Matrix.zero_mul] at this
      have hS : HopfAlgebra.antipode R (genericMatrix R n i j) = (genericMatrix R n)⁻¹ i j := by
        rw [← map_antipode_genericMatrix, Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply]
      dsimp only
      rw [← genericMatrix_apply, hS]
      simpa using this
  · intro hd
    -- A single iterate kills every entry of the generic matrix; apply the counit.
    choose m hm using hd
    let N := ∑ ij : Fin n × Fin n, m (genericMatrix R n ij.1 ij.2)
    refine ⟨N, ?_⟩
    rw [← map_counit_map_iterate_genericMatrix]
    ext i j
    have hle : m (genericMatrix R n i j) ≤ N :=
      Finset.single_le_sum (f := fun ij : Fin n × Fin n ↦ m (genericMatrix R n ij.1 ij.2))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (i, j))
    have hij : D^[N] (genericMatrix R n i j) = 0 := by
      rw [← Nat.sub_add_cancel hle, Function.iterate_add_apply, hm, iterate_map_zero]
    rw [Matrix.map_apply, Matrix.map_apply, hij, map_zero, Matrix.zero_apply]

variable [Algebra ℚ R] [Algebra ℚ (H R n)]

/-- **The exponential of a nilpotent tangent vector of `GLₙ` is the matrix exponential.** If the
invariant vector field of a tangent vector is locally nilpotent, then its exponential point
`ε ∘ exp D` is the invertible matrix `exp X = ∑ Xᵏ / k!` of the nilpotent tangent matrix `X`. -/
theorem pointToGeneralLinear_expPoint
    (d : Derivation R (H R n) (Bialgebra.CounitAlgebra R (H R n) R))
    (hd : ∀ h, ∃ m, (leftInvariantDerivation d)^[m] h = 0) :
    pointToGeneralLinear n (toConv (Bialgebra.expPoint d hd)) =
      nilpotentExpUnit ((isNilpotent_tangentMatrix_iff n d).2 hd) := by
  have hX : IsNilpotent (tangentMatrix n d) := (isNilpotent_tangentMatrix_iff n d).2 hd
  obtain ⟨N, hN⟩ := hX
  apply Units.ext
  rw [coe_nilpotentExpUnit, IsNilpotent.exp_eq_sum hN]
  ext i j
  have hzero := iterate_leftInvariantDerivation_genericMatrix_eq_zero n d hN i j
  rw [Matrix.sum_apply, pointToGeneralLinear_apply, ofConv_toConv, ← genericMatrix_apply,
    Bialgebra.expPoint_apply, Derivation.taylorExp_apply_eq_sum _ hd hzero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_rat_smul, Matrix.smul_apply, ← map_counit_map_iterate_genericMatrix, Matrix.map_apply,
    Matrix.map_apply, Bialgebra.counitAlgHom_apply]

end GeneralLinear

end TauCeti
