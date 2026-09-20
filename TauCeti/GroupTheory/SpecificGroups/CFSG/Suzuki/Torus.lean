/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generated

/-!
# The torus of the Suzuki group

The standard generators of `TauCeti.suzukiGroup m` are the lower unitriangular matrices `u(a, b)`
and the antidiagonal Weyl element `w`. This file adds the diagonal torus

```text
h(κ) = diag (κ, κ^θ / κ, κ / κ^θ, κ⁻¹),      θ = 2^(m+1),
```

as a homomorphism `TauCeti.Suzuki.torus` from the multiplicative group of the generator field, and
proves that its image lies in the generated group. The torus is not a generator, so its membership
is a computation: the rank-one Bruhat relation

```text
w u(0, b) w = u(b^(1-θ), b⁻¹) · h(b^θ) · w · u(b^(1-θ), 0)      (b ≠ 0)
```

exhibits `h(b^θ) w` as a product of generators, and since `x ↦ x^θ` is a bijection of the finite
generator field every torus element is some `h(b^θ)`. The Bruhat decomposition of the Suzuki group
with respect to the point at infinity, and the identification of the group with the Steinberg
fixed points, consume the torus in `TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Generation`.

## Main definitions

* `TauCeti.Suzuki.torusMatrix`: the diagonal torus matrix `h(κ)`.
* `TauCeti.Suzuki.torus`: the torus as a homomorphism `𝔽_q^× →* GL₄(𝔽_q)`.

## Main results

* `TauCeti.Suzuki.weyl_mul_unipotent_zero_mul_weyl`: the rank-one Bruhat relation.
* `TauCeti.Suzuki.torus_mem_suzukiGroup`: every torus element is a product of the standard
  generators.

## References

* M. Suzuki, *On a class of doubly transitive groups*, Annals of Mathematics **75** (1962),
  105--145.
* R. A. Wilson, *The Finite Simple Groups*, Springer GTM 251 (2009), §4.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace Suzuki

variable (m : ℕ)

/-! ## The torus -/

/-- The torus matrix of the Suzuki group at the parameter `κ`, `diag (κ, κ^θ / κ, κ / κ^θ, κ⁻¹)`
with `θ = 2^(m+1)`. Writing `κ = λ^(2^m + 1)`, which is possible since `2^m + 1` is prime to
`2^(2m+1) - 1`, this is the usual diagonal matrix `diag (λ^(2^m+1), λ^(2^m), λ^(-2^m), λ^(-2^m-1))`
of the literature. -/
def torusMatrix (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)) :=
  Matrix.diagonal ![κ, κ ^ 2 ^ (m + 1) * κ⁻¹, κ * (κ ^ 2 ^ (m + 1))⁻¹, κ⁻¹]

/-- An entry of the torus matrix. -/
@[simp]
theorem torusMatrix_apply (κ : (GaloisField 2 (2 * m + 1))ˣ) (i j : Fin 4) :
    torusMatrix m κ i j =
      Matrix.diagonal ![(κ : GaloisField 2 (2 * m + 1)),
        (κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1) * (κ : GaloisField 2 (2 * m + 1))⁻¹,
        (κ : GaloisField 2 (2 * m + 1)) * ((κ : GaloisField 2 (2 * m + 1)) ^ 2 ^ (m + 1))⁻¹,
        (κ : GaloisField 2 (2 * m + 1))⁻¹] i j := by
  simp [torusMatrix]

/-- The torus matrix has determinant one. -/
@[simp]
theorem det_torusMatrix (κ : (GaloisField 2 (2 * m + 1))ˣ) : (torusMatrix m κ).det = 1 := by
  have hκ : (κ : GaloisField 2 (2 * m + 1)) ≠ 0 := κ.ne_zero
  rw [torusMatrix, det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

/-- The torus matrix at `1` is the identity. -/
@[simp]
theorem torusMatrix_one : torusMatrix m 1 = 1 := by
  rw [torusMatrix, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

/-- The torus matrices multiply through their parameters. -/
theorem torusMatrix_mul (κ μ : (GaloisField 2 (2 * m + 1))ˣ) :
    torusMatrix m (κ * μ) = torusMatrix m κ * torusMatrix m μ := by
  rw [torusMatrix, torusMatrix, torusMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_pow] <;> ring

/-- The torus of the Suzuki group: the homomorphism `κ ↦ h(κ)` from the multiplicative group
of the generator field into the general linear group, with `h(κ)` the matrix `torusMatrix m κ`. -/
def torus : (GaloisField 2 (2 * m + 1))ˣ →* GL (Fin 4) (GaloisField 2 (2 * m + 1)) where
  toFun κ := Matrix.GeneralLinearGroup.mk'' (torusMatrix m κ) (by simp)
  map_one' := Matrix.GeneralLinearGroup.ext fun i j ↦ by
    rw [Matrix.GeneralLinearGroup.val_mk'', torusMatrix_one]
    rfl
  map_mul' κ μ := Matrix.GeneralLinearGroup.ext fun i j ↦ by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_mk'', Matrix.GeneralLinearGroup.val_mk'',
      Matrix.GeneralLinearGroup.val_mk'', torusMatrix_mul]

/-- The underlying matrix of `torus m κ` is `torusMatrix m κ`. -/
@[simp]
theorem coe_torus (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    (torus m κ : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) = torusMatrix m κ :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

/-! ## The rank-one Bruhat relation and the torus -/

/-- The rank-one Bruhat relation of the Suzuki group: conjugating the long-root generator
`u(0, b)` by the Weyl element lands in the big cell, `w u(0, b) w = u' h(b^θ) w u''` with
`u' = u(b^(1-θ), b⁻¹)` and `u'' = u(b^(1-θ), 0)`. -/
theorem weyl_mul_unipotent_zero_mul_weyl (b : GaloisField 2 (2 * m + 1)) (hb : b ≠ 0) :
    weyl m * unipotent m 0 b * weyl m =
      unipotent m (b / b ^ 2 ^ (m + 1)) b⁻¹ *
        torus m (Units.mk0 (b ^ 2 ^ (m + 1)) (pow_ne_zero _ hb)) * weyl m *
        unipotent m (b / b ^ 2 ^ (m + 1)) 0 := by
  have htwo : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  have hthree : (3 : GaloisField 2 (2 * m + 1)) = 1 := by linear_combination htwo
  have hfour : (4 : GaloisField 2 (2 * m + 1)) = 0 := by linear_combination 2 * htwo
  have hsix : (6 : GaloisField 2 (2 * m + 1)) = 0 := by linear_combination 3 * htwo
  have hB := pow_two_pow_succ_pow_two_pow_succ m b
  have hB0 : b ^ 2 ^ (m + 1) ≠ 0 := pow_ne_zero _ hb
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_weyl, coe_unipotent, coe_torus]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, div_pow, inv_pow, hB]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [htwo, hthree, hfour, hsix]

/-- Every torus element of the Suzuki group is a product of the standard generators: it is
read off the rank-one Bruhat relation at a `θ`-th root of its parameter. -/
theorem torus_mem_suzukiGroup (κ : (GaloisField 2 (2 * m + 1))ˣ) :
    torus m κ ∈ suzukiGroup m := by
  obtain ⟨b, hb⟩ :=
    (bijective_iterateFrobenius (GaloisField 2 (2 * m + 1)) 2 (m + 1)).2
      (κ : GaloisField 2 (2 * m + 1))
  rw [iterateFrobenius_def] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact κ.ne_zero (by simpa using hb.symm)
  have hκ : κ = Units.mk0 (b ^ 2 ^ (m + 1)) (pow_ne_zero _ hb0) := Units.ext (by simp [hb])
  have h := weyl_mul_unipotent_zero_mul_weyl m b hb0
  rw [← hκ] at h
  have ht : torus m κ =
      (unipotent m (b / b ^ 2 ^ (m + 1)) b⁻¹)⁻¹ * (weyl m * unipotent m 0 b * weyl m) *
        (unipotent m (b / b ^ 2 ^ (m + 1)) 0)⁻¹ * (weyl m)⁻¹ := by
    rw [h]
    group
  rw [ht]
  exact mul_mem (mul_mem (mul_mem (inv_mem (unipotent_mem_suzukiGroup _ _))
    (mul_mem (mul_mem weyl_mem_suzukiGroup (unipotent_mem_suzukiGroup _ _))
      weyl_mem_suzukiGroup)) (inv_mem (unipotent_mem_suzukiGroup _ _)))
    (inv_mem weyl_mem_suzukiGroup)

end Suzuki

end TauCeti
