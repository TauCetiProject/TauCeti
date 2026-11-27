/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# Quasi-reflections in the unitary group of a Hermitian matrix

Let `A` be a Hermitian matrix over a field `K` with an involution `star`, and write
`⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y` for its form, conjugate-linear in the first slot. For a vector `v` and
a scalar `s` with `s + star s = ⟨v, v⟩`, the **quasi-reflection** along `v` with parameter `s` is

`x ↦ x - s⁻¹ ⟨v, x⟩ v`,

the matrix `1 - s⁻¹ • v (star v ᵥ* A)` (`Matrix.unitaryGroupOf.quasiReflection`). It preserves
the form, and it is invertible with inverse the quasi-reflection along `v` with parameter
`star s`, so it lies in `Matrix.unitaryGroupOf A` even when `A` is not invertible. For
`⟨v, v⟩ ≠ 0` and `s = ⟨v, v⟩ / 2` it is the reflection `Matrix.unitaryGroupOf.reflection` in `v`;
for isotropic `v` and `s + star s = 0` it is a unitary transvection. This is the matrix form of
the quasi-reflections `TauCeti.SignedHermitianSpace.quasiReflection` of a signed Hermitian space.

The parameter is what makes quasi-reflections suited to carrying isotropic vectors explicitly.
If `y` is isotropic and `x` is any vector, then `v = x - y` and `s = ⟨x, x⟩ / 2 - ⟨x, y⟩` satisfy
`s + star s = ⟨v, v⟩`, and when `x` is isotropic too with `⟨x, y⟩ ≠ 0` the quasi-reflection sends
`y` to `x` (`Matrix.unitaryGroupOf.quasiReflection_sub_mulVec_of_isotropic`). The parameter is a
polynomial in the coordinates of `x` and their conjugates, so over `ℝ` or `ℂ` this element of
`unitaryGroupOf A` depends smoothly on `x` where `s ≠ 0`; this gives the smooth local sections of
the isotropic orbit in `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.IsotropicSection`.

## Main definitions

* `Matrix.unitaryGroupOf.quasiReflection`: the quasi-reflection along `v` with parameter `s`.

## Main results

* `Matrix.star_one_add_smul_vecMulVec_mul_mul`: the change of the form of `A` under the rank-one
  perturbation `1 + c • v (star v ᵥ* A)` of the identity, over a commutative ring.
* `Matrix.one_add_smul_vecMulVec_mul_one_add_smul_vecMulVec`: products of such perturbations.
* `Matrix.unitaryGroupOf.quasiReflection_mulVec`: the quasi-reflection sends `x` to
  `x - s⁻¹ ⟨v, x⟩ v`.
* `Matrix.unitaryGroupOf.inv_quasiReflection`: its inverse is the quasi-reflection with parameter
  `star s`.
* `Matrix.unitaryGroupOf.quasiReflection_eq_reflection`: for `s = ⟨v, v⟩ / 2` it is the reflection.
* `Matrix.unitaryGroupOf.quasiReflection_sub_mulVec_of_isotropic`: carrying one isotropic vector to
  another.

## Attribution

Quasi-reflections of an invertible Hermitian matrix are `New.quasiReflection` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/WittTheorem.lean`, which uses them in `src/Lib/Adelic/Witt/SmoothWitt.lean`
to carry isotropic vectors. Here they are stated for Hermitian matrices that need not be
invertible, with the form identity over a commutative ring, and the parameter
`⟨x, x⟩ / 2 - ⟨x, y⟩` is chosen so that the quasi-reflection along `x - y` lies in the unitary group
for every `x`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7, for quasi-reflections of Hermitian forms.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] [StarRing R] {A : Matrix n n R}

omit [DecidableEq n] in
/-- For Hermitian `A`, the conjugate transpose of the rank-one matrix `v (star v ᵥ* A)`, multiplied
by `A`, is `(A v) (star v ᵥ* A)`. -/
theorem star_vecMulVec_vecMul_mul (hA : A.IsHermitian) (v : n → R) :
    star (vecMulVec v (star v ᵥ* A)) * A = vecMulVec (A *ᵥ v) (star v ᵥ* A) := by
  rw [star_eq_conjTranspose, conjTranspose_vecMulVec, star_vecMul, star_star, hA.eq,
    vecMulVec_mul]

omit [DecidableEq n] in
/-- The rank-one matrix `P = v (star v ᵥ* A)` satisfies `M * P = ⟨v, v⟩ • M` for every matrix
`M = w (star v ᵥ* A)` with the same row vector. -/
private theorem vecMulVec_vecMul_mul_vecMulVec_vecMul (v w : n → R) :
    vecMulVec w (star v ᵥ* A) * vecMulVec v (star v ᵥ* A) =
      (star v ⬝ᵥ A *ᵥ v) • vecMulVec w (star v ᵥ* A) := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]

/-- **The form under a rank-one perturbation of the identity.** For Hermitian `A`, the matrix
`M = 1 + c • v (star v ᵥ* A)` changes the form of `A` by
`(c + star c + star c * c * ⟨v, v⟩) • (A v) (star v ᵥ* A)`. In particular `M` preserves the form
when `c + star c + star c * c * ⟨v, v⟩ = 0`. -/
theorem star_one_add_smul_vecMulVec_mul_mul (hA : A.IsHermitian) (c : R) (v : n → R) :
    star (1 + c • vecMulVec v (star v ᵥ* A)) * A * (1 + c • vecMulVec v (star v ᵥ* A)) =
      A + (c + star c + star c * c * (star v ⬝ᵥ A *ᵥ v)) •
        vecMulVec (A *ᵥ v) (star v ᵥ* A) := by
  have h : star (1 + c • vecMulVec v (star v ᵥ* A)) * A =
      A + star c • vecMulVec (A *ᵥ v) (star v ᵥ* A) := by
    rw [star_add, star_one, star_smul, add_mul, Matrix.one_mul, Matrix.smul_mul,
      star_vecMulVec_vecMul_mul hA]
  rw [h]
  simp only [add_mul, mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [vecMulVec_vecMul_mul_vecMulVec_vecMul, mul_vecMulVec]
  module

/-- The product of two rank-one perturbations `1 + a • P` and `1 + b • P` of the identity along
the same `P = v (star v ᵥ* A)` is `1 + (a + b + a * b * ⟨v, v⟩) • P`. -/
theorem one_add_smul_vecMulVec_mul_one_add_smul_vecMulVec (a b : R) (v : n → R) :
    (1 + a • vecMulVec v (star v ᵥ* A)) * (1 + b • vecMulVec v (star v ᵥ* A)) =
      1 + (a + b + a * b * (star v ⬝ᵥ A *ᵥ v)) • vecMulVec v (star v ᵥ* A) := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [vecMulVec_vecMul_mul_vecMulVec_vecMul]
  module

end CommRing

section Field

variable {K : Type*} [Field K] [StarRing K] {A : Matrix n n K}

omit [StarRing K] in
/-- The scalar identity behind quasi-reflections: if `a + b = q` and `a`, `b` vanish together,
then `-a⁻¹ + -b⁻¹ + -a⁻¹ * -b⁻¹ * q = 0`. -/
private theorem neg_inv_add_neg_inv_add_neg_inv_mul_neg_inv_mul_eq_zero {a b q : K}
    (hab : a + b = q) (h0 : a = 0 ↔ b = 0) : -a⁻¹ + -b⁻¹ + -a⁻¹ * -b⁻¹ * q = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [h0.mp rfl]
  have hb : b ≠ 0 := fun hb => ha (h0.mpr hb)
  subst hab
  field_simp
  ring

/-- For Hermitian `A` and `s + star s = ⟨v, v⟩`, the matrix `1 - s⁻¹ • v (star v ᵥ* A)` preserves
the form of `A`. -/
private theorem star_one_sub_inv_smul_vecMulVec_mul_mul (hA : A.IsHermitian) {v : n → K} {s : K}
    (hs : s + star s = star v ⬝ᵥ A *ᵥ v) :
    star (1 - s⁻¹ • vecMulVec v (star v ᵥ* A)) * A * (1 - s⁻¹ • vecMulVec v (star v ᵥ* A)) =
      A := by
  have h := neg_inv_add_neg_inv_add_neg_inv_mul_neg_inv_mul_eq_zero hs star_eq_zero.symm
  have h' : -s⁻¹ + -(star s)⁻¹ + -(star s)⁻¹ * -s⁻¹ * (star v ⬝ᵥ A *ᵥ v) = 0 := by
    linear_combination h
  rw [sub_eq_add_neg, ← neg_smul, star_one_add_smul_vecMulVec_mul_mul hA, star_neg, star_inv₀, h',
    zero_smul, add_zero]

/-- For `a + b = ⟨v, v⟩` with `a` and `b` vanishing together, the matrices
`1 - a⁻¹ • v (star v ᵥ* A)` and `1 - b⁻¹ • v (star v ᵥ* A)` are inverse to each other. -/
private theorem one_sub_inv_smul_vecMulVec_mul_one_sub_inv_smul_vecMulVec {v : n → K} {a b : K}
    (hab : a + b = star v ⬝ᵥ A *ᵥ v) (h0 : a = 0 ↔ b = 0) :
    (1 - a⁻¹ • vecMulVec v (star v ᵥ* A)) * (1 - b⁻¹ • vecMulVec v (star v ᵥ* A)) = 1 := by
  simp only [sub_eq_add_neg, ← neg_smul, one_add_smul_vecMulVec_mul_one_add_smul_vecMulVec,
    neg_inv_add_neg_inv_add_neg_inv_mul_neg_inv_mul_eq_zero hab h0, zero_smul, add_zero]

namespace unitaryGroupOf

/-- **The quasi-reflection** along `v` with parameter `s`, for a Hermitian matrix `A` and a scalar
`s` with `s + star s = ⟨v, v⟩`: the element `x ↦ x - s⁻¹ ⟨v, x⟩ v` of `unitaryGroupOf A`, whose
matrix is `1 - s⁻¹ • v (star v ᵥ* A)` (`val_quasiReflection`). Its inverse is the quasi-reflection
with parameter `star s` (`inv_quasiReflection`). -/
noncomputable def quasiReflection (hA : A.IsHermitian) (v : n → K) (s : K)
    (hs : s + star s = star v ⬝ᵥ A *ᵥ v) : unitaryGroupOf A :=
  ⟨⟨1 - s⁻¹ • vecMulVec v (star v ᵥ* A), 1 - (star s)⁻¹ • vecMulVec v (star v ᵥ* A),
      one_sub_inv_smul_vecMulVec_mul_one_sub_inv_smul_vecMulVec hs star_eq_zero.symm,
      one_sub_inv_smul_vecMulVec_mul_one_sub_inv_smul_vecMulVec (by rw [add_comm, hs])
        star_eq_zero⟩, by
    rw [mem_unitaryGroupOf_iff, Units.val_mk]
    exact star_one_sub_inv_smul_vecMulVec_mul_mul hA hs⟩

variable (hA : A.IsHermitian) (v : n → K) (s : K) (hs : s + star s = star v ⬝ᵥ A *ᵥ v)

@[simp]
theorem val_quasiReflection :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) =
      1 - s⁻¹ • vecMulVec v (star v ᵥ* A) :=
  (rfl)

/-- The quasi-reflection along `v` with parameter `s` sends `x` to `x - s⁻¹ ⟨v, x⟩ v`. -/
theorem quasiReflection_mulVec (x : n → K) :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) *ᵥ x =
      x - (s⁻¹ * (star v ⬝ᵥ A *ᵥ x)) • v := by
  simp [sub_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec, smul_smul]

/-- The quasi-reflection along `v` fixes every vector orthogonal to `v` for the form. -/
theorem quasiReflection_mulVec_of_dotProduct_eq_zero {x : n → K} (hx : star v ⬝ᵥ A *ᵥ x = 0) :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) *ᵥ x = x := by
  rw [quasiReflection_mulVec, hx, mul_zero, zero_smul, sub_zero]

/-- The inverse of the quasi-reflection along `v` with parameter `s` is the quasi-reflection
along `v` with parameter `star s`. -/
theorem inv_quasiReflection :
    (quasiReflection hA v s hs)⁻¹ =
      quasiReflection hA v (star s) (by rw [star_star, add_comm, hs]) := by
  ext : 1
  rw [Subgroup.coe_inv, val_quasiReflection]
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [val_quasiReflection]
  exact one_sub_inv_smul_vecMulVec_mul_one_sub_inv_smul_vecMulVec (by rw [add_comm, hs])
    star_eq_zero

/-- For a non-isotropic `v`, the quasi-reflection along `v` with parameter `⟨v, v⟩ / 2` is the
reflection in `v`. -/
theorem quasiReflection_eq_reflection [NeZero (2 : K)] (hA' : IsUnit A)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    quasiReflection hA v ((star v ⬝ᵥ A *ᵥ v) / 2)
        (by rw [star_div₀, star_ofNat, hA.star_dotProduct_mulVec_comm, add_halves]) =
      reflection hA hA' v hv := by
  ext : 1
  rw [val_quasiReflection, val_reflection, inv_div]

end unitaryGroupOf

variable [NeZero (2 : K)]

omit [DecidableEq n] in
/-- For Hermitian `A`, an isotropic `y` and any `x`, the parameter `s = ⟨x, x⟩ / 2 - ⟨x, y⟩` of the
quasi-reflection along `x - y` satisfies `s + star s = ⟨x - y, x - y⟩`. -/
theorem add_star_half_dotProduct_sub_dotProduct (hA : A.IsHermitian) {y : n → K}
    (hy : star y ⬝ᵥ A *ᵥ y = 0) (x : n → K) :
    (star x ⬝ᵥ A *ᵥ x / 2 - star x ⬝ᵥ A *ᵥ y) +
        star (star x ⬝ᵥ A *ᵥ x / 2 - star x ⬝ᵥ A *ᵥ y) =
      star (x - y) ⬝ᵥ A *ᵥ (x - y) := by
  have hxx : star (star x ⬝ᵥ A *ᵥ x / 2) = star x ⬝ᵥ A *ᵥ x / 2 := by
    rw [star_div₀, star_ofNat, hA.star_dotProduct_mulVec_comm]
  have hv : star (x - y) ⬝ᵥ A *ᵥ (x - y) =
      star x ⬝ᵥ A *ᵥ x - star x ⬝ᵥ A *ᵥ y - star y ⬝ᵥ A *ᵥ x := by
    simp only [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, hy]
    ring
  rw [star_sub, hxx, hA.star_dotProduct_mulVec_comm, hv]
  field_simp
  ring

namespace unitaryGroupOf

/-- **Carrying an isotropic vector to another.** For Hermitian `A` and isotropic vectors `x`, `y`
with `⟨x, y⟩ ≠ 0`, the quasi-reflection along `x - y` with parameter `⟨x, x⟩ / 2 - ⟨x, y⟩` sends
`y` to `x`. -/
theorem quasiReflection_sub_mulVec_of_isotropic (hA : A.IsHermitian) {x y : n → K}
    (hx : star x ⬝ᵥ A *ᵥ x = 0) (hy : star y ⬝ᵥ A *ᵥ y = 0) (hxy : star x ⬝ᵥ A *ᵥ y ≠ 0) :
    ((quasiReflection hA (x - y) _ (add_star_half_dotProduct_sub_dotProduct hA hy x) : GL n K) :
        Matrix n n K) *ᵥ y = x := by
  have hs : star x ⬝ᵥ A *ᵥ x / 2 - star x ⬝ᵥ A *ᵥ y = -(star x ⬝ᵥ A *ᵥ y) := by
    rw [hx, zero_div, zero_sub]
  have hv : star (x - y) ⬝ᵥ A *ᵥ y = star x ⬝ᵥ A *ᵥ y := by
    rw [star_sub, sub_dotProduct, hy, sub_zero]
  rw [quasiReflection_mulVec, hs, hv, inv_neg, neg_mul, inv_mul_cancel₀ hxy, neg_one_smul,
    sub_neg_eq_add, add_sub_cancel]

end unitaryGroupOf

end Field

end Matrix
