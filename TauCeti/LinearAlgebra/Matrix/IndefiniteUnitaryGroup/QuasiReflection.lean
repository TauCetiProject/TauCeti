/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
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

The form identity and the product formula for the rank-one perturbations
`1 + c • v (star v ᵥ* A)` of the identity behind these facts are
`Matrix.star_one_add_smul_vecMulVec_mul_mul` and
`Matrix.one_add_smul_vecMulVec_mul_one_add_smul_vecMulVec`, over a commutative ring, in
`TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup`, where they also give the reflections.

## Main results

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
invertible, and the parameter `⟨x, x⟩ / 2 - ⟨x, y⟩` is chosen so that the quasi-reflection along
`x - y` lies in the unitary group for every `x`.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7, for quasi-reflections of Hermitian forms.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

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
theorem quasiReflection_eq_reflection [NeZero (2 : K)] (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    quasiReflection hA v ((star v ⬝ᵥ A *ᵥ v) / 2)
        (by rw [star_div₀, star_ofNat, hA.star_dotProduct_mulVec_comm, add_halves]) =
      reflection hA v hv := by
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
  rw [quasiReflection_mulVec, hs, hv]
  simp [hxy]

end unitaryGroupOf

end Field

end Matrix
