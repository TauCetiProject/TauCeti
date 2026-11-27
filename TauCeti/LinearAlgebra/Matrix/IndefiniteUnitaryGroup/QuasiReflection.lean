/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Field.Basic
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.Tactic.FieldSimp

/-!
# Quasi-reflections in the unitary group of a Hermitian matrix

Let `A` be a Hermitian matrix over a field `K` with an involution `star`, and write
`⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y` for its form, conjugate-linear in the first slot. For a vector `v` and
a scalar `s` with `s + star s = ⟨v, v⟩`, the **quasi-reflection** along `v` with parameter `s` is

`x ↦ x - s⁻¹ ⟨v, x⟩ v`,

the matrix `1 - s⁻¹ • v (star v ᵥ* A)` (`Matrix.unitaryGroupOf.quasiReflection`), which is the
unitary transvection `Matrix.unitaryTransvection A (starRingEnd K) v (-s⁻¹)`. It preserves
the form, and it is invertible with inverse the quasi-reflection along `v` with parameter
`star s`, so it lies in `Matrix.unitaryGroupOf A` even when `A` is not invertible. For
`2 ≠ 0`, `⟨v, v⟩ ≠ 0` and `s = ⟨v, v⟩ / 2` it is the reflection
`Matrix.unitaryGroupOf.reflection` in `v`; for isotropic `v` and `s + star s = 0` it is a unitary
transvection. This is the matrix form of the quasi-reflections
`TauCeti.SignedHermitianSpace.quasiReflection` of a signed Hermitian space.

The parameter is what makes quasi-reflections suited to carrying isotropic vectors explicitly.
If `2 ≠ 0`, `y` is isotropic and `x` is any vector, then `v = x - y` and
`s = ⟨x, x⟩ / 2 - ⟨x, y⟩` satisfy `s + star s = ⟨v, v⟩`, and when `x` is isotropic too with
`⟨x, y⟩ ≠ 0` the quasi-reflection sends `y` to `x`
(`Matrix.unitaryGroupOf.quasiReflection_sub_mulVec_of_isotropic`). The parameter is a
polynomial in the coordinates of `x` and their conjugates, so over `ℝ` or `ℂ` this element of
`unitaryGroupOf A` depends smoothly on `x` where `s ≠ 0`; this gives the smooth local sections of
the isotropic orbit in `TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup.IsotropicSection`.

## Main definitions

* `Matrix.unitaryGroupOf.quasiReflection`: the quasi-reflection along `v` with parameter `s`.

The form identity and the product formula behind these facts are those of unitary
transvections, `Matrix.star_unitaryTransvection_mul_mul_self_of_eq_zero` (in
`TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup`, where it also gives the reflections) and
`Matrix.unitaryTransvection_mul_unitaryTransvection_eq`.

## Main results

* `Matrix.unitaryGroupOf.quasiReflection_mulVec`: the quasi-reflection sends `x` to
  `x - s⁻¹ ⟨v, x⟩ v`.
* `Matrix.unitaryGroupOf.inv_quasiReflection`: its inverse is the quasi-reflection with parameter
  `star s`.
* `Matrix.unitaryGroupOf.quasiReflection_eq_reflection`: when `2 ≠ 0`, for `s = ⟨v, v⟩ / 2` it is
  the reflection.
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

/-- For `a + b = ⟨v, v⟩` with `a` and `b` vanishing together, the unitary transvections
`τ_{v,-a⁻¹}` and `τ_{v,-b⁻¹}` are inverse to each other. -/
private theorem unitaryTransvection_neg_inv_mul_unitaryTransvection_neg_inv {v : n → K} {a b : K}
    (hab : a + b = star v ⬝ᵥ A *ᵥ v) (h0 : a = 0 ↔ b = 0) :
    A.unitaryTransvection (starRingEnd K) v (-a⁻¹) *
      A.unitaryTransvection (starRingEnd K) v (-b⁻¹) = 1 := by
  rw [unitaryTransvection_mul_unitaryTransvection_eq]
  exact (congrArg _ (TauCeti.neg_inv_add_neg_inv_add_neg_inv_mul_neg_inv_mul_eq_zero hab h0)).trans
    unitaryTransvection_zero

namespace unitaryGroupOf

/-- **The quasi-reflection** along `v` with parameter `s`, for a Hermitian matrix `A` and a scalar
`s` with `s + star s = ⟨v, v⟩`: the element `x ↦ x - s⁻¹ ⟨v, x⟩ v` of `unitaryGroupOf A`, whose
matrix `1 - s⁻¹ • v (star v ᵥ* A)` is the unitary transvection
`Matrix.unitaryTransvection A (starRingEnd K) v (-s⁻¹)` (`val_quasiReflection`). Its inverse is the
quasi-reflection with parameter `star s` (`inv_quasiReflection`). -/
noncomputable def quasiReflection (hA : A.IsHermitian) (v : n → K) (s : K)
    (hs : s + star s = star v ⬝ᵥ A *ᵥ v) : unitaryGroupOf A :=
  ⟨⟨A.unitaryTransvection (starRingEnd K) v (-s⁻¹),
      A.unitaryTransvection (starRingEnd K) v (-(star s)⁻¹),
      unitaryTransvection_neg_inv_mul_unitaryTransvection_neg_inv hs star_eq_zero.symm,
      unitaryTransvection_neg_inv_mul_unitaryTransvection_neg_inv (by rw [add_comm, hs])
        star_eq_zero⟩,
    mem_unitaryGroupOf_iff.mpr <| star_unitaryTransvection_mul_mul_self_of_eq_zero hA (by
      rw [star_neg, star_inv₀]
      exact TauCeti.neg_inv_add_neg_inv_add_neg_inv_mul_neg_inv_mul_eq_zero hs star_eq_zero.symm)⟩

variable (hA : A.IsHermitian) (v : n → K) (s : K) (hs : s + star s = star v ⬝ᵥ A *ᵥ v)

@[simp]
theorem val_quasiReflection :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) =
      A.unitaryTransvection (starRingEnd K) v (-s⁻¹) :=
  (rfl)

/-- The quasi-reflection along `v` with parameter `s` sends `x` to `x - s⁻¹ ⟨v, x⟩ v`. -/
theorem quasiReflection_mulVec (x : n → K) :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) *ᵥ x =
      x - (s⁻¹ * (star v ⬝ᵥ A *ᵥ x)) • v := by
  rw [val_quasiReflection, unitaryTransvection_mulVec, neg_mul, neg_smul, ← sub_eq_add_neg,
    TauCeti.starRingEnd_comp_eq_star]

/-- The quasi-reflection along `v` fixes every vector orthogonal to `v` for the form. -/
theorem quasiReflection_mulVec_of_dotProduct_eq_zero {x : n → K} (hx : star v ⬝ᵥ A *ᵥ x = 0) :
    ((quasiReflection hA v s hs : GL n K) : Matrix n n K) *ᵥ x = x := by
  rw [quasiReflection_mulVec, hx, mul_zero, zero_smul, sub_zero]

/-- The inverse of the quasi-reflection along `v` with parameter `s` is the quasi-reflection
along `v` with parameter `star s`. -/
@[simp]
theorem inv_quasiReflection :
    (quasiReflection hA v s hs)⁻¹ =
      quasiReflection hA v (star s) (by rw [star_star, add_comm, hs]) := by
  ext : 1
  rfl

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
