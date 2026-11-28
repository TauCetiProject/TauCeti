/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
public import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection
public import TauCeti.Algebra.Star.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.Star.Pi
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Admissible unitary transvections in the unitary group of a Hermitian matrix

Let `R` be a commutative semiring with involution `star`, `A` a Hermitian matrix over `R` and
`⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y` its form. For a vector `v` and a scalar `a`, the unitary transvection
`τ_{v,a} = 1 + a • v (star v ᵥ* A) : x ↦ x + a ⟨v, x⟩ v` is
`Matrix.unitaryTransvection A (starRingEnd R) v a`. It preserves the form when the coefficient
`a + star a + a star a ⟨v, v⟩` of its isometry defect vanishes; call such a parameter `a`
admissible for `v`, and `τ_{v,a}` an admissible transvection. For isotropic `v` the admissible
parameters are those with `a + star a = 0`, giving the unitary transvections. This file bundles
the admissible transvections as elements of `Matrix.unitaryGroupOf A`; `A` need not be invertible.
The inverse of `τ_{v,a}` is `τ_{v,star a}`, by the product formula
`Matrix.unitaryTransvection_mul_unitaryTransvection_eq`.

Over a field, with the convention `0⁻¹ = 0`, the parameter `a = -s⁻¹` is admissible whenever
`s + star s = ⟨v, v⟩`. For `s ≠ 0` this is the quasi-reflection `x ↦ x - s⁻¹ ⟨v, x⟩ v`; for
`s = 0` it is the identity. If `2 ≠ 0`, the choice `s = ⟨v, v⟩ / 2` gives
`Matrix.unitaryGroupOf.reflection`, defined for every vector `v`: the reflection in `v` when
`⟨v, v⟩ ≠ 0`, and the identity when `v` is isotropic.

Over a field in which `2 ≠ 0`, the transvection along `x - y` with parameter
`(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹` is admissible for every `x` and `y`
(`Matrix.unitaryGroupOf.orbitSection`). Where the denominator is nonzero it is a quasi-reflection,
and where the denominator vanishes it is the identity. When `⟨x, x⟩ = ⟨y, y⟩` and the denominator
is nonzero, it sends `y` to `x`. Its entries on the nonvanishing locus are rational functions of
the coordinates and their conjugates. For isotropic `y`, this gives smooth local sections of the
isotropic orbit over `ℝ` and `ℂ`.

## Main definitions

* `Matrix.unitaryGroupOf.unitaryTransvection`: the admissible transvection `τ_{v,a}` as an element
  of `unitaryGroupOf A`, for Hermitian `A` and admissible `a`.
* `Matrix.unitaryGroupOf.reflection`: when `2 ≠ 0`, the reflection in non-isotropic `v`, extended
  by the identity to isotropic `v`; in characteristic two it is always the identity.
* `Matrix.unitaryGroupOf.orbitSection`: the admissible transvection along `x - y` with parameter
  `(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹`, assuming `2 ≠ 0`; a quasi-reflection where the
  denominator is nonzero and the identity where it vanishes.

## Main results

* `Matrix.unitaryGroupOf.inv_unitaryTransvection`: the inverse of `τ_{v,a}` is `τ_{v,star a}`.
* `Matrix.unitaryGroupOf.unitaryTransvection_mulVec`: `τ_{v,a}` sends `x` to `x + a ⟨v, x⟩ v`.
* `Matrix.unitaryGroupOf.reflection_mulVec_self` and
  `Matrix.unitaryGroupOf.reflection_mulVec_of_dotProduct_eq_zero`: the reflection in a
  non-isotropic `v` sends `v` to `-v` and fixes the vectors orthogonal to `v`.
* `Matrix.unitaryGroupOf.inv_reflection` and
  `Matrix.unitaryGroupOf.reflection_eq_one_of_dotProduct_self_eq_zero`: the reflection is an
  involution, and is the identity at isotropic vectors.
* `Matrix.unitaryGroupOf.orbitSection_mulVec`: the orbit section sends `y` to every `x` of the
  same Hermitian norm with nonzero denominator.

## Attribution

Quasi-reflections and their use to carry one isotropic vector to another follow
`New.quasiReflection` and `New.exists_quasiReflection_mulVec_eq` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/WittTheorem.lean`; the module-level version is
`TauCeti.SignedHermitianSpace.quasiReflection`. The parameter
`(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹`, which keeps the transvection unitary away from the
equal-norm locus too, is particular to this file.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Ergebnisse der Mathematik 5, Springer
  (1955).
* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften 270,
  Springer (1985), Chapter 7.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommSemiring

variable {R : Type*} [CommSemiring R] [StarRing R] {A : Matrix n n R} {v : n → R} {a : R}

namespace unitaryGroupOf

/-- **The admissible transvection `τ_{v,a}` as an element of the unitary group** of a Hermitian
matrix `A`, for a parameter `a` with `a + star a + a * star a * ⟨v, v⟩ = 0`. It acts by
`x ↦ x + a ⟨v, x⟩ v` (`unitaryTransvection_mulVec`), and its inverse is `τ_{v,star a}`
(`inv_unitaryTransvection`). -/
def unitaryTransvection (hA : A.IsHermitian) (v : n → R) (a : R)
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) : unitaryGroupOf A :=
  ⟨Units.mkOfMulEqOne _ _
      (unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero ha),
    mem_unitaryGroupOf_iff.2 (star_unitaryTransvection_mul_mul_self_of_eq_zero hA ha)⟩

variable (hA : A.IsHermitian) (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0)

/-- The matrix of the unitary transvection `τ_{v,a}` in the unitary group. -/
@[simp]
theorem val_unitaryTransvection :
    ((unitaryTransvection hA v a ha : GL n R) : Matrix n n R) =
      A.unitaryTransvection (starRingEnd R) v a :=
  Units.val_mkOfMulEqOne _

/-- The inverse of the unitary transvection `τ_{v,a}` is `τ_{v,star a}`. -/
@[simp]
theorem inv_unitaryTransvection :
    (unitaryTransvection hA v a ha)⁻¹ =
      unitaryTransvection hA v (star a)
        (TauCeti.add_star_add_mul_eq_zero_star ha) := by
  apply inv_eq_of_mul_eq_one_right
  apply unitaryGroupOf.ext
  simpa only [Subgroup.coe_mul, Units.val_mul, val_unitaryTransvection,
    Subgroup.coe_one, Units.val_one] using
    unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero ha

/-- The unitary transvection `τ_{v,a}` sends `x` to `x + a ⟨v, x⟩ v`. -/
theorem unitaryTransvection_mulVec (x : n → R) :
    ((unitaryTransvection hA v a ha : GL n R) : Matrix n n R) *ᵥ x =
      x + (a * (star v ⬝ᵥ A *ᵥ x)) • v := by
  rw [val_unitaryTransvection, Matrix.unitaryTransvection_mulVec,
    TauCeti.starRingEnd_comp_eq_star]

/-- A zero parameter gives the identity element of the unitary group. -/
@[simp]
theorem unitaryTransvection_zero (v : n → R) :
    unitaryTransvection hA v 0 (by simp) = 1 := by
  apply unitaryGroupOf.ext
  simp

/-- A zero direction gives the identity for parameters satisfying `a + star a = 0`. -/
@[simp]
theorem unitaryTransvection_zero_left (a : R) (ha : a + star a = 0) :
    unitaryTransvection hA 0 a (by simpa using ha) = 1 := by
  apply unitaryGroupOf.ext
  simp

/-- Rescaling the direction transports admissibility and multiplies the parameter by the norm
`c * star c` of the scaling factor. -/
theorem unitaryTransvection_smul (c a : R)
    (ha : a + star a + a * star a * (star (c • v) ⬝ᵥ A *ᵥ (c • v)) = 0) :
    unitaryTransvection hA (c • v) a ha =
      unitaryTransvection hA v (a * c * star c) (by
        rw [← TauCeti.starRingEnd_comp_eq_star,
          comp_smul_dotProduct_mulVec_smul, starRingEnd_apply,
          TauCeti.starRingEnd_comp_eq_star] at ha
        calc
          _ = c * star c *
              (a + star a + a * star a * (star c * c * (star v ⬝ᵥ A *ᵥ v))) := by
            simp only [star_mul, star_star]
            ring
          _ = 0 := by rw [ha, mul_zero]) := by
  apply unitaryGroupOf.ext
  simp only [val_unitaryTransvection, Matrix.unitaryTransvection_smul, starRingEnd_apply]

/-- The product of two admissible transvections along the same vector is a transvection. -/
theorem unitaryTransvection_mul_unitaryTransvection {b : R}
    (hb : b + star b + b * star b * (star v ⬝ᵥ A *ᵥ v) = 0) :
    unitaryTransvection hA v a ha * unitaryTransvection hA v b hb =
      unitaryTransvection hA v (a + b + a * b * (star v ⬝ᵥ A *ᵥ v))
        (TauCeti.add_star_add_mul_eq_zero_add_add_mul
          (hA.star_dotProduct_mulVec_comm v v) ha hb) := by
  apply unitaryGroupOf.ext
  simp only [Subgroup.coe_mul, Units.val_mul, val_unitaryTransvection,
    Matrix.unitaryTransvection_mul_unitaryTransvection_eq, TauCeti.starRingEnd_comp_eq_star]

end unitaryGroupOf

end CommSemiring

section Field

variable {K : Type*} [Field K] [StarRing K] {A : Matrix n n K}

namespace unitaryGroupOf

/-- **The reflection in a vector**, for a Hermitian Gram matrix `A`: the admissible transvection
`1 - (2 / ⟨v, v⟩) • v (star v ᵥ* A)` in `unitaryGroupOf A`, defined for every `v`. For
non-isotropic `v` and `2 ≠ 0`, this is the usual reflection: it sends `v` to `-v`
(`reflection_mulVec_self`) and fixes the vectors orthogonal to `v` for the form
(`reflection_mulVec_of_dotProduct_eq_zero`). For isotropic `v` it is the
identity (`reflection_eq_one_of_dotProduct_self_eq_zero`). In characteristic two it is the
identity for every `v`, including non-isotropic vectors. -/
noncomputable def reflection (hA : A.IsHermitian) (v : n → K) : unitaryGroupOf A :=
  unitaryTransvection hA v (-(2 / (star v ⬝ᵥ A *ᵥ v)))
    (TauCeti.neg_two_div_add_star_add_mul_eq_zero (hA.star_dotProduct_mulVec_comm v v))

@[simp]
theorem val_reflection (hA : A.IsHermitian) (v : n → K) :
    ((reflection hA v : GL n K) : Matrix n n K) =
      1 - (2 / (star v ⬝ᵥ A *ᵥ v)) • vecMulVec v (star v ᵥ* A) := by
  simp [reflection, Matrix.unitaryTransvection_def, TauCeti.starRingEnd_comp_eq_star,
    sub_eq_add_neg]

/-- The reflection in `v` sends `x` to `x - (2 ⟨v, x⟩ / ⟨v, v⟩) v`. -/
theorem reflection_mulVec (hA : A.IsHermitian) (v : n → K) (x : n → K) :
    ((reflection hA v : GL n K) : Matrix n n K) *ᵥ x =
      x - (2 / (star v ⬝ᵥ A *ᵥ v) * (star v ⬝ᵥ A *ᵥ x)) • v := by
  rw [reflection, unitaryTransvection_mulVec]
  simp [sub_eq_add_neg]

/-- The reflection in a non-isotropic vector `v`, `⟨v, v⟩ ≠ 0`, sends `v` to `-v`. -/
theorem reflection_mulVec_self (hA : A.IsHermitian) (v : n → K)
    (hv : star v ⬝ᵥ A *ᵥ v ≠ 0) :
    ((reflection hA v : GL n K) : Matrix n n K) *ᵥ v = -v := by
  rw [reflection_mulVec]
  simp [div_mul_cancel₀ _ hv, two_smul]

/-- The reflection in `v` fixes every vector `w` orthogonal to `v` for the form. -/
theorem reflection_mulVec_of_dotProduct_eq_zero (hA : A.IsHermitian) (v : n → K)
    {w : n → K} (hw : star v ⬝ᵥ A *ᵥ w = 0) :
    ((reflection hA v : GL n K) : Matrix n n K) *ᵥ w = w := by
  rw [reflection, val_unitaryTransvection]
  exact Matrix.unitaryTransvection_mulVec_of_dotProduct_eq_zero _
    (by rwa [TauCeti.starRingEnd_comp_eq_star])

/-- The reflection in an isotropic vector is the identity. -/
@[simp]
theorem reflection_eq_one_of_dotProduct_self_eq_zero (hA : A.IsHermitian) {v : n → K}
    (hv : star v ⬝ᵥ A *ᵥ v = 0) : reflection hA v = 1 := by
  apply unitaryGroupOf.ext
  simp [hv]

/-- The reflection depends only on the line of its direction: a nonzero rescaling leaves it
unchanged. -/
theorem reflection_smul (hA : A.IsHermitian) (v : n → K) {c : K} (hc : c ≠ 0) :
    reflection hA (c • v) = reflection hA v := by
  rw [reflection, unitaryTransvection_smul]
  congr 1
  rw [← TauCeti.starRingEnd_comp_eq_star, comp_smul_dotProduct_mulVec_smul,
    starRingEnd_apply, TauCeti.starRingEnd_comp_eq_star]
  by_cases hv : star v ⬝ᵥ A *ᵥ v = 0
  · simp [hv]
  · have hsc : star c ≠ 0 := star_ne_zero.mpr hc
    field_simp

/-- The reflection in `v` is its own inverse. -/
@[simp]
theorem inv_reflection (hA : A.IsHermitian) (v : n → K) :
    (reflection hA v)⁻¹ = reflection hA v := by
  rw [reflection, inv_unitaryTransvection]
  congr 1
  rw [star_neg, star_div₀, star_ofNat, hA.star_dotProduct_mulVec_comm v v]

/-- Two consecutive reflections in the same direction cancel. -/
@[simp]
theorem reflection_mul_reflection (hA : A.IsHermitian) (v : n → K) :
    reflection hA v * reflection hA v = 1 := by
  simpa only [inv_reflection] using inv_mul_cancel (reflection hA v)

/-- In characteristic two every bundled reflection is the identity. -/
@[simp]
theorem reflection_eq_one_of_char_two [CharP K 2] (hA : A.IsHermitian) (v : n → K) :
    reflection hA v = 1 := by
  apply unitaryGroupOf.ext
  simp [CharTwo.two_eq_zero]

end unitaryGroupOf

end Field

section NeZeroTwo

variable {K : Type*} [Field K] [StarRing K] [NeZero (2 : K)] {A : Matrix n n K} {y : n → K}

omit [DecidableEq n] in
/-- For Hermitian `A` and `2 ≠ 0`, the parameter
`(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹` is admissible for `x - y`. -/
private theorem orbitSection_param_admissible (hA : A.IsHermitian)
    (y x : n → K) :
    (star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2)⁻¹ +
      star (star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2)⁻¹ +
      (star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2)⁻¹ *
        star (star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2)⁻¹ *
        (star (x - y) ⬝ᵥ A *ᵥ (x - y)) = 0 := by
  set b := star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2 with hb_def
  -- The scalar `b` satisfies `b + star b + ⟨x - y, x - y⟩ = 0`, so its inverse is admissible.
  have hb : b + star b + star (x - y) ⬝ᵥ A *ᵥ (x - y) = 0 := by
    have hsb : star b = star y ⬝ᵥ A *ᵥ x - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2 := by
      simp [hb_def, hA.star_dotProduct_mulVec_comm x x,
        hA.star_dotProduct_mulVec_comm x y, hA.star_dotProduct_mulVec_comm y y]
    have hc : star (x - y) ⬝ᵥ A *ᵥ (x - y) =
        star x ⬝ᵥ A *ᵥ x - star x ⬝ᵥ A *ᵥ y - star y ⬝ᵥ A *ᵥ x +
          star y ⬝ᵥ A *ᵥ y := by
      simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
      ring
    rw [hsb, hc, hb_def]
    field_simp
    ring
  exact TauCeti.inv_add_star_inv_add_mul_eq_zero_of_add_star_add_eq_zero hb

namespace unitaryGroupOf

/-- **A section of an equal-norm orbit by admissible transvections.** For Hermitian `A` and
`2 ≠ 0`, the transvection along `x - y` with parameter
`(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹` belongs to `unitaryGroupOf A` for every `x` and `y`.
It is a quasi-reflection where the denominator is nonzero, and the identity where it vanishes
(`orbitSection_eq_one_of_denominator_eq_zero`). When `⟨x, x⟩ = ⟨y, y⟩` and the denominator is
nonzero, it sends `y` to `x` (`orbitSection_mulVec`). -/
noncomputable def orbitSection (hA : A.IsHermitian) (y x : n → K) :
    unitaryGroupOf A :=
  unitaryTransvection hA (x - y) _
    (orbitSection_param_admissible hA y x)

/-- The matrix of the orbit section at `x` is the unitary transvection along `x - y` with parameter
`(⟨x, y⟩ - (⟨x, x⟩ + ⟨y, y⟩) / 2)⁻¹`. -/
@[simp]
theorem val_orbitSection (hA : A.IsHermitian) (y x : n → K) :
    ((orbitSection hA y x : GL n K) : Matrix n n K) =
      A.unitaryTransvection (starRingEnd K) (x - y)
        (star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2)⁻¹ := by
  unfold orbitSection
  exact val_unitaryTransvection _ _

/-- The total orbit section is the identity where its denominator vanishes. -/
@[simp]
theorem orbitSection_eq_one_of_denominator_eq_zero (hA : A.IsHermitian)
    {y x : n → K}
    (hx : star x ⬝ᵥ A *ᵥ y - (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2 = 0) :
    orbitSection hA y x = 1 := by
  apply unitaryGroupOf.ext
  simp [hx]

/-- **The orbit section carries `y` to `x`** when their Hermitian norms agree and its denominator
is nonzero. -/
theorem orbitSection_mulVec (hA : A.IsHermitian) {y x : n → K}
    (hx : star x ⬝ᵥ A *ᵥ x = star y ⬝ᵥ A *ᵥ y)
    (hxy : star x ⬝ᵥ A *ᵥ y -
      (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2 ≠ 0) :
    ((orbitSection hA y x : GL n K) : Matrix n n K) *ᵥ y = x := by
  rw [val_orbitSection]
  apply Matrix.unitaryTransvection_sub_mulVec_eq
  have hhalf : (star x ⬝ᵥ A *ᵥ x + star y ⬝ᵥ A *ᵥ y) / 2 =
      star y ⬝ᵥ A *ᵥ y := by rw [hx, ← two_mul, mul_div_cancel_left₀ _ (NeZero.ne 2)]
  simpa only [TauCeti.starRingEnd_comp_eq_star, star_sub, sub_dotProduct, hhalf] using
    inv_mul_cancel₀ hxy

end unitaryGroupOf

end NeZeroTwo

end Matrix
