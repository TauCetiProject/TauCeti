/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
public import TauCeti.LinearAlgebra.Matrix.UnitaryTransvection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Star.Pi

/-!
# Unitary transvections and quasi-reflections in the unitary group of a Hermitian matrix

Let `R` be a commutative semiring with involution `star`, `A` a Hermitian matrix over `R` and
`⟨x, y⟩ = star x ⬝ᵥ A *ᵥ y` its form. For a vector `v` and a scalar `a`, the unitary transvection
`τ_{v,a} = 1 + a • v (star v ᵥ* A) : x ↦ x + a ⟨v, x⟩ v` is
`Matrix.unitaryTransvection A (starRingEnd R) v a`. It preserves the form when the coefficient
`a + star a + a star a ⟨v, v⟩` of its isometry defect vanishes; call such a parameter `a`
admissible for `v`. For isotropic `v` the admissible parameters are those with `a + star a = 0`,
giving the unitary transvections. Over a field, `a = -s⁻¹` is admissible whenever
`s + star s = ⟨v, v⟩`, giving the quasi-reflections `x ↦ x - s⁻¹ ⟨v, x⟩ v`; if `2 ≠ 0` and
`⟨v, v⟩ ≠ 0`, the choice `s = ⟨v, v⟩ / 2` gives the reflection in `v`. This file bundles the
admissible unitary transvections as elements of `Matrix.unitaryGroupOf A`; `A` need not be
invertible. The inverse of `τ_{v,a}` is `τ_{v,star a}`, by the product formula
`Matrix.unitaryTransvection_mul_unitaryTransvection_eq`.

Over a field in which `2 ≠ 0`, one quasi-reflection carries an isotropic vector `y` to any
isotropic `x` with `⟨x, y⟩ ≠ 0`: it is the transvection along `x - y` with parameter
`(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹`, which is admissible for every `x`, isotropic or not
(`Matrix.unitaryGroupOf.orbitSection`). As a function of `x` it is a section of the orbit map
`g ↦ g y` over these isotropic vectors, given by rational functions of the coordinates of `x` and
their conjugates; this is how smooth local sections of the isotropic orbit are obtained over `ℝ`
and `ℂ`.

## Main definitions

* `Matrix.unitaryGroupOf.unitaryTransvection`: the element `τ_{v,a}` of `unitaryGroupOf A`, for
  Hermitian `A` and admissible `a`.
* `Matrix.unitaryGroupOf.orbitSection`: the quasi-reflection along `x - y` with parameter
  `(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹`, for isotropic `y`.

## Main results

* `Matrix.star_unitaryTransvection_mul_mul_self_of_eq_zero`: `star τ_{v,a} * A * τ_{v,a} = A` for
  Hermitian `A` and admissible `a`.
* `Matrix.unitaryGroupOf.inv_unitaryTransvection`: the inverse of `τ_{v,a}` is `τ_{v,star a}`.
* `Matrix.unitaryGroupOf.unitaryTransvection_mulVec`: `τ_{v,a}` sends `x` to `x + a ⟨v, x⟩ v`.
* `Matrix.unitaryTransvection_sub_mulVec_eq`: if `a B(x - y, y) = 1`, the raw transvection
  `τ_{x - y,a}` sends `y` to `x`.
* `Matrix.unitaryGroupOf.orbitSection_mulVec`: the orbit section sends `y` to every isotropic `x`
  with `⟨x, y⟩ ≠ 0`.

## Attribution

Quasi-reflections and their use to carry one isotropic vector to another follow
`New.quasiReflection` and `New.exists_quasiReflection_mulVec_eq` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/WittTheorem.lean`; the module-level version is
`TauCeti.SignedHermitianSpace.quasiReflection`. The parameter `(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹`, which
keeps the quasi-reflection unitary off the isotropic cone, is particular to this file.

## References

* J. Dieudonné, *La géométrie des groupes classiques*, Ergebnisse der Mathematik 5, Springer
  (1955).
* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften 270,
  Springer (1985), Chapter 7.
-/

public section

namespace TauCeti

/-- Inverting a scalar with `b + star b + c = 0` gives an admissible parameter for `c`,
including at `b = 0` with the field's total inverse. -/
theorem inv_param_admissible {K : Type*} [Field K] [StarRing K] {b c : K}
    (h : b + star b + c = 0) : b⁻¹ + star (b⁻¹) + b⁻¹ * star (b⁻¹) * c = 0 := by
  rw [star_inv₀]
  rcases eq_or_ne b 0 with h0 | h0
  · simp [h0]
  · have h0' : star b ≠ 0 := star_ne_zero.mpr h0
    field_simp
    linear_combination h

end TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommSemiring

variable {R : Type*} [CommSemiring R] [StarRing R] {A : Matrix n n R} {v : n → R} {a : R}

/-- **Admissible unitary transvections preserve a Hermitian form.** For Hermitian `A`, the unitary
transvection `τ_{v,a} = 1 + a • v (star v ᵥ* A)` satisfies `star τ_{v,a} * A * τ_{v,a} = A` when
`a + star a + a * star a * ⟨v, v⟩ = 0`. This is
`Matrix.transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero` for `σ = starRingEnd R` and
`ε = 1`. -/
theorem star_unitaryTransvection_mul_mul_self_of_eq_zero (hA : A.IsHermitian)
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) :
    star (A.unitaryTransvection (starRingEnd R) v a) * A *
      A.unitaryTransvection (starRingEnd R) v a = A := by
  have h := transpose_map_unitaryTransvection_mul_mul_self_of_eq_zero (v := v) (a := a)
    starRingEnd_self_apply (by rw [one_smul, transpose_map_starRingEnd, hA.eq])
    (by rwa [one_mul, one_mul, TauCeti.starRingEnd_comp_eq_star, starRingEnd_apply])
  rwa [transpose_map_starRingEnd, ← star_eq_conjTranspose] at h

/-- For admissible `a`, the unitary transvection `τ_{v,star a}` inverts `τ_{v,a}`. -/
theorem unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) :
    A.unitaryTransvection (starRingEnd R) v a * A.unitaryTransvection (starRingEnd R) v (star a) =
      1 := by
  rw [unitaryTransvection_mul_unitaryTransvection_eq, TauCeti.starRingEnd_comp_eq_star, ha,
    unitaryTransvection_zero]

omit [DecidableEq n] in
/-- The parameter `star a` is admissible for `v` when `a` is. -/
private theorem unitaryTransvection_star_param_admissible
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) :
    star a + star (star a) + star a * star (star a) * (star v ⬝ᵥ A *ᵥ v) = 0 := by
  rw [star_star, add_comm (star a), mul_comm (star a), ha]

namespace unitaryGroupOf

/-- **The unitary transvection, or quasi-reflection, `τ_{v,a}` as an element of the unitary group**
of a Hermitian matrix `A`, for a parameter `a` with `a + star a + a * star a * ⟨v, v⟩ = 0`. It acts
by `x ↦ x + a ⟨v, x⟩ v` (`unitaryTransvection_mulVec`), and its inverse is `τ_{v,star a}`
(`inv_unitaryTransvection`). -/
def unitaryTransvection (hA : A.IsHermitian) (v : n → R) (a : R)
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0) : unitaryGroupOf A :=
  have hinv := unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero ha
  ⟨⟨_, _, hinv, by
      simpa only [star_star] using
        unitaryTransvection_mul_unitaryTransvection_star_param_eq_one_of_eq_zero
          (unitaryTransvection_star_param_admissible ha)⟩,
    mem_unitaryGroupOf_iff.2 (star_unitaryTransvection_mul_mul_self_of_eq_zero hA ha)⟩

variable (hA : A.IsHermitian) (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0)

/-- The matrix of the unitary transvection `τ_{v,a}` in the unitary group. -/
@[simp]
theorem val_unitaryTransvection :
    ((unitaryTransvection hA v a ha : GL n R) : Matrix n n R) =
      A.unitaryTransvection (starRingEnd R) v a :=
  (rfl)

/-- The inverse of the unitary transvection `τ_{v,a}` is `τ_{v,star a}`. -/
@[simp]
theorem inv_unitaryTransvection :
    (unitaryTransvection hA v a ha)⁻¹ =
      unitaryTransvection hA v (star a)
        (by exact unitaryTransvection_star_param_admissible ha) := by
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

/-- A zero direction gives the identity element of the unitary group. -/
@[simp]
theorem unitaryTransvection_zero_left (a : R) (ha : a + star a = 0) :
    unitaryTransvection hA 0 a (by simpa using ha) = 1 := by
  apply unitaryGroupOf.ext
  simp

omit [DecidableEq n] in
private theorem unitaryTransvection_mul_param_admissible (hA : A.IsHermitian) {b : R}
    (ha : a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v) = 0)
    (hb : b + star b + b * star b * (star v ⬝ᵥ A *ᵥ v) = 0) :
    let d := a + b + a * b * (star v ⬝ᵥ A *ᵥ v)
    d + star d + d * star d * (star v ⬝ᵥ A *ᵥ v) = 0 := by
  dsimp only
  simp only [star_add, star_mul, hA.star_dotProduct_mulVec_comm v v]
  calc
    _ = (1 + (b + star b) * (star v ⬝ᵥ A *ᵥ v) +
        b * star b * (star v ⬝ᵥ A *ᵥ v) ^ 2) *
        (a + star a + a * star a * (star v ⬝ᵥ A *ᵥ v)) +
        (b + star b + b * star b * (star v ⬝ᵥ A *ᵥ v)) := by ring
    _ = 0 := by rw [ha, hb, mul_zero, add_zero]

/-- The product of two admissible transvections along the same vector is a transvection. -/
theorem unitaryTransvection_mul_unitaryTransvection {b : R}
    (hb : b + star b + b * star b * (star v ⬝ᵥ A *ᵥ v) = 0) :
    unitaryTransvection hA v a ha * unitaryTransvection hA v b hb =
      unitaryTransvection hA v (a + b + a * b * (star v ⬝ᵥ A *ᵥ v))
        (by exact unitaryTransvection_mul_param_admissible hA ha hb) := by
  apply unitaryGroupOf.ext
  simp only [Subgroup.coe_mul, Units.val_mul, val_unitaryTransvection,
    Matrix.unitaryTransvection_mul_unitaryTransvection_eq, TauCeti.starRingEnd_comp_eq_star]

end unitaryGroupOf

end CommSemiring

section Field

variable {K : Type*} [Field K] [StarRing K] [NeZero (2 : K)] {A : Matrix n n K} {y : n → K}

omit [DecidableEq n] in
/-- For Hermitian `A` and isotropic `y`, the parameter `(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹` is admissible for
the vector `x - y`, for every `x`. -/
private theorem orbitSection_param_admissible (hA : A.IsHermitian)
    (hy : star y ⬝ᵥ A *ᵥ y = 0) (x : n → K) :
    (star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2)⁻¹ + star (star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2)⁻¹ +
      (star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2)⁻¹ *
        star (star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2)⁻¹ *
        (star (x - y) ⬝ᵥ A *ᵥ (x - y)) = 0 := by
  set b := star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2 with hb_def
  -- The scalar `b` satisfies `b + star b + ⟨x - y, x - y⟩ = 0`, so its inverse is admissible.
  have hb : b + star b + star (x - y) ⬝ᵥ A *ᵥ (x - y) = 0 := by
    have hsb : star b = star y ⬝ᵥ A *ᵥ x - star x ⬝ᵥ A *ᵥ x / 2 := by
      simp [hb_def, hA.star_dotProduct_mulVec_comm x x,
        hA.star_dotProduct_mulVec_comm x y]
    have hc : star (x - y) ⬝ᵥ A *ᵥ (x - y) =
        star x ⬝ᵥ A *ᵥ x - star x ⬝ᵥ A *ᵥ y - star y ⬝ᵥ A *ᵥ x := by
      simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub, hy]
      ring
    rw [hsb, hc, hb_def]
    field_simp
    ring
  exact TauCeti.inv_param_admissible hb

namespace unitaryGroupOf

/-- **A section of the isotropic orbit by quasi-reflections.** For Hermitian `A`, isotropic `y` and
any `x`, the unitary transvection along `x - y` with parameter `(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹`, an element
of `unitaryGroupOf A`. When `x` is isotropic and `⟨x, y⟩ ≠ 0` it sends `y` to `x`
(`orbitSection_mulVec`), so `x ↦ orbitSection hA hy x` is a section of the orbit map `g ↦ g y` over
these vectors. -/
noncomputable def orbitSection (hA : A.IsHermitian) (hy : star y ⬝ᵥ A *ᵥ y = 0) (x : n → K) :
    unitaryGroupOf A :=
  unitaryTransvection hA (x - y) _
    (orbitSection_param_admissible hA hy x)

/-- The matrix of the orbit section at `x` is the unitary transvection along `x - y` with parameter
`(⟨x, y⟩ - ⟨x, x⟩ / 2)⁻¹`. -/
@[simp]
theorem val_orbitSection (hA : A.IsHermitian) (hy : star y ⬝ᵥ A *ᵥ y = 0) (x : n → K) :
    ((orbitSection hA hy x : GL n K) : Matrix n n K) =
      A.unitaryTransvection (starRingEnd K) (x - y)
        (star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2)⁻¹ := by
  unfold orbitSection
  exact val_unitaryTransvection _ _

/-- The total orbit section is the identity where its denominator vanishes. -/
theorem orbitSection_eq_one_of_denominator_eq_zero (hA : A.IsHermitian)
    (hy : star y ⬝ᵥ A *ᵥ y = 0) {x : n → K}
    (hx : star x ⬝ᵥ A *ᵥ y - star x ⬝ᵥ A *ᵥ x / 2 = 0) : orbitSection hA hy x = 1 := by
  apply unitaryGroupOf.ext
  simp [hx]

/-- The orbit section takes its source vector to the identity element. -/
@[simp]
theorem orbitSection_self (hA : A.IsHermitian) (hy : star y ⬝ᵥ A *ᵥ y = 0) :
    orbitSection hA hy y = 1 :=
  orbitSection_eq_one_of_denominator_eq_zero hA hy (by simp [hy])

/-- **The orbit section carries `y` to `x`** for every isotropic `x` with `⟨x, y⟩ ≠ 0`. -/
theorem orbitSection_mulVec (hA : A.IsHermitian) (hy : star y ⬝ᵥ A *ᵥ y = 0) {x : n → K}
    (hx : star x ⬝ᵥ A *ᵥ x = 0) (hxy : star x ⬝ᵥ A *ᵥ y ≠ 0) :
    ((orbitSection hA hy x : GL n K) : Matrix n n K) *ᵥ y = x := by
  rw [val_orbitSection]
  apply Matrix.unitaryTransvection_sub_mulVec_eq
  simpa [TauCeti.starRingEnd_comp_eq_star, star_sub, sub_dotProduct, hx, hy] using
    inv_mul_cancel₀ hxy

end unitaryGroupOf

end Field

end Matrix
