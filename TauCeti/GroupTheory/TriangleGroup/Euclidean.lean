/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Euclidean triangle groups are infinite

The triangle group `Δ(a, b, c)` is *Euclidean* when `1/a + 1/b + 1/c = 1`; for positive
parameters these are `(3, 3, 3)`, `(2, 4, 4)`, `(2, 3, 6)` and their permutations. This file
proves that such a group is infinite, by an explicit representation by affine maps of a field.

For units `ω, η` of a field `K`, send `x` to the homothety `z ↦ ω z` about `0` and `y` to the
homothety `z ↦ η (z - 1) + 1` about `1`. Their composite `y * x` is `z ↦ ω η z + (1 - η)`, which,
when `ω η ≠ 1`, is the homothety of ratio `ω η` about the point `(1 - η) / (1 - ω η)`. So if
`ω ^ a = 1`, `η ^ b = 1` and `(ω η) ^ c = 1`, the triangle relations hold and the universal
property gives `TauCeti.TriangleGroup.affineRep : Δ(a, b, c) →* (K ≃ᵃ[K] K)`. The commutator
`x * y * x⁻¹ * y⁻¹` goes to the translation by `(ω - 1) * (1 - η)`, which is nonzero when
`ω ≠ 1` and `η ≠ 1`, and so has infinite order in characteristic zero. Hence the commutator of
`x` and `y` has infinite order in `Δ(a, b, c)`.

In the Euclidean case take `K = ℂ`, `ω = exp (2πi / a)` and `η = exp (2πi / b)`: then
`ω η = exp (2πi (1/a + 1/b)) = exp (-2πi / c)` is a primitive `c`-th root of unity, and `x`, `y`
act by rotations of the plane through `2π / a` and `2π / b` about `0` and `1`.

## Main definitions

* `TauCeti.TriangleGroup.affineRep`: the representation of `Δ(a, b, c)` by homotheties of a
  field about `0` and `1`.

## Main results

* `TauCeti.TriangleGroup.affineRep_commutator_x_y`: the commutator of `x` and `y` acts by a
  translation.
* `TauCeti.TriangleGroup.not_isOfFinOrder_commutator_x_y`: if a field of characteristic zero has
  units `ω ≠ 1`, `η ≠ 1`, `ω η ≠ 1` with `ω ^ a = η ^ b = (ω η) ^ c = 1`, then the commutator of
  `x` and `y` has infinite order in `Δ(a, b, c)`.
* `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_eq_one`: for nonzero `a, b, c` with
  `1/a + 1/b + 1/c = 1`, the triangle group `Δ(a, b, c)` is infinite.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, Remark 2.30 (the Euclidean triangle
  groups are infinite).
-/

public section

noncomputable section

open scoped commutatorElement

namespace TauCeti

namespace TriangleGroup

variable {a b c : ℕ} {K : Type*} [Field K]

/-- The representation of the triangle group `Δ(a, b, c)` by affine maps of a field `K`, sending
`x` to the homothety of ratio `ω` about `0` and `y` to the homothety of ratio `η` about `1`. It
requires `ω ^ a = 1`, `η ^ b = 1` and `(ω * η) ^ c = 1`, together with `ω * η ≠ 1`, which makes
`y * x` a homothety of ratio `ω * η` rather than a translation. -/
def affineRep (ω η : Kˣ) (hω : ω ^ a = 1) (hη : η ^ b = 1) (hωη : (ω * η) ^ c = 1)
    (hωη₁ : ω * η ≠ 1) : TriangleGroup a b c →* K ≃ᵃ[K] K :=
  lift (AffineEquiv.homothetyUnitsMulHom 0 ω) (AffineEquiv.homothetyUnitsMulHom 1 η)
    (AffineEquiv.homothetyUnitsMulHom 1 η * AffineEquiv.homothetyUnitsMulHom 0 ω)⁻¹
    (by rw [← map_pow, hω, map_one]) (by rw [← map_pow, hη, map_one])
    (by
      -- `y * x` is the homothety of ratio `ω * η` about `(1 - η) / (1 - ω * η)`.
      have hyx : AffineEquiv.homothetyUnitsMulHom (1 : K) η *
          AffineEquiv.homothetyUnitsMulHom (0 : K) ω =
            AffineEquiv.homothetyUnitsMulHom ((1 - η) / (1 - η * ω) : K) (ω * η) := by
        have h : (1 : K) - η * ω ≠ 0 := sub_ne_zero.2 fun h ↦
          hωη₁ (Units.ext (by rw [Units.val_mul, mul_comm, ← h, Units.val_one]))
        ext z
        simp only [AffineEquiv.coe_mul, Function.comp_apply,
          AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply, vsub_eq_sub,
          vadd_eq_add, smul_eq_mul, Units.val_mul]
        field_simp
        ring
      rw [inv_pow, hyx, ← map_pow, hωη, map_one, inv_one])
    (by rw [mul_assoc, inv_mul_cancel])

variable (ω η : Kˣ) (hω : ω ^ a = 1) (hη : η ^ b = 1) (hωη : (ω * η) ^ c = 1)
  (hωη₁ : ω * η ≠ 1)

@[simp]
theorem affineRep_x :
    affineRep ω η hω hη hωη hωη₁ (x a b c) = AffineEquiv.homothetyUnitsMulHom 0 ω :=
  lift_x ..

@[simp]
theorem affineRep_y :
    affineRep ω η hω hη hωη hωη₁ (y a b c) = AffineEquiv.homothetyUnitsMulHom 1 η :=
  lift_y ..

@[simp]
theorem affineRep_z :
    affineRep ω η hω hη hωη hωη₁ (z a b c) =
      (AffineEquiv.homothetyUnitsMulHom 1 η * AffineEquiv.homothetyUnitsMulHom 0 ω)⁻¹ :=
  lift_z ..

/-- The commutator `x * y * x⁻¹ * y⁻¹` acts on `K` by the translation by `(ω - 1) * (1 - η)`. -/
theorem affineRep_commutator_x_y :
    affineRep ω η hω hη hωη hωη₁ ⁅x a b c, y a b c⁆ =
      AffineEquiv.constVAdd K K (((ω : K) - 1) * (1 - η)) := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, affineRep_x,
    affineRep_y, ← map_inv, ← map_inv]
  ext z
  simp only [AffineEquiv.coe_mul, Function.comp_apply,
    AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, smul_eq_mul, Units.val_inv_eq_inv_val, AffineEquiv.constVAdd_apply]
  field_simp
  ring

/-- If a field of characteristic zero has units `ω ≠ 1`, `η ≠ 1` with `ω * η ≠ 1` and
`ω ^ a = η ^ b = (ω * η) ^ c = 1`, then the commutator of the generators `x` and `y` of the
triangle group `Δ(a, b, c)` has infinite order. -/
theorem not_isOfFinOrder_commutator_x_y [CharZero K] (ω η : Kˣ) (hω : ω ^ a = 1)
    (hη : η ^ b = 1) (hωη : (ω * η) ^ c = 1) (hωη₁ : ω * η ≠ 1) (ω₁ : ω ≠ 1) (η₁ : η ≠ 1) :
    ¬ IsOfFinOrder ⁅x a b c, y a b c⁆ := fun h ↦ by
  have hv : ((ω : K) - 1) * (1 - η) ≠ 0 := mul_ne_zero
    (sub_ne_zero.2 fun h ↦ ω₁ (Units.ext h)) (sub_ne_zero.2 fun h ↦ η₁ (Units.ext h.symm))
  -- The image of the commutator is a translation by a nonzero vector; its `n`-th power moves
  -- `0` to `n • v ≠ 0`.
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1
    ((affineRep ω η hω hη hωη hωη₁).isOfFinOrder h)
  have h0 := congr($hpow (0 : K))
  rw [affineRep_commutator_x_y, ← AffineEquiv.constVAdd_nsmul, AffineEquiv.constVAdd_apply,
    vadd_eq_add, add_zero, AffineEquiv.one_def, AffineEquiv.refl_apply] at h0
  exact smul_ne_zero hn.ne' hv h0

/-- If `1/a + 1/b + 1/c = 1` with `a, b, c` nonzero, then the commutator of the generators `x` and
`y` of the triangle group `Δ(a, b, c)` has infinite order. The witnesses are the rotations of `ℂ`
through `2π / a` about `0` and through `2π / b` about `1`. -/
theorem not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_eq_one (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1) :
    ¬ IsOfFinOrder ⁅x a b c, y a b c⁆ := by
  -- None of `a`, `b`, `c` is `1`, since the other two reciprocals are positive.
  have ha' : a ≠ 1 := by
    rintro rfl
    have : (0 : ℚ) < (b : ℚ)⁻¹ + (c : ℚ)⁻¹ := by positivity
    linarith
  have hb' : b ≠ 1 := by
    rintro rfl
    have : (0 : ℚ) < (a : ℚ)⁻¹ + (c : ℚ)⁻¹ := by positivity
    linarith
  have hc' : c ≠ 1 := by
    rintro rfl
    have : (0 : ℚ) < (a : ℚ)⁻¹ + (b : ℚ)⁻¹ := by positivity
    linarith
  have hω := Complex.isPrimitiveRoot_exp a ha
  have hη := Complex.isPrimitiveRoot_exp b hb
  -- `exp (2πi / a) * exp (2πi / b) = exp (2πi / c)⁻¹`, a primitive `c`-th root of unity.
  have hωη : Complex.exp (2 * Real.pi * Complex.I / a) * Complex.exp (2 * Real.pi * Complex.I / b)
      = (Complex.exp (2 * Real.pi * Complex.I / c))⁻¹ := by
    have hC : (a : ℂ)⁻¹ + (b : ℂ)⁻¹ = 1 - (c : ℂ)⁻¹ := by
      have := congr((($h : ℚ) : ℂ))
      push_cast at this
      linear_combination this
    rw [← Complex.exp_add, ← Complex.exp_neg, div_eq_mul_inv, div_eq_mul_inv, ← mul_add, hC,
      mul_sub, mul_one, sub_eq_add_neg, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul,
      div_eq_mul_inv]
  have hζ := (Complex.isPrimitiveRoot_exp c hc).inv
  rw [← hωη] at hζ
  let ω : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (2 * Real.pi * Complex.I / a))
  let η : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (2 * Real.pi * Complex.I / b))
  exact not_isOfFinOrder_commutator_x_y ω η (by ext; simpa [ω] using hω.pow_eq_one)
    (by ext; simpa [η] using hη.pow_eq_one) (by ext; simpa [ω, η] using hζ.pow_eq_one)
    (fun h ↦ hζ.ne_one (by omega) (by simpa [ω, η] using congr(($h : ℂ))))
    (fun h ↦ hω.ne_one (by omega) (by simpa [ω] using congr(($h : ℂ))))
    (fun h ↦ hη.ne_one (by omega) (by simpa [η] using congr(($h : ℂ))))

/-- **The Euclidean triangle groups are infinite.** If `1/a + 1/b + 1/c = 1` with `a, b, c`
nonzero, that is for `(a, b, c)` a permutation of `(3, 3, 3)`, `(2, 4, 4)` or `(2, 3, 6)`, then
the triangle group `Δ(a, b, c)` is infinite. -/
theorem infinite_of_inv_add_inv_add_inv_eq_one (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1) : Infinite (TriangleGroup a b c) := by
  rw [← not_finite_iff_infinite]
  intro
  exact not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_eq_one ha hb hc h
    (isOfFinOrder_of_finite _)

end TriangleGroup

end TauCeti
