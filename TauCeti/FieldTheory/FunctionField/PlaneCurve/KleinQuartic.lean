/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.PlaneCurve.Projective

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.RingTheory.MvPolynomial.CommonZero

/-!
# The Klein quartic

The **Klein quartic** is the projective plane curve

`X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0`

(`TauCeti.kleinQuartic`), of degree `4`, with affine equation `x³ y + y³ + x = 0` in the chart
`X₂ = 1`. This file proves that it is nonsingular exactly away from characteristic `7`
(`TauCeti.forall_exists_aeval_pderiv_kleinQuartic_ne_zero_iff`), and deduces from the genus of a
smooth projective plane curve, `TauCeti.genus_eq_of_isHomogeneous`, that a function field
`F = k(x, y)` with `x` transcendental and `x³ y + y³ + x = 0` has exact constant field `k` and
genus `3 = (4 - 1)(4 - 2) / 2` whenever `7 ≠ 0` in `k`.

Nonsingularity is elementary. Write `a = X₀³ X₁`, `b = X₁³ X₂` and `c = X₂³ X₀`, so that the
equation is `a + b + c = 0`. Multiplying the partial derivatives
`∂/∂X₁ = X₀³ + 3 X₁² X₂` and `∂/∂X₀ = 3 X₀² X₁ + X₂³` by `X₁` and `X₀` gives `a + 3 b` and
`3 a + c`, and `(a + 3 b) + 3 (3 a + c) - 3 (a + b + c) = 7 a`. So at a singular point `7 a = 0`.
If `7 ≠ 0` then `X₀ = 0` or `X₁ = 0`, and the vanishing of the partial derivatives then forces
every coordinate to vanish. In characteristic `7` the point `(1 : 2 : 4)` is singular.

No exactness hypothesis on the constants is needed: nonsingularity makes the affine equation
absolutely irreducible, which forces `k` to be the exact constant field of `F`
(`TauCeti.isIntegrallyClosedIn_of_isHomogeneous`).

## Main definitions

* `TauCeti.kleinQuartic`: the homogeneous quartic `X₀³ X₁ + X₁³ X₂ + X₂³ X₀`.

## Main results

* `TauCeti.exists_aeval_pderiv_kleinQuartic_ne_zero`: away from characteristic `7`, every point of
  the Klein quartic is nonsingular.
* `TauCeti.forall_exists_aeval_pderiv_kleinQuartic_ne_zero_iff`: the Klein quartic is nonsingular
  exactly when `7 ≠ 0`.
* `TauCeti.irreducible_kleinQuartic`: away from characteristic `7`, the Klein quartic is
  irreducible.
* `TauCeti.isIntegrallyClosedIn_of_pow_three_mul_add_pow_three_add_eq_zero`: `k` is the exact
  constant field of `k(x, y)`.
* `TauCeti.genus_eq_three_of_pow_three_mul_add_pow_three_add_eq_zero`: **the Klein quartic has
  genus `3`**.

## References

* F. Klein, *Ueber die Transformation siebenter Ordnung der elliptischen Functionen*, Math. Ann.
  14 (1878), 428–471.
* W. Fulton, *Algebraic Curves*, Section 8.3, for the genus `(n - 1)(n - 2) / 2` of a smooth plane
  curve of degree `n`.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.4.14.
-/

public section

open MvPolynomial
open scoped IntermediateField

namespace TauCeti

section Polynomial

variable (R : Type*) [CommRing R]

/-- The **Klein quartic** `X₀³ X₁ + X₁³ X₂ + X₂³ X₀`, a homogeneous polynomial of degree `4` in
three variables. -/
noncomputable def kleinQuartic : MvPolynomial (Fin 3) R :=
  X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2 + X 2 ^ 3 * X 0

/-- The Klein quartic as an explicit polynomial. -/
theorem kleinQuartic_def : kleinQuartic R = X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2 + X 2 ^ 3 * X 0 :=
  (rfl)

/-- The Klein quartic is homogeneous of degree `4`. -/
theorem isHomogeneous_kleinQuartic : (kleinQuartic R).IsHomogeneous 4 :=
  ((((isHomogeneous_X R 0).pow 3).mul (isHomogeneous_X R 1)).add
    (((isHomogeneous_X R 1).pow 3).mul (isHomogeneous_X R 2))).add
    (((isHomogeneous_X R 2).pow 3).mul (isHomogeneous_X R 0))

variable {R} {A : Type*} [CommRing A] [Algebra R A]

/-- The value of the Klein quartic at a point `b`. -/
@[simp]
theorem aeval_kleinQuartic (b : Fin 3 → A) :
    aeval b (kleinQuartic R) = b 0 ^ 3 * b 1 + b 1 ^ 3 * b 2 + b 2 ^ 3 * b 0 := by
  simp [kleinQuartic]

/-- The partial derivative `∂/∂X₀ = 3 X₀² X₁ + X₂³` of the Klein quartic at a point `b`. -/
@[simp]
theorem aeval_pderiv_zero_kleinQuartic (b : Fin 3 → A) :
    aeval b (pderiv 0 (kleinQuartic R)) = 3 * b 0 ^ 2 * b 1 + b 2 ^ 3 := by
  simp [kleinQuartic, pderiv_X]
  ring

/-- The partial derivative `∂/∂X₁ = X₀³ + 3 X₁² X₂` of the Klein quartic at a point `b`. -/
@[simp]
theorem aeval_pderiv_one_kleinQuartic (b : Fin 3 → A) :
    aeval b (pderiv 1 (kleinQuartic R)) = b 0 ^ 3 + 3 * b 1 ^ 2 * b 2 := by
  simp [kleinQuartic, pderiv_X]
  ring

/-- The partial derivative `∂/∂X₂ = X₁³ + 3 X₂² X₀` of the Klein quartic at a point `b`. -/
@[simp]
theorem aeval_pderiv_two_kleinQuartic (b : Fin 3 → A) :
    aeval b (pderiv 2 (kleinQuartic R)) = b 1 ^ 3 + 3 * b 2 ^ 2 * b 0 := by
  simp [kleinQuartic, pderiv_X]
  ring

variable [IsDomain A]

/-- **The Klein quartic is nonsingular away from characteristic `7`**: if `7 ≠ 0` in the domain
`A`, then at every nonzero point `b` of `X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0` over `A` some partial
derivative of the Klein quartic is nonzero. -/
theorem exists_aeval_pderiv_kleinQuartic_ne_zero (h7 : (7 : A) ≠ 0) {b : Fin 3 → A}
    (hb : b ≠ 0) (h : aeval b (kleinQuartic R) = 0) :
    ∃ l, aeval b (pderiv l (kleinQuartic R)) ≠ 0 := by
  by_contra! hd
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  rw [aeval_pderiv_zero_kleinQuartic] at h₀
  rw [aeval_pderiv_one_kleinQuartic] at h₁
  rw [aeval_pderiv_two_kleinQuartic] at h₂
  rw [aeval_kleinQuartic] at h
  -- With `a = b₀³ b₁`, the relations `b₁ ∂₁ = a + 3 b`, `b₀ ∂₀ = 3 a + c` and `a + b + c = 0`
  -- give `7 a = 0`, so `b₀ = 0` or `b₁ = 0`.
  have ha : 7 * (b 0 ^ 3 * b 1) = 0 := by linear_combination b 1 * h₁ + 3 * b 0 * h₀ - 3 * h
  refine hb (funext fun i ↦ ?_)
  rcases mul_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left h7) with h0 | h1
  · replace h0 := eq_zero_of_pow_eq_zero h0
    have h2 : b 2 = 0 := by simpa [h0] using h₀
    have h1 : b 1 = 0 := by simpa [h2] using h₂
    fin_cases i <;> assumption
  · have h0 : b 0 = 0 := by simpa [h1] using h₁
    have h2 : b 2 = 0 := by simpa [h0] using h₀
    fin_cases i <;> assumption

/-- **The Klein quartic is nonsingular exactly away from characteristic `7`**: every nonzero point
of `X₀³ X₁ + X₁³ X₂ + X₂³ X₀ = 0` over the domain `A` has a nonzero partial derivative of the
Klein quartic if and only if `7 ≠ 0` in `A`. In characteristic `7` the point `(1 : 2 : 4)` is
singular. -/
theorem forall_exists_aeval_pderiv_kleinQuartic_ne_zero_iff :
    (∀ b : Fin 3 → A, b ≠ 0 → aeval b (kleinQuartic R) = 0 →
        ∃ l, aeval b (pderiv l (kleinQuartic R)) ≠ 0) ↔ (7 : A) ≠ 0 := by
  refine ⟨fun hsm h7 ↦ ?_, fun h7 _ ↦ exists_aeval_pderiv_kleinQuartic_ne_zero h7⟩
  -- The singular point `(1 : 2 : 4)`, given by its coordinates.
  obtain ⟨b, hb0, hb1, hb2⟩ : ∃ b : Fin 3 → A, b 0 = 1 ∧ b 1 = 2 ∧ b 2 = 4 :=
    ⟨![1, 2, 4], rfl, rfl, rfl⟩
  have hb : b ≠ 0 := fun h ↦ one_ne_zero (hb0 ▸ congr_fun h 0)
  obtain ⟨l, hl⟩ := hsm b hb (by
    rw [aeval_kleinQuartic, hb0, hb1, hb2]
    linear_combination 14 * h7)
  refine hl ?_
  match l with
  | 0 =>
    rw [aeval_pderiv_zero_kleinQuartic, hb0, hb1, hb2]
    linear_combination 10 * h7
  | 1 =>
    rw [aeval_pderiv_one_kleinQuartic, hb0, hb1, hb2]
    linear_combination 7 * h7
  | 2 =>
    rw [aeval_pderiv_two_kleinQuartic, hb0, hb1, hb2]
    linear_combination 8 * h7

end Polynomial

section Field

variable {k : Type*} [Field k]

/-- Over a field `k` with `7 ≠ 0`, every point of the Klein quartic over a field extension `K` of
`k` is nonsingular. This is the nonsingularity hypothesis in the form the theory of smooth plane
curves consumes, with `K` an algebraic closure of `k`. -/
theorem forall_exists_aeval_pderiv_kleinQuartic_ne_zero (K : Type*) [Field K] [Algebra k K]
    (h7 : (7 : k) ≠ 0) :
    ∀ b : Fin 3 → K, b ≠ 0 → aeval b (kleinQuartic k) = 0 →
      ∃ l, aeval b (pderiv l (kleinQuartic k)) ≠ 0 :=
  forall_exists_aeval_pderiv_kleinQuartic_ne_zero_iff.mpr <| by
    rw [← map_ofNat (algebraMap k K) 7]
    exact (map_ne_zero _).mpr h7

/-- **The Klein quartic is irreducible away from characteristic `7`**, as is every nonsingular
plane curve. -/
theorem irreducible_kleinQuartic (h7 : (7 : k) ≠ 0) : Irreducible (kleinQuartic k) :=
  irreducible_of_isHomogeneous le_rfl (isHomogeneous_kleinQuartic k) four_ne_zero
    (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7)

end Field

section FunctionField

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x y : F}

/-- On the Klein quartic, the point `(x, y)` of the affine chart `X₂ = 1` is the point
`(x : y : 1)`. -/
private theorem aeval_kleinQuartic_of_pow_three_mul_add_pow_three_add_eq_zero
    (h : x ^ 3 * y + y ^ 3 + x = 0) : aeval ![x, y, 1] (kleinQuartic k) = 0 := by
  simpa using h

/-- **The constant field of the Klein quartic**: let `F / k` be generated by a transcendental `x`
and an element `y` with `x³ y + y³ + x = 0`. If `7 ≠ 0` in `k`, then `k` is the exact constant
field of `F`. -/
theorem isIntegrallyClosedIn_of_pow_three_mul_add_pow_three_add_eq_zero (h7 : (7 : k) ≠ 0)
    (hx : Transcendental k x) (hgen : k⟮x, y⟯ = ⊤) (h : x ^ 3 * y + y ^ 3 + x = 0) :
    IsIntegrallyClosedIn k F :=
  isIntegrallyClosedIn_of_isHomogeneous (isHomogeneous_kleinQuartic k)
    (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7) hx hgen
    (aeval_kleinQuartic_of_pow_three_mul_add_pow_three_add_eq_zero h)

/-- **The Klein quartic has genus three**: let `F / k` be generated by a transcendental `x` and an
element `y` with `x³ y + y³ + x = 0`. If `7 ≠ 0` in `k`, then `F` has genus `3`. This is the genus
`(n - 1)(n - 2) / 2` of a smooth plane curve of degree `n = 4`. -/
theorem genus_eq_three_of_pow_three_mul_add_pow_three_add_eq_zero (h7 : (7 : k) ≠ 0)
    (hx : Transcendental k x) (hgen : k⟮x, y⟯ = ⊤) (h : x ^ 3 * y + y ^ 3 + x = 0) :
    genus k F = 3 :=
  genus_eq_of_isHomogeneous (isHomogeneous_kleinQuartic k)
    (forall_exists_aeval_pderiv_kleinQuartic_ne_zero (AlgebraicClosure k) h7) hx hgen
    (aeval_kleinQuartic_of_pow_three_mul_add_pow_three_add_eq_zero h)

end FunctionField

end TauCeti
