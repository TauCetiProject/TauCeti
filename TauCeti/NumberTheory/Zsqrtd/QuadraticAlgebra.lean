/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.NumberTheory.QuadraticOrder.Frobenius

/-!
# Equivalence between `ℤ√d` and `QuadraticAlgebra ℤ d 0`

For any integer `d : ℤ`, `ℤ√d` is canonically ring-isomorphic to `QuadraticAlgebra ℤ d 0`
via `Zsqrtd.equivQuadraticAlgebra d`, identifying the `re` and `im` coordinates, conjugation
`star`, and the square-root generator (`Zsqrtd.sqrtd ↔ QuadraticAlgebra.omega`).

This transports results proved for `QuadraticAlgebra ℤ d 0`, such as the integral Frobenius
congruence `QuadraticAlgebra.frobenius_congruence`, directly to `ℤ√d`
(`Zsqrtd.natCast_dvd_pow_sub_star`, and its Jacobi-symbol form
`Zsqrtd.natCast_dvd_pow_sub_star_of_jacobiSym_eq_neg_one`).

## Main results

* `Zsqrtd.equivQuadraticAlgebra`: canonical ring equivalence `ℤ√d ≃+* QuadraticAlgebra ℤ d 0`.
* `Zsqrtd.natCast_dvd_pow_sub_star`,
  `Zsqrtd.natCast_dvd_pow_sub_star_of_jacobiSym_eq_neg_one`: if `d` is not a square modulo a
  prime `p` (in particular, if `jacobiSym d p = -1`), then `(p : ℤ√d) ∣ u ^ p - star u` for every
  `u : ℤ√d`.
-/

public section

namespace Zsqrtd

/-- Canonical ring equivalence between `ℤ√d` and `QuadraticAlgebra ℤ d 0`, identifying the
`re` and `im` coordinates and sending `Zsqrtd.sqrtd` to `QuadraticAlgebra.omega`. -/
def equivQuadraticAlgebra (d : ℤ) : ℤ√d ≃+* QuadraticAlgebra ℤ d 0 where
  toFun u := ⟨u.re, u.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' u v := by ext <;> simp [mul_assoc]
  map_add' u v := by ext <;> simp

/-- Real part of `Zsqrtd.equivQuadraticAlgebra d u`. -/
@[simp]
theorem re_equivQuadraticAlgebra (d : ℤ) (u : ℤ√d) :
    (equivQuadraticAlgebra d u).re = u.re := by
  rfl

/-- Imaginary part of `Zsqrtd.equivQuadraticAlgebra d u`. -/
@[simp]
theorem im_equivQuadraticAlgebra (d : ℤ) (u : ℤ√d) :
    (equivQuadraticAlgebra d u).im = u.im := by
  rfl

/-- Real part of `(Zsqrtd.equivQuadraticAlgebra d).symm z`. -/
@[simp]
theorem re_equivQuadraticAlgebra_symm (d : ℤ) (z : QuadraticAlgebra ℤ d 0) :
    ((equivQuadraticAlgebra d).symm z).re = z.re := by
  rfl

/-- Imaginary part of `(Zsqrtd.equivQuadraticAlgebra d).symm z`. -/
@[simp]
theorem im_equivQuadraticAlgebra_symm (d : ℤ) (z : QuadraticAlgebra ℤ d 0) :
    ((equivQuadraticAlgebra d).symm z).im = z.im := by
  rfl

/-- `Zsqrtd.equivQuadraticAlgebra` commutes with conjugation `star`. -/
@[simp]
theorem equivQuadraticAlgebra_star (d : ℤ) (u : ℤ√d) :
    equivQuadraticAlgebra d (star u) = star (equivQuadraticAlgebra d u) := by
  ext <;> simp

/-- `(Zsqrtd.equivQuadraticAlgebra d).symm` commutes with conjugation `star`. -/
@[simp]
theorem equivQuadraticAlgebra_symm_star (d : ℤ) (z : QuadraticAlgebra ℤ d 0) :
    (equivQuadraticAlgebra d).symm (star z) = star ((equivQuadraticAlgebra d).symm z) := by
  ext <;> simp

/-- `Zsqrtd.equivQuadraticAlgebra` sends `Zsqrtd.sqrtd` to `QuadraticAlgebra.omega`. -/
@[simp]
theorem equivQuadraticAlgebra_sqrtd (d : ℤ) :
    equivQuadraticAlgebra d (sqrtd : ℤ√d) = QuadraticAlgebra.omega := by
  rfl

/-- `(Zsqrtd.equivQuadraticAlgebra d).symm` sends `QuadraticAlgebra.omega` to `Zsqrtd.sqrtd`. -/
@[simp]
theorem equivQuadraticAlgebra_symm_omega (d : ℤ) :
    (equivQuadraticAlgebra d).symm (QuadraticAlgebra.omega : QuadraticAlgebra ℤ d 0) = sqrtd := by
  rfl

/-- **The integral Frobenius congruence in `ℤ√d`.** If `d` is not a square modulo a prime `p`,
then `(p : ℤ√d) ∣ u ^ p - star u` for every `u : ℤ√d`, transported from
`QuadraticAlgebra.frobenius_congruence`. -/
theorem natCast_dvd_pow_sub_star {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hd : ¬ IsSquare (d : ZMod p)) (u : ℤ√d) :
    (p : ℤ√d) ∣ u ^ p - star u := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem := QuadraticAlgebra.frobenius_congruence hd (equivQuadraticAlgebra d u)
  rw [Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨q, hq⟩
  refine ⟨(equivQuadraticAlgebra d).symm q, ?_⟩
  apply (equivQuadraticAlgebra d).injective
  simp only [map_sub, map_pow, map_mul, map_natCast, equivQuadraticAlgebra_star,
    RingEquiv.apply_symm_apply, hq]

/-- **The integral Frobenius congruence in `ℤ√d` via the Jacobi symbol.** If `p` is prime and
`jacobiSym d p = -1`, then `(p : ℤ√d) ∣ u ^ p - star u` for every `u : ℤ√d`. -/
theorem natCast_dvd_pow_sub_star_of_jacobiSym_eq_neg_one {d : ℤ} {p : ℕ} (hp : p.Prime)
    (hjac : jacobiSym d p = -1) (u : ℤ√d) :
    (p : ℤ√d) ∣ u ^ p - star u := by
  have : Fact p.Prime := ⟨hp⟩
  have hns : ¬ IsSquare (d : ZMod p) := by
    rw [← legendreSym.eq_neg_one_iff p, jacobiSym.legendreSym.to_jacobiSym, hjac]
  exact natCast_dvd_pow_sub_star hp hns u

end Zsqrtd
