/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs

import Mathlib.Algebra.Order.Ring.Pow
import TauCeti.Analysis.AbsoluteValue.FiniteOrder

/-!
# Real-extending absolute values on `ℂ`

The complex modulus `‖·‖` is the unique real-valued absolute value on `ℂ` whose restriction to `ℝ`
is `|·|` (`AbsoluteValue.eq_norm_of_apply_ofReal`). Consequently, any ring homomorphism out of `ℂ`
into a normed division ring that preserves norms on `ℝ` is an isometry on all of `ℂ`
(`RingHom.norm_apply_of_norm_ofReal`, `RingHom.isometry_of_norm_ofReal`).

This supplies the analytic rigidity needed after the algebraic Gelfand–Mazur theorem: once a normed
`ℝ`-algebra is shown to be isomorphic to `ℂ` as an `ℝ`-algebra, pulling its norm back to `ℂ` yields
an absolute value agreeing with `|·|` on `ℝ`, so the algebra isomorphism is automatically an
isometry.

## Main results

* `AbsoluteValue.map_I`: any absolute value on `ℂ` takes the value `1` at `Complex.I`.
* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value on `ℂ` agreeing with `|·|` on `ℝ`
  equals `‖·‖` everywhere.
* `AbsoluteValue.eq_toAbsoluteValue_norm_of_apply_ofReal`: bundled form of the same uniqueness
  statement.
* `AbsoluteValue.eq_norm_of_liesOver_abs` and `AbsoluteValue.liesOver_abs_iff`: characterization of
  the absolute values on `ℂ` lying over `AbsoluteValue.abs` on `ℝ`.
* `RingHom.norm_apply_of_norm_ofReal` and `RingHom.isometry_of_norm_ofReal`: a ring homomorphism
  from `ℂ` into a normed division ring that is isometric on `ℝ` is isometric on `ℂ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.2.
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §4.
-/

public section

namespace AbsoluteValue

/-- Every absolute value on `ℂ` with values in a linearly ordered ring sends `Complex.I` to `1`. -/
@[simp]
theorem map_I {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
    (v : AbsoluteValue ℂ S) : v Complex.I = 1 :=
  v.map_eq_one_of_isOfFinOrder
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by positivity, Complex.I_pow_four⟩)

private theorem apply_le_two_mul_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ)
    (hv : ∀ r : ℝ, v r = |r|) (z : ℂ) : v z ≤ 2 * ‖z‖ := by
  calc
    v z = v ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by rw [Complex.re_add_im]
    _ ≤ v (z.re : ℂ) + v ((z.im : ℂ) * Complex.I) := v.add_le _ _
    _ = |z.re| + |z.im| := by rw [map_mul, hv, hv, map_I, mul_one]
    _ ≤ ‖z‖ + ‖z‖ := add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
    _ = 2 * ‖z‖ := (two_mul ‖z‖).symm

private theorem apply_le_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ)
    (hv : ∀ r : ℝ, v r = |r|) (z : ℂ) : v z ≤ ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  by_contra! hlt
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set d : ℝ := v z / ‖z‖ - 1
  have hd_pos : 0 < d := sub_pos.mpr ((one_lt_div hnorm_pos).mpr hlt)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / d)
  have hpow : (1 + d) ^ n ≤ 2 := by
    have h1 : 1 + d = v z / ‖z‖ := add_sub_cancel 1 (v z / ‖z‖)
    rw [h1, div_pow, div_le_iff₀ (pow_pos hnorm_pos n), ← map_pow, ← norm_pow]
    exact apply_le_two_mul_norm_of_apply_ofReal v hv (z ^ n)
  have hbern : 1 + (n : ℝ) * d ≤ (1 + d) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hnd : 1 < (n : ℝ) * d := (div_lt_iff₀ hd_pos).mp hn
  linarith

/-- An absolute value on `ℂ` whose restriction to `ℝ` is `|·|` agrees with the complex norm `‖·‖`
at every complex number. -/
theorem eq_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ) (hv : ∀ r : ℝ, v r = |r|) (z : ℂ) :
    v z = ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  refine le_antisymm (apply_le_norm_of_apply_ofReal v hv z) ?_
  have hinv := apply_le_norm_of_apply_ofReal v hv z⁻¹
  rw [map_inv₀, norm_inv] at hinv
  exact (inv_le_inv₀ (v.pos hz) (norm_pos_iff.mpr hz)).mp hinv

/-- An absolute value on `ℂ` agreeing with `|·|` on `ℝ` is the bundled complex norm. -/
theorem eq_toAbsoluteValue_norm_of_apply_ofReal (v : AbsoluteValue ℂ ℝ)
    (hv : ∀ r : ℝ, v r = |r|) :
    v = IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ) :=
  ext (eq_norm_of_apply_ofReal v hv)

/-- An absolute value on `ℂ` lying over `AbsoluteValue.abs` on `ℝ` agrees with `‖·‖` everywhere. -/
theorem eq_norm_of_liesOver_abs (v : AbsoluteValue ℂ ℝ) [v.LiesOver AbsoluteValue.abs] (z : ℂ) :
    v z = ‖z‖ :=
  eq_norm_of_apply_ofReal v (fun r ↦ congr($(LiesOver.under_eq v AbsoluteValue.abs) r)) z

/-- An absolute value on `ℂ` lies over `AbsoluteValue.abs` on `ℝ` if and only if it is the bundled
complex norm. -/
theorem liesOver_abs_iff (v : AbsoluteValue ℂ ℝ) :
    v.LiesOver AbsoluteValue.abs ↔ v = IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ) := by
  refine ⟨fun _ ↦ ext (eq_norm_of_liesOver_abs v), ?_⟩
  rintro rfl
  exact ⟨ext Complex.norm_real⟩

end AbsoluteValue

namespace RingHom

/-- A ring homomorphism from `ℂ` into a normed division ring that preserves norms on `ℝ` preserves
norms on all of `ℂ`. -/
theorem norm_apply_of_norm_ofReal {A : Type*} [NormedDivisionRing A] (f : ℂ →+* A)
    (hf : ∀ r : ℝ, ‖f r‖ = |r|) (z : ℂ) : ‖f z‖ = ‖z‖ :=
  AbsoluteValue.eq_norm_of_apply_ofReal
    ((IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) hf z

/-- A ring homomorphism from `ℂ` into a normed division ring that preserves norms on `ℝ` is an
isometry. -/
theorem isometry_of_norm_ofReal {A : Type*} [NormedDivisionRing A] (f : ℂ →+* A)
    (hf : ∀ r : ℝ, ‖f r‖ = |r|) : Isometry f :=
  AddMonoidHomClass.isometry_of_norm f (f.norm_apply_of_norm_ofReal hf)

end RingHom
