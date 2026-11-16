/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic identities and norm bounds for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.ext_of_re_eq_of_re_I_mul_eq`: two scalars in `K` with equal real parts before and after
  multiplying by `RCLike.I` are equal (uniformly over `ℝ` and `ℂ`).
* `RCLike.apply_eq_of_re_eq_of_re_I_smul_eq`: the `I`-test equating `f v` and `g v` for `K`-action
  homomorphisms from real-part equalities at `v` and `RCLike.I • v`.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

/-- The norm of a scalar is at most the sum of the absolute values of its real and imaginary
parts. -/
theorem norm_le_abs_re_add_abs_im (z : K) : ‖z‖ ≤ |re z| + |im z| := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_def]
  nlinarith [abs_mul_abs_self (re z), abs_mul_abs_self (im z), abs_nonneg (re z),
    abs_nonneg (im z)]

/-- A scalar with zero imaginary part is the image of its real part. -/
theorem re_eq_self_of_im_eq_zero {z : K} (h : im z = 0) : (re z : K) = z :=
  conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)

/-- Two scalars in an `RCLike` field are equal if they have the same real part and their products
with `RCLike.I` also have the same real part. Over `ℝ` the second hypothesis is `0 = 0`; over `ℂ`
it equates the imaginary parts via `re (I * z) = -im z`. -/
theorem ext_of_re_eq_of_re_I_mul_eq {z w : K} (hre : re z = re w)
    (him : re (I * z) = re (I * w)) : z = w := by
  refine ext hre (neg_inj.mp ?_)
  simpa only [I_mul_re] using him

/-- **The `I`-test.** Two `K`-homogeneous maps `f` and `g` take the same value at `v` when their
real parts agree both at `v` and at `(I : K) • v`. Over `ℂ`, testing `I • v` supplies the imaginary
part; a single real-part equality does not suffice (`f 1 = I`, `g 1 = 0` has `re (f 1) = 0`). -/
theorem apply_eq_of_re_eq_of_re_I_smul_eq {V F G : Type*} [SMul K V]
    [FunLike F V K] [MulActionHomClass F K V K] [FunLike G V K] [MulActionHomClass G K V K]
    {f : F} {g : G} {v : V} (hre : re (f v) = re (g v))
    (him : re (f ((I : K) • v)) = re (g ((I : K) • v))) : f v = g v := by
  refine ext_of_re_eq_of_re_I_mul_eq hre ?_
  simpa only [map_smul, smul_eq_mul] using him

end RCLike
