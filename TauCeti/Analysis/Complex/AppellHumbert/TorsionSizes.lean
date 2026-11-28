/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Valuation sizes of theta functions at torsion points

Let `D = (B, χ)` be an Appell–Humbert datum for a subgroup `L` of a complex normed space `V`
(`TauCeti.AppellHumbertData`), and let `v : Valuation ℂ ℝ≥0` be a multiplicative non-archimedean
valuation on `ℂ`. The *size* of a function `f : V → ℂ` at `x ∈ V` is
`v (D.twistedTranslate x f 0) = v (exp (-B x x / 2) * f x)`
(`TauCeti.AppellHumbertData.thetaSize`).

At torsion points of `V / L`, the Riemann phase `exp (π i E (a, b))` is a root of unity and
therefore has valuation `1` (`TauCeti.AppellHumbertData.valuation_exp_riemannForm_eq_one`).
Consequently, `thetaSize` is multiplicative on products and powers, shifts cleanly under
`twistedTranslate` at torsion points, and is periodic modulo `L` for theta functions whose
semicharacter has finite order at `l ∈ L`.

## Main results

* `TauCeti.AppellHumbertData.thetaSize`: the valuation size `v (D.twistedTranslate x f 0)`.
* `TauCeti.AppellHumbertData.thetaSize_mul`, `TauCeti.AppellHumbertData.thetaSize_pow`:
  multiplicativity under products and powers of data and functions.
* `TauCeti.AppellHumbertData.valuation_exp_riemannForm_eq_one`: at torsion points `a, b` of
  `V / L`, `v (exp (π i E (a, b))) = 1`.
* `TauCeti.AppellHumbertData.thetaSize_twistedTranslate`: `D.thetaSize v (D.twistedTranslate a f) x
  = D.thetaSize v f (x + a)` at torsion points `a, x`.
* `TauCeti.AppellHumbertData.thetaSize_add_of_mem_thetaSpace`: periodicity modulo `L` for theta
  functions when `D.semichar l` has finite order.

## Provenance

Adapted from `New.ThetaTori.LatticeForm.sizeAt`, `New.ThetaTori.sizeAt_mul`,
`New.ThetaTori.sizeAt_pow`, `New.IsAppellHumbert.valuation_exp_riemannForm`,
`New.IsAppellHumbert.sizeAt_thetaShift`, and `New.ThetaTori.factorsThrough_mkQ_of_mem_sizes`
(file `src/Lib/Shimura/GoodReduction/TorsionSizes.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Complex
open scoped NNReal Real

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D D' : AppellHumbertData L) (v : Valuation ℂ ℝ≥0)

/-- The valuation size of `f : V → ℂ` at `x ∈ V` with respect to an Appell–Humbert datum `D` and
valuation `v`: `v (D.twistedTranslate x f 0) = v (exp (-B x x / 2) * f x)`. -/
noncomputable def thetaSize (f : V → ℂ) (x : V) : ℝ≥0 :=
  v (D.twistedTranslate x f 0)

variable {D D' v}

/-- The valuation size is multiplicative in the datum and the function. -/
@[simp]
theorem thetaSize_mul (f g : V → ℂ) (x : V) :
    (D + D').thetaSize v (f * g) x = D.thetaSize v f x * D'.thetaSize v g x := by
  rw [thetaSize, twistedTranslate_mul, Pi.mul_apply, map_mul, thetaSize, thetaSize]

/-- The valuation size of a power `f ^ n` in degree `n • D` is the `n`-th power of the size. -/
@[simp]
theorem thetaSize_pow (f : V → ℂ) (n : ℕ) (x : V) :
    (n • D).thetaSize v (f ^ n) x = D.thetaSize v f x ^ n := by
  rw [thetaSize, twistedTranslate_pow, Pi.pow_apply, map_pow, thetaSize]

/-- At torsion points `a, b` of `V / L`, the phase `exp (π i E (a, b))` is a root of unity, so
every `ℝ≥0`-valued valuation of `ℂ` sends it to `1`. -/
theorem valuation_exp_riemannForm_eq_one {a b : V} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (ha : m • a ∈ L) (hb : n • b ∈ L) :
    v (exp (π * I * D.riemannForm a b)) = 1 := by
  obtain ⟨k, hk⟩ := D.exists_riemannForm_eq_intCast ⟨m • a, ha⟩ ⟨n • b, hb⟩
  have hpow : exp (π * I * D.riemannForm a b) ^ (2 * m * n) = 1 := by
    rw [← exp_natCast_mul]
    have hmul : (↑(2 * m * n) : ℂ) * (π * I * D.riemannForm a b) = (k : ℂ) * (2 * π * I) := by
      have hE : (m : ℝ) * (n : ℝ) * D.riemannForm a b = (k : ℝ) := by
        simpa [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, mul_left_comm, mul_assoc] using hk
      calc (↑(2 * m * n) : ℂ) * (π * I * D.riemannForm a b)
          = ((m : ℝ) * (n : ℝ) * D.riemannForm a b : ℝ) * (2 * π * I) := by push_cast; ring
        _ = (k : ℂ) * (2 * π * I) := by rw [hE]; push_cast; ring
    rw [hmul, exp_int_mul_two_pi_mul_I]
  have hmn : 2 * m * n ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hm) hn
  have hv := congrArg v hpow
  rw [map_pow, map_one] at hv
  exact (pow_eq_one_iff_of_nonneg zero_le hmn).mp hv

/-- Shifting a function by a torsion point `a` shifts its valuation size at any torsion point `x`
to `x + a`. -/
theorem thetaSize_twistedTranslate (f : V → ℂ) {a x : V} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (ha : m • a ∈ L) (hx : n • x ∈ L) :
    D.thetaSize v (D.twistedTranslate a f) x = D.thetaSize v f (x + a) := by
  rw [thetaSize, thetaSize, D.twistedTranslate_twistedTranslate, Pi.smul_apply, smul_eq_mul,
    map_mul, exp_neg, map_inv₀, D.valuation_exp_riemannForm_eq_one hn hm hx ha, inv_one, one_mul]

/-- For a theta function `f ∈ D.thetaSpace`, if `D.semichar l` has finite order then the valuation
size of `f` at a torsion point `x` is unchanged by adding `l ∈ L`. -/
theorem thetaSize_add_of_mem_thetaSpace {f : V → ℂ} (hf : f ∈ D.thetaSpace) {l : L} {k : ℕ}
    (hk : k ≠ 0) (hχ : (D.semichar l : ℂ) ^ k = 1) {x : V} {m : ℕ} (hm : m ≠ 0) (hx : m • x ∈ L) :
    D.thetaSize v f (x + l) = D.thetaSize v f x := by
  rw [thetaSize, thetaSize, twistedTranslate_add_eq_smul_of_mem_thetaSpace hf x l, Pi.smul_apply,
    smul_eq_mul, map_mul, map_mul,
    D.valuation_exp_riemannForm_eq_one hm one_ne_zero hx (by simp), one_mul]
  have hvχ : v (D.semichar l : ℂ) = 1 := by
    have hv := congrArg v hχ
    rw [map_pow, map_one] at hv
    exact (pow_eq_one_iff_of_nonneg zero_le hk).mp hv
  rw [hvχ, one_mul]

end TauCeti.AppellHumbertData
