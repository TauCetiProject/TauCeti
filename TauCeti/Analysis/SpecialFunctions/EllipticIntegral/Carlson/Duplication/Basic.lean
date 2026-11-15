/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.IntermediateValue

/-!
# The duplication theorem for Carlson's `R_F`

This file proves the duplication theorem for Carlson's symmetric integral of the first kind
(DLMF 19.26.18) at nonnegative real arguments: with `λ = √x √y + √y √z + √z √x`,

`R_F(x, y, z) = R_F((x + λ)/4, (y + λ)/4, (z + λ)/4)`.

Iterating it drives the three arguments together towards a common value, where `R_F` is given by
its diagonal value `R_F(x, x, x) = x^(-1/2)`; this is the basis of Carlson's duplication algorithm
for computing elliptic integrals.

## Main results

* `Complex.carlsonRF_ofReal_duplication` — the duplication theorem for `R_F` at nonnegative real
  arguments.

## Implementation notes

The proof is a change of variables in the defining integral. Write `a = √(t + x)`, `b = √(t + y)`,
`c = √(t + z)` and `λ(t) = ab + bc + ca`, so that `λ = λ(0)`. The substitution
`u = (t + λ(t) - λ)/4` maps `(0, ∞)` increasingly onto itself, and it satisfies
`u + (x + λ)/4 = (a + b)(a + c)/4` together with its two cyclic companions. Since
`du/dt · abc = (a + b)(b + c)(c + a)/8`, it carries the integrand of the right-hand side to that of
the left-hand side. The identity holds as an equality of Bochner integrals, so no convergence
hypothesis is needed.

## References

* NIST *Digital Library of Mathematical Functions*, §19.26(ii), <https://dlmf.nist.gov/19.26>.
* B. C. Carlson, Computing elliptic integrals by duplication, *Numer. Math.* 33 (1979), 1–16.
* B. C. Carlson, Numerical computation of real or complex elliptic integrals, *Numer. Algorithms*
  10 (1995), 13–26.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) also proves the duplication
theorem, on top of Carlson's general `R`-function. This file works directly from the integral
definition of `Complex.carlsonRF` and is not ported from it.
-/

public section

open MeasureTheory Set Filter

namespace Complex

/-- The Jacobian identity behind the duplication theorem: for `a, b, c > 0`, the derivative
`(1 + (ab + bc + ca)′)/4` of the substitution, computed with `a′ = 1/(2a)` and its companions,
times `8/((a + b)(b + c)(c + a))` is `(abc)⁻¹`. -/
private theorem duplication_jacobian {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (1 + (1 / (2 * a) * b + a * (1 / (2 * b)) + (1 / (2 * b) * c + b * (1 / (2 * c))) +
      (1 / (2 * c) * a + c * (1 / (2 * a))))) / 4 * ((a + b) * (b + c) * (c + a) / 8)⁻¹ =
      (a * b * c)⁻¹ := by
  field_simp
  ring

/-- The duplication theorem for the real integral `∫₀^∞ (√(t + x) √(t + y) √(t + z))⁻¹ dt`, proved
by the substitution `u = (t + λ(t) - λ(0))/4` with `λ(t) = Σ √(t + x) √(t + y)`. -/
private theorem integral_inv_sqrt_mul_duplication {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (l : ℝ) (hl : l = √x * √y + √y * √z + √z * √x) :
    ∫ u in Ioi (0 : ℝ), (√(u + (x + l) / 4) * √(u + (y + l) / 4) * √(u + (z + l) / 4))⁻¹ =
      ∫ t in Ioi (0 : ℝ), (√(t + x) * √(t + y) * √(t + z))⁻¹ := by
  set g : ℝ → ℝ := fun u => (√(u + (x + l) / 4) * √(u + (y + l) / 4) * √(u + (z + l) / 4))⁻¹
  -- The shifted square roots and their symmetric function `lam t = λ(t)`.
  set a : ℝ → ℝ := fun t => √(t + x)
  set b : ℝ → ℝ := fun t => √(t + y)
  set c : ℝ → ℝ := fun t => √(t + z)
  set lam : ℝ → ℝ := fun t => a t * b t + b t * c t + c t * a t
  set σ : ℝ → ℝ := fun t => (t + lam t - l) / 4
  have hσ0 : σ 0 = 0 := by simp [σ, lam, a, b, c, hl]
  -- `σ` is strictly increasing and continuous, and maps `(0, ∞)` onto itself.
  have hmono (w : ℝ) : Monotone fun t : ℝ => √(t + w) := fun s t hst =>
    Real.sqrt_le_sqrt (by linarith)
  have hlam : Monotone lam :=
    (((hmono x).mul (hmono y) (fun _ => Real.sqrt_nonneg _) fun _ => Real.sqrt_nonneg _).add
      ((hmono y).mul (hmono z) (fun _ => Real.sqrt_nonneg _) fun _ => Real.sqrt_nonneg _)).add
      ((hmono z).mul (hmono x) (fun _ => Real.sqrt_nonneg _) fun _ => Real.sqrt_nonneg _)
  have hσmono : StrictMono σ := fun s t hst => by
    simp only [σ]
    linarith [hlam hst.le]
  have hlam0 : lam 0 = l := by simp [lam, a, b, c, hl]
  have hσcont : Continuous σ := by
    simp only [σ, lam, a, b, c]
    fun_prop
  have hσtop : Tendsto σ atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 4))
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [σ, id]
    linarith [hlam ht, hlam0]
  have himage : σ '' Ioi 0 = Ioi 0 := by
    simpa only [hσ0] using
      hσcont.continuousOn.image_Ioi_of_strictMonoOn (hσmono.strictMonoOn (Ici 0)) hσtop
  -- The derivative of `σ` on `(0, ∞)`, where the square roots are differentiable.
  set σ' : ℝ → ℝ := fun t =>
    (1 + (1 / (2 * a t) * b t + a t * (1 / (2 * b t)) +
      (1 / (2 * b t) * c t + b t * (1 / (2 * c t))) +
        (1 / (2 * c t) * a t + c t * (1 / (2 * a t))))) / 4
  have hsqrt {w t : ℝ} (hw : 0 ≤ w) (ht : 0 < t) :
      HasDerivAt (fun t : ℝ => √(t + w)) (1 / (2 * √(t + w))) t :=
    ((hasDerivAt_id' t).add_const w).sqrt (by linarith)
  have hσderiv (t : ℝ) (ht : t ∈ Ioi 0) : HasDerivWithinAt σ (σ' t) (Ioi 0) t := by
    have hx' := hsqrt hx ht
    have hy' := hsqrt hy ht
    have hz' := hsqrt hz ht
    exact (((((hasDerivAt_id' t).add (((hx'.mul hy').add (hy'.mul hz')).add
      (hz'.mul hx'))).sub_const l).div_const 4)).hasDerivWithinAt
  have hsubst := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hσderiv
    hσmono.injective.injOn g
  rw [himage] at hsubst
  rw [hsubst]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  -- In terms of `a, b, c`, the integrand transforms by `(a + b)(b + c)(c + a)/8 = σ' · abc`.
  have ha : 0 < a t := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b t := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < c t := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a t ^ 2 = t + x := Real.sq_sqrt (by linarith)
  have hb2 : b t ^ 2 = t + y := Real.sq_sqrt (by linarith)
  have hc2 : c t ^ 2 = t + z := Real.sq_sqrt (by linarith)
  have hσx : σ t + (x + l) / 4 = (a t + b t) * (a t + c t) / 4 := by
    simp only [σ, lam]
    linear_combination (-1 / 4 : ℝ) * ha2
  have hσy : σ t + (y + l) / 4 = (a t + b t) * (b t + c t) / 4 := by
    simp only [σ, lam]
    linear_combination (-1 / 4 : ℝ) * hb2
  have hσz : σ t + (z + l) / 4 = (a t + c t) * (b t + c t) / 4 := by
    simp only [σ, lam]
    linear_combination (-1 / 4 : ℝ) * hc2
  have hprod : √(σ t + (x + l) / 4) * √(σ t + (y + l) / 4) * √(σ t + (z + l) / 4) =
      (a t + b t) * (b t + c t) * (c t + a t) / 8 := by
    rw [hσx, hσy, hσz, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [show (a t + b t) * (a t + c t) / 4 * ((a t + b t) * (b t + c t) / 4) *
        ((a t + c t) * (b t + c t) / 4) = ((a t + b t) * (b t + c t) * (c t + a t) / 8) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hσ'pos : 0 < σ' t := by
    simp only [σ']
    positivity
  simp only [g, smul_eq_mul]
  rw [abs_of_pos hσ'pos, hprod]
  exact duplication_jacobian ha hb hc

/-- **The duplication theorem for `R_F`** (DLMF 19.26.18) at nonnegative real arguments: for real
`x, y, z ≥ 0`, with `λ = √x √y + √y √z + √z √x`,
`R_F(x, y, z) = R_F((x + λ)/4, (y + λ)/4, (z + λ)/4)`.

No hypothesis beyond nonnegativity is needed. When two of `x, y, z` vanish, the defining integrals
on both sides diverge and the identity is between the totalized values `0`. -/
theorem carlsonRF_ofReal_duplication {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let l := √x * √y + √y * √z + √z * √x
    carlsonRF x y z = carlsonRF ((x + l) / 4 : ℝ) ((y + l) / 4 : ℝ) ((z + l) / 4 : ℝ) := by
  intro l
  rw [carlsonRF_ofReal_eq_integral hx hy hz,
    carlsonRF_ofReal_eq_integral (by positivity) (by positivity) (by positivity),
    integral_inv_sqrt_mul_duplication hx hy hz l rfl]

end Complex
