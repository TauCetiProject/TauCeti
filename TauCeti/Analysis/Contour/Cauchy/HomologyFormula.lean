/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.ArcFTC
import TauCeti.Analysis.Contour.HomologyCauchy
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Cauchy's integral formula in homology form, for all derivatives

For `f` holomorphic on an open `U`, a closed absolutely continuous curve `γ` in `U` that is
**null-homologous** there, and a point `z` off the curve,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`

for every `k : ℕ`, with `n_z(γ)` the generalized winding number. The case `k = 0` is Cauchy's
integral formula `TauCeti.Contour.cauchyIntegralFormula_nullHomologous`, which Dixon's argument
gives together with the homology Cauchy theorem, and the general `k` is its derivative form.

The general case follows from `k = 0` by induction on `k`. For `f`, `γ` and `z` as above, the
kernel quotient `w ↦ f w / (w − z) ^ (k + 1)` is holomorphic on the open set `U ∖ {z}`, which
contains the closed curve, so the contour integral of its derivative vanishes
(`AbsolutelyContinuousOnInterval.integral_deriv_smul_deriv_comp_eq_zero_of_closed`):

`(k + 1) · ∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 2))
  = ∫ t in a..b, γ' t • (f' (γ t) / (γ t − z) ^ (k + 1))`.

This reduces the formula of order `k + 1` for `f` to the formula of order `k` for `f'`, which is
again holomorphic on `U`.

The formulas here use the parametrization directly, so applications can express the contour
integral as an interval integral over the oriented interval `a..b`. The statement for a contour
cycle is `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, which is
proved from the residue theorem.

## Main results

* `TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous` — the formula above, for
  every order `k`.
* `TauCeti.Contour.cauchyIntegralFormula_deriv_nullHomologous` — its `k = 1` case, stated with
  `deriv f z`.

## Relation to Mathlib

Mathlib's Cauchy integral formulas are all stated for a round circle.
`Complex.circleIntegral_one_div_sub_pow_smul_of_differentiable_on_off_countable` and its
`DiffContOnCl` / `DifferentiableOn` variants evaluate the circle integral of
`(1 / (z − w) ^ (k + 1)) • f z` as `(2πi / k !) • iteratedDeriv k f w` at every point `w` of the
open disc, for `f` continuous on the closed disc and holomorphic inside it; the case `k = 0` is
`Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`. Mathlib has no winding number
for a general curve, hence no formula weighted by one; that is what the statements here supply.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 (the index of a point and the homology form of Cauchy's
  theorem and integral formula).
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.

## Provenance

No formal source is vendored: the induction on the order is written here, on top of the case
`k = 0` from `HomologyCauchy.lean`, which is migrated from the AINTLIB `LeanModularForms`
development.
-/

public section

open Complex MeasureTheory Set

open scoped Interval Real

namespace TauCeti.Contour

/-- **Lowering the order of the Cauchy kernel.** For `f` holomorphic on an open `U`, a closed
absolutely continuous curve `γ` in `U`, and `z` off the curve,

`(k + 1) · ∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 2))
  = ∫ t in a..b, γ' t • (f' (γ t) / (γ t − z) ^ (k + 1))`. -/
private theorem add_one_mul_integral_deriv_smul_div_sub_pow {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) (k : ℕ) :
    ((k : ℂ) + 1) * ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 2))
      = ∫ t in a..b, deriv γ t • (deriv f (γ t) / (γ t - z) ^ (k + 1)) := by
  have hne : ∀ t ∈ uIcc a b, ∀ n : ℕ, (γ t - z) ^ n ≠ 0 := fun t ht n ↦
    pow_ne_zero n (sub_ne_zero.mpr (hoff t ht))
  -- The contour integrand `γ' • (g ∘ γ / (γ - z) ^ n)` is integrable for `g` continuous on `U`.
  have hint : ∀ {g : ℂ → ℂ} (n : ℕ), ContinuousOn g U →
      IntervalIntegrable (fun t ↦ deriv γ t • (g (γ t) / (γ t - z) ^ n)) volume a b := fun n hg ↦
    hγ.intervalIntegrable_deriv_of_finiteDimensional.smul_continuousOn
      ((hg.comp hγ.continuousOn hγU).div ((hγ.continuousOn.sub continuousOn_const).pow n)
        fun t ht ↦ hne t ht n)
  -- The kernel quotient `w ↦ f w / (w - z) ^ (k + 1)` is holomorphic on `U \ {z}`, which contains
  -- the closed curve, so the contour integral of its derivative vanishes.
  have hG : DifferentiableOn ℂ (fun w ↦ f w / (w - z) ^ (k + 1)) (U \ {z}) :=
    (hf.mono sdiff_subset).div (by fun_prop) fun w hw ↦ pow_ne_zero _ (sub_ne_zero.mpr hw.2)
  have h := hγ.integral_deriv_smul_deriv_comp_eq_zero_of_closed (hU.sdiff isClosed_singleton) hG
    (fun t ht ↦ ⟨hγU t ht, hoff t ht⟩) hclosed
  -- That derivative is the difference of the two integrands.
  have hd : ∀ t ∈ uIcc a b, deriv γ t • deriv (fun w ↦ f w / (w - z) ^ (k + 1)) (γ t) =
      deriv γ t • (deriv f (γ t) / (γ t - z) ^ (k + 1)) -
        ((k : ℂ) + 1) * (deriv γ t • (f (γ t) / (γ t - z) ^ (k + 2))) := fun t ht ↦ by
    have hpow : HasDerivAt (fun w ↦ (w - z) ^ (k + 1)) ((k + 1) * (γ t - z) ^ k) (γ t) := by
      simpa using ((hasDerivAt_id (γ t)).sub_const z).fun_pow (k + 1)
    rw [((hf.differentiableAt (hU.mem_nhds (hγU t ht))).hasDerivAt.fun_div hpow (hne t ht _)).deriv]
    have := sub_ne_zero.mpr (hoff t ht)
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hd, intervalIntegral.integral_sub
    (hint _ (hf.deriv hU).continuousOn) ((hint _ hf.continuousOn).const_mul _),
    intervalIntegral.integral_const_mul] at h
  linear_combination -h

/-- **Cauchy's integral formula for the `k`-th derivative, homology form.** Let `f` be holomorphic
on an open `U`, let `γ` be a closed absolutely continuous curve in `U` that is null-homologous
there, and let `z` lie off the curve. Then for every `k`,

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ (k + 1)) = 2πi · n_z(γ) · f⁽ᵏ⁾(z) / k !`,

with `n_z(γ) = windingNumber γ a b z` the generalized winding number of `γ` about `z`. For `z ∈ U`
the right side is `2πi · n_z(γ)` times the `k`-th Taylor coefficient of `f` at `z`; for `z ∉ U` the
winding number vanishes by null-homology, and the formula says that the integral is `0`. The case
`k = 0` is `TauCeti.Contour.cauchyIntegralFormula_nullHomologous`. -/
theorem cauchyIntegralFormula_iteratedDeriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z)
    (k : ℕ) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ (k + 1))
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z *
          (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  -- Induction on `k`: the order `k + 1` for `f` reduces to the order `k` for `deriv f`, which is
  -- again holomorphic on `U`.
  induction k generalizing f with
  | zero => simpa using cauchyIntegralFormula_nullHomologous hU hf hγ hγU hclosed hnull hoff
  | succ k ih =>
    have h := add_one_mul_integral_deriv_smul_div_sub_pow hU hf hγ hγU hclosed hoff k
    rw [ih (hf.deriv hU), ← iteratedDeriv_succ'] at h
    have hk : (k : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
    have hfact : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp at h ⊢
    linear_combination h

/-- **Cauchy's integral formula for the first derivative, homology form.** The `k = 1` case of
`TauCeti.Contour.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, stated with `deriv f z`:

`∫ t in a..b, γ' t • (f (γ t) / (γ t − z) ^ 2) = 2πi · n_z(γ) · f' z`. -/
theorem cauchyIntegralFormula_deriv_nullHomologous {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (hnull : IsNullHomologous γ a b U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ z) :
    ∫ t in a..b, deriv γ t • (f (γ t) / (γ t - z) ^ 2)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b z * deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hγ hγU hclosed hnull hoff 1

end TauCeti.Contour

end
