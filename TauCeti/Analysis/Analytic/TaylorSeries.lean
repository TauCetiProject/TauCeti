/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.RingTheory.PowerSeries.Basic
import TauCeti.Analysis.Analytic.ExtractZeros
public import TauCeti.Analysis.Calculus.DSlope.Basic

/-!
# Taylor series of functions of one variable

The Taylor series `TauCeti.taylorSeries f a` of a function `f : 𝕜 → A` at `a`, with values in a
normed algebra `A`, is the formal power series whose `n`-th coefficient is the value at `a` of the
`n`-th iterated divided difference `(swap dslope a)^[n] f`. It uses no choice of a power series of
`f`, and it depends only on the germ of `f` at `a` (`TauCeti.taylorSeries_congr`). When `f` has a
power series `p` at `a`, its coefficients are the coefficients `p.coeff n`
(`HasFPowerSeriesAt.coeff_taylorSeries`). Mathlib's `ftaylorSeries` records the iterated derivatives
of a function as a formal multilinear series at each point; `TauCeti.taylorSeries` is the
one-variable expansion as an element of the ring `PowerSeries A`, where formal expansions can be
multiplied.

For functions analytic at `a`, the Taylor series is additive and multiplicative. Multiplicativity
rests on the product rule for divided differences, `TauCeti.dslope_mul`, which gives the Cauchy
product formula for the coefficients of the power series of a product
(`HasFPowerSeriesAt.coeff_mul`). This is the coefficient calculus with which formal expansions of
germs of analytic and meromorphic functions are compared with the functions themselves.

## Main declarations

* `HasFPowerSeriesAt.coeff_mul`: the coefficients of the power series of `f * g` are the Cauchy
  products of those of `f` and `g`.
* `TauCeti.taylorSeries`: the Taylor series at a point, as a formal power series.
* `TauCeti.taylorSeries_add`, `TauCeti.taylorSeries_mul`, `TauCeti.taylorSeries_const`,
  `TauCeti.taylorSeries_pow`: the Taylor series of analytic functions respects the ring
  operations.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd edition, McGraw-Hill, 1979, Chapter 5, §1.2.
-/

public noncomputable section

open Filter Finset Function Topology

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  {f g : 𝕜 → A} {a : 𝕜}

namespace FormalMultilinearSeries

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The coefficients of a sum of formal multilinear series in one variable are the sums of their
coefficients. -/
@[simp]
theorem coeff_add (p q : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    (p + q).coeff n = p.coeff n + q.coeff n :=
  (rfl)

/-- The coefficients of a scalar multiple of a formal multilinear series in one variable are the
scalar multiples of its coefficients. -/
@[simp]
theorem coeff_smul {R : Type*} [Semiring R] [Module R E] [ContinuousConstSMul R E]
    [SMulCommClass 𝕜 R E] (c : R) (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    (c • p).coeff n = c • p.coeff n :=
  (rfl)

end FormalMultilinearSeries

/-- **The Cauchy product formula for power series coefficients.** If `f`, `g` and `f * g` have
the power series `p`, `q` and `r` at `a`, then the `n`-th coefficient of `r` is
`∑_{i + j = n} p.coeff i * q.coeff j`. -/
theorem HasFPowerSeriesAt.coeff_mul {p q r : FormalMultilinearSeries 𝕜 𝕜 A}
    (hf : HasFPowerSeriesAt f p a) (hg : HasFPowerSeriesAt g q a)
    (hfg : HasFPowerSeriesAt (f * g) r a) (n : ℕ) :
    r.coeff n = ∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2 := by
  induction n generalizing f p r with
  | zero =>
    rw [Finset.Nat.antidiagonal_zero, sum_singleton, FormalMultilinearSeries.coeff, hfg.coeff_zero,
      FormalMultilinearSeries.coeff, hf.coeff_zero, FormalMultilinearSeries.coeff, hg.coeff_zero,
      Pi.mul_apply]
  | succ n ih =>
    -- The divided difference of `f * g` is `f a • dslope g a + dslope f a * g`, whose power
    -- series is `f a • q.fslope + r'` for a power series `r'` of `dslope f a * g`.
    obtain ⟨r', hr'⟩ := (hf.analyticAt.dslope a).mul hg.analyticAt
    have hd : dslope (f * g) a = f a • dslope g a + dslope f a * g :=
      funext (TauCeti.dslope_mul hf.differentiableAt hg.differentiableAt)
    have hfg' : HasFPowerSeriesAt (dslope (f * g) a) (f a • q.fslope + r') a := by
      rw [hd]
      exact hg.dslope_fslope.const_smul.add hr'
    have hcoeff := congrArg (FormalMultilinearSeries.coeff · n)
      (hfg.dslope_fslope.eq_formalMultilinearSeries hfg')
    have ih' := ih hf.dslope_fslope hr'
    simp only [FormalMultilinearSeries.coeff_fslope] at hcoeff ih'
    rw [hcoeff, Finset.Nat.sum_antidiagonal_succ, ← ih', ← q.coeff_fslope,
      FormalMultilinearSeries.coeff_add, FormalMultilinearSeries.coeff_smul, smul_eq_mul,
      show p.coeff 0 = f a from hf.coeff_zero 1]

namespace TauCeti

variable (f a) in
/-- The **Taylor series** of `f` at `a`: the formal power series whose `n`-th coefficient is the
value at `a` of the `n`-th iterated divided difference `(swap dslope a)^[n] f`. If `f` has a power
series `p` at `a`, these are the coefficients of `p` (`HasFPowerSeriesAt.coeff_taylorSeries`). -/
def taylorSeries : PowerSeries A :=
  PowerSeries.mk fun n ↦ (swap dslope a)^[n] f a

variable (f a) in
/-- The `n`-th coefficient of the Taylor series of `f` at `a` is the value at `a` of the `n`-th
iterated divided difference. -/
@[simp]
theorem coeff_taylorSeries (n : ℕ) :
    PowerSeries.coeff n (taylorSeries f a) = (swap dslope a)^[n] f a :=
  PowerSeries.coeff_mk _ _

/-- The coefficients of the Taylor series of `f` at `a` are those of any power series of `f`
at `a`. -/
theorem _root_.HasFPowerSeriesAt.coeff_taylorSeries {p : FormalMultilinearSeries 𝕜 𝕜 A}
    (hp : HasFPowerSeriesAt f p a) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries f a) = p.coeff n := by
  rw [TauCeti.coeff_taylorSeries, hp.iterate_dslope_apply_eq_coeff]

/-- The Taylor series of `f` at `a` depends only on the germ of `f` at `a`. -/
theorem taylorSeries_congr (h : f =ᶠ[𝓝 a] g) : taylorSeries f a = taylorSeries g a := by
  have key : ∀ n, (swap dslope a)^[n] f =ᶠ[𝓝 a] (swap dslope a)^[n] g := fun n ↦ by
    induction n with
    | zero => exact h
    | succ n ih =>
      simp only [iterate_succ_apply']
      exact ih.dslope
  ext n
  rw [coeff_taylorSeries, coeff_taylorSeries, (key n).eq_of_nhds]

/-- The Taylor series of a constant function is constant. -/
@[simp]
theorem taylorSeries_const (c : A) : taylorSeries (fun _ : 𝕜 ↦ c) a = PowerSeries.C c := by
  ext n
  rw [hasFPowerSeriesAt_const.coeff_taylorSeries, PowerSeries.coeff_C]
  rcases n with _ | n
  · simp only [↓reduceIte]
    exact (hasFPowerSeriesAt_const (𝕜 := 𝕜) (e := a) (c := c)).coeff_zero 1
  · simp only [Nat.succ_ne_zero, ↓reduceIte, FormalMultilinearSeries.coeff,
      constFormalMultilinearSeries_apply_succ, zero_apply]

/-- The Taylor series of a sum of functions analytic at `a` is the sum of their Taylor series. -/
@[simp]
theorem taylorSeries_add (hf : AnalyticAt 𝕜 f a) (hg : AnalyticAt 𝕜 g a) :
    taylorSeries (f + g) a = taylorSeries f a + taylorSeries g a := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  ext n
  rw [map_add, (hp.add hq).coeff_taylorSeries, hp.coeff_taylorSeries, hq.coeff_taylorSeries,
    FormalMultilinearSeries.coeff_add]

/-- **Taylor series of a product.** The Taylor series of a product of functions analytic at `a`
is the product of their Taylor series. -/
@[simp]
theorem taylorSeries_mul (hf : AnalyticAt 𝕜 f a) (hg : AnalyticAt 𝕜 g a) :
    taylorSeries (f * g) a = taylorSeries f a * taylorSeries g a := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  obtain ⟨r, hr⟩ := (hp.analyticAt.mul hq.analyticAt : AnalyticAt 𝕜 (f * g) a)
  ext n
  rw [hr.coeff_taylorSeries, hp.coeff_mul hq hr, PowerSeries.coeff_mul]
  simp only [hp.coeff_taylorSeries, hq.coeff_taylorSeries]

/-- The Taylor series of a power of a function analytic at `a` is the power of its Taylor
series. -/
@[simp]
theorem taylorSeries_pow (hf : AnalyticAt 𝕜 f a) (n : ℕ) :
    taylorSeries (f ^ n) a = taylorSeries f a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Pi.one_def, taylorSeries_const, map_one]
  | succ n ih => rw [pow_succ, taylorSeries_mul (hf.pow n) hf, ih, pow_succ]

/-- The Taylor series at `a` of the coordinate `z ↦ z - a` is the variable `X`. -/
@[simp]
theorem taylorSeries_sub_const : taylorSeries (fun z : 𝕜 ↦ z - a) a = PowerSeries.X := by
  have hd : dslope (fun z : 𝕜 ↦ z - a) a = fun _ ↦ 1 := funext fun b ↦ by
    rcases eq_or_ne b a with rfl | hb
    · rw [dslope_same, deriv_sub_const, deriv_id'']
    · rw [dslope_of_ne _ hb, slope_def_field, sub_self, sub_zero, div_self (sub_ne_zero.2 hb)]
  ext n
  rcases n with _ | n
  · simp
  · -- `swap dslope a f` is `dslope f a` by the definition of `Function.swap`.
    rw [coeff_taylorSeries, iterate_succ_apply, show swap dslope a (fun z : 𝕜 ↦ z - a) = _ from hd,
      ← coeff_taylorSeries, taylorSeries_const, PowerSeries.coeff_C, PowerSeries.coeff_X]
    rcases n with _ | n <;> simp

end TauCeti
