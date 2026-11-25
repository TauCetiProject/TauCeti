/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.PowerSeries.Substitution
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

For functions analytic at `a`, the Taylor series is additive and multiplicative, it determines the
germ of the function, and it turns composition into formal substitution (`PowerSeries.subst`).
Multiplicativity rests on the product rule for divided differences, `TauCeti.dslope_mul`, which
gives the Cauchy product formula for the coefficients of the power series of a product
(`HasFPowerSeriesAt.coeff_mul`). This is the coefficient calculus with which formal expansions of
germs of analytic and meromorphic functions are compared with the functions themselves.

## Main declarations

* `HasFPowerSeriesAt.coeff_mul`: the coefficients of the power series of `f * g` are the Cauchy
  products of those of `f` and `g`.
* `TauCeti.taylorSeries`: the Taylor series at a point, as a formal power series.
* `TauCeti.taylorSeries_add`, `TauCeti.taylorSeries_mul`, `TauCeti.taylorSeries_const`,
  `TauCeti.taylorSeries_pow`: the Taylor series of analytic functions respects the ring
  operations.
* `TauCeti.taylorSeries_eq_C_add_X_mul`: the constant term and divided-difference tail.
* `TauCeti.taylorSeries_inj`: two functions analytic at `a` have the same Taylor series at `a`
  exactly when they agree near `a`.
* `AnalyticAt.factorial_smul_coeff_taylorSeries`: `n! • aₙ` is the `n`-th iterated derivative.
* `TauCeti.taylorSeries_comp`: the Taylor series of a composition `F ∘ φ` of scalar analytic
  functions is the formal substitution of the Taylor series of `φ - φ a` into that of `F`.

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
    have hp0 : p.coeff 0 = f a := by rw [FormalMultilinearSeries.coeff, hf.coeff_zero]
    simp only [FormalMultilinearSeries.coeff_fslope] at hcoeff ih'
    rw [hcoeff, Finset.Nat.sum_antidiagonal_succ, ← ih', ← q.coeff_fslope,
      FormalMultilinearSeries.coeff_add, FormalMultilinearSeries.coeff_smul, smul_eq_mul, hp0]

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

/-- The Taylor series is its constant term plus `X` times the Taylor series of the
divided difference at the same centre. -/
theorem taylorSeries_eq_C_add_X_mul :
    taylorSeries f a = PowerSeries.C (f a) +
      PowerSeries.X * taylorSeries (dslope f a) a := by
  ext (_ | n)
  · simp
  · simp only [map_add, PowerSeries.coeff_C, Nat.succ_ne_zero, ↓reduceIte,
      PowerSeries.coeff_succ_X_mul, zero_add, coeff_taylorSeries, iterate_succ_apply]

/-- The constant coefficient of the Taylor series of `f` at `a` is `f a`. -/
@[simp]
theorem constantCoeff_taylorSeries : PowerSeries.constantCoeff (taylorSeries f a) = f a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorSeries, iterate_zero_apply]

/-- The Taylor series of the zero function is zero. -/
@[simp]
theorem taylorSeries_zero : taylorSeries (0 : 𝕜 → A) a = 0 := by
  rw [Pi.zero_def, taylorSeries_const, map_zero]

/-- The Taylor series of the negative of a function is the negative of its Taylor series. -/
@[simp]
theorem taylorSeries_neg : taylorSeries (-f) a = -taylorSeries f a := by
  have key : ∀ n, (swap dslope a)^[n] (-f) = -(swap dslope a)^[n] f := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih]
      -- `swap dslope a f` is `dslope f a` by the definition of `Function.swap`.
      exact dslope_neg _ a
  ext n
  rw [coeff_taylorSeries, map_neg, coeff_taylorSeries, key, Pi.neg_apply]

/-- The Taylor series of a difference of functions analytic at `a` is the difference of their
Taylor series. -/
@[simp]
theorem taylorSeries_sub (hf : AnalyticAt 𝕜 f a) (hg : AnalyticAt 𝕜 g a) :
    taylorSeries (f - g) a = taylorSeries f a - taylorSeries g a := by
  rw [sub_eq_add_neg, taylorSeries_add hf hg.neg, taylorSeries_neg, sub_eq_add_neg]

/-- The Taylor series of a finite sum of functions analytic at `a` is the sum of their Taylor
series. -/
theorem taylorSeries_sum {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → A}
    (hf : ∀ i ∈ s, AnalyticAt 𝕜 (f i) a) :
    taylorSeries (∑ i ∈ s, f i) a = ∑ i ∈ s, taylorSeries (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : AnalyticAt 𝕜 (∑ j ∈ s, f j) a := by
      simpa only [← Finset.sum_fn] using
        Finset.analyticAt_sum s fun j hj ↦ hf j (mem_insert_of_mem hj)
    rw [sum_insert hi, sum_insert hi, taylorSeries_add (hf i (mem_insert_self i s)) hs,
      ih fun j hj ↦ hf j (mem_insert_of_mem hj)]

/-- **Uniqueness of Taylor expansions.** Two functions analytic at `a` have the same Taylor series
at `a` if and only if they agree on a neighbourhood of `a`. -/
theorem taylorSeries_inj (hf : AnalyticAt 𝕜 f a) (hg : AnalyticAt 𝕜 g a) :
    taylorSeries f a = taylorSeries g a ↔ f =ᶠ[𝓝 a] g := by
  refine ⟨fun h ↦ ?_, taylorSeries_congr⟩
  obtain ⟨p, hp⟩ := hf.sub hg
  have hp0 : p = 0 := funext fun n ↦ by
    rw [FormalMultilinearSeries.zero_apply, ← FormalMultilinearSeries.coeff_eq_zero,
      ← hp.coeff_taylorSeries, taylorSeries_sub hf hg, h, sub_self, map_zero]
  filter_upwards [(hp0 ▸ hp).eventually_eq_zero] with z hz
  exact sub_eq_zero.1 hz

end TauCeti

/-- The `n`-th Taylor coefficient of a function analytic at `a`, multiplied by `n!`, is its `n`-th
iterated derivative at `a`. -/
theorem AnalyticAt.factorial_smul_coeff_taylorSeries [CompleteSpace A] (hf : AnalyticAt 𝕜 f a)
    (n : ℕ) :
    n.factorial • PowerSeries.coeff n (TauCeti.taylorSeries f a) = iteratedDeriv n f a := by
  obtain ⟨p, r, hp⟩ := hf
  rw [hp.hasFPowerSeriesAt.coeff_taylorSeries, iteratedDeriv_eq_iteratedFDeriv,
    ← hp.factorial_smul, p.apply_eq_pow_smul_coeff, one_pow, one_smul]

namespace TauCeti

/-- **Taylor series of a composition.** If `φ` is analytic at `a` and `F` is analytic at `φ a`,
the Taylor series of `F ∘ φ` at `a` is obtained by substituting the Taylor series of `φ - φ a` at
`a`, which has constant coefficient `0`, into the Taylor series of `F` at `φ a`. -/
theorem taylorSeries_comp {F φ : 𝕜 → 𝕜} (hF : AnalyticAt 𝕜 F (φ a)) (hφ : AnalyticAt 𝕜 φ a) :
    taylorSeries (F ∘ φ) a =
      (taylorSeries F (φ a)).subst (taylorSeries φ a - PowerSeries.C (φ a)) := by
  set b := φ a
  set ψ := taylorSeries φ a - PowerSeries.C b
  have hψ0 : PowerSeries.constantCoeff ψ = 0 := by simp [ψ, b]
  have hψ : PowerSeries.HasSubst ψ := .of_constantCoeff_zero' hψ0
  set u : 𝕜 → 𝕜 := φ - fun _ ↦ b
  have hu : AnalyticAt 𝕜 u a := hφ.sub analyticAt_const
  have hTu : taylorSeries u a = ψ := by
    rw [taylorSeries_sub hφ analyticAt_const, taylorSeries_const]
  -- A product with `ψ ^ (n + 1)` has vanishing coefficients below `n + 1`.
  have hcoeff : ∀ n (S : PowerSeries 𝕜), PowerSeries.coeff n (ψ ^ (n + 1) * S) = 0 := fun n S ↦
    PowerSeries.X_pow_dvd_iff.1 ((pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hψ0) _).mul_right S)
      n (Nat.lt_succ_self n)
  ext n
  set c : ℕ → 𝕜 := fun j ↦ (swap dslope b)^[j] F b
  set D := (swap dslope b)^[n + 1] F
  -- Function side: Taylor's formula for `F` around `b`, to order `n + 1`, composed with `φ`.
  have hFφ : F ∘ φ = ∑ j ∈ range (n + 1), (fun _ ↦ c j) * u ^ j + u ^ (n + 1) * (D ∘ φ) := by
    funext z
    simpa [u, c, D, Finset.sum_apply, mul_comm] using
      (sum_add_pow_sub_smul_iterate_dslope F b (φ z) (n + 1)).symm
  have hD : AnalyticAt 𝕜 (D ∘ φ) a := (hF.iterate_dslope (n + 1)).comp hφ
  have hL : taylorSeries (F ∘ φ) a =
      ∑ j ∈ range (n + 1), PowerSeries.C (c j) * ψ ^ j + ψ ^ (n + 1) * taylorSeries (D ∘ φ) a := by
    rw [hFφ, taylorSeries_add (Finset.analyticAt_sum _ fun j _ ↦ analyticAt_const.mul (hu.pow j))
      ((hu.pow _).mul hD), taylorSeries_sum _ fun j _ ↦ analyticAt_const.mul (hu.pow j),
      taylorSeries_mul (hu.pow _) hD, taylorSeries_pow hu, hTu]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    rw [taylorSeries_mul analyticAt_const (hu.pow j), taylorSeries_const, taylorSeries_pow hu, hTu]
  -- Formal side: the Taylor series of `F` agrees with its truncation up to a multiple of
  -- `X ^ (n + 1)`.
  obtain ⟨Q, hQ⟩ : PowerSeries.X ^ (n + 1) ∣
      taylorSeries F b - ∑ j ∈ range (n + 1), PowerSeries.C (c j) * PowerSeries.X ^ j := by
    refine PowerSeries.X_pow_dvd_iff.2 fun k hk ↦ ?_
    simp [map_sum, Finset.mem_range.2 hk, c]
  have hR : (taylorSeries F b).subst ψ =
      ∑ j ∈ range (n + 1), PowerSeries.C (c j) * ψ ^ j + ψ ^ (n + 1) * Q.subst ψ := by
    rw [eq_add_of_sub_eq hQ, ← PowerSeries.coe_substAlgHom hψ]
    simp only [map_add, map_sum, map_mul, map_pow, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_C]
    exact add_comm _ _
  rw [hL, hR, map_add, map_add, hcoeff, hcoeff]

end TauCeti
