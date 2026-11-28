/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Evaluation
public import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Power series over the `p`-adic integers: evaluation and division by `X - c`

An arbitrary power series `ψ ∈ ℤ_[p]⟦X⟧` can be evaluated at a `p`-adic integer `c` exactly when
`p ∣ c`: this is the condition `PowerSeries.HasEval c`, which for `ℤ_[p]` is topological
nilpotence (`TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd`), and `ψ ↦ ψ(c)` is then
Mathlib's continuous `ℤ_[p]`-algebra homomorphism `PowerSeries.aeval : ℤ_[p]⟦X⟧ →ₐ[ℤ_[p]] ℤ_[p]`,
given by the convergent sum of the monomials (`PowerSeries.hasSum_aeval`). The linear topology
on `ℤ_[p]` that this evaluation needs is `TauCeti.Huber.PadicInt.instIsLinearTopology`. For such
`c`, division by `X - c` is `ψ = (X - c) * q + ψ(c)` with the explicit quotient
`PowerSeries.divXSubC`, whose `n`-th coefficient is the convergent series `∑ₖ ψ_{n+1+k} c^k`, so a
power series is divisible by `X - c` exactly when it vanishes at `c`: this is the special case of
Weierstrass division that produces the basis corrections in Labute's classification of Demushkin
groups, and the specialisation to `ℤ_[p]` and its maximal ideal `(p)` of the results of
`TauCeti.RingTheory.PowerSeries.Evaluation`.

Over any complete ultrametric normed (possibly noncommutative) `ℤ_[p]`-algebra `R` with contractive
scalar action, every power series `φ ∈ ℤ_[p]⟦X⟧` evaluates continuously at any topologically
nilpotent element `t ∈ R` via `PowerSeries.evalAt` (`TauCeti.padicPowerSeriesEval`), compatible
with formal substitution (`TauCeti.padicPowerSeriesEval_subst`).

## Main results

* `PadicInt.X_sub_C_mul_divXSubC_add_C_aeval`: for `p ∣ c`, `ψ = (X - C c) * q + C (ψ(c))` with
  the explicit quotient `q = PowerSeries.divXSubC _ ψ`.
* `PadicInt.X_sub_C_mul_divXSubC`: for `p ∣ c` and `ψ(c) = 0`, `ψ = (X - C c) * q`.
* `PadicInt.X_sub_C_dvd_iff_aeval_eq_zero`: for `p ∣ c`, `(X - C c) ∣ ψ ↔ ψ(c) = 0`.
* `TauCeti.padicPowerSeriesEval`: continuous `ℤ_[p]`-algebra evaluation of `ℤ_[p]⟦X⟧` at a
  topologically nilpotent element of a complete ultrametric normed `ℤ_[p]`-algebra, with
  `TauCeti.hasSum_padicPowerSeriesEval`, `TauCeti.continuous_padicPowerSeriesEval`,
  `TauCeti.tendsto_padicPowerSeriesEval_pow`, and `TauCeti.padicPowerSeriesEval_subst`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, p. 122.
-/

public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Division by `X - c` over `ℤ_[p]`.** For a `p`-adic integer `c` divisible by `p`, a power
series `f` over `ℤ_[p]` is `(X - C c) * q + C (f(c))`, with the explicit quotient
`q = PowerSeries.divXSubC _ f`. -/
theorem X_sub_C_mul_divXSubC_add_C_aeval {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c)
    (f : PowerSeries ℤ_[p]) :
    (PowerSeries.X - PowerSeries.C c) *
        PowerSeries.divXSubC (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f +
      PowerSeries.C
        (PowerSeries.aeval (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f) =
      f :=
  PowerSeries.X_sub_C_mul_divXSubC_add_C_aeval _ f

/-- For a `p`-adic integer `c` divisible by `p`, a power series over `ℤ_[p]` vanishing at `c`
factors as `(X - C c) * q` with the explicit quotient `q = PowerSeries.divXSubC _ f`. -/
theorem X_sub_C_mul_divXSubC {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c) {f : PowerSeries ℤ_[p]}
    (hf : PowerSeries.aeval (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f
      = 0) :
    (PowerSeries.X - PowerSeries.C c) *
        PowerSeries.divXSubC (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f =
      f :=
  PowerSeries.X_sub_C_mul_divXSubC _ hf

/-- **Divisibility by `X - c` over `ℤ_[p]`.** For a `p`-adic integer `c` divisible by `p`, a power
series over `ℤ_[p]` is divisible by `X - C c` exactly when its value at `c` is zero. -/
theorem X_sub_C_dvd_iff_aeval_eq_zero {c : ℤ_[p]} (hc : (p : ℤ_[p]) ∣ c) (f : PowerSeries ℤ_[p]) :
    (PowerSeries.X - PowerSeries.C c) ∣ f ↔
      PowerSeries.aeval (TauCeti.Huber.PadicInt.isTopologicallyNilpotent_iff_dvd.mpr hc) f = 0 :=
  PowerSeries.X_sub_C_dvd_iff_aeval_eq_zero _ f

end PadicInt

namespace TauCeti

section PadicPowerSeriesEval

open Filter Topology
open scoped PowerSeries.WithPiTopology

variable (p : ℕ) [Fact p.Prime] {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
  [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R]

omit [IsUltrametricDist R] in
private theorem continuous_algebraMap_padicInt : Continuous (algebraMap ℤ_[p] R) :=
  (continuous_id.smul continuous_const).congr fun a ↦ (Algebra.algebraMap_eq_smul_one a).symm

omit [IsUltrametricDist R] in
private theorem norm_algebraMap_padicInt_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] R a‖ ≤ ‖(1 : R)‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))

variable [CompleteSpace R]

/-- For a topologically nilpotent `t ∈ R`, `∑ n, φ.coeff n • t ^ n` is summable for `φ ∈ ℤ_p⟦X⟧`. -/
theorem summable_coeff_smul_pow {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) : Summable fun n : ℕ ↦ φ.coeff n • t ^ n :=
  PowerSeries.summable_smul_pow_of_norm_algebraMap_le (norm_algebraMap_padicInt_le p) ht φ

/-- **Evaluation of integral power series at a topologically nilpotent element** of a complete
ultrametric normed `ℤ_p`-algebra `R` with contractive scalar action. -/
noncomputable def padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    PowerSeries ℤ_[p] →ₐ[ℤ_[p]] R :=
  PowerSeries.evalAtAlgHom (continuous_algebraMap_padicInt p) (norm_algebraMap_padicInt_le p) ht

theorem padicPowerSeriesEval_apply {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) : padicPowerSeriesEval p ht φ = φ.evalAt t :=
  PowerSeries.evalAtAlgHom_apply φ
theorem hasSum_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ φ.coeff n • t ^ n) (padicPowerSeriesEval p ht φ) :=
  PowerSeries.hasSum_evalAtAlgHom (continuous_algebraMap_padicInt p)
    (norm_algebraMap_padicInt_le p) ht φ
theorem continuous_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    Continuous (padicPowerSeriesEval p ht) :=
  PowerSeries.continuous_evalAtAlgHom (continuous_algebraMap_padicInt p)
    (norm_algebraMap_padicInt_le p) ht
@[simp] theorem padicPowerSeriesEval_X {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    padicPowerSeriesEval p ht PowerSeries.X = t :=
  PowerSeries.evalAtAlgHom_X (continuous_algebraMap_padicInt p) (norm_algebraMap_padicInt_le p) ht
@[simp] theorem padicPowerSeriesEval_C {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) (a : ℤ_[p]) :
    padicPowerSeriesEval p ht (PowerSeries.C a) = algebraMap ℤ_[p] R a :=
  PowerSeries.evalAtAlgHom_C (continuous_algebraMap_padicInt p) (norm_algebraMap_padicInt_le p) ht a

/-- Evaluating a substitutable power series `b ∈ ℤ_p⟦X⟧` at a topologically nilpotent element `t`
produces a topologically nilpotent element. -/
theorem tendsto_padicPowerSeriesEval_pow {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    {b : PowerSeries ℤ_[p]} (hb : PowerSeries.HasSubst b) :
    Tendsto ((padicPowerSeriesEval p ht b) ^ ·) atTop (𝓝 0) :=
  PowerSeries.tendsto_evalAtAlgHom_pow (continuous_algebraMap_padicInt p)
    (norm_algebraMap_padicInt_le p) ht hb

/-- Substituting `b` (`PowerSeries.HasSubst b`) before evaluating at `t` equals evaluating at
`padicPowerSeriesEval p ht b` (which is automatically topologically nilpotent). -/
theorem padicPowerSeriesEval_subst {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    {b : PowerSeries ℤ_[p]} (hb : PowerSeries.HasSubst b) (φ : PowerSeries ℤ_[p]) :
    padicPowerSeriesEval p ht (φ.subst b) =
      padicPowerSeriesEval p (tendsto_padicPowerSeriesEval_pow p ht hb) φ :=
  PowerSeries.evalAtAlgHom_subst (continuous_algebraMap_padicInt p)
    (norm_algebraMap_padicInt_le p) ht hb φ

end PadicPowerSeriesEval

end TauCeti
