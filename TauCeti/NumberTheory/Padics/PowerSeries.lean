/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Padic.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Evaluation
import TauCeti.NumberTheory.Padics.Basic

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

For restricted power series `f ∈ ℤ_[p]⟦X⟧`, coercing coefficients along the isometric embedding
`ℤ_[p] ↪ ℚ_[p]` transports convergence
(`PowerSeries.isRestricted_norm_iff_summable_coe_coeff_mul_pow`) and evaluation
(`PowerSeries.IsRestricted.hasSum_coe_evalAt`) between `ℤ_[p]` and `ℚ_[p]`.

## Main results

* `PadicInt.X_sub_C_mul_divXSubC_add_C_aeval`: for `p ∣ c`, `ψ = (X - C c) * q + C (ψ(c))` with
  the explicit quotient `q = PowerSeries.divXSubC _ ψ`.
* `PadicInt.X_sub_C_mul_divXSubC`: for `p ∣ c` and `ψ(c) = 0`, `ψ = (X - C c) * q`.
* `PadicInt.X_sub_C_dvd_iff_aeval_eq_zero`: for `p ∣ c`, `(X - C c) ∣ ψ ↔ ψ(c) = 0`.
* `PowerSeries.isRestricted_norm_iff_summable_coe_coeff_mul_pow`: restrictedness of `f : ℤ_[p]⟦X⟧`
  at radius `‖x‖` is equivalent to summability of `∑ n, (coeff n f : ℚ_[p]) * x ^ n` in `ℚ_[p]`.
* `PowerSeries.IsRestricted.hasSum_coe_evalAt`: if `f : ℤ_[p]⟦X⟧` is restricted at `c` and
  `‖x‖ ≤ c`, then `∑ n, (coeff n f : ℚ_[p]) * (x : ℚ_[p]) ^ n` sums to `(f.evalAt x : ℚ_[p])`.

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

namespace PowerSeries

open scoped PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- **Restrictedness of an integral `p`-adic power series via `ℚ_[p]`-summability.** For
`f : ℤ_[p]⟦X⟧` and `x : ℚ_[p]`, `f` is restricted at radius `‖x‖` iff the termwise series
`∑ n, (coeff n f : ℚ_[p]) * x ^ n` is summable in `ℚ_[p]`. -/
theorem isRestricted_norm_iff_summable_coe_coeff_mul_pow (f : ℤ_[p]⟦X⟧) (x : ℚ_[p]) :
    f.IsRestricted ‖x‖ ↔ Summable fun n ↦ ((coeff n f : ℤ_[p]) : ℚ_[p]) * x ^ n := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    tendsto_zero_iff_norm_tendsto_zero, isRestricted_iff']
  simp only [norm_mul, norm_pow, PadicInt.norm_def]

/-- **Termwise convergence in `ℚ_[p]` of a restricted integral power series.** For `f : ℤ_[p]⟦X⟧`
restricted at radius `c` and `x : ℤ_[p]` with `‖x‖ ≤ c`, the series
`∑ n, (coeff n f : ℚ_[p]) * (x : ℚ_[p]) ^ n` sums to `(f.evalAt x : ℚ_[p])` in `ℚ_[p]`. -/
theorem IsRestricted.hasSum_coe_evalAt {c : ℝ} {f : ℤ_[p]⟦X⟧} (hf : f.IsRestricted c)
    {x : ℤ_[p]} (hx : ‖x‖ ≤ c) :
    HasSum (fun n ↦ ((coeff n f : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) ^ n)
      ((f.evalAt x : ℤ_[p]) : ℚ_[p]) := by
  rw [← PadicInt.Coe.ringHom_apply]
  simpa only [Function.comp_def, smul_eq_mul, map_mul, map_pow, PadicInt.Coe.ringHom_apply] using
    (hf.hasSum_evalAt hx).map PadicInt.Coe.ringHom PadicInt.isEmbedding_coe_ringHom.continuous

end PowerSeries
