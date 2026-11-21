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
import Mathlib.Topology.UniformSpace.UniformApproximation

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
  `TauCeti.hasSum_padicPowerSeriesEval`, `TauCeti.continuous_padicPowerSeriesEval`, and
  `TauCeti.padicPowerSeriesEval_subst`.

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
private theorem norm_coeff_smul_pow_le (φ : PowerSeries ℤ_[p]) (t : R) (n : ℕ) :
    ‖φ.coeff n • t ^ n‖ ≤ ‖t ^ n‖ :=
  (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))

variable [CompleteSpace R]

/-- For a topologically nilpotent `t ∈ R`, `∑ n, φ.coeff n • t ^ n` is summable for `φ ∈ ℤ_p⟦X⟧`. -/
theorem summable_coeff_smul_pow {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) : Summable fun n : ℕ ↦ φ.coeff n • t ^ n :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (norm_coeff_smul_pow_le p φ t)
      (tendsto_zero_iff_norm_tendsto_zero.mp ht)

private theorem padicPowerSeriesEval_fun_continuous {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    Continuous fun φ : PowerSeries ℤ_[p] ↦ φ.evalAt t := by
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (half_pos hε)
  refine ⟨fun φ ↦ ∑ n ∈ Finset.range N, φ.coeff n • t ^ n, continuous_finsetSum _ fun n _ ↦
    (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] n).smul continuous_const, fun φ ↦ hεu ?_⟩
  rw [dist_eq_norm, PowerSeries.evalAt_def,
    ← (summable_coeff_smul_pow p ht φ).sum_add_tsum_nat_add N, add_sub_cancel_left]
  exact (IsUltrametricDist.norm_tsum_le_of_forall_le (C := ε / 2) fun k ↦
    le_of_lt <| (norm_coeff_smul_pow_le p φ t (k + N)).trans_lt
      (by simpa [dist_zero_right] using hN (k + N) (Nat.le_add_left N k))).trans_lt
    (half_lt_self hε)

/-- **Evaluation of integral power series at a topologically nilpotent element** of a complete
ultrametric normed `ℤ_p`-algebra `R` with contractive scalar action. -/
noncomputable def padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    PowerSeries ℤ_[p] →ₐ[ℤ_[p]] R where
  toFun φ := φ.evalAt t
  map_one' := PowerSeries.evalAt_one t
  map_zero' := PowerSeries.evalAt_zero t
  commutes' a := by rw [← PowerSeries.C_eq_algebraMap, PowerSeries.evalAt_C]
  map_add' φ ψ := by
    simp only [PowerSeries.evalAt_def, map_add, add_smul]
    exact (summable_coeff_smul_pow p ht φ).tsum_add (summable_coeff_smul_pow p ht ψ)
  map_mul' φ ψ :=
    have hcont := padicPowerSeriesEval_fun_continuous p ht
    congrFun (((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).prodMap
      (PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p])).equalizer
      (hcont.comp continuous_mul) ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd))
      (funext fun ⟨P, Q⟩ ↦ by simp [← Polynomial.coe_mul, PowerSeries.evalAt_coe])) (φ, ψ)

theorem padicPowerSeriesEval_apply {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) : padicPowerSeriesEval p ht φ = φ.evalAt t := (rfl)
theorem hasSum_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    (φ : PowerSeries ℤ_[p]) :
    HasSum (fun n : ℕ ↦ φ.coeff n • t ^ n) (padicPowerSeriesEval p ht φ) := by
  rw [padicPowerSeriesEval_apply, PowerSeries.evalAt_def]
  exact (summable_coeff_smul_pow p ht φ).hasSum
theorem continuous_padicPowerSeriesEval {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    Continuous (padicPowerSeriesEval p ht) := padicPowerSeriesEval_fun_continuous p ht
@[simp] theorem padicPowerSeriesEval_X {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    padicPowerSeriesEval p ht PowerSeries.X = t := PowerSeries.evalAt_X t
@[simp] theorem padicPowerSeriesEval_C {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0)) (a : ℤ_[p]) :
    padicPowerSeriesEval p ht (PowerSeries.C a) = algebraMap ℤ_[p] R a := PowerSeries.evalAt_C a t

/-- Substituting `b` (`PowerSeries.HasSubst b`) before evaluating at `t` equals evaluating at
`padicPowerSeriesEval p ht b`, whenever the latter is topologically nilpotent. -/
theorem padicPowerSeriesEval_subst {t : R} (ht : Tendsto (t ^ ·) atTop (𝓝 0))
    {b : PowerSeries ℤ_[p]} (hb : PowerSeries.HasSubst b)
    (hb' : Tendsto ((padicPowerSeriesEval p ht b) ^ ·) atTop (𝓝 0)) (φ : PowerSeries ℤ_[p]) :
    padicPowerSeriesEval p ht (φ.subst b) = padicPowerSeriesEval p hb' φ := by
  let L := (padicPowerSeriesEval p ht).comp (PowerSeries.substAlgHom hb)
  have hL_cont : Continuous L := ((continuous_padicPowerSeriesEval p ht).comp <|
    Continuous.powerSeries_subst continuous_id continuous_const fun _ ↦
      IsNilpotent.eq_zero hb).congr fun _ ↦ by simp [L, PowerSeries.coe_substAlgHom]
  have hLX : L PowerSeries.X = padicPowerSeriesEval p ht b := by
    simp [L, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hb]
  simpa [L, PowerSeries.coe_substAlgHom] using congrFun
    ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer hL_cont
      (continuous_padicPowerSeriesEval p hb') <| funext fun P ↦ by
        simp only [Function.comp_apply, PowerSeries.algHom_coe_eq_aeval, hLX,
          padicPowerSeriesEval_X]) φ

end PadicPowerSeriesEval

end TauCeti
