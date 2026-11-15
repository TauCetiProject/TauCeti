/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Series
import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Power series of `H^s` functions, `s > n / 2`

Let `E` be a finite-dimensional real inner product space of dimension `n` and `s > n / 2`. Since
`H^s(E)` is an algebra (`TemperedDistribution.exists_norm_toBesselPotentialSpace_mul_le`), with
`‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}`, the powers of `u ∈ H^s` satisfy
`‖u ^ (n + 1)‖_{H^s} ≤ C ^ n ‖u‖_{H^s} ^ (n + 1)`
(`TemperedDistribution.exists_norm_toBesselPotentialSpace_pow_le`), and a power series without
constant term,

`f(u) = ∑ₙ aₙ u ^ (n + 1)`,

converges in `H^s` as soon as `∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n` converges. The sum is the pointwise
sum of the series: by the Sobolev embedding, convergence in `H^s` implies convergence almost
everywhere (`TemperedDistribution.ae_tendsto_of_tendsto_toBesselPotentialSpace`). Hence

`‖f(u)‖_{H^s} ≤ ‖u‖_{H^s} ∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n`

(`TemperedDistribution.exists_hasSum_mul_pow`). For an entire function, such as `exp z - 1`,
there is no condition on `u`; for a function analytic on a disc, such as `log (1 + z)`, the
condition is a bound on `‖u‖_{H^s}`. This is how analytic functions act on the Sobolev algebra
without any composition (Moser) estimate. In particular, for `U ∈ H^s` the function `exp U - 1`
lies in `H^s`, and for a real `f ∈ H^s` so do `exp (c f) - 1`, `cos f - 1` and `sin f`. For
`U ∈ H^s` with small `H^s` norm, `log (1 + U)` lies in `H^s`.

The action is moreover locally Lipschitz. Differences of powers satisfy
`‖u ^ (n + 1) - w ^ (n + 1)‖_{H^s} ≤ (n + 1) (C R) ^ n ‖u - w‖_{H^s}` for
`‖u‖_{H^s}, ‖w‖_{H^s} ≤ R`
(`TemperedDistribution.exists_norm_toBesselPotentialSpace_pow_sub_pow_le`), so the power series
above satisfies

`‖f(u) - f(w)‖_{H^s} ≤ (∑ₙ |aₙ| (n + 1) (C R) ^ n) ‖u - w‖_{H^s}`

(`TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow`). For the
exponential the factor is `exp (C R)`, and for `log (1 + z)` it is `(1 - C R)⁻¹` when `C R < 1`.
These estimates make `U ↦ exp U - 1` and `U ↦ log (1 + U)` continuous for the `H^s` norm, which is
what the charts of a gauge group modelled on `H^s` require.

## Main declarations

* `TemperedDistribution.exists_hasSum_mul_pow`: a power series without constant term whose
  majorant series converges at `C ‖u‖_{H^s}` maps `u ∈ H^s` to an `H^s` function, which is the
  pointwise sum almost everywhere, with the norm bound above.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`: for an `L²` function `U ∈ H^s`,
  `exp U - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_mul_sub_one`: for a real `f ∈ H^s` and a
  complex constant `c`, `exp (c f) - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.exists_memSobolev_ae_eq_log_one_add`: for an `L²` function `U ∈ H^s`
  with `C ‖U‖_{H^s} < 1`, `log (1 + U)` is an `L²` function in `H^s`.
* `TemperedDistribution.cos_sub_one_mem_realSobolevFunctions`,
  `TemperedDistribution.sin_mem_realSobolevFunctions`: for a real `f ∈ H^s`, the real functions
  `cos f - 1` and `sin f` lie in `H^s`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow`: the
  Lipschitz estimate for power series without constant term.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp_sub_one`:
  `‖(exp U - 1) - (exp W - 1)‖_{H^s} ≤ exp (C R) ‖U - W‖_{H^s}`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_log_one_add`:
  `‖log (1 + U) - log (1 + W)‖_{H^s} ≤ (1 - C R)⁻¹ ‖U - W‖_{H^s}` when `C R < 1`.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

open MeasureTheory Module Filter
open scoped Nat SchwartzMap ENNReal Topology BesselPotentialSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

/-- **Power series act on `H^s`, `s > n / 2`.** There is a constant `C`, depending only on `s` and
`E`, with the following property. Let `u` be an `L²` function in `H^s` and `aₙ` complex
coefficients with `∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n < ∞`. Then the series `∑ₙ aₙ u(x) ^ (n + 1)`
converges for almost every `x`, and its sum is an `L²` function `v` in `H^s` with
`‖v‖_{H^s} ≤ ‖u‖_{H^s} ∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n`. -/
theorem exists_hasSum_mul_pow {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
      {a : ℕ → ℂ}, Summable (fun n ↦ ‖a n‖ * (C * ‖hu.toBesselPotentialSpace‖) ^ n) →
      ∃ v : Lp ℂ 2 (volume : Measure E),
        (∀ᵐ x ∂volume, HasSum (fun n ↦ a n * u x ^ (n + 1)) (v x)) ∧
        ∃ hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)), ‖hv.toBesselPotentialSpace‖ ≤
          ‖hu.toBesselPotentialSpace‖ *
            ∑' n, ‖a n‖ * (C * ‖hu.toBesselPotentialSpace‖) ^ n := by
  obtain ⟨C₁, hC₁, hpow⟩ := exists_norm_toBesselPotentialSpace_pow_le (E := E) hs
  obtain ⟨C₂, _, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := E) (F := ℂ) hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {u} hu {a} ha ↦ ?_⟩
  set C := max C₁ C₂
  set R := ‖hu.toBesselPotentialSpace‖
  -- The powers of `u`, with their `H^s` elements `w n`.
  choose p hpu hp hpn using hpow hu
  set w : ℕ → H^{s}(E) := fun n ↦ (hp n).toBesselPotentialSpace
  have hw (n : ℕ) : ‖a n • w n‖ ≤ R * (‖a n‖ * (C * R) ^ n) := by
    rw [norm_smul]
    calc ‖a n‖ * ‖w n‖ ≤ ‖a n‖ * (C₁ ^ n * R ^ (n + 1)) := by gcongr; exact hpn n
      _ ≤ ‖a n‖ * (C ^ n * R ^ (n + 1)) := by gcongr; exact le_max_left _ _
      _ = R * (‖a n‖ * (C * R) ^ n) := by ring
  have hsum : Summable fun n ↦ a n • w n := (ha.mul_left R).of_norm_bounded hw
  -- The series converges in `H^s` to the `H^s` element of an `L²` function `v`, and almost
  -- everywhere to `v`.
  obtain ⟨v, hv, hvF, hlim⟩ := exists_toBesselPotentialSpace_eq_tsum_and_ae_tendsto hs hp hsum
  refine ⟨v, ?_, hv, ?_⟩
  · filter_upwards [hlim, ae_all_iff.2 hpu, hsup hu] with x hx hpx hux
    -- The pointwise series is dominated by `C R` times the majorant series.
    have hbound (n : ℕ) : ‖a n * u x ^ (n + 1)‖ ≤ C * R * (‖a n‖ * (C * R) ^ n) := by
      rw [norm_mul, norm_pow]
      have hux' : ‖u x‖ ≤ C * R := hux.trans (by gcongr; exact le_max_right _ _)
      calc ‖a n‖ * ‖u x‖ ^ (n + 1) ≤ ‖a n‖ * (C * R) ^ (n + 1) := by gcongr
        _ = C * R * (‖a n‖ * (C * R) ^ n) := by ring
    refine ((ha.mul_left (C * R)).of_norm_bounded hbound).hasSum_iff_tendsto_nat.2 ?_
    simpa only [hpx, smul_eq_mul] using hx
  · rw [hvF, ← tsum_mul_left]
    exact tsum_of_norm_bounded (ha.mul_left R).hasSum hw

/-- **The exponential of an `H^s` function, `s > n / 2`.** For an `L²` function `U ∈ H^s`, the
function `exp U - 1` is an `L²` function in `H^s`: it is the exponential series of `U` without its
constant term. -/
theorem exists_memSobolev_ae_eq_exp_sub_one {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {U : Lp ℂ 2 (volume : Measure E)} (hU : MemSobolev s 2 (U : 𝓢'(E, ℂ))) :
    ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ Complex.exp (U x) - 1) ∧
      MemSobolev s 2 (v : 𝓢'(E, ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_hasSum_mul_pow hs
  set R := C * ‖hU.toBesselPotentialSpace‖
  -- The exponential series `∑ₙ w ^ (n + 1) / (n + 1)!`, majorized by `∑ₙ Rⁿ / n!`.
  have hsum : Summable fun n ↦ ‖(((n + 1)! : ℂ))⁻¹‖ * R ^ n := by
    refine (Real.summable_pow_div_factorial R).of_nonneg_of_le (fun n ↦ by positivity)
      fun n ↦ ?_
    rw [norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact_mod_cast n.le_succ
  obtain ⟨v, hv, hvs, -⟩ := hC hU hsum
  refine ⟨v, ?_, hvs⟩
  filter_upwards [hv] with x hx
  exact hx.unique (Complex.hasSum_exp_sub_one _)

/-- **The exponential of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s` and a complex
constant `c`, the function `exp (c f) - 1` is an `L²` function in `H^s`. This is
`exists_memSobolev_ae_eq_exp_sub_one` for the complex function `c f`. -/
theorem exists_memSobolev_ae_eq_exp_mul_sub_one {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) (c : ℂ) :
    ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ Complex.exp (c * f x) - 1) ∧
      MemSobolev s 2 (v : 𝓢'(E, ℂ)) := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  set U := c • Complex.ofRealCLM.compLp u
  have hU : MemSobolev s 2 (U : 𝓢'(E, ℂ)) := hu.toTemperedDistribution_smul c
  obtain ⟨v, hv, hvs⟩ := exists_memSobolev_ae_eq_exp_sub_one hs hU
  refine ⟨v, ?_, hvs⟩
  filter_upwards [hv, Lp.coeFn_smul c (Complex.ofRealCLM.compLp u),
    Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, huf] with x hx hUx hcx hfx
  rw [hx, hUx, Pi.smul_apply, hcx, Complex.ofRealCLM_apply, hfx, smul_eq_mul]

/-- **The logarithm of `1 + U` for small `U ∈ H^s`, `s > n / 2`.** There is a constant `C`,
depending only on `s` and `E`, such that for an `L²` function `U ∈ H^s` with `C ‖U‖_{H^s} < 1`, the
function `log (1 + U)` is an `L²` function in `H^s`: it is the logarithm series of `U`, which
converges since `|U| < 1` almost everywhere by the Sobolev embedding. -/
theorem exists_memSobolev_ae_eq_log_one_add {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {U : Lp ℂ 2 (volume : Measure E)} (hU : MemSobolev s 2 (U : 𝓢'(E, ℂ))),
      C * ‖hU.toBesselPotentialSpace‖ < 1 →
      ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ Complex.log (1 + U x)) ∧
        MemSobolev s 2 (v : 𝓢'(E, ℂ)) := by
  obtain ⟨C₁, hC₁, hser⟩ := exists_hasSum_mul_pow hs
  obtain ⟨C₂, -, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := E) (F := ℂ) hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {U} hU hCU ↦ ?_⟩
  set R := ‖hU.toBesselPotentialSpace‖
  have hR : 0 ≤ R := norm_nonneg _
  have hC₁R : C₁ * R < 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) hR).trans_lt hCU
  have hC₂R : C₂ * R < 1 := (mul_le_mul_of_nonneg_right (le_max_right _ _) hR).trans_lt hCU
  -- The logarithm series `∑ₙ (-1)ⁿ z ^ (n + 1) / (n + 1)`, majorized by the geometric series.
  have hsum : Summable fun n : ℕ ↦ ‖((-1) ^ n / (n + 1) : ℂ)‖ * (C₁ * R) ^ n := by
    refine (summable_geometric_of_lt_one (by positivity) hC₁R).of_nonneg_of_le
      (fun n ↦ by positivity) fun n ↦ ?_
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [Complex.norm_neg_one_pow_div_add_one]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left n.cast_nonneg)
  obtain ⟨v, hv, hvs, -⟩ := hser hU hsum
  refine ⟨v, ?_, hvs⟩
  filter_upwards [hv, hsup hU] with x hx hUx
  exact hx.unique (Complex.hasSum_taylorSeries_log' (hUx.trans_lt hC₂R))

/-- **The cosine of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s`, the function
`cos f - 1` lies in `H^s`: it is the half sum of `exp (i f) - 1` and `exp (-i f) - 1`. -/
theorem cos_sub_one_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) :
    (fun x ↦ Real.cos (f x) - 1) ∈ realSobolevFunctions E s 2 := by
  obtain ⟨vp, hvp, hsp⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf Complex.I
  obtain ⟨vm, hvm, hsm⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf (-Complex.I)
  refine mem_realSobolevFunctions_of_ae_eq_ofReal (v := (2⁻¹ : ℂ) • (vp + vm)) ?_ ?_
  · exact (hsp.toTemperedDistribution_add hsm).toTemperedDistribution_smul _
  · filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (vp + vm), Lp.coeFn_add vp vm, hvp, hvm]
      with x h h' hp hm
    rw [h, Pi.smul_apply, h', Pi.add_apply, hp, hm, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_cos, Complex.ofReal_one]
    have h2 := Complex.two_cos (f x : ℂ)
    simp only [neg_mul, mul_comm Complex.I] at h2 ⊢
    linear_combination (-2⁻¹ : ℂ) * h2

/-- **The sine of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s`, the function
`sin f` lies in `H^s`: it is the half difference of `exp (i f) - 1` and `exp (-i f) - 1`, divided
by `i`. -/
theorem sin_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) :
    (fun x ↦ Real.sin (f x)) ∈ realSobolevFunctions E s 2 := by
  obtain ⟨vp, hvp, hsp⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf Complex.I
  obtain ⟨vm, hvm, hsm⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf (-Complex.I)
  refine mem_realSobolevFunctions_of_ae_eq_ofReal
    (v := (-(2⁻¹ * Complex.I) : ℂ) • (vp - vm)) ?_ ?_
  · exact (hsp.toTemperedDistribution_sub hsm).toTemperedDistribution_smul _
  · filter_upwards [Lp.coeFn_smul (-(2⁻¹ * Complex.I) : ℂ) (vp - vm), Lp.coeFn_sub vp vm, hvp,
      hvm] with x h h' hp hm
    rw [h, Pi.smul_apply, h', Pi.sub_apply, hp, hm, smul_eq_mul, Complex.ofReal_sin]
    have h2 := Complex.two_sin (f x : ℂ)
    simp only [neg_mul, mul_comm Complex.I] at h2 ⊢
    linear_combination (-2⁻¹ : ℂ) * h2

/-- **Power series act Lipschitz continuously on `H^s`, `s > n / 2`.** There is a constant `C`,
depending only on `s` and `E`, with the following property. Let `u, w` be `L²` functions in `H^s`
with `‖u‖_{H^s}, ‖w‖_{H^s} ≤ R`, and let `aₙ` be complex coefficients with
`∑ₙ |aₙ| (n + 1) (C R) ^ n < ∞`. If `v` and `v'` are `L²` functions in `H^s` which are almost
everywhere the sums of `∑ₙ aₙ u ^ (n + 1)` and `∑ₙ aₙ w ^ (n + 1)`, then

`‖v - v'‖_{H^s} ≤ (∑ₙ |aₙ| (n + 1) (C R) ^ n) ‖u - w‖_{H^s}`.

The majorant is the derivative of the majorant series `∑ₙ |aₙ| (C R) ^ (n + 1)` of
`exists_hasSum_mul_pow`. -/
theorem exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {u w : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
      (hw : MemSobolev s 2 (w : 𝓢'(E, ℂ))) {R : ℝ}, ‖hu.toBesselPotentialSpace‖ ≤ R →
      ‖hw.toBesselPotentialSpace‖ ≤ R → ∀ {a : ℕ → ℂ},
      Summable (fun n ↦ ‖a n‖ * (n + 1) * (C * R) ^ n) →
      ∀ {v v' : Lp ℂ 2 (volume : Measure E)} (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)))
        (hv' : MemSobolev s 2 (v' : 𝓢'(E, ℂ))),
        (∀ᵐ x ∂volume, HasSum (fun n ↦ a n * u x ^ (n + 1)) (v x)) →
        (∀ᵐ x ∂volume, HasSum (fun n ↦ a n * w x ^ (n + 1)) (v' x)) →
        ‖hv.toBesselPotentialSpace - hv'.toBesselPotentialSpace‖ ≤
          (∑' n, ‖a n‖ * (n + 1) * (C * R) ^ n) *
            ‖hu.toBesselPotentialSpace - hw.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC, hdiff⟩ := exists_norm_toBesselPotentialSpace_pow_sub_pow_le (E := E) hs
  refine ⟨C, hC, fun {u w} hu hw {R} huR hwR {a} ha {v v'} hv hv' hvu hvw ↦ ?_⟩
  set δ := ‖hu.toBesselPotentialSpace - hw.toBesselPotentialSpace‖
  -- The differences of powers, with their `H^s` elements `D n`.
  choose d hdu hd hdn using hdiff hu hw huR hwR
  set D : ℕ → H^{s}(E) := fun n ↦ (hd n).toBesselPotentialSpace
  have hD (n : ℕ) : ‖a n • D n‖ ≤ δ * (‖a n‖ * (n + 1) * (C * R) ^ n) := by
    rw [norm_smul]
    calc ‖a n‖ * ‖D n‖ ≤ ‖a n‖ * ((n + 1) * (C * R) ^ n * δ) := by gcongr; exact hdn n
      _ = δ * (‖a n‖ * (n + 1) * (C * R) ^ n) := by ring
  have hsum : Summable fun n ↦ a n • D n := (ha.mul_left δ).of_norm_bounded hD
  -- The series converges in `H^s`, and almost everywhere, to an `L²` function `g = v - v'`.
  obtain ⟨g, hg, hgF, hlim⟩ := exists_toBesselPotentialSpace_eq_tsum_and_ae_tendsto hs hd hsum
  have hgv : g = v - v' := by
    refine Lp.ext ?_
    filter_upwards [hlim, ae_all_iff.2 hdu, hvu, hvw, Lp.coeFn_sub v v'] with x hx hdx h₁ h₂ hsub
    rw [hsub, Pi.sub_apply]
    refine tendsto_nhds_unique hx ?_
    simpa only [hdx, smul_eq_mul, mul_sub, Finset.sum_sub_distrib] using
      (h₁.sub h₂).tendsto_sum_nat
  subst hgv
  rw [← hv.toBesselPotentialSpace_toTemperedDistribution_sub hv' hg, hgF, ← tsum_mul_right]
  refine tsum_of_norm_bounded ((ha.mul_right δ).hasSum) fun n ↦ (hD n).trans_eq (mul_comm _ _)

/-- **The exponential is locally Lipschitz on `H^s`, `s > n / 2`.** There is a constant `C`,
depending only on `s` and `E`, such that for `L²` functions `U, W ∈ H^s` with
`‖U‖_{H^s}, ‖W‖_{H^s} ≤ R`, the `H^s` functions `exp U - 1` and `exp W - 1`
(`exists_memSobolev_ae_eq_exp_sub_one`) satisfy
`‖(exp U - 1) - (exp W - 1)‖_{H^s} ≤ exp (C R) ‖U - W‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp_sub_one {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {U W : Lp ℂ 2 (volume : Measure E)} (hU : MemSobolev s 2 (U : 𝓢'(E, ℂ)))
      (hW : MemSobolev s 2 (W : 𝓢'(E, ℂ))) {R : ℝ}, ‖hU.toBesselPotentialSpace‖ ≤ R →
      ‖hW.toBesselPotentialSpace‖ ≤ R →
      ∀ {v v' : Lp ℂ 2 (volume : Measure E)} (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)))
        (hv' : MemSobolev s 2 (v' : 𝓢'(E, ℂ))),
        v =ᵐ[volume] (fun x ↦ Complex.exp (U x) - 1) →
        v' =ᵐ[volume] (fun x ↦ Complex.exp (W x) - 1) →
        ‖hv.toBesselPotentialSpace - hv'.toBesselPotentialSpace‖ ≤
          Real.exp (C * R) * ‖hU.toBesselPotentialSpace - hW.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow hs
  refine ⟨C, hC, fun {U W} hU hW {R} hUR hWR {v v'} hv hv' hvU hvW ↦ ?_⟩
  -- The exponential series `∑ₙ z ^ (n + 1) / (n + 1)!`, whose majorant is `∑ₙ x ^ n / n!`.
  have ha (n : ℕ) : ‖(((n + 1)! : ℂ))⁻¹‖ * (n + 1) * (C * R) ^ n = (C * R) ^ n / n ! := by
    rw [norm_inv, Complex.norm_natCast, Nat.factorial_succ]
    push_cast
    field_simp
  have h := hlip hU hW hUR hWR (a := fun n ↦ (((n + 1)! : ℂ))⁻¹)
    (by simpa only [ha] using Real.summable_pow_div_factorial (C * R)) hv hv'
    (by filter_upwards [hvU] with x hx; rw [hx]; exact Complex.hasSum_exp_sub_one _)
    (by filter_upwards [hvW] with x hx; rw [hx]; exact Complex.hasSum_exp_sub_one _)
  have hexp : Real.exp (C * R) = ∑' n, (C * R) ^ n / n ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rwa [tsum_congr ha, ← hexp] at h

/-- **The logarithm is Lipschitz near `1` on `H^s`, `s > n / 2`.** There is a constant `C`,
depending only on `s` and `E`, such that for `L²` functions `U, W ∈ H^s` with
`‖U‖_{H^s}, ‖W‖_{H^s} ≤ R` and `C R < 1`, any `L²` functions in `H^s` agreeing almost everywhere
with `log (1 + U)` and `log (1 + W)` satisfy
`‖log (1 + U) - log (1 + W)‖_{H^s} ≤ (1 - C R)⁻¹ ‖U - W‖_{H^s}`. The condition `C R < 1` makes
`|U|, |W| < 1` almost everywhere, by the Sobolev embedding, so that the logarithm series
converges. -/
theorem exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_log_one_add {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {U W : Lp ℂ 2 (volume : Measure E)} (hU : MemSobolev s 2 (U : 𝓢'(E, ℂ)))
      (hW : MemSobolev s 2 (W : 𝓢'(E, ℂ))) {R : ℝ}, ‖hU.toBesselPotentialSpace‖ ≤ R →
      ‖hW.toBesselPotentialSpace‖ ≤ R → C * R < 1 →
      ∀ {v v' : Lp ℂ 2 (volume : Measure E)} (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)))
        (hv' : MemSobolev s 2 (v' : 𝓢'(E, ℂ))),
        v =ᵐ[volume] (fun x ↦ Complex.log (1 + U x)) →
        v' =ᵐ[volume] (fun x ↦ Complex.log (1 + W x)) →
        ‖hv.toBesselPotentialSpace - hv'.toBesselPotentialSpace‖ ≤
          (1 - C * R)⁻¹ * ‖hU.toBesselPotentialSpace - hW.toBesselPotentialSpace‖ := by
  obtain ⟨C₁, hC₁, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_hasSum_mul_pow hs
  obtain ⟨C₂, -, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := E) (F := ℂ) hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {U W} hU hW {R} hUR hWR hCR {v v'} hv hv' hvU
    hvW ↦ ?_⟩
  set C := max C₁ C₂
  have hR : 0 ≤ R := (norm_nonneg _).trans hUR
  have hC₁R : 0 ≤ C₁ * R := by positivity
  have hC₁R' : C₁ * R < 1 := (mul_le_mul_of_nonneg_right (le_max_left _ _) hR).trans_lt hCR
  -- The logarithm series `∑ₙ (-1)ⁿ z ^ (n + 1) / (n + 1)`, whose majorant is geometric.
  set a : ℕ → ℂ := fun n ↦ (-1) ^ n / (n + 1)
  have ha (n : ℕ) : ‖a n‖ * (n + 1) * (C₁ * R) ^ n = (C₁ * R) ^ n := by
    rw [Complex.norm_neg_one_pow_div_add_one]
    field_simp
  have hsmall {X : Lp ℂ 2 (volume : Measure E)} (hX : MemSobolev s 2 (X : 𝓢'(E, ℂ)))
      (hXR : ‖hX.toBesselPotentialSpace‖ ≤ R) : ∀ᵐ x ∂volume, ‖X x‖ < 1 := by
    filter_upwards [hsup hX] with x hx
    calc ‖X x‖ ≤ C₂ * ‖hX.toBesselPotentialSpace‖ := hx
      _ ≤ C * R := by gcongr; exact le_max_right _ _
      _ < 1 := hCR
  have h := hlip hU hW hUR hWR (a := a)
    (by simpa only [ha] using summable_geometric_of_lt_one hC₁R hC₁R') hv hv'
    (by filter_upwards [hvU, hsmall hU hUR] with x hx hx'
        rw [hx]; exact Complex.hasSum_taylorSeries_log' hx')
    (by filter_upwards [hvW, hsmall hW hWR] with x hx hx'
        rw [hx]; exact Complex.hasSum_taylorSeries_log' hx')
  rw [tsum_congr ha, tsum_geometric_of_lt_one hC₁R hC₁R'] at h
  have hle : C₁ * R ≤ C * R := mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  have hinv : (1 - C₁ * R)⁻¹ ≤ (1 - C * R)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  exact h.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))

end TemperedDistribution
