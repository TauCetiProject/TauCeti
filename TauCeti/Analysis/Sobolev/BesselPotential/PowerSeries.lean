/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

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
lies in `H^s`, and for a real `f ∈ H^s` so do `exp (c f) - 1`, `cos f - 1` and `sin f`.

## Main declarations

* `TemperedDistribution.exists_hasSum_mul_pow`: a power series without constant term whose
  majorant series converges at `C ‖u‖_{H^s}` maps `u ∈ H^s` to an `H^s` function, which is the
  pointwise sum almost everywhere, with the norm bound above.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`: for an `L²` function `U ∈ H^s`,
  `exp U - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_mul_sub_one`: for a real `f ∈ H^s` and a
  complex constant `c`, `exp (c f) - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.exp_mul_sub_one_mem_realSobolevFunctions`: for a real `f ∈ H^s` and a
  real constant `c`, the real function `exp (c f) - 1` lies in `H^s`.
* `TemperedDistribution.cos_sub_one_mem_realSobolevFunctions`,
  `TemperedDistribution.sin_mem_realSobolevFunctions`: for a real `f ∈ H^s`, the real functions
  `cos f - 1` and `sin f` lie in `H^s`.

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
  have hs0 : 0 ≤ s := by
    have := (finrank ℝ E).cast_nonneg (α := ℝ)
    linarith
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
  set F := ∑' n, a n • w n
  -- The limit `F` is the `H^s` element of an `L²` function `v`.
  obtain ⟨v, hFv⟩ := memSobolev_zero_iff.1 (F.memSobolev_toDistr.mono hs0)
  have hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)) := hFv ▸ F.memSobolev_toDistr
  have hvF : hv.toBesselPotentialSpace = F := BesselPotentialSpace.ext (by simp [hFv])
  refine ⟨v, ?_, hv, ?_⟩
  · -- The partial sums converge to `F` in `H^s`, hence almost everywhere.
    set S : ℕ → Lp ℂ 2 (volume : Measure E) := fun N ↦ ∑ n ∈ Finset.range N, a n • p n
    have hS (N : ℕ) : MemSobolev s 2 (S N : 𝓢'(E, ℂ)) := by
      simpa only [S, Lp.toTemperedDistribution_sum, Lp.toTemperedDistribution_smul] using
        MemSobolev.sum fun n (_ : n ∈ Finset.range N) ↦ (hp n).smul (a n)
    have hlim := ae_tendsto_of_tendsto_toBesselPotentialSpace hs hS hv <| by
      simpa only [MemSobolev.toBesselPotentialSpace_toTemperedDistribution_sum_smul
        fun n _ ↦ hp n, Finset.sum_attach _ fun n ↦ a n • (hp n).toBesselPotentialSpace, hvF] using
        hsum.hasSum.tendsto_sum_nat
    have hpart : ∀ᵐ x ∂volume, ∀ N, S N x = ∑ n ∈ Finset.range N, a n * u x ^ (n + 1) :=
      ae_all_iff.2 fun N ↦ by
        filter_upwards [(Lp.coeFn_finsetSum _ _).trans <| eventuallyEq_sum fun n _ ↦
          (Lp.coeFn_smul (a n) (p n)).trans ((hpu n).const_smul (a n))] with x h
        simpa [S] using h
    filter_upwards [hlim, hpart, hsup hu] with x hx hSx hux
    -- The pointwise series is dominated by `C R` times the majorant series.
    have hbound (n : ℕ) : ‖a n * u x ^ (n + 1)‖ ≤ C * R * (‖a n‖ * (C * R) ^ n) := by
      rw [norm_mul, norm_pow]
      have hux' : ‖u x‖ ≤ C * R := hux.trans (by gcongr; exact le_max_right _ _)
      calc ‖a n‖ * ‖u x‖ ^ (n + 1) ≤ ‖a n‖ * (C * R) ^ (n + 1) := by gcongr
        _ = C * R * (‖a n‖ * (C * R) ^ n) := by ring
    refine ((ha.mul_left (C * R)).of_norm_bounded hbound).hasSum_iff_tendsto_nat.2 ?_
    simpa only [hSx] using hx
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
  refine hx.unique ?_
  have h := (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp (U x))
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, ← Complex.exp_eq_exp_ℂ] at h
  simpa only [div_eq_inv_mul] using h

/-- **The exponential of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s` and a complex
constant `c`, the function `exp (c f) - 1` is an `L²` function in `H^s`. This is
`exists_memSobolev_ae_eq_exp_sub_one` for the complex function `c f`. -/
theorem exists_memSobolev_ae_eq_exp_mul_sub_one {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) (c : ℂ) :
    ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ Complex.exp (c * f x) - 1) ∧
      MemSobolev s 2 (v : 𝓢'(E, ℂ)) := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  set U := c • Complex.ofRealCLM.compLp u
  have hU : MemSobolev s 2 (U : 𝓢'(E, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul]
    exact hu.smul c
  obtain ⟨v, hv, hvs⟩ := exists_memSobolev_ae_eq_exp_sub_one hs hU
  refine ⟨v, ?_, hvs⟩
  filter_upwards [hv, Lp.coeFn_smul c (Complex.ofRealCLM.compLp u),
    Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, huf] with x hx hUx hcx hfx
  rw [hx, hUx, Pi.smul_apply, hcx, Complex.ofRealCLM_apply, hfx, smul_eq_mul]

/-- **The real exponential of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s` and a
real constant `c`, the real function `exp (c f) - 1` lies in `H^s`. This is
`exists_memSobolev_ae_eq_exp_mul_sub_one`, whose `L²` representative is real valued. -/
theorem exp_mul_sub_one_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) (c : ℝ) :
    (fun x ↦ Real.exp (c * f x) - 1) ∈ realSobolevFunctions E s 2 := by
  obtain ⟨v, hv, hvs⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf c
  refine mem_realSobolevFunctions_of_ae_eq_ofReal hvs ?_
  filter_upwards [hv] with x hx
  rw [hx, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_one]

/-- **The cosine of a real `H^s` function, `s > n / 2`.** For a real `f ∈ H^s`, the function
`cos f - 1` lies in `H^s`: it is the half sum of `exp (i f) - 1` and `exp (-i f) - 1`. -/
theorem cos_sub_one_mem_realSobolevFunctions {s : ℝ} (hs : finrank ℝ E < 2 * s) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E s 2) :
    (fun x ↦ Real.cos (f x) - 1) ∈ realSobolevFunctions E s 2 := by
  obtain ⟨vp, hvp, hsp⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf Complex.I
  obtain ⟨vm, hvm, hsm⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hf (-Complex.I)
  refine mem_realSobolevFunctions_of_ae_eq_ofReal (v := (2⁻¹ : ℂ) • (vp + vm)) ?_ ?_
  · rw [Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_add]
    exact (hsp.add hsm).smul _
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
  · rw [Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_sub]
    exact (hsp.sub hsm).smul _
  · filter_upwards [Lp.coeFn_smul (-(2⁻¹ * Complex.I) : ℂ) (vp - vm), Lp.coeFn_sub vp vm, hvp,
      hvm] with x h h' hp hm
    rw [h, Pi.smul_apply, h', Pi.sub_apply, hp, hm, smul_eq_mul, Complex.ofReal_sin]
    have h2 := Complex.two_sin (f x : ℂ)
    simp only [neg_mul, mul_comm Complex.I] at h2 ⊢
    linear_combination (-2⁻¹ : ℂ) * h2

end TemperedDistribution
