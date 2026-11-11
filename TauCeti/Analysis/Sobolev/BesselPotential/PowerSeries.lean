/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
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

The same majorants bound the exponential quantitatively:
`‖exp U - 1‖_{H^s} ≤ ‖U‖_{H^s} exp (C ‖U‖_{H^s})` and
`‖exp U - 1 - U‖_{H^s} ≤ C ‖U‖_{H^s}² exp (C ‖U‖_{H^s})`
(`TemperedDistribution.exists_norm_toBesselPotentialSpace_exp_sub_one_le`). Writing
`exp U₁ - exp U₂ - (U₁ - U₂) = (exp U₂ - 1)(exp δ - 1) + (exp δ - 1 - δ)` with `δ = U₁ - U₂`, the
algebra estimate then shows that `U ↦ exp U - 1` is tangent to the identity at `0`
(`TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_sub_le`), hence bi-Lipschitz, with
constants `1 / 2` and `2`, on a small ball about `0`
(`TemperedDistribution.exists_pos_forall_norm_toBesselPotentialSpace_sub_le`). This is the estimate
behind exponential charts of Sobolev gauge groups `{u = 1 + h : h ∈ H^s, |u| = 1}`.

## Main declarations

* `TemperedDistribution.exists_hasSum_mul_pow`: a power series without constant term whose
  majorant series converges at `C ‖u‖_{H^s}` maps `u ∈ H^s` to an `H^s` function, which is the
  pointwise sum almost everywhere, with the norm bound above.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`: for an `L²` function `U ∈ H^s`,
  `exp U - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.exists_memSobolev_ae_eq_exp_mul_sub_one`: for a real `f ∈ H^s` and a
  complex constant `c`, `exp (c f) - 1` is an `L²` function in `H^s`.
* `TemperedDistribution.cos_sub_one_mem_realSobolevFunctions`,
  `TemperedDistribution.sin_mem_realSobolevFunctions`: for a real `f ∈ H^s`, the real functions
  `cos f - 1` and `sin f` lie in `H^s`.
* `TemperedDistribution.exists_memSobolev_ae_eq_log_one_add`: for a small `L²` function `h ∈ H^s`,
  `log (1 + h)` is an `L²` function in `H^s`, of norm at most `2 ‖h‖_{H^s}`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_exp_sub_one_le`: the `H^s` norms of
  `exp U - 1` and of `exp U - 1 - U`.
* `TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_sub_le`: `exp U₁ - exp U₂` differs
  from `U₁ - U₂` by at most a constant times `(‖U₂‖_{H^s} + ‖U₁ - U₂‖_{H^s}) ‖U₁ - U₂‖_{H^s}` on
  bounded sets.
* `TemperedDistribution.exists_pos_forall_norm_toBesselPotentialSpace_sub_le`: `U ↦ exp U - 1` is
  bi-Lipschitz on a ball about `0` in `H^s`.

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
  obtain ⟨C₂, hC₂, hsup⟩ :=
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

/-- **The logarithm on `H^s`, `s > n / 2`.** There is a constant `C ≥ 0`, depending only on `s`
and `E`, such that every `L²` function `h ∈ H^s` with `C ‖h‖_{H^s} ≤ 1 / 2` satisfies
`‖h(x)‖ ≤ 1 / 2` for almost every `x`, and `log (1 + h)` is then an `L²` function `v ∈ H^s` with
`‖v‖_{H^s} ≤ 2 ‖h‖_{H^s}`. -/
theorem exists_memSobolev_ae_eq_log_one_add {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {h : Lp ℂ 2 (volume : Measure E)} (hh : MemSobolev s 2 (h : 𝓢'(E, ℂ))),
      C * ‖hh.toBesselPotentialSpace‖ ≤ 1 / 2 →
      (∀ᵐ x ∂volume, ‖h x‖ ≤ 1 / 2) ∧
        ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ Complex.log (1 + h x)) ∧
          ∃ hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)),
            ‖hv.toBesselPotentialSpace‖ ≤ 2 * ‖hh.toBesselPotentialSpace‖ := by
  obtain ⟨C₁, hC₁, hser⟩ := exists_hasSum_mul_pow hs
  obtain ⟨C₂, hC₂, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := E) (F := ℂ) hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {h} hh hCR ↦ ?_⟩
  set R := ‖hh.toBesselPotentialSpace‖
  have hR0 : 0 ≤ R := norm_nonneg _
  have hC₁R : C₁ * R ≤ 1 / 2 := (by gcongr; exact le_max_left _ _ : C₁ * R ≤ _).trans hCR
  have hC₂R : C₂ * R ≤ 1 / 2 := (by gcongr; exact le_max_right _ _ : C₂ * R ≤ _).trans hCR
  have hsmall : ∀ᵐ x ∂volume, ‖h x‖ ≤ 1 / 2 := by
    filter_upwards [hsup hh] with x hx
    exact hx.trans hC₂R
  -- The logarithm series `∑ₙ (-1)ⁿ wⁿ⁺¹ / (n + 1)`, majorized by the geometric series.
  set a : ℕ → ℂ := fun n ↦ (-1) ^ n / (n + 1)
  have ha (n : ℕ) : ‖a n‖ * (C₁ * R) ^ n ≤ (C₁ * R) ^ n := by
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    exact_mod_cast Nat.le_add_left 1 n
  have hgeom := summable_geometric_of_lt_one (by positivity) (hC₁R.trans_lt (by norm_num))
  have hsum : Summable fun n ↦ ‖a n‖ * (C₁ * R) ^ n :=
    hgeom.of_nonneg_of_le (fun n ↦ by positivity) ha
  obtain ⟨v, hv, hvs, hvn⟩ := hser hh hsum
  refine ⟨hsmall, v, ?_, hvs, ?_⟩
  · filter_upwards [hv, hsmall] with x hvx hx
    have hlog := (hasSum_nat_add_iff' 1).2
      (Complex.hasSum_taylorSeries_log (hx.trans_lt (by norm_num)))
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, CharP.cast_eq_zero, div_zero,
      sub_zero] at hlog
    refine hvx.unique ?_
    convert hlog using 1
    ext n
    simp only [a]
    push_cast
    ring
  · -- The majorant is at most `∑ₙ (C R)ⁿ = (1 - C R)⁻¹ ≤ 2`.
    have htsum : ∑' n, ‖a n‖ * (C₁ * R) ^ n ≤ 2 := by
      calc ∑' n, ‖a n‖ * (C₁ * R) ^ n ≤ ∑' n, (C₁ * R) ^ n := hsum.tsum_le_tsum ha hgeom
        _ = (1 - C₁ * R)⁻¹ := tsum_geometric_of_lt_one (by positivity) (by linarith)
        _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
    calc ‖hvs.toBesselPotentialSpace‖ ≤ R * ∑' n, ‖a n‖ * (C₁ * R) ^ n := hvn
      _ ≤ R * 2 := by gcongr
      _ = 2 * R := mul_comm _ _

/-- The majorant of the exponential series without its constant term: for `x ≥ 0`,
`∑ₙ xⁿ / (n + 1)! ≤ exp x`. -/
private theorem summable_and_tsum_le_exp {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n ↦ ‖(((n + 1)! : ℂ))⁻¹‖ * x ^ n) ∧
      ∑' n, ‖(((n + 1)! : ℂ))⁻¹‖ * x ^ n ≤ Real.exp x := by
  have hexp : HasSum (fun n ↦ x ^ n / n !) (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have hle (n : ℕ) : ‖(((n + 1)! : ℂ))⁻¹‖ * x ^ n ≤ x ^ n / n ! := by
    rw [norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact_mod_cast n.le_succ
  have hsum : Summable (fun n ↦ ‖(((n + 1)! : ℂ))⁻¹‖ * x ^ n) :=
    hexp.summable.of_nonneg_of_le (fun n ↦ by positivity) hle
  exact ⟨hsum, hexp.tsum_eq ▸ hsum.tsum_le_tsum hle hexp.summable⟩

/-- The majorant of the exponential series without its constant and linear terms: for `x ≥ 0`,
`∑ₙ₌₁ xⁿ / (n + 1)! ≤ x exp x`. -/
private theorem summable_and_tsum_ite_le_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n ↦ ‖(if n = 0 then 0 else (((n + 1)! : ℂ))⁻¹)‖ * x ^ n) ∧
      ∑' n, ‖(if n = 0 then 0 else (((n + 1)! : ℂ))⁻¹)‖ * x ^ n ≤ x * Real.exp x := by
  set f : ℕ → ℝ := fun n ↦ ‖(if n = 0 then 0 else (((n + 1)! : ℂ))⁻¹)‖ * x ^ n
  have hexp : HasSum (fun n ↦ x * (x ^ n / n !)) (x * Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp x).mul_left x
  have hle (n : ℕ) : f (n + 1) ≤ x * (x ^ n / n !) := by
    simp only [f, Nat.add_one_ne_zero, ite_false, norm_inv, Complex.norm_natCast]
    rw [pow_succ, div_eq_inv_mul]
    calc ((n + 1 + 1)! : ℝ)⁻¹ * (x ^ n * x) ≤ (n ! : ℝ)⁻¹ * (x ^ n * x) := by
          gcongr
          omega
      _ = x * ((n ! : ℝ)⁻¹ * x ^ n) := by ring
  have hsum : Summable fun n ↦ f (n + 1) :=
    hexp.summable.of_nonneg_of_le (fun n ↦ by positivity) hle
  have hf := hsum.hasSum.zero_add
  have hf0 : f 0 = 0 := by simp [f]
  refine ⟨hf.summable, ?_⟩
  rw [hf.tsum_eq, hf0, zero_add]
  exact hexp.tsum_eq ▸ hsum.tsum_le_tsum hle hexp.summable

/-- **Norm bounds for the exponential on `H^s`, `s > n / 2`.** There is a constant `C ≥ 0`,
depending only on `s` and `E`, such that for every `L²` function `U ∈ H^s`, every `L²` function
`v ∈ H^s` equal almost everywhere to `exp U - 1` satisfies
`‖v‖_{H^s} ≤ ‖U‖_{H^s} exp (C ‖U‖_{H^s})`, and every `L²` function `w ∈ H^s` equal almost
everywhere to `exp U - 1 - U` satisfies `‖w‖_{H^s} ≤ C ‖U‖_{H^s}² exp (C ‖U‖_{H^s})`. Such
`v` exist by `exists_memSobolev_ae_eq_exp_sub_one`, and then `w = v - U`. -/
theorem exists_norm_toBesselPotentialSpace_exp_sub_one_le {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {U : Lp ℂ 2 (volume : Measure E)} (hU : MemSobolev s 2 (U : 𝓢'(E, ℂ))),
      (∀ {v : Lp ℂ 2 (volume : Measure E)} (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ))),
        v =ᵐ[volume] (fun x ↦ Complex.exp (U x) - 1) →
        ‖hv.toBesselPotentialSpace‖ ≤
          ‖hU.toBesselPotentialSpace‖ * Real.exp (C * ‖hU.toBesselPotentialSpace‖)) ∧
      (∀ {w : Lp ℂ 2 (volume : Measure E)} (hw : MemSobolev s 2 (w : 𝓢'(E, ℂ))),
        w =ᵐ[volume] (fun x ↦ Complex.exp (U x) - 1 - U x) →
        ‖hw.toBesselPotentialSpace‖ ≤
          C * ‖hU.toBesselPotentialSpace‖ ^ 2 * Real.exp (C * ‖hU.toBesselPotentialSpace‖)) := by
  obtain ⟨C, hC0, hC⟩ := exists_hasSum_mul_pow hs
  refine ⟨C, hC0, fun {U} hU ↦ ⟨fun {v} hv hvU ↦ ?_, fun {w} hw hwU ↦ ?_⟩⟩
  · set R := ‖hU.toBesselPotentialSpace‖
    obtain ⟨hsum, hle⟩ := summable_and_tsum_le_exp (x := C * R) (by positivity)
    obtain ⟨v₀, hv₀, hv₀s, hv₀n⟩ := hC hU hsum
    -- `v₀` is the sum of the exponential series of `U` without its constant term.
    have hvv₀ : v = v₀ := by
      refine Lp.ext (hvU.trans ?_)
      filter_upwards [hv₀] with x hx
      refine (hx.unique ?_).symm
      have h := (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp (U x))
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, ← Complex.exp_eq_exp_ℂ] at h
      simpa only [div_eq_inv_mul] using h
    subst hvv₀
    exact hv₀n.trans (by gcongr)
  · set R := ‖hU.toBesselPotentialSpace‖
    obtain ⟨hsum, hle⟩ := summable_and_tsum_ite_le_mul_exp (x := C * R) (by positivity)
    obtain ⟨w₀, hw₀, hw₀s, hw₀n⟩ := hC hU hsum
    -- `w₀` is the sum of the exponential series of `U` without its constant and linear terms.
    have hww₀ : w = w₀ := by
      refine Lp.ext (hwU.trans ?_)
      filter_upwards [hw₀] with x hx
      refine (hx.unique ?_).symm
      have h := (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp (U x))
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, ← Complex.exp_eq_exp_ℂ] at h
      convert h.sub (hasSum_ite_eq 0 (U x)) using 1
      funext n
      rcases n with _ | n
      · simp
      · simp [div_eq_inv_mul]
    subst hww₀
    calc ‖hw₀s.toBesselPotentialSpace‖ ≤ R * (C * R * Real.exp (C * R)) :=
          hw₀n.trans (by gcongr)
      _ = C * R ^ 2 * Real.exp (C * R) := by ring


/-- The identity `exp U₁ - exp U₂ - (U₁ - U₂) = (exp U₂ - 1) w + (w - δ)` in `H^s`, where
`δ = U₁ - U₂` and `w` represents `exp δ - 1`. -/
private theorem toBesselPotentialSpace_sub_sub_eq {s : ℝ} (hs : finrank ℝ E < 2 * s)
    {U₁ U₂ v₁ v₂ w : Lp ℂ 2 (volume : Measure E)}
    (hU₁ : MemSobolev s 2 (U₁ : 𝓢'(E, ℂ))) (hU₂ : MemSobolev s 2 (U₂ : 𝓢'(E, ℂ)))
    (hv₁ : MemSobolev s 2 (v₁ : 𝓢'(E, ℂ))) (hv₂ : MemSobolev s 2 (v₂ : 𝓢'(E, ℂ)))
    (hw : MemSobolev s 2 (w : 𝓢'(E, ℂ)))
    (hr : MemSobolev s 2 ((w - (U₁ - U₂) : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)))
    (hv₁U : v₁ =ᵐ[volume] (fun x ↦ Complex.exp (U₁ x) - 1))
    (hv₂U : v₂ =ᵐ[volume] (fun x ↦ Complex.exp (U₂ x) - 1))
    (hwδ : w =ᵐ[volume] (fun x ↦ Complex.exp ((U₁ - U₂ : Lp ℂ 2 (volume : Measure E)) x) - 1)) :
    hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace -
        (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace) =
      (hv₂.mul hs hw).toBesselPotentialSpace + hr.toBesselPotentialSpace := by
  have hL : v₁ - v₂ - (U₁ - U₂) = (hv₂.memLp_mul hs w).toLp _ + (w - (U₁ - U₂)) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub (v₁ - v₂) (U₁ - U₂), Lp.coeFn_sub v₁ v₂, Lp.coeFn_sub U₁ U₂,
      Lp.coeFn_add ((hv₂.memLp_mul hs w).toLp _) (w - (U₁ - U₂)),
      (hv₂.memLp_mul hs w).coeFn_toLp, Lp.coeFn_sub w (U₁ - U₂), hv₁U, hv₂U, hwδ]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₄, Pi.add_apply, h₅, h₆, Pi.sub_apply, h₉, h₇, h₈,
      h₃, Pi.sub_apply]
    have he : Complex.exp (U₁ x) = Complex.exp (U₂ x) * Complex.exp (U₁ x - U₂ x) := by
      rw [← Complex.exp_add, add_sub_cancel]
    rw [he]
    ring
  refine BesselPotentialSpace.ext ?_
  have h := congrArg (fun f : Lp ℂ 2 (volume : Measure E) ↦ (f : 𝓢'(E, ℂ))) hL
  simp only [Lp.toTemperedDistribution_sub, Lp.toTemperedDistribution_add] at h
  simpa [Lp.toTemperedDistribution_sub] using h

/-- **The exponential on `H^s`, `s > n / 2`, is tangent to the identity at `0`.** There is a
constant `C ≥ 0`, depending only on `s` and `E`, with the following property. Let `U₁, U₂` be `L²`
functions in `H^s`, and `v₁, v₂` `L²` functions in `H^s` equal almost everywhere to `exp U₁ - 1`
and `exp U₂ - 1`. Writing `a = ‖U₂‖_{H^s}` and `d = ‖U₁ - U₂‖_{H^s}`,

`‖(v₁ - v₂) - (U₁ - U₂)‖_{H^s} ≤ C (a + d) exp (C (a + d)) d`.

In particular `U ↦ exp U - 1` has derivative the identity at `0`. -/
theorem exists_norm_toBesselPotentialSpace_sub_sub_le {s : ℝ} (hs : finrank ℝ E < 2 * s) :
    ∃ C, 0 ≤ C ∧ ∀ {U₁ U₂ v₁ v₂ : Lp ℂ 2 (volume : Measure E)}
      (hU₁ : MemSobolev s 2 (U₁ : 𝓢'(E, ℂ))) (hU₂ : MemSobolev s 2 (U₂ : 𝓢'(E, ℂ)))
      (hv₁ : MemSobolev s 2 (v₁ : 𝓢'(E, ℂ))) (hv₂ : MemSobolev s 2 (v₂ : 𝓢'(E, ℂ))),
      v₁ =ᵐ[volume] (fun x ↦ Complex.exp (U₁ x) - 1) →
      v₂ =ᵐ[volume] (fun x ↦ Complex.exp (U₂ x) - 1) →
      ‖hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace -
          (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace)‖ ≤
        C * (‖hU₂.toBesselPotentialSpace‖ +
            ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖) *
          Real.exp (C * (‖hU₂.toBesselPotentialSpace‖ +
            ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖)) *
          ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC0, hexp⟩ := exists_norm_toBesselPotentialSpace_exp_sub_one_le hs
  obtain ⟨M, hM0, hmul⟩ := exists_norm_toBesselPotentialSpace_mul_le hs
  refine ⟨C + M, by positivity, fun {U₁ U₂ v₁ v₂} hU₁ hU₂ hv₁ hv₂ hv₁U hv₂U ↦ ?_⟩
  -- The difference `δ = U₁ - U₂`, the function `w = exp δ - 1` and the remainder `w - δ`.
  set δ := U₁ - U₂
  have hδ : MemSobolev s 2 (δ : 𝓢'(E, ℂ)) := by
    rw [Lp.toTemperedDistribution_sub]
    exact hU₁.sub hU₂
  have hδn : hδ.toBesselPotentialSpace =
      hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace :=
    BesselPotentialSpace.ext (by simp [δ, Lp.toTemperedDistribution_sub])
  obtain ⟨w, hwδ, hw⟩ := exists_memSobolev_ae_eq_exp_sub_one hs hδ
  have hr : MemSobolev s 2 ((w - δ : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
    rw [Lp.toTemperedDistribution_sub]
    exact hw.sub hδ
  have hrδ : (w - δ : Lp ℂ 2 (volume : Measure E)) =ᵐ[volume]
      fun x ↦ Complex.exp (δ x) - 1 - δ x := by
    filter_upwards [Lp.coeFn_sub w δ, hwδ] with x hx hwx
    rw [hx, Pi.sub_apply, hwx]
  -- `exp U₁ - exp U₂ - δ = (exp U₂ - 1) w + (w - δ)`; bound the two terms.
  have hB := toBesselPotentialSpace_sub_sub_eq hs hU₁ hU₂ hv₁ hv₂ hw hr hv₁U hv₂U hwδ
  -- The norm bounds.
  set a := ‖hU₂.toBesselPotentialSpace‖
  set d := ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖
  have ha : 0 ≤ a := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hv₂n : ‖hv₂.toBesselPotentialSpace‖ ≤ a * Real.exp (C * a) := (hexp hU₂).1 hv₂ hv₂U
  have hwn : ‖hw.toBesselPotentialSpace‖ ≤ d * Real.exp (C * d) := by
    simpa only [hδn] using (hexp hδ).1 hw hwδ
  have hrn : ‖hr.toBesselPotentialSpace‖ ≤ C * d ^ 2 * Real.exp (C * d) := by
    simpa only [hδn] using (hexp hδ).2 hr hrδ
  have hPn := hmul hv₂ hw
  have e₁ : Real.exp (C * a) * Real.exp (C * d) ≤ Real.exp ((C + M) * (a + d)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have e₂ : Real.exp (C * d) ≤ Real.exp ((C + M) * (a + d)) :=
    Real.exp_le_exp.2 (by nlinarith)
  rw [hB]
  calc ‖(hv₂.mul hs hw).toBesselPotentialSpace + hr.toBesselPotentialSpace‖
      ≤ M * (a * Real.exp (C * a)) * (d * Real.exp (C * d)) +
          C * d ^ 2 * Real.exp (C * d) := by
        refine (norm_add_le _ _).trans (add_le_add (hPn.trans ?_) hrn)
        gcongr
    _ = M * a * d * (Real.exp (C * a) * Real.exp (C * d)) + C * d ^ 2 * Real.exp (C * d) := by
        ring
    _ ≤ (C + M) * a * d * Real.exp ((C + M) * (a + d)) +
          (C + M) * d ^ 2 * Real.exp ((C + M) * (a + d)) := by
        gcongr <;> linarith
    _ = (C + M) * (a + d) * Real.exp ((C + M) * (a + d)) * d := by ring

/-- **The exponential on `H^s`, `s > n / 2`, is bi-Lipschitz near `0`.** There is `ρ > 0`,
depending only on `s` and `E`, such that for `L²` functions `U₁, U₂ ∈ H^s` with
`‖U₁‖_{H^s}, ‖U₂‖_{H^s} ≤ ρ`, and `L²` functions `v₁, v₂ ∈ H^s` equal almost everywhere to
`exp U₁ - 1` and `exp U₂ - 1`,

`‖U₁ - U₂‖_{H^s} ≤ 2 ‖v₁ - v₂‖_{H^s}`  and  `‖v₁ - v₂‖_{H^s} ≤ 2 ‖U₁ - U₂‖_{H^s}`. -/
theorem exists_pos_forall_norm_toBesselPotentialSpace_sub_le {s : ℝ}
    (hs : finrank ℝ E < 2 * s) :
    ∃ ρ, 0 < ρ ∧ ∀ {U₁ U₂ v₁ v₂ : Lp ℂ 2 (volume : Measure E)}
      (hU₁ : MemSobolev s 2 (U₁ : 𝓢'(E, ℂ))) (hU₂ : MemSobolev s 2 (U₂ : 𝓢'(E, ℂ)))
      (hv₁ : MemSobolev s 2 (v₁ : 𝓢'(E, ℂ))) (hv₂ : MemSobolev s 2 (v₂ : 𝓢'(E, ℂ))),
      v₁ =ᵐ[volume] (fun x ↦ Complex.exp (U₁ x) - 1) →
      v₂ =ᵐ[volume] (fun x ↦ Complex.exp (U₂ x) - 1) →
      ‖hU₁.toBesselPotentialSpace‖ ≤ ρ → ‖hU₂.toBesselPotentialSpace‖ ≤ ρ →
      ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖ ≤
          2 * ‖hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace‖ ∧
        ‖hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace‖ ≤
          2 * ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_toBesselPotentialSpace_sub_sub_le hs
  -- With `ρ = 1 / (6 (C + 1) e³)`, the factor `C (a + d) exp (C (a + d))` is at most `1 / 2`.
  refine ⟨(6 * (C + 1) * Real.exp 3)⁻¹, by positivity,
    fun {U₁ U₂ v₁ v₂} hU₁ hU₂ hv₁ hv₂ hv₁U hv₂U hρ₁ hρ₂ ↦ ?_⟩
  set ρ := (6 * (C + 1) * Real.exp 3)⁻¹
  set a := ‖hU₂.toBesselPotentialSpace‖
  set d := ‖hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace‖
  set e := ‖hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace‖
  have ha : 0 ≤ a := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have had : a + d ≤ 3 * ρ := by
    have : d ≤ ‖hU₁.toBesselPotentialSpace‖ + a := norm_sub_le _ _
    linarith
  have hρ1 : (C + 1) * (3 * ρ) * Real.exp 3 = 1 / 2 := by
    simp only [ρ]
    field_simp
    ring
  have hρ3 : C * (3 * ρ) ≤ 3 := by
    have h1 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
    have : (C + 1) * (3 * ρ) ≤ 1 / 2 := by nlinarith [Real.exp_pos 3]
    nlinarith
  have hfac : C * (a + d) * Real.exp (C * (a + d)) ≤ 1 / 2 := by
    calc C * (a + d) * Real.exp (C * (a + d)) ≤ (C + 1) * (3 * ρ) * Real.exp 3 := by
          gcongr
          · linarith
          · exact (mul_le_mul_of_nonneg_left had hC0).trans hρ3
      _ = 1 / 2 := hρ1
  have hmain := hC hU₁ hU₂ hv₁ hv₂ hv₁U hv₂U
  have hle : ‖hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace -
      (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace)‖ ≤ d / 2 :=
    hmain.trans (by nlinarith)
  constructor
  · have := norm_sub_norm_le (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace)
      (hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace)
    rw [norm_sub_rev (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace)] at this
    linarith
  · have := norm_sub_norm_le (hv₁.toBesselPotentialSpace - hv₂.toBesselPotentialSpace)
      (hU₁.toBesselPotentialSpace - hU₂.toBesselPotentialSpace)
    linarith

end TemperedDistribution
