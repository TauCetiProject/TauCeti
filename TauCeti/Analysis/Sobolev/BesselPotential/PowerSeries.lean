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
`‖u ^ (n + 1)‖_{H^s} ≤ C ^ n ‖u‖_{H^s} ^ (n + 1)`, and a power series without constant term,

`f(u) = ∑ₙ aₙ u ^ (n + 1)`,

converges in `H^s` as soon as `∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n` converges. The sum is the pointwise
sum of the series: the Sobolev embedding `|w(x)| ≤ C ‖w‖_{H^s}`
(`TemperedDistribution.exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace`) turns convergence
in `H^s` into uniform convergence almost everywhere. Hence

`‖f(u)‖_{H^s} ≤ ‖u‖_{H^s} ∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n`

(`TemperedDistribution.MemSobolev.exists_hasSum_mul_pow`). For an entire function, such as
`exp z - 1`, there is no condition on `u`; for a function analytic on a disc, such as
`log (1 + z)`, the condition is a bound on `‖u‖_{H^s}`. This is how analytic functions act on the
Sobolev algebra without any composition (Moser) estimate, and it gives the exponential and
logarithm charts of gauge groups modelled on `H^s`.

## Main declarations

* `TemperedDistribution.MemSobolev.exists_hasSum_mul_pow`: a power series without constant term
  whose majorant series converges at `C ‖u‖_{H^s}` maps `u ∈ H^s` to an `H^s` function, which is
  the pointwise sum almost everywhere, with the norm bound above.
* `TemperedDistribution.mem_realSobolevFunctions_of_ae_eq_ofReal`: a real function represented by
  a complex `H^s` function is a real `H^s` function.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

open MeasureTheory Module Filter
open scoped SchwartzMap ENNReal Topology BesselPotentialSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TemperedDistribution

/-- A finite linear combination of `L²` functions in `H^s` lies in `H^s`, and its `H^s` element is
the same linear combination. -/
private theorem exists_memSobolev_sum_smul {ι : Type*} {s : ℝ} (t : Finset ι) (a : ι → ℂ)
    {v : ι → Lp ℂ 2 (volume : Measure E)} (hv : ∀ n, MemSobolev s 2 (v n : 𝓢'(E, ℂ))) :
    ∃ h : MemSobolev s 2 ((∑ n ∈ t, a n • v n : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)),
      h.toBesselPotentialSpace = ∑ n ∈ t, a n • (hv n).toBesselPotentialSpace := by
  have hmem : MemSobolev s 2 (∑ n ∈ t, a n • (v n : 𝓢'(E, ℂ))) :=
    mem_sobolevSubmodule.1 <| (sobolevSubmodule E ℂ s 2).sum_mem fun n _ ↦
      (sobolevSubmodule E ℂ s 2).smul_mem _ (mem_sobolevSubmodule.2 (hv n))
  have hdist : ((∑ n ∈ t, a n • v n : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) =
      ∑ n ∈ t, a n • (v n : 𝓢'(E, ℂ)) := by
    simp only [Lp.toTemperedDistribution_sum, Lp.toTemperedDistribution_smul]
  rw [← hdist] at hmem
  refine ⟨hmem, BesselPotentialSpace.ext ?_⟩
  rw [MemSobolev.toBesselPotentialSpace_toDistr, hdist]
  clear hmem hdist
  induction t using Finset.cons_induction with
  | empty => simp [BesselPotentialSpace.toDistr_zero]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, BesselPotentialSpace.toDistr_add,
      BesselPotentialSpace.toDistr_smul, ← ih, MemSobolev.toBesselPotentialSpace_toDistr]

/-- The `H^s` element of a difference of `L²` functions in `H^s` is the difference of their
`H^s` elements. -/
private theorem toBesselPotentialSpace_sub {s : ℝ} {u v : Lp ℂ 2 (volume : Measure E)}
    (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)))
    (huv : MemSobolev s 2 ((u - v : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ))) :
    huv.toBesselPotentialSpace = hu.toBesselPotentialSpace - hv.toBesselPotentialSpace := by
  refine BesselPotentialSpace.ext ?_
  rw [BesselPotentialSpace.toDistr_sub, MemSobolev.toBesselPotentialSpace_toDistr,
    Lp.toTemperedDistribution_sub, MemSobolev.toBesselPotentialSpace_toDistr,
    MemSobolev.toBesselPotentialSpace_toDistr]

/-- **Powers in `H^s`.** If `‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}` on `H^s`, then
`u ^ (n + 1)` lies in `H^s` with `‖u ^ (n + 1)‖_{H^s} ≤ C ^ n ‖u‖_{H^s} ^ (n + 1)`. -/
private theorem exists_memSobolev_pow {s : ℝ} (hs : finrank ℝ E < 2 * s) {C : ℝ} (hC : 0 ≤ C)
    (hmul : ∀ {u v : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
      (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ))),
      ‖(hu.mul hs hv).toBesselPotentialSpace‖ ≤
        C * ‖hu.toBesselPotentialSpace‖ * ‖hv.toBesselPotentialSpace‖)
    {u : Lp ℂ 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (n : ℕ) :
    ∃ v : Lp ℂ 2 (volume : Measure E), v =ᵐ[volume] (fun x ↦ u x ^ (n + 1)) ∧
      ∃ hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)),
        ‖hv.toBesselPotentialSpace‖ ≤ C ^ n * ‖hu.toBesselPotentialSpace‖ ^ (n + 1) := by
  induction n with
  | zero => exact ⟨u, .of_forall fun x ↦ (pow_one _).symm, hu, by simp⟩
  | succ n ih =>
    obtain ⟨v, hvu, hv, hvn⟩ := ih
    refine ⟨(hv.memLp_mul hs u).toLp _, ?_, hv.mul hs hu, (hmul hv hu).trans ?_⟩
    · filter_upwards [(hv.memLp_mul hs u).coeFn_toLp, hvu] with x h h'
      rw [h, h', ← pow_succ]
    · calc C * ‖hv.toBesselPotentialSpace‖ * ‖hu.toBesselPotentialSpace‖
          ≤ C * (C ^ n * ‖hu.toBesselPotentialSpace‖ ^ (n + 1)) *
              ‖hu.toBesselPotentialSpace‖ := by gcongr
        _ = C ^ (n + 1) * ‖hu.toBesselPotentialSpace‖ ^ (n + 1 + 1) := by ring

/-- **Power series act on `H^s`, `s > n / 2`.** There is a constant `C`, depending only on `s` and
`E`, with the following property. Let `u` be an `L²` function in `H^s` and `aₙ` complex
coefficients with `∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n < ∞`. Then the series `∑ₙ aₙ u(x) ^ (n + 1)`
converges for almost every `x`, and its sum is an `L²` function `v` in `H^s` with
`‖v‖_{H^s} ≤ ‖u‖_{H^s} ∑ₙ |aₙ| (C ‖u‖_{H^s}) ^ n`. -/
theorem MemSobolev.exists_hasSum_mul_pow {s : ℝ} (hs : finrank ℝ E < 2 * s) :
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
  obtain ⟨C₁, hC₁, hmul⟩ := exists_norm_toBesselPotentialSpace_mul_le (E := E) hs
  obtain ⟨C₂, hC₂, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := E) (F := ℂ) hs
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun {u} hu {a} ha ↦ ?_⟩
  set C := max C₁ C₂
  set R := ‖hu.toBesselPotentialSpace‖
  -- The powers of `u`, with their `H^s` elements `w n`.
  choose p hpu hp hpn using exists_memSobolev_pow hs hC₁ hmul hu
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
  · -- The partial sums converge to `F` in `H^s`, hence uniformly almost everywhere.
    have hdiff (N : ℕ) := exists_memSobolev_sum_smul (Finset.range N) a hp
    choose hS hSw using hdiff
    have hD (N : ℕ) : MemSobolev s 2
        ((v - ∑ n ∈ Finset.range N, a n • p n : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
      rw [Lp.toTemperedDistribution_sub]
      exact hv.sub (hS N)
    have htend : Tendsto (fun N ↦ ‖(hD N).toBesselPotentialSpace‖) atTop (𝓝 0) := by
      have h := (hsum.hasSum.tendsto_sum_nat).const_sub F
      rw [sub_self] at h
      refine (tendsto_norm_zero.comp h).congr fun N ↦ ?_
      rw [Function.comp_apply, toBesselPotentialSpace_sub hv (hS N) (hD N), hvF, hSw N]
    have hae : ∀ᵐ x ∂volume, ∀ N, ‖(v - ∑ n ∈ Finset.range N, a n • p n :
        Lp ℂ 2 (volume : Measure E)) x‖ ≤ C₂ * ‖(hD N).toBesselPotentialSpace‖ :=
      ae_all_iff.2 fun N ↦ hsup (hD N)
    have hpow : ∀ᵐ x ∂volume, ∀ n, p n x = u x ^ (n + 1) := ae_all_iff.2 hpu
    have hsmul : ∀ᵐ x ∂volume, ∀ n, (a n • p n : Lp ℂ 2 (volume : Measure E)) x = a n * p n x :=
      ae_all_iff.2 fun n ↦ by
        filter_upwards [Lp.coeFn_smul (a n) (p n)] with x h
        rw [h, Pi.smul_apply, smul_eq_mul]
    have hsums : ∀ᵐ x ∂volume, ∀ N, (∑ n ∈ Finset.range N, a n • p n :
        Lp ℂ 2 (volume : Measure E)) x =
          ∑ n ∈ Finset.range N, (a n • p n : Lp ℂ 2 (volume : Measure E)) x :=
      ae_all_iff.2 fun N ↦ by
        filter_upwards [Lp.coeFn_finsetSum (Finset.range N) fun n ↦ a n • p n] with x h
        rw [h, Finset.sum_apply]
    have hsubs : ∀ᵐ x ∂volume, ∀ N, (v - ∑ n ∈ Finset.range N, a n • p n :
        Lp ℂ 2 (volume : Measure E)) x = v x - (∑ n ∈ Finset.range N, a n • p n :
          Lp ℂ 2 (volume : Measure E)) x :=
      ae_all_iff.2 fun N ↦ Lp.coeFn_sub _ _
    filter_upwards [hae, hpow, hsmul, hsums, hsubs, hsup hu] with x hx hpx hmx hsx hdx hux
    -- The pointwise series is dominated by `C R` times the majorant series.
    have hbound (n : ℕ) : ‖a n * u x ^ (n + 1)‖ ≤ C * R * (‖a n‖ * (C * R) ^ n) := by
      rw [norm_mul, norm_pow]
      have hux' : ‖u x‖ ≤ C * R := hux.trans (by gcongr; exact le_max_right _ _)
      calc ‖a n‖ * ‖u x‖ ^ (n + 1) ≤ ‖a n‖ * (C * R) ^ (n + 1) := by gcongr
        _ = C * R * (‖a n‖ * (C * R) ^ n) := by ring
    refine ((ha.mul_left (C * R)).of_norm_bounded hbound).hasSum_iff_tendsto_nat.2 ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun N ↦ ?_)
      (by simpa only [mul_zero] using htend.const_mul C₂)
    calc ‖∑ n ∈ Finset.range N, a n * u x ^ (n + 1) - v x‖
        = ‖(v - ∑ n ∈ Finset.range N, a n • p n : Lp ℂ 2 (volume : Measure E)) x‖ := by
          rw [hdx N, hsx N, norm_sub_rev]
          simp only [hmx, hpx]
      _ ≤ C₂ * ‖(hD N).toBesselPotentialSpace‖ := hx N
  · rw [hvF, ← tsum_mul_left]
    exact tsum_of_norm_bounded (ha.mul_left R).hasSum hw

/-- **Real-valued `H^s` functions.** A real function that agrees almost everywhere with a complex
`L²` function in `H^s` lies in `realSobolevFunctions E s 2`. This recovers real `H^s` functions,
such as `cos u - 1` and `sin u`, from complex power series whose sums are real. -/
theorem mem_realSobolevFunctions_of_ae_eq_ofReal {s : ℝ} {g : E → ℝ}
    {v : Lp ℂ 2 (volume : Measure E)} (hv : MemSobolev s 2 (v : 𝓢'(E, ℂ)))
    (hvg : v =ᵐ[volume] fun x ↦ (g x : ℂ)) : g ∈ realSobolevFunctions E s 2 := by
  have hg : MemLp g 2 volume := by
    simpa [Function.comp_def] using Complex.reCLM.comp_memLp' ((Lp.memLp v).ae_eq hvg)
  refine mem_realSobolevFunctions.2 ⟨hg.toLp g, hg.coeFn_toLp, ?_⟩
  have heq : Complex.ofRealCLM.compLp (hg.toLp g) = v := by
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume) (hg.toLp g),
      hg.coeFn_toLp, hvg] with x h₁ h₂ h₃
    rw [h₁, h₃, Complex.ofRealCLM_apply, h₂]
  rwa [heq]

end TemperedDistribution
