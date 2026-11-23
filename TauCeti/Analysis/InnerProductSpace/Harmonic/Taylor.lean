/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import TauCeti.Analysis.Analytic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Convergence
import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation
import TauCeti.Analysis.InnerProductSpace.Harmonic.IteratedFDeriv

/-!
# Taylor polynomials of harmonic functions are harmonic

Let `f : E → F` be harmonic at a point `x` of a finite-dimensional real inner product space
`E`, with values in a real normed space `F`, and let `∑ₖ pₖ` be a power series of `f` at `x`.
Each homogeneous term `y ↦ pₖ (y, …, y)` is then harmonic on all of `E`
(`HasFPowerSeriesAt.harmonicAt_apply`), and so is every Taylor polynomial `p.partialSum n`
(`HasFPowerSeriesAt.harmonicAt_partialSum`). Combined with the convergence of
the partial sums (`HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn`), a function represented by a
power series on `eball x r` that is harmonic at `x` is harmonic on the whole ball
(`HasFPowerSeriesOnBall.harmonicOnNhd`). When `F` is finite-dimensional, interior derivative
estimates (`TendstoLocallyUniformlyOn.iteratedFDeriv_of_harmonicOnNhd`) upgrade this to locally
uniform convergence of all iterated derivatives on `eball 0 r`
(`HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt`) and
uniform convergence on every smaller closed ball `closedBall 0 s`
(`HasFPowerSeriesOnBall.tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt`). This applies
to every harmonic function with values in a finite-dimensional space, which is analytic
(`InnerProductSpace.HarmonicAt.analyticAt`), and is how functionals that annihilate global harmonic
polynomials are seen to annihilate exterior multipole expansions of potentials.

## The argument

For real-valued `f`, argue by strong induction on `k`: the terms of degree below `k` are
harmonic. For `t ≠ 0` the rescaled remainders

`gₜ y = t⁻ᵏ (f (x + t • y) - ∑_{j < k} tʲ pⱼ (y, …, y))`

are therefore harmonic on any fixed ball once `t` is small, harmonicity being invariant under
dilations and translations. Homogeneity of the terms turns `gₜ y - pₖ (y, …, y)` into `t⁻ᵏ` times
the Taylor remainder of order `k + 1` at `t • y`, which is `O (t)` uniformly on the ball. Locally
uniform limits of harmonic functions are harmonic, so `pₖ` is harmonic on every ball. For general
`F`, the Laplacian of `pₖ` vanishes because it does after composition with every continuous
linear functional on `F`.

## Main declarations

* `HasFPowerSeriesAt.harmonicAt_apply`: the homogeneous terms of the power series of a harmonic
  function are harmonic everywhere.
* `HasFPowerSeriesAt.harmonicAt_partialSum`: so are its Taylor polynomials.
* `HasFPowerSeriesOnBall.harmonicOnNhd`: a function with a power series on `eball x r` that is
  harmonic at `x` is harmonic on `eball x r`.
* `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt` and
  `HasFPowerSeriesOnBall.tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt`: locally
  uniform and closed-ball uniform convergence of all iterated derivatives of the Taylor polynomials.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapters 1 and 5.
-/

public section

open Filter InnerProductSpace Metric Set Topology TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E}

namespace HasFPowerSeriesAt

/-- The scalar case of `HasFPowerSeriesAt.harmonicAt_apply`, by strong induction on the degree. -/
private theorem harmonicAt_apply_real {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hp : HasFPowerSeriesAt f p x) (hf : HarmonicAt f x) (k : ℕ) (z : E) :
    HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  induction k using Nat.strong_induction_on generalizing z with
  | _ k ih =>
  have hsum : ∀ w, HarmonicAt (p.partialSum k) w := fun w ↦
    HarmonicAt.sum fun j hj ↦ ih j (Finset.mem_range.1 hj) w
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_setOfPred_harmonicAt (f := f)) x hf
  -- It suffices to prove harmonicity on the ball of radius `‖z‖ + 1` about the origin.
  set R := ‖z‖ + 1
  have hR : 0 < R := by positivity
  refine harmonicOnNhd_of_tendstoLocallyUniformlyOn (p := 𝓝[≠] (0 : ℝ)) isOpen_ball ?_
    (hp.tendstoUniformlyOn_inv_pow_smul_sub_partialSum k
      isBounded_ball).tendstoLocallyUniformlyOn z (mem_ball_zero_iff.2 (lt_add_one _))
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℝ) (div_pos hr hR)),
    self_mem_nhdsWithin] with t htr (ht : t ≠ 0) y hy
  have hty : x + t • y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖y‖ ≤ ‖t‖ * R := by gcongr; exact (mem_ball_zero_iff.1 hy).le
      _ < r := (lt_div_iff₀ hR).1 (mem_ball_zero_iff.1 htr)
  have hf' : HarmonicAt (fun w ↦ f (x + t • w)) y :=
    (harmonicAt_comp_const_add_smul_iff x ht).2 (hball hty)
  have hp' : HarmonicAt (fun w ↦ p.partialSum k (t • w)) y :=
    (harmonicAt_comp_smul_right_iff t ht).2 (hsum _)
  simpa [Pi.smul_def] using (hf'.sub hp').const_smul (c := (t ^ k)⁻¹)

/-- **The homogeneous Taylor terms of a harmonic function are harmonic.** If `f` is harmonic at
`x` with power series `∑ₖ pₖ` there, then for every `k` the homogeneous polynomial function
`y ↦ pₖ (y, …, y)` is harmonic at every point of `E`. -/
theorem harmonicAt_apply (hp : HasFPowerSeriesAt f p x) (hf : HarmonicAt f x) (k : ℕ) (z : E) :
    HarmonicAt (fun y ↦ p k fun _ ↦ y) z := by
  have hcd : ContDiff ℝ 2 (fun y : E ↦ p k fun _ ↦ y) :=
    (p k).contDiff.comp (contDiff_pi.2 fun _ ↦ contDiff_id)
  refine ⟨hcd.contDiffAt, Eventually.of_forall fun w ↦ ?_⟩
  -- The Laplacian vanishes because it does after composition with every continuous functional.
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  obtain ⟨r, hr⟩ := hp
  have hℓ := harmonicAt_apply_real ⟨r, ℓ.comp_hasFPowerSeriesOnBall hr⟩ (hf.comp_CLM ℓ) k w
  rw [← Function.comp_apply (f := ℓ), ← hcd.contDiffAt.laplacian_CLM_comp_left]
  simpa [Function.comp_def] using hℓ.2.self_of_nhds

/-- **The Taylor polynomials of a harmonic function are harmonic.** If `f` is harmonic at `x`
with power series `p` there, every partial sum `p.partialSum n` is harmonic at every point of
`E`. -/
theorem harmonicAt_partialSum (hp : HasFPowerSeriesAt f p x) (hf : HarmonicAt f x) (n : ℕ)
    (z : E) : HarmonicAt (p.partialSum n) z :=
  HarmonicAt.sum fun k _ ↦ hp.harmonicAt_apply hf k z

end HasFPowerSeriesAt

namespace HasFPowerSeriesOnBall

open scoped ENNReal

variable {r : ℝ≥0∞}

/-- The scalar case of `HasFPowerSeriesOnBall.harmonicOnNhd`, from locally uniform convergence of
the harmonic Taylor polynomials. -/
private theorem harmonicOnNhd_real {f : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ}
    (hp : HasFPowerSeriesOnBall f p x r) (hf : HarmonicAt f x) :
    HarmonicOnNhd f (eball x r) := by
  refine harmonicOnNhd_of_tendstoLocallyUniformlyOn isOpen_eball ?_ hp.tendstoLocallyUniformlyOn'
  refine .of_forall fun n y _ ↦ ?_
  have hsub : (fun z ↦ p.partialSum n (z - x)) = fun z ↦ p.partialSum n (z + -x) := by
    ext z
    rw [sub_eq_add_neg]
  rw [hsub, harmonicAt_comp_add_right_iff]
  exact hp.hasFPowerSeriesAt.harmonicAt_partialSum hf n _

/-- **A function with a power series on a ball that is harmonic at the center is harmonic on the
whole ball.** Every Taylor polynomial is harmonic everywhere and the partial sums converge locally
uniformly to `f` on `eball x r`. -/
theorem harmonicOnNhd [CompleteSpace F] (hp : HasFPowerSeriesOnBall f p x r)
    (hf : HarmonicAt f x) : HarmonicOnNhd f (eball x r) := by
  intro y hy
  refine ⟨(hp.analyticOnNhd y hy).contDiffAt, ?_⟩
  filter_upwards [isOpen_eball.mem_nhds hy] with z hz
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  have hℓ := harmonicOnNhd_real (ℓ.comp_hasFPowerSeriesOnBall hp) (hf.comp_CLM ℓ) z hz
  rw [← Function.comp_apply (f := ℓ), ← (hp.analyticOnNhd z hz).contDiffAt.laplacian_CLM_comp_left]
  simpa [Function.comp_def] using hℓ.2.self_of_nhds

/-- **Locally uniform `C^k` convergence of the Taylor polynomials of a harmonic function.**
If `f` is harmonic at `x` and represented by `p` on `eball x r`, then on `eball 0 r` the `k`-th
iterated Fréchet derivatives of `p.partialSum N` converge locally uniformly to those of
`y ↦ f (x + y)`. -/
theorem tendstoLocallyUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt [FiniteDimensional ℝ F]
    (hp : HasFPowerSeriesOnBall f p x r) (hf : HarmonicAt f x) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (p.partialSum N))
      (iteratedFDeriv ℝ k fun y ↦ f (x + y)) atTop (eball 0 r) := by
  have hP (N : ℕ) : HarmonicOnNhd (p.partialSum N) (eball 0 r) :=
    fun z _ ↦ hp.hasFPowerSeriesAt.harmonicAt_partialSum hf N z
  have hF : HarmonicOnNhd (fun y ↦ f (x + y)) (eball 0 r) := by
    intro y hy
    have hcomm : (fun z ↦ f (x + z)) = fun z ↦ f (z + x) := by
      ext z
      rw [add_comm]
    rw [hcomm, harmonicAt_comp_add_right_iff]
    refine hp.harmonicOnNhd hf (y + x) ?_
    simpa [mem_eball, eDist_eq_eNorm_sub] using hy
  exact hp.tendstoLocallyUniformlyOn.iteratedFDeriv_of_harmonicOnNhd (.of_forall hP) hF
    isOpen_eball k

/-- **Uniform `C^k` convergence of the Taylor polynomials of a harmonic function on closed balls.**
If `f` is harmonic at `x` and represented by `p` on `eball x r`, then for every real `s` with
`ENNReal.ofReal s < r`, the `k`-th iterated Fréchet derivatives of `p.partialSum N` converge
uniformly on `closedBall 0 s` to those of `y ↦ f (x + y)`. -/
theorem tendstoUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt [FiniteDimensional ℝ F]
    (hp : HasFPowerSeriesOnBall f p x r) (hf : HarmonicAt f x)
    {s : ℝ} (hs : ENNReal.ofReal s < r) (k : ℕ) :
    TendstoUniformlyOn (fun N ↦ iteratedFDeriv ℝ k (p.partialSum N))
      (iteratedFDeriv ℝ k fun y ↦ f (x + y)) atTop (closedBall 0 s) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_eball).1
    (hp.tendstoLocallyUniformlyOn_iteratedFDeriv_partialSum_of_harmonicAt hf k)
    (closedBall 0 s) (fun y hy ↦ ?_) (isCompact_closedBall 0 s)
  rw [mem_eball, edist_dist]
  exact (ENNReal.ofReal_le_ofReal (mem_closedBall.1 hy)).trans_lt hs

end HasFPowerSeriesOnBall
