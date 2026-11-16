/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import TauCeti.Analysis.Analytic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Convergence
import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation

/-!
# Taylor polynomials of harmonic functions are harmonic

Let `f : E → F` be harmonic at a point `x` of a finite-dimensional real inner product space
`E`, with values in a real normed space `F`, and let `∑ₖ pₖ` be a power series of `f` at `x`.
Each homogeneous term `y ↦ pₖ (y, …, y)` is then harmonic on all of `E`
(`HasFPowerSeriesAt.harmonicAt_apply`), and so is every Taylor polynomial `p.partialSum n`
(`HasFPowerSeriesAt.harmonicAt_partialSum`). Combined with the convergence of
the partial sums (`HasFPowerSeriesOnBall.tendstoUniformlyOn`), a harmonic function admitting a
power series is, near each point, a uniform limit of polynomial functions harmonic on the whole
space. This applies to every harmonic function with values in a finite-dimensional space, which
is analytic (`InnerProductSpace.HarmonicAt.analyticAt`). This is how functionals that annihilate
every function harmonic on an open set, and are continuous for uniform convergence of
derivatives up to some finite order, are seen to annihilate the expansions of potentials whose
poles lie far away.

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
