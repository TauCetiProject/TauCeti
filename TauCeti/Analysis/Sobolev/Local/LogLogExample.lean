/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients
import TauCeti.Analysis.Sobolev.Local.W1p
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Log.InvLog
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# An unbounded function in the local class `W^{1,2}` of a planar disc

On the disc `ball 0 4 ⊆ ℂ` let

`u(z) = log log (4 / ‖z‖)`

(`TauCeti.logLogInterior`). With `r = ‖z‖ ∈ (0, 4)` the inner logarithm is positive, so on the
punctured disc `u` is smooth (`TauCeti.contDiffOn_logLogInterior`,
`TauCeti.hasFDerivAt_logLogInterior`) and its gradient has size `1 / (r log (4 / r))`
(`TauCeti.norm_fderiv_logLogInterior`). In polar coordinates both `u²` and `‖∇u‖²` have
integrable radial profiles on `(0, R)` for every `R < 4`, so `u` and its classical derivative are
square integrable on `ball 0 R` (`TauCeti.memLp_logLogInterior`,
`TauCeti.memLp_fderiv_logLogInterior`).

The classical derivative is also the weak derivative across the singularity at the origin
(`TauCeti.hasWeakFDerivOn_logLogInterior`). Near the origin `u = log v` for
`v(z) = log 4 - log ‖z‖`, which lies in `W^{1,1}` of `ball 0 (1 / 2)` with weak gradient
`-z / ‖z‖²` (`TauCeti.hasWeakFDerivOn_log_norm`) and is bounded below by `log 4 > 0` there, so the
chain rule `TauCeti.W1p.exists_value_gradient_ae_eq_log` gives the weak derivative of `u`. Away
from the origin `u` is smooth. Hence `u` lies in the local class `W^{1,p}` of `ball 0 4` for every
`p ≤ 2` (`TauCeti.memWkpLoc_logLogInterior`).

On the other hand `u(z) → ∞` as `z → 0` (`TauCeti.tendsto_logLogInterior`), so no function equal
to `u` almost everywhere near the origin is continuous at the origin
(`TauCeti.not_continuousAt_of_ae_eq_logLogInterior`). Cutting `u` off with a bump function and
translating it, every planar set `U` with nonempty interior carries, for `p ≤ 2`, a member of the
local class `W^{1,p}` of `U` with no continuous representative on `U`
(`TauCeti.exists_memWkpLoc_one_not_continuousOn_of_ae_eq`). For `p > 2` and `U` open there is
always one, by Morrey's inequality `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`. So
continuity of `W^{1,p}_loc` functions, needed to define Sobolev maps into a manifold through
charts, requires `p > 2`.

## Implementation notes

The radial calculus is shared with `TauCeti.logLogTraceExample`, the same profile placed at a
boundary point of the unit disc: `Real.hasDerivAt_log_log_div`, `Real.tendsto_log_log_div`,
`TauCeti.integrableOn_mul_log_log_div_sq` and `TauCeti.integrableOn_mul_inv_mul_log_div_sq`, all
with `c = 4`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B
  (Sobolev spaces, the borderline case `kp = n` of the Sobolev embedding).
* L. C. Evans, *Partial Differential Equations*, §5.6.3 (the example `log log (1 / |x|)` of an
  unbounded `W^{1,n}` function).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace TauCeti

/-- The function `u(z) = log log (4 / ‖z‖)`. On the disc `ball 0 4` it lies in the local class
`W^{1,2}`, but it tends to `∞` at the origin. -/
def logLogInterior (z : ℂ) : ℝ :=
  Real.log (Real.log (4 / ‖z‖))

/-- The defining formula of `TauCeti.logLogInterior`. -/
theorem logLogInterior_def (z : ℂ) :
    logLogInterior z = Real.log (Real.log (4 / ‖z‖)) := (rfl)

/-- The function `u(z) = log log (4 / ‖z‖)` is measurable. -/
@[fun_prop]
theorem measurable_logLogInterior : Measurable logLogInterior := by
  rw [show logLogInterior = fun z : ℂ => Real.log (Real.log (4 / ‖z‖)) from
    funext logLogInterior_def]
  fun_prop

/-- The function `u(z) = log log (4 / ‖z‖)` is smooth on the punctured disc `ball 0 4`, where its
inner logarithm is positive. -/
theorem contDiffOn_logLogInterior : ContDiffOn ℝ ∞ logLogInterior (ball (0 : ℂ) 4 \ {0}) := by
  rintro z ⟨hz, hz0⟩
  rw [mem_ball_zero_iff] at hz
  have h0 := norm_pos_iff.2 hz0
  have hd : ContDiffAt ℝ ∞ (fun w : ℂ => 4 / ‖w‖) z :=
    contDiffAt_const.div (contDiffAt_norm ℝ hz0) h0.ne'
  exact ((hd.log (by positivity)).log (Real.log_div_pos h0 hz).ne').contDiffWithinAt

/-- On the punctured disc `ball 0 4` the function `u(z) = log log (4 / ‖z‖)` has derivative
`-(‖z‖ log (4 / ‖z‖))⁻¹` times the derivative of the norm. -/
theorem hasFDerivAt_logLogInterior {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) (hz0 : z ≠ 0) :
    HasFDerivAt logLogInterior
      (-(‖z‖ * Real.log (4 / ‖z‖))⁻¹ • fderiv ℝ (fun w : ℂ => ‖w‖) z) z := by
  rw [mem_ball_zero_iff] at hz
  have hn : HasFDerivAt (fun w : ℂ => ‖w‖) (fderiv ℝ (fun w : ℂ => ‖w‖) z) z :=
    ((contDiffAt_norm ℝ hz0 (n := 1)).differentiableAt one_ne_zero).hasFDerivAt
  exact (Real.hasDerivAt_log_log_div four_ne_zero (norm_ne_zero_iff.2 hz0) hz.ne
    (by linarith [norm_nonneg z])).comp_hasFDerivAt z hn

/-- On the punctured disc `ball 0 4` the classical derivative of `u(z) = log log (4 / ‖z‖)` has
norm `(‖z‖ log (4 / ‖z‖))⁻¹`. -/
theorem norm_fderiv_logLogInterior {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) (hz0 : z ≠ 0) :
    ‖fderiv ℝ logLogInterior z‖ = (‖z‖ * Real.log (4 / ‖z‖))⁻¹ := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_norm ℝ hz0 (n := 1)).differentiableAt one_ne_zero
  have := Real.log_div_pos (norm_pos_iff.2 hz0) (mem_ball_zero_iff.1 hz)
  rw [(hasFDerivAt_logLogInterior hz hz0).fderiv, norm_smul, norm_fderiv_norm hn, mul_one,
    norm_neg, Real.norm_of_nonneg (by positivity)]

namespace LogLogInterior

private theorem ae_mem_ne (R : ℝ) : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) R),
    z ∈ ball (0 : ℂ) R ∧ z ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)))] with z hz hz0
  exact ⟨hz, hz0⟩

private theorem integrableOn_inv_mul_log_sq {R : ℝ} (hR : R < 4) :
    IntegrableOn (fun z : ℂ => ((‖z‖ * Real.log (4 / ‖z‖))⁻¹) ^ 2) (ball (0 : ℂ) R) := by
  refine (integrableOn_fun_norm_addHaar volume
    (f := fun r => ((r * Real.log (4 / r))⁻¹) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using integrableOn_mul_inv_mul_log_div_sq hR

/-- Away from the origin, `u` has the derivative of `log (log 4 - log ‖z‖)`. -/
private theorem hasFDerivAt_logLogInterior_log_norm {z : ℂ} (hz : ‖z‖ < 4) (hz0 : z ≠ 0) :
    HasFDerivAt logLogInterior
      ((Real.log 4 - Real.log ‖z‖)⁻¹ • -((‖z‖ ^ 2)⁻¹ • innerSL ℝ z)) z := by
  have hpos : 0 < Real.log 4 - Real.log ‖z‖ := by
    rw [← Real.log_div four_ne_zero (norm_ne_zero_iff.2 hz0)]
    exact Real.log_div_pos (norm_pos_iff.2 hz0) hz
  refine (((hasFDerivAt_log_norm_of_ne hz0).const_sub (Real.log 4)).log
    hpos.ne').congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
  rw [logLogInterior_def, Real.log_div four_ne_zero (norm_ne_zero_iff.2 hw)]

/-- Near the origin, the chain rule for `log` applied to `log 4 - log ‖z‖ ∈ W^{1,1}` gives the
weak derivative of `u`. -/
private theorem hasWeakFDerivOn_logLogInterior_ball :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩ logLogInterior
      (fderiv ℝ logLogInterior) := by
  set B : Opens ℂ := ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have : IsFiniteMeasure (volume.restrict (B : Set ℂ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `log ‖z‖` as an element of `W^{1,1}(B)`.
  have hlog : MemWkpLoc 1 (⊤ : Opens ℂ) 1 (fun z : ℂ => Real.log ‖z‖) :=
    (memWkpLoc_one_log_norm_iff (by simp)).2 (by norm_num)
  have hBc : IsCompact (closure (B : Set ℂ)) := by
    simp only [B, Opens.coe_mk]
    rw [closure_ball _ (by norm_num)]
    exact isCompact_closedBall _ _
  obtain ⟨v, hvv, hvg⟩ := hlog.exists_w1p (hasWeakFDerivOn_log_norm ⊤) hBc (subset_univ _)
  -- `a = log 4 - log ‖z‖`, bounded below by `log 4` on `B`.
  set a : W1p volume B 1 := W1p.const (Real.log 4) - v
  have hav : W1p.value a =ᵐ[volume.restrict B] fun z => Real.log 4 - Real.log ‖z‖ := by
    filter_upwards [W1p.value_sub_ae (W1p.const (Real.log 4)) v,
      Lp.coeFn_const 1 (volume.restrict (B : Set ℂ)) (Real.log 4), hvv] with z h1 h2 h3
    rw [h1, Pi.sub_apply, W1p.value_const, h2, h3, Function.const_apply]
  have hag : W1p.gradient a =ᵐ[volume.restrict B]
      fun z => -(InnerProductSpace.toDual ℝ ℂ).symm ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) := by
    filter_upwards [Lp.coeFn_sub (W1p.gradient (W1p.const (Real.log 4) : W1p volume B 1))
      (W1p.gradient v), Lp.coeFn_zero ℂ 1 (volume.restrict (B : Set ℂ)), hvg] with z h1 h2 h3
    rw [W1p.gradient_sub, h1, Pi.sub_apply, W1p.gradient_const, h2, h3, Pi.zero_apply, zero_sub]
  have hlow : ∀ᵐ z ∂volume.restrict B, Real.log 4 ≤ W1p.value a z := by
    filter_upwards [hav, ae_restrict_mem B.isOpen.measurableSet] with z hz hzB
    have hz1 : ‖z‖ ≤ 1 := by
      have : ‖z‖ < 1 / 2 := mem_ball_zero_iff.1 hzB
      linarith
    rw [hz]
    linarith [Real.log_nonpos (norm_nonneg z) hz1]
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_log (by simp)
    (Real.log_pos (by norm_num : (1 : ℝ) < 4)) hlow
  refine ((W1p.hasWeakFDerivOn w).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [hwv, hav, ae_mem_ne (1 / 2)] with z h1 h2 hz
    rw [h1, h2, logLogInterior_def, Real.log_div four_ne_zero (norm_ne_zero_iff.2 hz.2)]
  · filter_upwards [hwg, hav, hag, ae_mem_ne (1 / 2)] with z h1 h2 h3 hz
    have hz4 : ‖z‖ < 4 := by
      have : ‖z‖ < 1 / 2 := mem_ball_zero_iff.1 hz.1
      linarith
    have hd : (InnerProductSpace.toDual ℝ ℂ).symm ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) =
        (‖z‖ ^ 2)⁻¹ • z := by
      have hz : innerSL ℝ z = InnerProductSpace.toDual ℝ ℂ z :=
        ContinuousLinearMap.ext fun _ => by
          rw [innerSL_apply_apply, InnerProductSpace.toDual_apply_apply]
      rw [hz, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [(hasFDerivAt_logLogInterior_log_norm hz4 hz.2).fderiv, h1, h2, h3, hd]
    simp only [map_smul, map_neg]

/-- Off the origin `u` is smooth, so its classical derivative is its weak derivative there. -/
private theorem hasWeakFDerivOn_logLogInterior_punctured :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) 4 \ {0}, isOpen_ball.sdiff isClosed_singleton⟩
      logLogInterior (fderiv ℝ logLogInterior) := by
  have hV : IsOpen (ball (0 : ℂ) 4 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  refine hasWeakFDerivOn_of_hasFDerivAt_off_countable countable_empty
    contDiffOn_logLogInterior.continuousOn
    ((contDiffOn_logLogInterior.continuousOn_fderiv_of_isOpen hV (by simp)).locallyIntegrableOn
      hV.measurableSet) fun z hz => ?_
  exact (hasFDerivAt_logLogInterior hz.1.1 hz.1.2).differentiableAt.hasFDerivAt

end LogLogInterior

open LogLogInterior

/-- The function `u(z) = log log (4 / ‖z‖)` is square integrable on the disc `ball 0 R` for every
`R < 4`. -/
theorem memLp_logLogInterior {R : ℝ} (hR : R < 4) :
    MemLp logLogInterior 2 (volume.restrict (ball (0 : ℂ) R)) := by
  refine (memLp_two_iff_integrable_sq measurable_logLogInterior.aestronglyMeasurable).2 ?_
  refine (integrableOn_fun_norm_addHaar volume (f := fun r => Real.log (Real.log (4 / r)) ^ 2)).2 ?_
  simpa [Complex.finrank_real_complex] using integrableOn_mul_log_log_div_sq hR

/-- The classical derivative of `u(z) = log log (4 / ‖z‖)` is square integrable on the disc
`ball 0 R` for every `R < 4`, although it is unbounded near the origin. -/
theorem memLp_fderiv_logLogInterior {R : ℝ} (hR : R < 4) :
    MemLp (fderiv ℝ logLogInterior) 2 (volume.restrict (ball (0 : ℂ) R)) := by
  have hm := (measurable_fderiv ℝ logLogInterior).aestronglyMeasurable
    (μ := volume.restrict (ball (0 : ℂ) R))
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine (integrableOn_inv_mul_log_sq hR).mono' (hm.norm.pow 2) ?_
  filter_upwards [ae_mem_ne _] with z hz
  have hz4 : z ∈ ball (0 : ℂ) 4 := ball_subset_ball hR.le hz.1
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_fderiv_logLogInterior hz4 hz.2]

/-- **The classical derivative of `log log (4 / ‖z‖)` is its weak derivative across the
origin.** On the disc `ball 0 4` the function `u(z) = log log (4 / ‖z‖)`, which is unbounded at
the origin, has its classical derivative as weak derivative. -/
theorem hasWeakFDerivOn_logLogInterior :
    HasWeakFDerivOn volume ⟨ball (0 : ℂ) 4, isOpen_ball⟩ logLogInterior
      (fderiv ℝ logLogInterior) := by
  refine (hasWeakFDerivOn_logLogInterior_ball.sup
    hasWeakFDerivOn_logLogInterior_punctured).mono fun z hz => ?_
  rw [← SetLike.mem_coe, Opens.coe_sup]
  by_cases hz0 : z = 0
  · left
    rw [hz0]
    exact mem_ball_self (by norm_num)
  · exact Or.inr ⟨hz, hz0⟩

/-- Square integrability on every smaller disc `ball 0 R`, `R < 4`, is local square integrability
on `ball 0 4`. -/
private theorem memLpLoc_two_ball_four {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (hf : ∀ R < 4, MemLp f 2 (volume.restrict (ball (0 : ℂ) R))) :
    MemLpLoc 2 (ball (0 : ℂ) 4) f := by
  refine memLpLoc_iff.2 fun K hK hKc => ?_
  obtain ⟨R, hR, hKR⟩ := exists_lt_subset_ball hKc.isClosed hK
  exact (hf R hR).mono_measure (Measure.restrict_mono hKR le_rfl)

/-- **`log log (4 / ‖z‖)` is in the local class `W^{1,p}` for `p ≤ 2`.** On every subset of the
disc `ball 0 4` the function `u(z) = log log (4 / ‖z‖)`, unbounded at the origin, lies in the
local Sobolev class `W^{1,p}` for every exponent `p ≤ 2`. -/
theorem memWkpLoc_logLogInterior {p : ℝ≥0∞} {U : Set ℂ} (hp : p ≤ 2)
    (hU : U ⊆ ball (0 : ℂ) 4) : MemWkpLoc p U 1 logLogInterior := by
  have h2 : MemWkpLoc 2 (ball (0 : ℂ) 4) 1 logLogInterior :=
    (memWkpLoc_succ_iff_of_isOpen (Ω := ⟨ball (0 : ℂ) 4, isOpen_ball⟩)).2
      ⟨memLpLoc_two_ball_four fun _ hR => memLp_logLogInterior hR, _,
        hasWeakFDerivOn_logLogInterior,
        memWkpLoc_zero_iff.2 (memLpLoc_two_ball_four fun _ hR => memLp_fderiv_logLogInterior hR)⟩
  exact (h2.mono_exponent hp).mono hU

/-- The function `u(z) = log log (4 / ‖z‖)` tends to `∞` at the origin. -/
theorem tendsto_logLogInterior : Tendsto logLogInterior (𝓝[≠] 0) atTop :=
  (Real.tendsto_log_log_div four_ne_zero).comp
    ((tendsto_norm_nhdsNE_zero (E := ℂ)).mono_right (nhdsGT_le_nhdsNE 0))

/-- No function equal almost everywhere on a neighbourhood `s` of the origin to
`u(z) = log log (4 / ‖z‖)` is continuous at the origin. -/
theorem not_continuousAt_of_ae_eq_logLogInterior {s : Set ℂ} {g : ℂ → ℝ} (hs : s ∈ 𝓝 0)
    (hg : g =ᵐ[volume.restrict s] logLogInterior) :
    ¬ ContinuousAt g 0 :=
  not_continuousAt_of_ae_eq_of_tendsto_atTop tendsto_logLogInterior hs hg

/-- **For `p ≤ 2` some member of the local class `W^{1,p}` has no continuous representative.**
For every `p ≤ 2` and every planar set `U` with nonempty interior, some function in the local
class `W^{1,p}` of `U` agrees almost everywhere on `U` with no function continuous on `U`; one
example is `u(z - z₀) = log log (4 / ‖z - z₀‖)`, cut off by a bump function about a point `z₀` of
the interior of `U`. For `p > 2` and `U` open, Morrey's inequality
`TauCeti.MemWkpLoc.continuousOn_preciseRepresentative` gives a continuous representative. -/
theorem exists_memWkpLoc_one_not_continuousOn_of_ae_eq {p : ℝ≥0∞} {U : Set ℂ} (hp : p ≤ 2)
    (hU : (interior U).Nonempty) :
    ∃ f : ℂ → ℝ, MemWkpLoc p U 1 f ∧
      ∀ g : ℂ → ℝ, g =ᵐ[volume.restrict U] f → ¬ ContinuousOn g U := by
  obtain ⟨z₀, hz₀⟩ := hU
  -- The translate `u(z - z₀)` lies in the local class of `ball z₀ 4`.
  have htr : MemWkpLoc p (ball z₀ 4) 1 fun z => logLogInterior (z - z₀) := by
    have h := (memWkpLoc_logLogInterior hp subset_rfl).comp_continuousLinearEquiv_add
      (ContinuousLinearEquiv.refl ℝ ℂ) (-z₀) (U := ball z₀ 4) fun z hz => by
        simpa [← sub_eq_add_neg, mem_ball, dist_eq_norm] using hz
    simpa only [ContinuousLinearEquiv.coe_refl', id, ← sub_eq_add_neg] using h
  -- Cut it off by a bump function equal to `1` on `closedBall z₀ 1`, supported in `ball z₀ 4`.
  let χ : ContDiffBump z₀ := ⟨1, 2, one_pos, one_lt_two⟩
  have hsupp : tsupport χ ⊆ interior (ball z₀ 4) := by
    rw [χ.tsupport_eq, isOpen_ball.interior_eq]
    exact closedBall_subset_ball (by norm_num [χ])
  have hf := htr.contDiff_smul_of_tsupport_subset (χ.contDiff (n := 1)) (by simp) hsupp
  refine ⟨fun z => χ z • logLogInterior (z - z₀), hf.mono (subset_univ U), fun g hg hc => ?_⟩
  have hU0 : U ∈ 𝓝 z₀ := mem_interior_iff_mem_nhds.1 hz₀
  refine not_continuousAt_of_ae_eq_of_tendsto_atTop ?_ hU0 hg (hc.continuousAt hU0)
  have hsub : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).tendsto' z₀ 0
      (sub_self z₀)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => sub_ne_zero.2 hz⟩
  refine (tendsto_logLogInterior.comp hsub).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z₀ one_pos)] with z hz
  rw [Function.comp_apply, χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_smul]

end TauCeti
