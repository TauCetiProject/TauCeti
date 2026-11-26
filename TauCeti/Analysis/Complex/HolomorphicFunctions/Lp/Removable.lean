/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Removable singularities of square-integrable holomorphic functions

A function holomorphic on a punctured neighbourhood of a point `c` of the plane whose squared norm
is integrable there extends holomorphically across `c`. This is the `L²` form of Riemann's removable
singularity theorem: the Bergman space of a punctured disc is that of the disc.

The proof reduces to Riemann's theorem in the form
`Complex.differentiableOn_update_limUnder_of_isLittleO`, which asks for `f(z) = o(|z - c|⁻¹)`. For a
point `z` at distance `d` from `c`, the disc of radius `d / 2` about `z` avoids `c`, and `f` is
harmonic there, so the pointwise `L²` bound for harmonic functions
`InnerProductSpace.HarmonicOnNhd.measureReal_ball_mul_norm_sq_le_setIntegral` gives

`‖f z‖² ≤ 4 (π d²)⁻¹ ∫_{0 < |y - c| < 3d/2} ‖f y‖²`,

and the integral tends to zero with `d` because `‖f‖²` is integrable
(`TauCeti.HolomorphicFunctions.isLittleO_sub_inv_of_integrableOn_sq_norm`). The integrability of
`‖f‖²` cannot be weakened to that of `‖f‖ ^ p` for a `p < 2`: the function `(z - c)⁻¹` is
holomorphic off `c` and `‖·‖ ^ p`-integrable near `c` for every `p < 2`, but has a pole there.

At the point at infinity, a function `G` holomorphic on `|w| > T` with `‖G‖²` integrable there is
read through the holomorphic `1`-form `G dw` in the coordinate `q = w⁻¹`. Since `dw = -q⁻² dq` and
the inversion distorts area by `|q|⁻⁴`
(`TauCeti.integrableOn_image_iff_integrableOn_norm_deriv_sq_smul`), the coefficient
`(q²)⁻¹ • G q⁻¹` is again square-integrable on a punctured disc about `0`, so the theorem at a
point extends it across `q = 0`
(`TauCeti.HolomorphicFunctions.exists_differentiableOn_eq_inv_sq_smul_comp_inv`).

## Main results

* `TauCeti.HolomorphicFunctions.isLittleO_sub_inv_of_integrableOn_sq_norm`: a holomorphic function
  with square-integrable norm on a punctured neighbourhood of `c` is `o(|z - c|⁻¹)` at `c`.
* `TauCeti.HolomorphicFunctions.differentiableOn_update_limUnder_of_integrableOn_sq_norm`: **the
  `L²` removable singularity theorem.**
* `TauCeti.HolomorphicFunctions.exists_differentiableOn_eq_inv_sq_smul_comp_inv`: the version at
  infinity, for the `1`-form `G dw` read in the coordinate `q = w⁻¹`.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter I, on Bergman spaces.
-/

public section

open Filter Metric Set Topology MeasureTheory Asymptotics

namespace TauCeti.HolomorphicFunctions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : ℂ → F} {s : Set ℂ} {c : ℂ}

/-- A holomorphic function whose squared norm is integrable on a punctured neighbourhood of `c` is
`o(|z - c|⁻¹)` at `c`. -/
theorem isLittleO_sub_inv_of_integrableOn_sq_norm (hs : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hi : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (s \ {c})) :
    f =o[𝓝[≠] c] fun z ↦ (z - c)⁻¹ := by
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.1 hs
  have hiR : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (ball c R \ {c}) :=
    hi.mono_set (sdiff_subset_sdiff_left hRs)
  refine IsLittleO.of_bound fun ε hε ↦ ?_
  obtain ⟨ρ, hρI, hρpos, hρR⟩ := ((((hiR.tendsto_setIntegral_ball_nhds_zero c).eventually
    (gt_mem_nhds (show (0 : ℝ) < Real.pi * ε ^ 2 / 4 by positivity))).filter_mono
    nhdsWithin_le_nhds).and (Ioc_mem_nhdsGT hR)).exists
  rw [Measure.restrict_restrict measurableSet_ball] at hρI
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c (half_pos hρpos)), self_mem_nhdsWithin]
    with z hzb hzc
  have hd0 : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  rw [mem_ball, dist_eq_norm] at hzb
  set d := ‖z - c‖ with hdz
  have hball : closedBall z (d / 2) ⊆ ball c ρ ∩ (ball c R \ {c}) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have hyρ : y ∈ ball c ρ := by
      rw [mem_ball, dist_eq_norm]
      calc ‖y - c‖ = ‖(y - z) + (z - c)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - z‖ + ‖z - c‖ := norm_add_le _ _
        _ < ρ := by linarith
    refine ⟨hyρ, ball_subset_ball hρR hyρ, fun hyc ↦ ?_⟩
    rw [mem_singleton_iff] at hyc
    rw [hyc, norm_sub_rev] at hy
    linarith
  have hopen : IsOpen (ball c ρ ∩ (ball c R \ {c})) :=
    isOpen_ball.inter (isOpen_ball.sdiff isClosed_singleton)
  have hh : InnerProductSpace.HarmonicOnNhd f (closedBall z (d / 2)) := fun y hy ↦
    ((hd.mono (inter_subset_right.trans (sdiff_subset_sdiff_left hRs))).analyticAt
      (hopen.mem_nhds (hball hy))).harmonicAt
  have hmv := hh.measureReal_ball_mul_norm_sq_le_setIntegral (μ := volume)
  rw [Complex.volume_real_ball z (by positivity)] at hmv
  have hmono : ∫ y in ball z (d / 2), ‖f y‖ ^ 2 ≤ ∫ y in ball c ρ ∩ (ball c R \ {c}), ‖f y‖ ^ 2 :=
    setIntegral_mono_set (hiR.mono_set inter_subset_right)
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall (ball_subset_closedBall.trans hball))
  have hsq : ‖f z‖ ^ 2 ≤ (ε * ‖(z - c)⁻¹‖) ^ 2 := by
    rw [norm_inv, ← hdz, mul_pow, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith [hmv.trans (hmono.trans hρI.le), Real.pi_pos]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The `L²` removable singularity theorem.** If `s` is a neighbourhood of `c`, and `f` is
holomorphic on `s \ {c}` with `‖f‖²` integrable there, then `f`, redefined at `c` to be its limit
`limUnder (𝓝[≠] c) f`, is holomorphic on `s`. -/
theorem differentiableOn_update_limUnder_of_integrableOn_sq_norm (hs : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hi : IntegrableOn (fun z ↦ ‖f z‖ ^ 2) (s \ {c})) :
    DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠] c) f)) s :=
  Complex.differentiableOn_update_limUnder_of_isLittleO hs hd <|
    (isLittleO_sub_inv_of_integrableOn_sq_norm hs hd hi).sub
      (IsBoundedUnder.isLittleO_sub_self_inv isBoundedUnder_const)

/-- **The `L²` removable singularity at infinity.** If `G` is holomorphic on `|w| > T` and `‖G‖²`
is integrable there, then the holomorphic `1`-form `G dw` read in the coordinate `q = w⁻¹` of the
point at infinity has a coefficient, `q ↦ (q²)⁻¹ • G q⁻¹` up to sign, that extends holomorphically
across `q = 0` to the disc `|q| < T⁻¹`. The statement has content only for `0 < T`: for `T ≤ 0`
Lean's `T⁻¹ ≤ 0` makes that disc empty. -/
theorem exists_differentiableOn_eq_inv_sq_smul_comp_inv {G : ℂ → F} {T : ℝ}
    (hd : DifferentiableOn ℂ G {w | T < ‖w‖})
    (hi : IntegrableOn (fun w ↦ ‖G w‖ ^ 2) {w | T < ‖w‖}) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g (ball 0 T⁻¹) ∧
      ∀ q ∈ ball (0 : ℂ) T⁻¹, q ≠ 0 → g q = (q ^ 2)⁻¹ • G q⁻¹ := by
  rcases le_or_gt T 0 with hT | hT
  · -- For `T ≤ 0` the disc `|q| < T⁻¹` is empty.
    refine ⟨0, by simp [ball_eq_empty.2 (inv_nonpos.2 hT)], fun q hq ↦ ?_⟩
    exact absurd ((norm_nonneg q).trans_lt (by simpa using hq)) (inv_nonpos.2 hT).not_gt
  set H : ℂ → F := fun q ↦ (q ^ 2)⁻¹ • G q⁻¹
  have hopen : IsOpen {w : ℂ | T < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hmem {q : ℂ} (hq : q ∈ ball (0 : ℂ) T⁻¹ \ {0}) : T < ‖q⁻¹‖ := by
    have hq0 : q ≠ 0 := hq.2
    have hqT : ‖q‖ < T⁻¹ := by simpa using hq.1
    rw [norm_inv]
    exact (lt_inv_comm₀ (norm_pos_iff.2 hq0) hT).1 hqT
  have hHd : DifferentiableOn ℂ H (ball 0 T⁻¹ \ {0}) := fun q hq ↦
    (((differentiableAt_id.pow 2).inv (pow_ne_zero 2 hq.2)).smul
      ((hd.differentiableAt (hopen.mem_nhds (hmem hq))).comp q
        (differentiableAt_inv hq.2))).differentiableWithinAt
  have himage : (·⁻¹) '' (ball (0 : ℂ) T⁻¹ \ {0}) = {w : ℂ | T < ‖w‖} := by
    ext w
    refine ⟨fun ⟨q, hq, hqw⟩ ↦ hqw ▸ hmem hq, fun hw ↦ ⟨w⁻¹, ⟨?_, ?_⟩, inv_inv w⟩⟩
    · have hw0 : 0 < ‖w‖ := hT.trans hw
      simpa [norm_inv] using (inv_lt_inv₀ hw0 hT).2 hw
    · simpa using (hT.trans (show T < ‖w‖ from hw)).ne'
  have hHi : IntegrableOn (fun q ↦ ‖H q‖ ^ 2) (ball 0 T⁻¹ \ {0}) := by
    rw [← himage, integrableOn_image_iff_integrableOn_norm_deriv_sq_smul
      (fun q (hq : q ∈ ball (0 : ℂ) T⁻¹ \ {0}) ↦ differentiableAt_inv hq.2)
      (measurableSet_ball.diff (measurableSet_singleton 0))
      inv_injective.injOn] at hi
    refine hi.congr_fun (fun q _ ↦ ?_) (measurableSet_ball.diff (measurableSet_singleton 0))
    simp [H, deriv_inv, norm_smul, mul_pow]
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] 0) H),
    differentiableOn_update_limUnder_of_integrableOn_sq_norm (ball_mem_nhds 0 (inv_pos.2 hT))
      hHd hHi, fun q _ hq ↦ ?_⟩
  rw [Function.update_of_ne hq]

end TauCeti.HolomorphicFunctions
