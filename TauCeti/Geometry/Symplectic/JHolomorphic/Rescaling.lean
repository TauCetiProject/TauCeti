/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Rescaling
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Order.Field

/-!
# Normalized rescaling of pseudoholomorphic curves

For curves satisfying the Cauchy--Riemann equation on shrinking discs, a diverging
radius--derivative product gives normalized curves on expanding discs. Their differentials
have norm one at the origin and norm at most two throughout their domains. Their centers
converge to the original blow-up point, their dilation factors tend to zero, and the curves
retain their regularity, target constraint, and Cauchy--Riemann equation. Real-direction
energy is unchanged by nonzero real affine rescaling of the domain.

The target structure can vary with both the curve and its image point. No tameness,
compatibility, or regularity of the structure is needed for this rescaling step. The theorem
does not extract a limit or assert that a limit is nonconstant; that requires convergence of
differentials, in addition to convergence of the maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.2 (bubbling by rescaling and Hofer point selection).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped ContDiff Pointwise

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Translation and real dilation in the source preserve the Cauchy--Riemann equation,
including when the target coefficient depends on the map value. -/
theorem fderiv_comp_add_real_smul_I_eq {u : ℂ → V} {J : V → V →L[ℝ] V}
    {a z : ℂ} {d : ℝ}
    (hCR : fderiv ℝ u (a + d • z) I = J (u (a + d • z)) (fderiv ℝ u (a + d • z) 1)) :
    fderiv ℝ (fun w ↦ u (a + d • w)) z I =
      J (u (a + d • z)) (fderiv ℝ (fun w ↦ u (a + d • w)) z 1) := by
  simp only [fderiv_comp_smul (f := fun w ↦ u (a + w)), fderiv_comp_add_left,
    smul_apply, hCR, map_smul]

/-- Real-direction energy is invariant under nonzero real affine rescaling of a plane domain.
The image set is exactly the portion of the original domain used by the rescaled map.
This change-of-variables identity does not require the Cauchy--Riemann equation. -/
theorem integral_norm_fderiv_comp_add_real_smul_one_sq (u : ℂ → V) (a : ℂ)
    {d : ℝ} (hd : d ≠ 0) (s : Set ℂ) :
    ∫ z in s, ‖fderiv ℝ (fun w ↦ u (a + d • w)) z 1‖ ^ 2 =
      ∫ z in (fun w ↦ a + d • w) '' s, ‖fderiv ℝ u z 1‖ ^ 2 := by
  simp_rw [fderiv_comp_smul (f := fun w ↦ u (a + w)), fderiv_comp_add_left,
    smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, Measure.setIntegral_comp_smul volume
    (fun z : ℂ ↦ ‖fderiv ℝ u (a + z) 1‖ ^ 2) s hd]
  have hcancel (energy : ℝ) : d ^ 2 * (|(d ^ 2)⁻¹| • energy) = energy := by
    simp only [abs_inv, abs_of_nonneg (sq_nonneg d), smul_eq_mul]
    field_simp [hd]
  simp only [Complex.finrank_real_complex, hcancel]
  have htrans := (measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (d • s)
  have hset : (fun z : ℂ ↦ a + z) '' (d • s) = (fun z ↦ a + d • z) '' s :=
    Set.image_image _ _ _
  rw [← htrans, hset]

/-- **Normalized rescaling on expanding discs.** Suppose the original disc radii tend to zero,
their centers converge, and radius times differential norm tends to infinity. Hofer selection
then gives nearby centers and positive dilations tending to zero for which the rescaled curves
are defined on discs with radii tending to infinity. They satisfy the same Cauchy--Riemann
equation, have derivative norm one at zero, and have derivative norm at most two on each disc.
Regularity and the original target constraint are preserved. -/
theorem exists_rescaling_tendsto_of_radius_mul_norm_fderiv
    {ι : Type*} {l : Filter ι} {u : ι → ℂ → V} {J : ι → V → V →L[ℝ] V}
    {x : ι → ℂ} {x₀ : ℂ} {r : ι → ℝ} {U : ι → Set ℂ} {K : Set V} {n : ℕ∞ω}
    (hn : 1 ≤ n) (hU : ∀ i, IsOpen (U i)) (hu : ∀ i, ContDiffOn ℝ n (u i) (U i))
    (hr : ∀ i, 0 < r i) (hsub : ∀ i, closedBall (x i) (r i) ⊆ U i)
    (hx : ∀ i, 0 < ‖fderiv ℝ (u i) (x i)‖)
    (hCR : ∀ i, ∀ z ∈ U i, fderiv ℝ (u i) z I = J i (u i z) (fderiv ℝ (u i) z 1))
    (hK : ∀ i, MapsTo (u i) (U i) K)
    (hxlim : Tendsto x l (𝓝 x₀)) (hrlim : Tendsto r l (𝓝 0))
    (hblow : Tendsto (fun i ↦ r i * ‖fderiv ℝ (u i) (x i)‖) l atTop) :
    ∃ (a : ι → ℂ) (d R : ι → ℝ),
      Tendsto a l (𝓝 x₀) ∧ Tendsto d l (𝓝 0) ∧ Tendsto R l atTop ∧
      ∀ i, 0 < d i ∧ 0 < R i ∧ dist (a i) (x i) ≤ r i / 2 ∧
        MapsTo (fun z ↦ a i + d i • z) (closedBall 0 (R i)) (U i) ∧
        ContDiffOn ℝ n (fun z ↦ u i (a i + d i • z)) (closedBall 0 (R i)) ∧
        MapsTo (fun z ↦ u i (a i + d i • z)) (closedBall 0 (R i)) K ∧
        ‖fderiv ℝ (fun z ↦ u i (a i + d i • z)) 0‖ = 1 ∧
        ∀ z ∈ closedBall 0 (R i),
          ‖fderiv ℝ (fun w ↦ u i (a i + d i • w)) z‖ ≤ 2 ∧
          fderiv ℝ (fun w ↦ u i (a i + d i • w)) z I =
            J i (u i (a i + d i • z))
              (fderiv ℝ (fun w ↦ u i (a i + d i • w)) z 1) := by
  have hselect (i : ι) := exists_pos_norm_fderiv_rescale_le (hr i)
    (((hu i).continuousOn_fderiv_of_isOpen (hU i) hn).mono (hsub i)) (hx i)
  choose a d R hd hR hax hprod hdR hmaps hnorm hbound using hselect
  have hRlim : Tendsto R l atTop := by
    apply tendsto_atTop_mono hprod
    simpa only [div_mul_eq_mul_div] using hblow.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  have halim : Tendsto a l (𝓝 x₀) := hxlim.congr_dist <|
    squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ by simpa [dist_comm] using hax i)
      (by simpa using hrlim.div_const 2)
  have hdlim : Tendsto d l (𝓝 0) :=
    squeeze_zero (fun i ↦ (hd i).le)
      (fun i ↦ (le_div_iff₀ (hR i)).mpr (hdR i))
      ((hrlim.div_const 4).div_atTop hRlim)
  refine ⟨a, d, R, halim, hdlim, hRlim, fun i ↦ ?_⟩
  have hmapsU : MapsTo (fun z ↦ a i + d i • z) (closedBall 0 (R i)) (U i) :=
    fun _ hz ↦ hsub i (hmaps i hz)
  refine ⟨hd i, hR i, hax i, hmapsU, (hu i).comp (by fun_prop) hmapsU,
    (hK i).comp hmapsU, hnorm i, fun z hz ↦ ⟨hbound i z hz, ?_⟩⟩
  exact fderiv_comp_add_real_smul_I_eq (hCR i _ (hmapsU hz))

end TauCeti
