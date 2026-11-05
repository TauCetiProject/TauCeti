/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Holomorphy and partial derivatives of Carlson's first integral

Carlson's `R_F` is holomorphic in each slit-plane argument, with the other two arguments fixed
in the slit plane or at zero (at most one zero). Its partial derivative in the third argument is
`-R_D(x, y, z) / 6`; symmetry gives the other two partial derivatives. These formulas connect
the first and second kinds and allow differentiation of elliptic-integral identities.

The domination used here allows a fixed zero argument: near the origin the majorant is
`O(t^(-1/2))`, while at infinity it is `O(t^(-5/2))`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.18, <https://dlmf.nist.gov/19.18>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>),
`Carlson/Elliptic/RF.lean` at commit `2b8cba1`, constructs `R_F` through the general Carlson
`R`-function. Here the derivatives are proved directly from the defining improper integral;
no proof is ported from that development.
-/

public section

open MeasureTheory Set Filter Topology

namespace Complex

private theorem hasDerivAt_carlsonRF_integrand {x y w : ℂ} (hw : w ∈ slitPlane)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℂ => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(1 / 2) : ℂ))
      ((-(1 / 2) : ℂ) * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(3 / 2) : ℂ))) w := by
  have h := (((hasDerivAt_id w).const_add (t : ℂ)).cpow_const (c := (-(1 / 2) : ℂ))
    (TauCeti.ofReal_add_mem_slitPlane hw ht.le)).const_mul
    (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ))
  have hexponent : (-(1 / 2) : ℂ) - 1 = -(3 / 2) := by norm_num
  simpa only [id_eq, hexponent, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using h

private theorem exists_carlsonRF_deriv_bound {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    ∃ s ∈ 𝓝 z, s ⊆ slitPlane ∧ ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi 0) ∧
      ∀ t : ℝ, 0 < t → ∀ w ∈ s,
        ‖(-(1 / 2) : ℂ) * (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
          ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(3 / 2) : ℂ))‖ ≤ bound t := by
  -- Restrict the varying argument to a ball where its translated powers have a uniform bound.
  obtain ⟨c, hc, hbound⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_slitPlane z hz
  let s := Metric.ball z (min c ε)
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z (lt_min hc hε)
  have hsc {w : ℂ} (hw : w ∈ s) : w ∈ Metric.ball z c :=
    Metric.ball_subset_ball (min_le_left c ε) hw
  have hslit {w : ℂ} (hw : w ∈ s) : w ∈ slitPlane :=
    hεsub (Metric.ball_subset_ball (min_le_right c ε) hw)
  obtain ⟨Cx, hCx⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_rpow hx
    (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
  obtain ⟨Cy, hCy0, hCy⟩ := TauCeti.exists_norm_ofReal_add_cpow_le_mul_one_add_rpow hy
    (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
  push_cast at hCx hCy
  have hCx0 : 0 ≤ Cx := by simpa using (norm_nonneg _).trans (hCx 1 one_pos)
  have hwbound {w : ℂ} (hw : w ∈ s) {t : ℝ} (ht : 0 < t) :
      ‖((t : ℂ) + w) ^ (-(3 / 2) : ℂ)‖ ≤
        c ^ (-(3 / 2) : ℝ) * (1 + t) ^ (-(3 / 2) : ℝ) := by
    have hle := hbound w (hsc hw) ⟨t, ht.le⟩
    rw [add_comm w] at hle
    have hexponent : (-(3 / 2) : ℂ) = ((-(3 / 2) : ℝ) : ℂ) := by push_cast; rfl
    rw [hexponent, norm_cpow_real, ← Real.mul_rpow hc.le (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  -- The remaining fixed factors give the beta-integral majorant t^(-1/2) (1+t)^(-2).
  have hmajorant : IntegrableOn (fun t : ℝ =>
      (1 / 2 * Cx * Cy * c ^ (-(3 / 2) : ℝ)) *
        (t ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-2 : ℝ))) (Ioi 0) := by
    have ha : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
    have hab : -((1 / 2 : ℝ) + 3 / 2) = -2 := by norm_num
    have hbase : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) *
        (1 + t) ^ (-2 : ℝ)) (Ioi 0) := by
      simpa only [ha, hab] using (TauCeti.integrableOn_rpow_mul_one_add_rpow
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 3 / 2))
    exact hbase.const_mul _
  refine ⟨s, hs, fun _ hw => hslit hw, _, hmajorant, fun t ht0 w hw => ?_⟩
  have hp : (1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-(3 / 2) : ℝ) =
      (1 + t) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < 1 + t)]
    norm_num
  simp only [norm_mul, norm_neg, norm_div, norm_one, norm_ofNat]
  calc _ ≤ 1 / 2 * ((Cx * t ^ (-(1 / 2) : ℝ)) *
        (Cy * (1 + t) ^ (-(1 / 2) : ℝ)) *
        (c ^ (-(3 / 2) : ℝ) * (1 + t) ^ (-(3 / 2) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul (hCx t ht0) (hCy t ht0.le) (norm_nonneg _)
              (by positivity)) (hwbound hw ht0) (norm_nonneg _) (by positivity))
            (by norm_num)
    _ = (1 / 2 * Cx * Cy * c ^ (-(3 / 2) : ℝ)) *
        (t ^ (-(1 / 2) : ℝ) *
          ((1 + t) ^ (-(1 / 2) : ℝ) * (1 + t) ^ (-(3 / 2) : ℝ))) := by ring
    _ = _ := by rw [hp]

/-- The partial derivative of `R_F` in its third argument is `-R_D(x, y, z) / 6`.
The first argument may be zero. -/
theorem hasDerivAt_carlsonRF_right {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    HasDerivAt (carlsonRF x y) (-carlsonRD x y z / 6) z := by
  obtain ⟨s, hs, hslit, bound, hbound_int, hbound⟩ := exists_carlsonRF_deriv_bound hx hy hz
  let F := fun (w : ℂ) (t : ℝ) => ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
    ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + w) ^ (-(1 / 2) : ℂ)
  let F' := fun (w : ℂ) (t : ℝ) => (-(1 / 2) : ℂ) *
    (((t : ℂ) + x) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) *
      ((t : ℂ) + w) ^ (-(3 / 2) : ℂ))
  have hmeas_loc : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact (integrableOn_carlsonRF_integrand hx hy hw).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (((((TauCeti.continuousOn_ofReal_add_cpow hx (-(1 / 2))).mul
      (TauCeti.continuousOn_ofReal_add_cpow (Or.inl hy) (-(1 / 2)))).mul
      (TauCeti.continuousOn_ofReal_add_cpow (Or.inl hz) (-(3 / 2)))).const_mul
      (-(1 / 2) : ℂ)).aestronglyMeasurable measurableSet_Ioi)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (μ := volume.restrict (Ioi 0)) hs hmeas_loc
    (integrableOn_carlsonRF_integrand hx hy hz) hmeas'
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound)) hbound_int
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht w hw =>
      hasDerivAt_carlsonRF_integrand (hslit hw) ht))
  have hderiv := h.2.const_mul (1 / 2 : ℂ)
  have hscale (I : ℂ) : (1 / 2 : ℂ) * (-(1 / 2) * I) = -((3 / 2) * I) / 6 := by ring
  have hvalue : (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), F' z t = -carlsonRD x y z / 6 := by
    simpa only [F', integral_const_mul, carlsonRD_eq_integral] using
      hscale (∫ t in Ioi (0 : ℝ), ((t : ℂ) + x) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + y) ^ (-(1 / 2) : ℂ) * ((t : ℂ) + z) ^ (-(3 / 2) : ℂ))
  rw [hvalue] at hderiv
  exact hderiv.congr_of_eventuallyEq (Eventually.of_forall fun w => carlsonRF_def x y w)

/-- The partial derivative of `R_F` in its second argument. The first argument may be zero. -/
theorem hasDerivAt_carlsonRF_middle {x y z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRF x w z) (-carlsonRD x z y / 6) y := by
  simpa only [carlsonRF_comm_right x] using hasDerivAt_carlsonRF_right hx hz hy

/-- The partial derivative of `R_F` in its first argument. The second argument may be zero. -/
theorem hasDerivAt_carlsonRF_left {x y z : ℂ} (hx : x ∈ slitPlane)
    (hy : y ∈ slitPlane ∪ {0}) (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => carlsonRF w y z) (-carlsonRD y z x / 6) x := by
  simpa only [carlsonRF_comm_left y] using hasDerivAt_carlsonRF_middle hy hx hz

/-- `R_F` is holomorphic in its third argument, even when its first argument is zero. -/
theorem analyticOnNhd_carlsonRF_right {x y : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hy : y ∈ slitPlane) : AnalyticOnNhd ℂ (carlsonRF x y) slitPlane := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_slitPlane
  exact fun z hz => (hasDerivAt_carlsonRF_right hx hy hz).differentiableAt.differentiableWithinAt

/-- `R_F` is holomorphic in its second argument, even when its first argument is zero. -/
theorem analyticOnNhd_carlsonRF_middle {x z : ℂ} (hx : x ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) : AnalyticOnNhd ℂ (fun y => carlsonRF x y z) slitPlane := by
  simpa only [carlsonRF_comm_right x] using analyticOnNhd_carlsonRF_right hx hz

/-- `R_F` is holomorphic in its first argument, even when its second argument is zero. -/
theorem analyticOnNhd_carlsonRF_left {y z : ℂ} (hy : y ∈ slitPlane ∪ {0})
    (hz : z ∈ slitPlane) : AnalyticOnNhd ℂ (fun x => carlsonRF x y z) slitPlane := by
  simpa only [carlsonRF_comm_left y] using analyticOnNhd_carlsonRF_middle hy hz

end Complex

end
