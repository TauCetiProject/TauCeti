/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.PointwiseDecay
public import Mathlib.Topology.Compactification.OnePoint.Basic
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Puncture

/-!
# Continuous removal of finite-energy punctures

A finite-energy solution of the Cauchy--Riemann equation on a punctured disc, with compact
image and a uniformly taming target structure, extends continuously across the puncture.
The extension takes values in the same compact set and is continuous on the entire original
disc. The target structure may vary with the image point. The original value of the map at
the puncture is unrestricted and is replaced by its limit using `Function.update`.

The same holds at the end of a plane. A finite-energy solution on the exterior `‖z‖ > R` of a
disc, with compact image, has a limit at infinity
(`SymplecticForm.exists_tendsto_cocompact_of_finite_energy`). The inverted map `w ↦ u w⁻¹` again
solves the Cauchy--Riemann equation on the punctured disc of radius `R⁻¹`, since the inversion is
holomorphic, and it again has finite energy: the Jacobian `‖w‖⁻⁴` of the inversion cancels the
square of its conformal factor `‖w‖⁻²`, up to a factor depending on the norm of the target
structure, which is bounded on the compact set `K`. The factor is needed because the structure is
only tamed, so it need not be an isometry (`TauCeti.fderiv_comp_inv_apply_I_eq`,
`TauCeti.integrableOn_norm_fderiv_comp_inv_apply_one_sq`). A finite-energy solution on the whole
plane therefore extends to a continuous map on the Riemann sphere `OnePoint ℂ`
(`SymplecticForm.exists_continuous_onePoint_elim_of_finite_energy`). This identifies the end at
infinity of a finite-energy plane with a point of a sphere, continuously only.

This is the continuous part of removal of singularities for pseudoholomorphic curves. That the
filling solves the Cauchy--Riemann equation weakly across the puncture, and the inverted filling
weakly at infinity, is proved in `TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative`
(`SymplecticForm.exists_isWeakCauchyRiemannOn_update_of_finite_energy`,
`SymplecticForm.exists_isWeakCauchyRiemannOn_update_comp_inv_of_finite_energy`). Differentiability
of the filling and the classical equation at the puncture or at infinity still require elliptic
regularity for the extended map.

The analytic inputs are
`SymplecticForm.exists_pos_integrableOn_deriv_radial` (finite radial length) and
`TauCeti.tendsto_norm_sub_mul_norm_fderiv_nhdsNE` (shrinking circle images).
`TauCeti.exists_continuousOn_update_of_integrableOn_radial_deriv_of_tendsto` combines them.
The real inner product is the caller's, identified with a fixed compatible symplectic metric;
no alternative norm or inner-product instance is installed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c : ℝ} {W K : Set V}

open Classical in
/-- **Continuous removal of a finite-energy puncture.** A `C³` pseudoholomorphic curve on a
punctured disc with compact image, uniformly positive taming constant, and `C²`
target structure near its image has a limit at the puncture. Updating the map at that point yields a
continuous map on the original disc with image in the same compact set.

The fixed structure `J₀` identifies the given inner product with a symplectic metric. The
varying structure `J` need only be tamed, not compatible. No regularity at the puncture is
assumed or concluded beyond continuity. -/
theorem exists_continuousOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧
      ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  have hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M := fun z hz ↦ hM _ (huK hz)
  obtain ⟨ε, hε, hεR, hrad⟩ := ω.exists_pos_integrableOn_deriv_radial
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  have hsub : ball z₀ ε \ {z₀} ⊆ ball z₀ R \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_ball hεR.le)
  have hdiff : DifferentiableOn ℝ u (ball z₀ ε \ {z₀}) :=
    (hu.mono hsub).differentiableOn (by norm_num)
  have hrad' : IntegrableOn (deriv (fun t : ℝ ↦ u (z₀ + (t : ℂ)))) (Ioo 0 ε) := by
    simpa only [Complex.real_smul, mul_one] using hrad (1 : ℂ) (by simp)
  obtain ⟨q, hlim, _⟩ :=
    exists_continuousOn_update_of_integrableOn_radial_deriv_of_tendsto hε hdiff hrad'
      (tendsto_norm_sub_mul_norm_fderiv_nhdsNE hW hJ hK hKW hJsq hR hu hCR huK henergy)
  have hqK : q ∈ K := hK.isClosed.mem_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds z₀ hR)] with z hz hzR
    exact huK ⟨hzR, hz⟩)
  -- The limit is local, but the original map is already continuous everywhere else in the disc.
  refine ⟨q, hqK, hlim, continuousOn_update_iff.mpr ⟨hu.continuousOn, fun _ ↦ ?_⟩, ?_⟩
  · exact hlim.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))
  · intro z hz
    by_cases hzz : z = z₀
    · subst z
      simpa using hqK
    · simpa [Function.update_of_ne hzz] using huK ⟨hz, hzz⟩

/-- **A finite-energy plane has a limit at infinity.** A `C³` pseudoholomorphic curve on the
exterior `‖z‖ > R` of a disc, with compact image, uniformly positive taming constant, `C²` target
structure near its image and integrable energy density, converges as `z → ∞` to a point of the
compact set `K` containing its image. -/
theorem exists_tendsto_cocompact_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (closedBall 0 R)ᶜ K)
    (htame : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    ∃ q ∈ K, Tendsto u (cocompact ℂ) (𝓝 q) := by
  -- A radius `R ≤ 0` is replaced by `1`: the exterior of the unit disc is smaller.
  wlog hR : 0 < R generalizing R
  · have hS : (closedBall (0 : ℂ) 1)ᶜ ⊆ (closedBall (0 : ℂ) R)ᶜ :=
      compl_subset_compl.2 (closedBall_subset_closedBall (by linarith [not_lt.1 hR]))
    exact this (hu.mono hS) (fun z hz ↦ hCR z (hS hz)) (huK.mono_left hS)
      (fun z hz ↦ htame z (hS hz)) (henergy.mono_set hS) one_pos
  have hDE := mapsTo_inv_ball_diff_singleton_compl_closedBall (𝕜 := ℂ) R
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  -- The inverted map `w ↦ u w⁻¹` is a finite-energy solution on the punctured disc of radius `R⁻¹`.
  have hCRv (w : ℂ) (hw : w ∈ ball 0 R⁻¹ \ {0}) : fderiv ℝ (fun w ↦ u w⁻¹) w I =
      J (u w⁻¹) (fderiv ℝ (fun w ↦ u w⁻¹) w 1) :=
    fderiv_comp_inv_apply_I_eq hw.2 (hCR _ (hDE hw)) (hJsq _ (huK (hDE hw)))
  obtain ⟨q, hqK, hlim, -, -⟩ := ω.exists_continuousOn_update_of_finite_energy hg hc
    (inv_pos.2 hR) hW hJ hK hKW hJsq (hu.comp ((contDiffOn_inv ℝ).mono fun w hw ↦ hw.2) hDE)
    hCRv (huK.comp hDE) (fun w hw ↦ htame _ (hDE hw))
    (integrableOn_norm_fderiv_comp_inv_apply_one_sq hCR (fun z hz ↦ hM _ (huK hz)) henergy)
  refine ⟨q, hqK, ?_⟩
  rw [← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using hlim.comp tendsto_inv₀_cobounded'

/-- **A finite-energy plane extends to a sphere.** A `C³` pseudoholomorphic curve on the whole
plane, with compact image, uniformly positive taming constant, `C²` target structure near its image
and integrable energy density, extends continuously to the Riemann sphere `OnePoint ℂ`: sending
the point at infinity to the limit of the curve gives a continuous map with image in the same
compact set. -/
theorem exists_continuous_onePoint_elim_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hu : ContDiff ℝ 3 u)
    (hCR : ∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1)) (huK : ∀ z, u z ∈ K)
    (htame : ∀ z v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : Integrable (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2)) :
    ∃ q ∈ K, Continuous (fun x : OnePoint ℂ ↦ x.elim q u) := by
  obtain ⟨q, hqK, hlim⟩ := ω.exists_tendsto_cocompact_of_finite_energy (R := 1) hg hc hW hJ hK
    hKW hJsq hu.contDiffOn (fun z _ ↦ hCR z) (fun z _ ↦ huK z) (fun z _ ↦ htame z)
    henergy.integrableOn
  refine ⟨q, hqK, (OnePoint.continuous_iff _).2 ⟨?_, hu.continuous⟩⟩
  rw [coclosedCompact_eq_cocompact]
  exact hlim

end TauCeti.SymplecticForm
