/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.PointwiseDecay
import TauCeti.Analysis.Calculus.FDeriv.Puncture
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Puncture

/-!
# Continuous removal of finite-energy punctures

A finite-energy solution of the Cauchy--Riemann equation on a punctured disc, with compact
image and a uniformly taming target structure, extends continuously across the puncture.
The extension takes values in the same compact set and is continuous on the entire original
disc. The target structure may vary with the image point. The original value of the map at
the puncture is unrestricted and is replaced by its limit using `Function.update`.

This is the continuous part of removal of singularities for pseudoholomorphic curves.
It does not assert differentiability at the puncture or the Cauchy--Riemann equation there;
those require elliptic regularity for the extended map.

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

end TauCeti.SymplecticForm
