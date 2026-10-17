/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Higher integrability across a finite-energy puncture

A finite-energy pseudoholomorphic curve with compact image has full differential in `Lᵖ`
near a puncture for some `p > 2`. More precisely, if the taming constant is `c > 0` and
`‖J‖ ≤ M`, set `β = c / (1 + M)²`. The pointwise estimate
`‖du(z)‖ ≤ C * ‖z - z₀‖^(β - 1)` gives integrability for every positive finite exponent
satisfying `p * (1 - β) < 2`. One radius works for all these exponents.

The continuously extended curve enjoys the same higher integrability: changing its value at
the puncture changes its classical differential only at that point. This is an integrability
statement about the classical differential off the puncture, with no assertion yet that it is
the weak differential of the extension. Identifying the weak differential and elliptic
bootstrapping are separate steps towards smooth removal of singularities.

The proof combines `SymplecticForm.exists_pos_norm_fderiv_le_rpow` with integrability of
norm powers in real dimension two. No regularity at the missing point is assumed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c M : ℝ} {W K : Set V}

/-- The differential of a finite-energy pseudoholomorphic curve belongs to `Lᵖ` near a
puncture whenever `p > 0` and `p * (1 - c / (1 + M)²) < 2`. The radius is independent of
`p`; the derivative is integrated over the entire ball, including the puncture. -/
theorem exists_pos_forall_memLp_fderiv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ ε > 0, ε < R ∧ ∀ p : ℝ, 0 < p → p * (1 - c / (1 + M) ^ 2) < 2 →
      MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  obtain ⟨ε, hε, hεR, C, hC, hpoint⟩ := ω.exists_pos_norm_fderiv_le_rpow
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  refine ⟨ε, hε, hεR, fun p hp hprange ↦ ?_⟩
  have hnull : volume.restrict (ball z₀ ε \ {z₀}) = volume.restrict (ball z₀ ε) :=
    Measure.restrict_congr_set (sdiff_null_ae_eq_self (measure_singleton z₀))
  have hmeas : AEStronglyMeasurable (fderiv ℝ u) (volume.restrict (ball z₀ ε)) := by
    rw [← hnull]
    have hsmall : ContDiffOn ℝ 3 u (ball z₀ ε \ {z₀}) :=
      hu.mono (sdiff_subset_sdiff_left (ball_subset_ball hεR.le))
    have hcont := hsmall.continuousOn_fderiv_of_isOpen
      (isOpen_ball.sdiff isClosed_singleton) (by norm_num)
    exact hcont.aestronglyMeasurable
      (measurableSet_ball.diff (measurableSet_singleton _))
  rw [← integrable_norm_rpow_iff hmeas (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  have hexponent : -(Module.finrank ℝ ℂ : ℝ) < (c / (1 + M) ^ 2 - 1) * p := by
    rw [Complex.finrank_real_complex]
    nlinarith
  have hmajorant := (integrableOn_norm_sub_rpow_ball (mu := volume)
    hexponent z₀ (R := ε)).const_mul (C ^ p)
  refine hmajorant.mono' (hmeas.norm.aemeasurable.pow_const p).aestronglyMeasurable ?_
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ z₀ := volume.ae_ne z₀
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with z hz hzz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    ‖fderiv ℝ u z‖ ^ p ≤ (C * ‖z - z₀‖ ^ (c / (1 + M) ^ 2 - 1)) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (hpoint z ⟨hz, hzz⟩) hp.le
    _ = C ^ p * ‖z₀ - z‖ ^ ((c / (1 + M) ^ 2 - 1) * p) := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _), norm_sub_rev z z₀]

open Classical in
/-- A finite-energy pseudoholomorphic curve with compact image extends continuously across
its puncture, and the full classical differential of the extension belongs to some `Lᵖ`
with `p > 2` on a smaller disc. The extension remains in the same compact target set.
This does not assert differentiability at the puncture or identify a weak derivative. -/
theorem exists_continuousOn_update_memLp_fderiv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, ContinuousOn (Function.update u z₀ q) (ball z₀ R) ∧
      MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
        MemLp (fderiv ℝ (Function.update u z₀ q)) (ENNReal.ofReal p)
          (volume.restrict (ball z₀ ε)) := by
  obtain ⟨q, hq, _, hcont, hmaps⟩ := ω.exists_continuousOn_update_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame henergy
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M := fun z hz ↦
    (hB _ (huK hz)).trans (le_max_left _ _)
  obtain ⟨ε, hε, hεR, hmem⟩ := ω.exists_pos_forall_memLp_fderiv_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame hbound henergy
  let β := c / (1 + M) ^ 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hprange : (2 + β) * (1 - β) < 2 := by nlinarith [sq_nonneg β]
  refine ⟨q, hq, hcont, hmaps, ε, hε, hεR, 2 + β, by linarith, ?_⟩
  apply (hmem (2 + β) (by linarith) hprange).ae_eq
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ z₀ := volume.ae_ne z₀
  filter_upwards [ae_restrict_of_ae hne] with z hz
  symm
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact Function.update_of_ne hw _ _

end TauCeti.SymplecticForm
