/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity
public import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Weak differentiation of a filled pseudoholomorphic puncture

The continuous filling of a finite-energy pseudoholomorphic puncture has weak derivative
represented by the original classical differential. In particular there is no distribution
supported at the missing point in the first derivative. The result concerns varying tame
structures and does not require compatibility of that structure.

The full differential is integrable across the puncture: the Cauchy--Riemann equation bounds
it by a constant times the real-direction derivative, and finite energy gives integrability
on the bounded disc. The continuous filling from
`SymplecticForm.exists_continuousOn_update_of_finite_energy` then satisfies integration by
parts across the exceptional point. Smooth removal still requires elliptic regularity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities).
-/

public section

open Complex Filter MeasureTheory Metric Set TopologicalSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c : ℝ} {W K : Set V}

open Classical in
/-- The continuous filling of a finite-energy pseudoholomorphic puncture is weakly
differentiable across the puncture, with weak derivative equal almost everywhere to the
original classical differential. No differentiability at the puncture is assumed or concluded.
The filling remains in the original compact target set. -/
theorem exists_hasWeakFDerivOn_update_of_finite_energy
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
      HasWeakFDerivOn volume ⟨ball z₀ R, isOpen_ball⟩ (Function.update u z₀ q)
        (fderiv ℝ u) := by
  obtain ⟨q, hq, -, hcont, hmaps⟩ := ω.exists_continuousOn_update_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame henergy
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  -- The energy controls the full differential, not just its value on `1`.
  have hbound : ∀ z ∈ ball z₀ R \ {z₀},
      ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * (1 + ‖fderiv ℝ u z 1‖ ^ 2) := by
    intro z hz
    have hI : ‖fderiv ℝ u z I‖ ≤ max M 0 * ‖fderiv ℝ u z 1‖ := by
      rw [hCR z hz]
      exact ((J (u z)).le_opNorm _).trans (by
        gcongr
        exact (hM _ (huK hz)).trans (le_max_left _ _))
    have hop : ‖fderiv ℝ u z‖ ≤ ‖fderiv ℝ u z 1‖ + ‖fderiv ℝ u z I‖ :=
      (fderiv ℝ u z).opNorm_le_bound (by positivity)
        (fderiv ℝ u z).norm_apply_le_norm_one_add_norm_I
    have hs : ‖fderiv ℝ u z 1‖ ≤ 1 + ‖fderiv ℝ u z 1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖fderiv ℝ u z 1‖ - 1)]
    calc
      ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * ‖fderiv ℝ u z 1‖ := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hi : IntegrableOn (fderiv ℝ u) (ball z₀ R) := by
    have hmajor : IntegrableOn
        (fun z ↦ (1 + max M 0) * (1 + ‖fderiv ℝ u z 1‖ ^ 2)) (ball z₀ R) :=
      ((integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne).fun_add henergy).const_mul _
    refine hmajor.mono' (measurable_fderiv ℝ u).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hzne
    exact hbound z ⟨hz, hzne⟩
  refine ⟨q, hq, hcont, hmaps,
    hasWeakFDerivOn_of_hasFDerivAt_off_countable (s := {z₀}) (countable_singleton z₀)
      hcont hi.locallyIntegrableOn ?_⟩
  intro z hz
  have hz' : z ∈ ball z₀ R \ {z₀} := hz
  have hdu := (hu.differentiableOn (by norm_num) z hz').differentiableAt
    ((isOpen_ball.sdiff isClosed_singleton).mem_nhds hz')
  have heq : Function.update u z₀ q =ᶠ[nhds z] u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz'.2] with w hw
    exact Function.update_of_ne hw _ _
  exact hdu.hasFDerivAt.congr_of_eventuallyEq heq

end TauCeti.SymplecticForm
