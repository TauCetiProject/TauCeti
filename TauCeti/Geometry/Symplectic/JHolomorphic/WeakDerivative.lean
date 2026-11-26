/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity
public import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.HigherIntegrability
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.RCLike.OperatorNorm
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
parts across the exceptional point.

Together with the higher integrability of the differential
(`SymplecticForm.exists_pos_forall_memLp_fderiv_of_finite_energy`), this makes the filling a weak
solution of the Cauchy--Riemann equation `∂ₛu + J(u) ∂ₜu = 0` across the puncture, in the sense of
`TauCeti.IsWeakCauchyRiemannOn`, with exponent `p > 2` on a smaller disc
(`SymplecticForm.exists_isWeakCauchyRiemannOn_update_of_finite_energy`). The form `∂ₜu = J(u) ∂ₛu`
of the classical equation is equivalent to it because `J² = -1` along the image. The same holds
at the end of a finite-energy plane: the inverted map `w ↦ u w⁻¹`, filled at `0` with the limit of
`u` at infinity, is such a weak solution near `0`
(`SymplecticForm.exists_isWeakCauchyRiemannOn_update_comp_inv_of_finite_energy`). Both give a
continuous `W^{1,p}` weak solution with `p > 2` for a `C²` structure `J`, the input of interior
elliptic regularity for the nonlinear Cauchy--Riemann equation. The regularity it gives the filling
is limited by that of `J`, so a smooth filling, which completes the removal of singularities, also
needs a smooth `J`; this is done in
`TauCeti.Geometry.Symplectic.JHolomorphic.RemovableSingularity.Smooth`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology TopologicalSpace

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
    have hop : ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * ‖fderiv ℝ u z 1‖ :=
      (fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hz) ((hM _ (huK hz)).trans (le_max_left _ _))
        le_rfl
    have hs : ‖fderiv ℝ u z 1‖ ≤ 1 + ‖fderiv ℝ u z 1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖fderiv ℝ u z 1‖ - 1)]
    calc
      ‖fderiv ℝ u z‖ ≤ (1 + max M 0) * ‖fderiv ℝ u z 1‖ := hop
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

open Classical in
/-- **The filled puncture is a weak solution.** The continuous filling of a finite-energy
pseudoholomorphic puncture solves the Cauchy--Riemann equation `∂ₛu + J(u) ∂ₜu = 0` weakly on a
smaller disc around the puncture, with weak derivative in `Lᵖ` for some `p > 2`. The filling value
`q` is the limit of `u` at the puncture, and the filling keeps the image in the compact set `K`. -/
theorem exists_isWeakCauchyRiemannOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c) (hR : 0 < R)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (ball z₀ R \ {z₀}) K)
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R)) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ MapsTo (Function.update u z₀ q) (ball z₀ R) K ∧
      ∃ ε > 0, ε < R ∧ ∃ p : ℝ, 2 < p ∧
        IsWeakCauchyRiemannOn (ENNReal.ofReal p) (ball z₀ ε) (fun _ ↦ J) 0
          (Function.update u z₀ q) := by
  obtain ⟨q, hq, hcont, hmaps, hweak⟩ := ω.exists_hasWeakFDerivOn_update_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame henergy
  obtain ⟨ε, hε, hεR, p, hp, hmem⟩ := ω.exists_pos_two_lt_memLp_fderiv_of_finite_energy
    hg hc hR hW hJ hK hKW hJsq hu hCR huK htame henergy
  have hεR' : ball z₀ ε ⊆ ball z₀ R := ball_subset_ball hεR.le
  refine ⟨q, hq, continuousAt_update_same.1 (hcont.continuousAt (ball_mem_nhds z₀ hR)), hmaps,
    ε, hε, hεR, p, hp, ?_⟩
  -- Pass to the open ball as an element of `Opens ℂ`, the form taken by the weak derivative.
  rw [← Opens.coe_mk (U := ball z₀ ε) (hU := isOpen_ball), isWeakCauchyRiemannOn_iff_of_isOpen]
  refine ⟨hcont.mono hεR', (hcont.mono hεR').memLpLoc, fderiv ℝ u,
    hweak.mono (SetLike.coe_subset_coe.1 hεR'), hmem.memLpLoc, ?_⟩
  -- Off the puncture the classical equation `∂ₜu = J(u) ∂ₛu` and `J² = -1` give the weak one.
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hzz
  have hz' : z ∈ ball z₀ R \ {z₀} := ⟨hεR' hz, hzz⟩
  rw [Function.update_of_ne hzz, hCR z hz', hJsq _ (huK hz')]
  simp

open Classical in
/-- **The filled end of a plane is a weak solution.** For a finite-energy pseudoholomorphic curve
on the exterior `‖z‖ > R` of a disc, with compact image, the inverted map `w ↦ u w⁻¹`, filled at
`0` with the limit `q` of `u` at infinity, solves the Cauchy--Riemann equation
`∂ₛv + J(v) ∂ₜv = 0` weakly on a disc around `0`, with weak derivative in `Lᵖ` for some `p > 2`.
This is the chart of the Riemann sphere at the point at infinity of the plane. -/
theorem exists_isWeakCauchyRiemannOn_update_comp_inv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v)
    (hu : ContDiffOn ℝ 3 u (closedBall 0 R)ᶜ)
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (huK : MapsTo u (closedBall 0 R)ᶜ K)
    (htame : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    ∃ q ∈ K, Tendsto u (cocompact ℂ) (𝓝 q) ∧ ∃ ε > 0, ∃ p : ℝ, 2 < p ∧
      IsWeakCauchyRiemannOn (ENNReal.ofReal p) (ball 0 ε) (fun _ ↦ J) 0
        (Function.update (fun w ↦ u w⁻¹) 0 q) := by
  -- A radius `R ≤ 0` is replaced by `1`: the exterior of the unit disc is smaller.
  wlog hR : 0 < R generalizing R
  · have hS : (closedBall (0 : ℂ) 1)ᶜ ⊆ (closedBall (0 : ℂ) R)ᶜ :=
      compl_subset_compl.2 (closedBall_subset_closedBall (by linarith [not_lt.1 hR]))
    exact this (hu.mono hS) (fun z hz ↦ hCR z (hS hz)) (huK.mono_left hS)
      (fun z hz ↦ htame z (hS hz)) (henergy.mono_set hS) one_pos
  have hDE := mapsTo_inv_ball_diff_singleton_compl_closedBall (𝕜 := ℂ) R
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  -- The inverted map is a finite-energy solution on the punctured disc of radius `R⁻¹`.
  obtain ⟨q, hq, hlim, -, ε, hε, -, p, hp, hweak⟩ :=
    ω.exists_isWeakCauchyRiemannOn_update_of_finite_energy hg hc (inv_pos.2 hR) hW hJ hK hKW
      hJsq (hu.comp ((contDiffOn_inv ℝ).mono fun w hw ↦ hw.2) hDE)
      (fun w hw ↦ fderiv_comp_inv_apply_I_eq hw.2 (hCR _ (hDE hw)) (hJsq _ (huK (hDE hw))))
      (huK.comp hDE) (fun w hw ↦ htame _ (hDE hw))
      (integrableOn_norm_fderiv_comp_inv_apply_one_sq hCR (fun z hz ↦ hM _ (huK hz)) henergy)
  refine ⟨q, hq, ?_, ε, hε, p, hp, hweak⟩
  rw [← Metric.cobounded_eq_cocompact]
  simpa [Function.comp_def] using hlim.comp tendsto_inv₀_cobounded'

end TauCeti.SymplecticForm
