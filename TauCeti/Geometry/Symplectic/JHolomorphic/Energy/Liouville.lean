/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Convergence
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Decay
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-energy pseudoholomorphic planes in a symplectic vector space, and no bubbling

Let `(V, ω)` be a symplectic vector space whose inner product is a compatible metric
`⟪v, w⟫ = ω(v, J₀ w)`, and let `J : V → (V →L[ℝ] V)` be uniformly tamed by `ω` along the image of
a curve `u : ℂ → V` solving the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu`. The symplectic form
of `V` is exact, and the energy `E(r)` of `u` on the disc of radius `r` about a point obeys the
power law `E(r) ≤ E(b) (r / b)^α`, `α = 2c / (1 + M)²`, for `r ≤ b`
(`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_ball_le_rpow`), with no extension of `u`
across the centre needed. This file draws the two consequences for the bubbling analysis of
Gromov compactness.

* **Liouville theorem.** If `u` has finite energy on the whole plane, possibly punctured at one
  point, then letting `b → ∞` in the power law gives `E(r) = 0` for every `r`, so `u` is
  constant (`TauCeti.SymplecticForm.apply_eq_apply_of_integrable_of_ne`,
  `TauCeti.SymplecticForm.apply_eq_apply_of_integrable`). Thus a symplectic vector space
  contains no nonconstant finite-energy pseudoholomorphic planes, spheres or cylinders, which are
  the planes punctured at the origin.
* **No bubbling.** If `ω` tames `J` uniformly on a compact set `K`, the power law makes the
  energy of small discs uniformly small among curves with image in `K` and bounded energy
  (`TauCeti.SymplecticForm.exists_pos_lt_forall_setIntegral_norm_fderiv_one_sq_ball_lt`). For a
  `C²` structure `J` on a neighbourhood of `K`, the small-energy mean-value inequality therefore
  applies on these discs, and the derivative at the centre of a disc of radius `ρ` is bounded in
  terms of `ρ` and the energy alone
  (`TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_setIntegral_le`). For a sequence of
  curves of bounded energy with image in `K` no energy concentrates at any point, and the
  compactness theorem `TauCeti.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`
  holds with no bubbling points: a subsequence converges locally uniformly on the whole domain,
  with derivatives bounded on its compact subsets
  (`TauCeti.SymplecticForm.exists_tendstoLocallyUniformlyOn_subseq`).

The bubbles of Floer solutions are pseudoholomorphic planes for the almost complex structure
frozen at the bubbling point (`TauCeti.SymplecticForm.isComplexLinearMap_of_tendsto_rescale`), with
image in the compact set containing the solutions. The Liouville theorem shows that such a bubble
is constant when the target is a symplectic vector space, or more generally when the image of the
bubble lies in a compact subset of a Darboux chart.

Finite energy in the Liouville theorems means that `‖du‖²` is integrable, as in
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Decay`. Energy bounds elsewhere are bounds on the
real-direction energy `∫ ‖∂ₛu‖²` of `TauCeti.Geometry.Symplectic.JHolomorphic.Energy.MeanValue`;
the Cauchy--Riemann equation makes the two comparable.

## Main results

* `TauCeti.SymplecticForm.fderiv_eq_zero_of_integrable`: a finite-energy pseudoholomorphic map on
  the plane punctured at a point has vanishing derivative.
* `TauCeti.SymplecticForm.apply_eq_apply_of_integrable_of_ne`,
  `TauCeti.SymplecticForm.apply_eq_apply_of_integrable`: such maps, on the punctured or the whole
  plane, are constant.
* `TauCeti.SymplecticForm.exists_pos_lt_forall_setIntegral_norm_fderiv_one_sq_ball_lt`: energy
  does not concentrate at points.
* `TauCeti.SymplecticForm.exists_forall_norm_fderiv_le_of_setIntegral_le`: an a priori bound on the
  derivative at the centre of a disc in terms of its radius and energy.
* `TauCeti.SymplecticForm.exists_tendstoLocallyUniformlyOn_subseq`: Gromov compactness without
  bubbling points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Sections 4.2 and 4.5 (bubbling and the energy decay at a
  puncture) and Section 4.6 (the bubbling points of a sequence of curves).
-/

public section

namespace TauCeti.SymplecticForm

open Complex Filter MeasureTheory Metric Set Topology
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {c M : ℝ}

/-- **Finite-energy planes have no energy on discs about the puncture.** If a finite-energy
solution of `∂ₜu = J(u) ∂ₛu` on the plane punctured at `z₀` is uniformly tamed by `ω`, then its
energy vanishes on every disc about `z₀`: letting the outer radius `b` tend to infinity in the
power law `E(r) ≤ E(b) (r / b)^α` bounds `E(r)` by a multiple of `b^(-α) → 0`. -/
private theorem integral_norm_fderiv_one_sq_ball_eq_zero_of_integrable
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hu : ContDiffOn ℝ 2 u {z₀}ᶜ)
    (hCR : ∀ z ≠ z₀, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ≠ z₀, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ≠ z₀, ‖J (u z)‖ ≤ M) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
    (r : ℝ) : ∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2 = 0 := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hJ (z₀ + 1) (by simp))
  set α := 2 * c / (1 + M) ^ 2
  have hα : 0 < α := by positivity
  set E := ∫ z, ‖fderiv ℝ u z 1‖ ^ 2
  have hbound : ∀ b, r ≤ b → ∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2 ≤ E * (r / b) ^ α := by
    intro b hb
    refine (ω.integral_norm_fderiv_one_sq_ball_le_rpow hg hc (R := b + 1)
      (hu.mono fun z hz ↦ hz.2) (fun z hz ↦ hCR z hz.2) (fun z hz ↦ htame z hz.2)
      (fun z hz ↦ hJ z hz.2) henergy.integrableOn hr hb (by linarith)).trans
      (mul_le_mul_of_nonneg_right
        (setIntegral_le_integral (integrable_norm_fderiv_apply_sq henergy 1)
          (Eventually.of_forall fun _ ↦ sq_nonneg _))
        (Real.rpow_nonneg (div_nonneg hr.le (hr.le.trans hb)) _))
  -- `E (r / b)^α = E r^α b^(-α)` tends to zero as `b → ∞`.
  have hlim : Tendsto (fun b : ℝ ↦ E * (r / b) ^ α) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hα).const_mul (r ^ α)).const_mul E
    rw [mul_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with b hb
    rw [Real.div_rpow hr.le hb.le, Real.rpow_neg hb.le, div_eq_mul_inv]
  exact le_antisymm (ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop r] with b hb using hbound b hb))
    (setIntegral_nonneg measurableSet_ball fun _ _ ↦ sq_nonneg _)

/-- **A finite-energy pseudoholomorphic punctured plane has vanishing derivative.** Let `u` be a
`C²` solution of `∂ₜu = J(u) ∂ₛu` on the plane punctured at `z₀`, uniformly tamed by `ω` with
`‖J(u)‖ ≤ M`, and of finite energy. Then `du = 0` away from `z₀`. -/
theorem fderiv_eq_zero_of_integrable
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hu : ContDiffOn ℝ 2 u {z₀}ᶜ)
    (hCR : ∀ z ≠ z₀, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ≠ z₀, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ≠ z₀, ‖J (u z)‖ ≤ M) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
    {z : ℂ} (hz : z ≠ z₀) : fderiv ℝ u z = 0 := by
  have hcont : ContinuousOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) {z₀}ᶜ :=
    ((hu.continuousOn_fderiv_of_isOpen isOpen_compl_singleton one_le_two).clm_apply
      continuousOn_const).norm.pow 2
  -- The real-direction energy density vanishes almost everywhere on a disc containing `z`, and it
  -- is continuous off `z₀`, so it vanishes at `z`.
  set r := ‖z - z₀‖ + 1
  have hzr : z ∈ ball z₀ r ∩ {z₀}ᶜ := ⟨by simp [r, dist_eq_norm], hz⟩
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
    (integrable_norm_fderiv_apply_sq henergy 1).integrableOn).1
    (integral_norm_fderiv_one_sq_ball_eq_zero_of_integrable hg hc hu hCR htame hJ henergy r)
  have h1 : fderiv ℝ u z 1 = 0 := by
    simpa using Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
      inter_subset_left hae) (isOpen_ball.inter isOpen_compl_singleton)
      (hcont.mono inter_subset_right) continuousOn_const hzr
  refine norm_le_zero_iff.mp ?_
  simpa [h1] using (fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hz) (hJ z hz) le_rfl

/-- **Liouville theorem for finite-energy pseudoholomorphic punctured planes.** A `C²` solution of
`∂ₜu = J(u) ∂ₛu` of finite energy on the plane punctured at `z₀`, uniformly tamed by `ω` with
`‖J(u)‖ ≤ M`, is constant off `z₀`. The plane punctured at the origin is the cylinder `ℝ × S¹`
through `z ↦ e^z`, and the energy is conformally invariant, so this is also the statement for
finite-energy pseudoholomorphic cylinders. -/
theorem apply_eq_apply_of_integrable_of_ne
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hu : ContDiffOn ℝ 2 u {z₀}ᶜ)
    (hCR : ∀ z ≠ z₀, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ≠ z₀, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ≠ z₀, ‖J (u z)‖ ≤ M) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2)
    {z w : ℂ} (hz : z ≠ z₀) (hw : w ≠ z₀) : u z = u w :=
  isOpen_compl_singleton.is_const_of_fderiv_eq_zero
    (isConnected_compl_singleton_of_one_lt_rank
      (by simp [Complex.rank_real_complex]) z₀).isPreconnected
    (hu.differentiableOn two_ne_zero)
    (fun _ hy ↦ fderiv_eq_zero_of_integrable hg hc hu hCR htame hJ henergy hy) hz hw

/-- **Liouville theorem for finite-energy pseudoholomorphic planes.** A `C²` solution of
`∂ₜu = J(u) ∂ₛu` on the whole plane of finite energy, uniformly tamed by `ω` with `‖J(u)‖ ≤ M`, is
constant. In particular a symplectic vector space contains no nonconstant pseudoholomorphic
sphere: its restriction to the complement of a point is such a plane. -/
theorem apply_eq_apply_of_integrable
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (hu : ContDiff ℝ 2 u)
    (hCR : ∀ z, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) (hJ : ∀ z, ‖J (u z)‖ ≤ M)
    (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (z w : ℂ) : u z = u w := by
  classical
  obtain ⟨z₀, hz₀⟩ := Infinite.exists_notMem_finset ({z, w} : Finset ℂ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz₀
  exact apply_eq_apply_of_integrable_of_ne (z₀ := z₀) hg hc hu.contDiffOn
    (fun z _ ↦ hCR z) (fun z _ ↦ htame z) (fun z _ ↦ hJ z) henergy (Ne.symm hz₀.1)
    (Ne.symm hz₀.2)

section NoBubbling

variable {W K : Set V}

/-- The power law `E(r) ≤ E(b) (r / b)^α` on discs about the centre of a disc `B_ρ(z)`, for a
curve with image in a compact set on which `ω` tames `J` with constant `c` and `‖J‖ ≤ M`. -/
private theorem setIntegral_ball_le_rpow_of_mapsTo
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c)
    (htame : ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J x v)) (hM : ∀ x ∈ K, ‖J x‖ ≤ M)
    {z : ℂ} {ρ : ℝ} (hu : ContDiffOn ℝ 2 u (ball z ρ))
    (hCR : ∀ y ∈ ball z ρ, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (huK : MapsTo u (ball z ρ) K)
    (hint : IntegrableOn (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) (ball z ρ))
    {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) (hb : b < ρ) :
    ∫ y in ball z r, ‖fderiv ℝ u y 1‖ ^ 2 ≤
      (∫ y in ball z b, ‖fderiv ℝ u y 1‖ ^ 2) * (r / b) ^ (2 * c / (1 + M) ^ 2) := by
  -- By the Cauchy--Riemann equation `‖du‖ ≤ (1 + M) ‖∂ₛu‖`, so the full energy is finite.
  have hcont : ContinuousOn (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) (ball z ρ) :=
    (hu.continuousOn_fderiv_of_isOpen isOpen_ball one_le_two).norm.pow 2
  have henergy : IntegrableOn (fun y ↦ ‖fderiv ℝ u y‖ ^ 2) (ball z ρ) := by
    refine Integrable.mono' (hint.const_mul ((1 + M) ^ 2))
      (hcont.aestronglyMeasurable measurableSet_ball) ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((fderiv ℝ u y).norm_le_of_apply_I_eq (hCR y hy) (hM _ (huK hy)) le_rfl) 2
  exact ω.integral_norm_fderiv_one_sq_ball_le_rpow hg hc (hu.mono sdiff_subset)
    (fun y hy ↦ hCR y hy.1) (fun y hy ↦ htame _ (huK hy.1)) (fun y hy ↦ hM _ (huK hy.1))
    henergy hr hrb hb

/-- **No energy concentration.** Let `ω` tame `J` with constant `c > 0` on a compact set `K` on
which `J` is continuous. For every radius `ρ > 0`, energy bound `E` and threshold `δ > 0` there is
a radius `0 < r < ρ` such that every `C²` solution of `∂ₜu = J(u) ∂ₛu` on a disc `B_ρ(z)` with
image in `K` and energy at most `E` on it has energy less than `δ` on `B_r(z)`. -/
theorem exists_pos_lt_forall_setIntegral_norm_fderiv_one_sq_ball_lt
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hK : IsCompact K) (hJ : ContinuousOn J K) (hc : 0 < c)
    (htame : ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J x v)) {ρ : ℝ} (hρ : 0 < ρ) (E : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ r, 0 < r ∧ r < ρ ∧ ∀ ⦃u : ℂ → V⦄ ⦃z : ℂ⦄, ContDiffOn ℝ 2 u (ball z ρ) →
      (∀ y ∈ ball z ρ, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1)) → MapsTo u (ball z ρ) K →
      IntegrableOn (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) (ball z ρ) →
      ∫ y in ball z ρ, ‖fderiv ℝ u y 1‖ ^ 2 ≤ E → ∫ y in ball z r, ‖fderiv ℝ u y 1‖ ^ 2 < δ := by
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn hJ
  have hM : ∀ x ∈ K, ‖J x‖ ≤ max a 0 := fun x hx ↦ (ha x hx).trans (le_max_left _ _)
  set α := 2 * c / (1 + max a 0) ^ 2
  have hα : 0 < α := by positivity
  -- The power law with outer radius `ρ / 2` bounds the energy of `B_r(z)` by
  -- `max E 0 (2 r / ρ)^α`, which tends to zero with `r`.
  have hlim : Tendsto (fun r : ℝ ↦ max E 0 * (r / (ρ / 2)) ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun r : ℝ ↦ max E 0 * (r / (ρ / 2)) ^ α) 0 :=
      continuousAt_const.mul ((continuousAt_id.div_const _).rpow_const (Or.inr hα.le))
    simpa [Real.zero_rpow hα.ne'] using h.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨r, hrδ, hr, hrb⟩ :=
    ((hlim.eventually (gt_mem_nhds hδ)).and (Ioc_mem_nhdsGT (half_pos hρ))).exists
  refine ⟨r, hr, hrb.trans_lt (half_lt_self hρ), fun u z hu hCR huK hint hE ↦ ?_⟩
  have hball : ∫ y in ball z (ρ / 2), ‖fderiv ℝ u y 1‖ ^ 2 ≤ max E 0 :=
    (setIntegral_mono_set hint (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (ball_subset_ball (half_lt_self hρ).le).eventuallyLE).trans (hE.trans (le_max_left _ _))
  exact ((setIntegral_ball_le_rpow_of_mapsTo hg hc htame hM hu hCR huK hint hr hrb
    (half_lt_self hρ)).trans (mul_le_mul_of_nonneg_right hball
      (Real.rpow_nonneg (by positivity) _))).trans_lt hrδ

/-- **A priori derivative bound without bubbling.** Let `J` be `C²` on an open set `W` containing
a compact set `K`, with `J(x)² = -1` on `K`, and let `ω` tame `J` on `K` with constant `c > 0`.
For every radius `ρ > 0` and energy bound `E` there is a constant `C` such that every `C³`
solution of `∂ₜu = J(u) ∂ₛu` on a disc `B_ρ(z)` with image in `K` and energy at most `E` on it
satisfies `‖du(z)‖ ≤ C`. No smallness of the energy is assumed: in a symplectic vector space
energy cannot concentrate at a point. -/
theorem exists_forall_norm_fderiv_le_of_setIntegral_le
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hc : 0 < c)
    (htame : ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J x v)) {ρ : ℝ} (hρ : 0 < ρ) (E : ℝ) :
    ∃ C, ∀ ⦃u : ℂ → V⦄ ⦃z : ℂ⦄, ContDiffOn ℝ 3 u (ball z ρ) →
      (∀ y ∈ ball z ρ, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1)) → MapsTo u (ball z ρ) K →
      IntegrableOn (fun y ↦ ‖fderiv ℝ u y 1‖ ^ 2) (ball z ρ) →
      ∫ y in ball z ρ, ‖fderiv ℝ u y 1‖ ^ 2 ≤ E → ‖fderiv ℝ u z‖ ≤ C := by
  obtain ⟨δ, hδ, hmean⟩ :=
    TauCeti.exists_pos_forall_pi_mul_sq_mul_norm_fderiv_one_sq_le_eight_mul_setIntegral_ball
      hW hJ hK hKW hJsq
  obtain ⟨a, ha⟩ := hK.exists_bound_of_continuousOn (hJ.continuousOn.mono hKW)
  have hM : ∀ x ∈ K, ‖J x‖ ≤ max a 0 := fun x hx ↦ (ha x hx).trans (le_max_left _ _)
  -- A radius `r < ρ` on which the energy is smaller than the mean-value threshold `δ`.
  obtain ⟨r, hr, hrρ, hsmall⟩ := exists_pos_lt_forall_setIntegral_norm_fderiv_one_sq_ball_lt hg hK
    (hJ.continuousOn.mono hKW) hc htame hρ E hδ
  refine ⟨(1 + max a 0) * √(8 * δ / (Real.pi * r ^ 2)), fun u z hu hCR huK hint hE ↦ ?_⟩
  have hsmall := hsmall (hu.of_le (by norm_num)) hCR huK hint hE
  -- The mean-value inequality on `B_r(z)` bounds `∂ₛu(z)`, and the equation bounds `du(z)`.
  have hDu := hu.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  have hmv := hmean hr.le (hu.mono (ball_subset_ball hrρ.le))
    ((hDu.clm_apply continuousOn_const).mono (closedBall_subset_ball hrρ))
    (fun y hy ↦ hCR y (ball_subset_ball hrρ.le hy)) (fun y hy ↦ huK (ball_subset_ball hrρ.le hy))
    hsmall
  have hsq : ‖fderiv ℝ u z 1‖ ^ 2 ≤ 8 * δ / (Real.pi * r ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hz : z ∈ ball z ρ := mem_ball_self hρ
  exact (fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hz) (hM _ (huK hz))
    (by simpa using Real.abs_le_sqrt hsq)

/-- **Gromov compactness without bubbling in a symplectic vector space.** Let `J` be `C²` on an
open set `W` containing a compact set `K`, with `J(x)² = -1` on `K`, and let `ω` tame `J` on `K`
with constant `c > 0`. Every sequence of `C³` solutions of `∂ₜu = J(u) ∂ₛu` on an open set
`Ω ⊆ ℂ` with image in `K` and energy at most `E` has a subsequence converging locally uniformly
on all of `Ω`, with derivatives bounded on every compact subset of `Ω`: the set of bubbling
points of `TauCeti.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` is empty. -/
theorem exists_tendstoLocallyUniformlyOn_subseq
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hJsq : ∀ x ∈ K, ∀ v, J x (J x v) = -v) (hc : 0 < c)
    (htame : ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J x v)) {Ω : Set ℂ} {u : ℕ → ℂ → V} {E : ℝ}
    (hΩ : IsOpen Ω) (hu : ∀ k, ContDiffOn ℝ 3 (u k) Ω)
    (hCR : ∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I = J (u k y) (fderiv ℝ (u k) y 1))
    (huK : ∀ k, MapsTo (u k) Ω K)
    (hint : ∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω)
    (hE : ∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → V), StrictMono φ ∧
      (∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
      ContinuousOn v Ω ∧ MapsTo v Ω K ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop Ω := by
  obtain ⟨δ, hδ, hconv⟩ :=
    TauCeti.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW hJ hK hKW hJsq
  obtain ⟨φ, Z, v, hφ, hZΩ, -, hconc, hbound, hv, hvK, hlim⟩ := hconv hΩ hu hCR huK hint hE
  -- At a bubbling point `z`, energy `δ` would concentrate in every small disc about `z`, but the
  -- energy of small discs is uniformly smaller than `δ`.
  have hZ : Z = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ z (hZΩ hz)
    obtain ⟨r, hr, hrρ, hsmall⟩ := exists_pos_lt_forall_setIntegral_norm_fderiv_one_sq_ball_lt hg
      hK (hJ.continuousOn.mono hKW) hc htame hρ E hδ
    obtain ⟨n, hn⟩ := (hconc z hz r hr).exists
    rw [inter_eq_left.2 ((ball_subset_ball hrρ.le).trans hρΩ)] at hn
    exact (hsmall (((hu (φ n)).mono hρΩ).of_le (by norm_num)) (fun y hy ↦ hCR _ y (hρΩ hy))
      ((huK (φ n)).mono_left hρΩ) ((hint (φ n)).mono_set hρΩ)
      ((setIntegral_mono_set (hint (φ n)) (Eventually.of_forall fun _ ↦ sq_nonneg _)
        hρΩ.eventuallyLE).trans (hE _))).not_ge hn
  subst hZ
  simp only [Finset.coe_empty, sdiff_empty] at hbound hv hvK hlim
  exact ⟨φ, v, hφ, hbound, hv, hvK, hlim⟩

end NoBubbling

end TauCeti.SymplecticForm
