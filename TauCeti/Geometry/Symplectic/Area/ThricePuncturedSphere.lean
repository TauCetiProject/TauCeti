/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
import TauCeti.Analysis.Normed.Group.Annulus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Symplectic area on the truncated thrice-punctured sphere

Let `(V, ω)` be a symplectic vector space and let `u` be a `C²` map from the thrice-punctured
sphere `S = ℂ ∖ {0, 1}` to `V`. The truncation `S_R` (`TauCeti.ThricePuncturedSphere.truncation`)
is bounded by the three circles `±s = R` of the cylindrical ends, and in the end coordinates
`z = s + i t` of the end `q` the restriction of `u` to the circle `±s = R` is the loop
`ℓ_q(t) = u(φ_q(±R + i t))`, where `φ_q` is the end lift `Puncture.cylindricalEndLift`. This file
proves Stokes' formula for the symplectic area of `u` over `S_R`:

`∫_{S_R} u^*ω = a(ℓ_0) + a(ℓ_1) - a(ℓ_∞)`

for `R ≥ 1`, where `a` is the loop area `TauCeti.SymplecticForm.loopArea`, the integral of the
primitive `λₓ(v) = ½ ω(x, v)` of `ω` (`SymplecticForm.integral_fderiv_apply_truncation`). All
three loops run clockwise in the plane. This is the boundary orientation of `S_R` on the two
inner circles, about `0` and `1`, and the reverse of it on the outer circle, which gives the
signs of the ends: `+` on the input ends `0` and `1`, `-` on the output end `∞`.

The domain `S_R` is a disc with two holes, so the annulus formula
`TauCeti.SymplecticForm.integral_fderiv_apply_annulus` does not apply to it directly. Instead the
map is cut off near the puncture at `1`: the product `uc = (1 - χ) u` with a bump function `χ`
about `1` is `C²` on `ℂ ∖ {0}`, so the annulus formula applies to `uc` on the annulus about `0`
bounded by the circles at `0` and `∞`. The annulus formula for `uc` and for `u` on two annuli
about `1` then removes the contribution of the disc about `1`. No extension of `u` itself across
the punctures is needed.

In the energy identity of the pair-of-pants product, adding the Hamiltonian terms turns these loop
areas into the Hamiltonian actions of the end loops; see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5.
-/

public section

open Set Metric MeasureTheory Complex Filter Topology
open scoped Real

namespace TauCeti.SymplecticForm

open ThricePuncturedSphere ThricePuncturedSphere.Puncture

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The area `½ ∫_{-π}^{π} ω(u, ∂_θ u) dθ` of `u` along the counterclockwise circle of radius `r`
about `c`: the boundary term of `SymplecticForm.integral_fderiv_apply_annulus`. -/
private noncomputable def circleArea (ω : SymplecticForm V) (u : ℂ → V) (c : ℂ) (r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ θ in -π..π, ω (u (circleMap c r θ)) (deriv (fun θ ↦ u (circleMap c r θ)) θ)

/-- The circle area only depends on the values of the map on the circle. -/
private theorem circleArea_congr (ω : SymplecticForm V) {u v : ℂ → V} {c : ℂ} {r : ℝ}
    (h : ∀ θ, u (circleMap c r θ) = v (circleMap c r θ)) :
    ω.circleArea u c r = ω.circleArea v c r := by
  simp only [circleArea, h]

/-- The circle area of a map vanishing on the circle is zero. -/
private theorem circleArea_eq_zero (ω : SymplecticForm V) {u : ℂ → V} {c : ℂ} {r : ℝ}
    (h : ∀ θ, u (circleMap c r θ) = 0) : ω.circleArea u c r = 0 := by
  rw [circleArea_congr ω (v := fun _ ↦ 0) h]
  simp [circleArea]

/-- The loop area of the circle `s = x` of an end is minus the circle area of the corresponding
circle about the center of the end. -/
private theorem loopArea_cylindricalEndLift (ω : SymplecticForm V) (u : ℂ → V) (q : Puncture)
    (x : ℝ) :
    ω.loopArea (fun t ↦ u (q.cylindricalEndLift (x + t * I))) =
      -ω.circleArea u q.endCenter (‖q.endScale‖ * Real.exp (-(2 * π * x))) := by
  simp only [cylindricalEndLift_ofReal_add_ofReal_mul_I]
  rw [circleArea]
  exact ω.loopArea_comp_sub_mul
    (g := fun θ ↦ u (circleMap q.endCenter (‖q.endScale‖ * Real.exp (-(2 * π * x))) θ))
    ((periodic_circleMap _ _).comp u) _

variable [FiniteDimensional ℝ V]

/-- Stokes' formula on a closed annulus, in terms of circle areas. -/
private theorem integral_annulus (ω : SymplecticForm V) {u : ℂ → V} (c : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    ∫ z in {z : ℂ | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      ω.circleArea u c b - ω.circleArea u c a := by
  rw [ω.integral_fderiv_apply_annulus c ha hab hu, circleArea, circleArea, mul_sub]

/-- The truncation `S_R` splits along the circle of radius `3/4` about `1` into the part of the
annulus `r ≤ ‖z‖ ≤ ρ` outside that circle and the part of the annulus `r ≤ ‖z - 1‖ ≤ 3/4` inside
it. -/
private theorem truncation_eq_union {R r ρ : ℝ} (hr : r = Real.exp (-(2 * π * R)) / 2)
    (hρ : ρ = 2 * Real.exp (2 * π * R)) (hr' : r ≤ 1 / 4) (hρ' : 7 / 4 ≤ ρ) :
    truncation R = ({z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ} \ ball 1 (3 / 4)) ∪
      ({z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4} ∩ ball 1 (3 / 4)) := by
  subst hr hρ
  ext w
  have t₁ := norm_sub_norm_le w 1
  have t₂ := norm_sub_norm_le 1 w
  rw [norm_one] at t₁ t₂
  rw [norm_sub_rev] at t₂
  rw [truncation_eq]
  simp only [mem_inter_iff, mem_ofPred_eq, mem_closedBall, mem_union, Set.mem_sdiff,
    mem_ball, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    by_cases h : ‖w - 1‖ < 3 / 4
    · exact Or.inr ⟨⟨h₂, h.le⟩, h⟩
    · exact Or.inl ⟨⟨h₁, h₃⟩, h⟩
  · rintro (⟨⟨h₁, h₃⟩, h⟩ | ⟨⟨h₂, -⟩, h⟩)
    · exact ⟨⟨h₁, by linarith [not_lt.1 h]⟩, h₃⟩
    · exact ⟨⟨by linarith, h₂⟩, by linarith⟩

/-- A point of an annulus about `1` with positive inner radius and outer radius `3/4` is neither
`0` nor `1`. -/
private theorem ne_zero_ne_one_of_mem_annulus {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ {z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}) : z ≠ 0 ∧ z ≠ 1 := by
  refine ⟨ne_zero_of_norm_sub_one_lt (by linarith [hz.2]), fun h ↦ ?_⟩
  subst h
  have := hz.1
  simp only [sub_self, norm_zero] at this
  linarith

/-- The sphere of radius `3/4` about `1` is almost nowhere. -/
private theorem ae_notMem_sphere : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (1 : ℂ) (3 / 4) :=
  measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere (μ := volume) (1 : ℂ) (3 / 4))

omit [FiniteDimensional ℝ V] in
/-- A map which is `C²` on `ℂ ∖ {0, 1}` can be cut off near `1`: there is a map `uc` which equals
`u` away from `1`, vanishes near `1`, and is `C²` on `ℂ ∖ {0}`. -/
private theorem exists_cutoff {u : ℂ → V} (hu : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ContDiffAt ℝ 2 u w) :
    ∃ uc : ℂ → V, (∀ {w : ℂ}, 1 / 2 ≤ ‖w - 1‖ → uc w = u w) ∧
      (∀ {w : ℂ}, ‖w - 1‖ ≤ 1 / 4 → uc w = 0) ∧
      (∀ {w : ℂ}, ‖w - 1‖ < 1 / 4 → uc =ᶠ[𝓝 w] fun _ ↦ 0) ∧
      (∀ {w : ℂ}, 1 / 2 < ‖w - 1‖ → uc =ᶠ[𝓝 w] u) ∧ ∀ {w : ℂ}, w ≠ 0 → ContDiffAt ℝ 2 uc w := by
  let χ : ContDiffBump (1 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let uc : ℂ → V := fun w ↦ (1 - χ w) • u w
  have huc_eq {w : ℂ} (hw : 1 / 2 ≤ ‖w - 1‖) : uc w = u w := by
    simp [uc, χ.zero_of_le_dist (by rw [dist_eq_norm]; exact hw)]
  have huc_zero {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 4) : uc w = 0 := by
    simp [uc, χ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw)]
  refine ⟨uc, huc_eq, huc_zero, fun {w} hw ↦ ?_, fun {w} hw ↦ ?_, fun {w} h₀ ↦ ?_⟩
  · filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm
      continuous_const).mem_nhds hw] with z hz using huc_zero hz.le
  · filter_upwards [(isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).mem_nhds hw] with z hz using huc_eq hz.le
  · by_cases h₁ : w = 1
    · subst h₁
      refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm
        continuous_const).mem_nhds (show ‖(1 : ℂ) - 1‖ < 1 / 4 by norm_num)] with z hz using
        huc_zero hz.le
    · exact (contDiffAt_const.sub χ.contDiffAt).smul (hu w h₀ h₁)

/-- The integral of the area density over the annulus about `0` of the cut-off map, outside the
disc about `1`, plus its integral over that disc, is the difference of the two circle areas. -/
private theorem integral_cutoff_sdiff (ω : SymplecticForm V) {u uc : ℂ → V} {r ρ : ℝ}
    (hr₀ : 0 < r) (hr : r ≤ 1 / 10) (hρ : 10 ≤ ρ)
    (huc : ∀ {w : ℂ}, w ≠ 0 → ContDiffAt ℝ 2 uc w)
    (huc_eq : ∀ {w : ℂ}, 1 / 2 ≤ ‖w - 1‖ → uc w = u w)
    (huc_near_eq : ∀ {w : ℂ}, 1 / 2 < ‖w - 1‖ → uc =ᶠ[𝓝 w] u) :
    (∫ z in {z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ} \ ball 1 (3 / 4),
        ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) +
      ∫ z in ball (1 : ℂ) (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
    ω.circleArea u 0 ρ - ω.circleArea u 0 r := by
  set A₀ : Set ℂ := {z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ}
  have hA : IsCompact (A₀ \ ball 1 (3 / 4)) := (isCompact_annulus 0 r ρ).diff isOpen_ball
  have hballA₀ : ball (1 : ℂ) (3 / 4) ⊆ A₀ := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    have h₁ : ‖z‖ - 1 ≤ ‖z - 1‖ := by simpa using norm_sub_norm_le z (1 : ℂ)
    have h₂ : 1 - ‖z‖ ≤ ‖z - 1‖ := by
      simpa only [norm_one, norm_sub_rev] using norm_sub_norm_le (1 : ℂ) z
    refine ⟨?_, ?_⟩ <;> simp only [sub_zero] <;> linarith
  have hI₀ : ∫ z in A₀, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ω.circleArea u 0 ρ - ω.circleArea u 0 r := by
    rw [integral_annulus ω 0 hr₀ (by linarith) fun z hz ↦ huc (Metric.ne_of_mem_annulus hr₀ hz)]
    congr 1 <;> refine circleArea_congr ω fun θ ↦ huc_eq ?_
    · have := norm_sub_norm_le (circleMap 0 ρ θ) 1
      rw [norm_circleMap_zero, abs_of_nonneg (by linarith), norm_one] at this
      linarith
    · have := norm_sub_norm_le 1 (circleMap 0 r θ)
      rw [norm_one, norm_sub_rev, norm_circleMap_zero, abs_of_nonneg hr₀.le] at this
      linarith
  have hAu : ∫ z in A₀ \ ball 1 (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ∫ z in A₀ \ ball 1 (3 / 4), ω (fderiv ℝ u z 1) (fderiv ℝ u z I) :=
    setIntegral_congr_fun hA.measurableSet fun z hz ↦ by
      rw [(huc_near_eq (by
        have := hz.2
        rw [mem_ball, dist_eq_norm, not_lt] at this
        linarith)).fderiv_eq]
  have hAsplit : ∫ z in A₀, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      (∫ z in A₀ \ ball 1 (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I)) +
        ∫ z in ball (1 : ℂ) (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) := by
    conv_lhs => rw [← sdiff_union_of_subset hballA₀]
    exact setIntegral_union disjoint_sdiff_left measurableSet_ball
      (integrableOn_fderiv_apply_of_contDiffAt ω hA fun z hz ↦
        (huc (Metric.ne_of_mem_annulus hr₀ hz.1)).of_le (by norm_num))
      ((integrableOn_fderiv_apply_of_contDiffAt ω (isCompact_closedBall 1 (3 / 4))
        fun z hz ↦ (huc (ne_zero_of_norm_sub_one_lt
          (by rw [mem_closedBall, dist_eq_norm] at hz; linarith))).of_le (by norm_num)).mono_set
        ball_subset_closedBall)
  rw [← hAu, ← hI₀, hAsplit]

/-- The disc about `1` of the cut-off map, which vanishes near `1`: its area integral is the circle
area of `u` on the boundary circle. -/
private theorem integral_ball_cutoff (ω : SymplecticForm V) {u uc : ℂ → V}
    (huc : ∀ {w : ℂ}, w ≠ 0 → ContDiffAt ℝ 2 uc w)
    (huc_eq : ∀ {w : ℂ}, 1 / 2 ≤ ‖w - 1‖ → uc w = u w)
    (huc_zero : ∀ {w : ℂ}, ‖w - 1‖ ≤ 1 / 4 → uc w = 0)
    (huc_near_zero : ∀ {w : ℂ}, ‖w - 1‖ < 1 / 4 → uc =ᶠ[𝓝 w] fun _ ↦ 0) :
    ∫ z in ball (1 : ℂ) (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ω.circleArea u 1 (3 / 4) := by
  have hC : ∫ z in {z : ℂ | 1 / 8 ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4},
      ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) = ω.circleArea u 1 (3 / 4) := by
    rw [integral_annulus ω 1 (by norm_num) (by norm_num)
      fun z hz ↦ huc (ne_zero_of_norm_sub_one_lt (by linarith [hz.2])),
      circleArea_eq_zero ω (c := 1) (r := 1 / 8) fun θ ↦
        huc_zero (by norm_num),
      sub_zero]
    exact circleArea_congr ω fun θ ↦
      huc_eq (by norm_num)
  rw [← hC, ← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    measurableSet_closedBall.nullMeasurableSet ball_subset_closedBall ?_]
  · refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_closedBall
      (fun z hz ↦ ?_) fun z hz ↦ ?_
    · rw [mem_closedBall, dist_eq_norm]
      exact hz.2
    · have hz' : ‖z - 1‖ < 1 / 8 := by
        by_contra h
        exact hz.2 ⟨not_lt.1 h, by simpa [dist_eq_norm] using hz.1⟩
      rw [(huc_near_zero (by linarith)).fderiv_eq]
      simp
  · filter_upwards [ae_notMem_sphere] with z hz hz'
    exact absurd (mem_sphere.2 (le_antisymm hz'.1 (not_lt.1 hz'.2))) hz

/-- Stokes' formula on the annulus about `1`, for a map which is `C²` on `ℂ ∖ {0, 1}`. -/
private theorem integral_annulus_one (ω : SymplecticForm V) {u : ℂ → V} {r : ℝ} (hr₀ : 0 < r)
    (hr : r ≤ 1 / 10) (hu : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ContDiffAt ℝ 2 u w) :
    ∫ z in {z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      ω.circleArea u 1 (3 / 4) - ω.circleArea u 1 r :=
  integral_annulus ω 1 hr₀ (by linarith) fun _ hz ↦
    hu _ (ne_zero_ne_one_of_mem_annulus hr₀ hz).1 (ne_zero_ne_one_of_mem_annulus hr₀ hz).2

/-- The area integral over the truncation is the integral over the part of the annulus about `0`
outside the disc about `1` plus the integral over the annulus about `1`. -/
private theorem integral_truncation_eq (ω : SymplecticForm V) {u : ℂ → V} {R r ρ : ℝ}
    (hr_def : r = Real.exp (-(2 * π * R)) / 2) (hρ_def : ρ = 2 * Real.exp (2 * π * R))
    (hr₀ : 0 < r) (hr : r ≤ 1 / 10) (hρ : 10 ≤ ρ)
    (hu : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → ContDiffAt ℝ 2 u w) :
    ∫ w in truncation R, ω (fderiv ℝ u w 1) (fderiv ℝ u w I) =
      (∫ z in {z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ} \ ball 1 (3 / 4),
          ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) +
        ∫ z in {z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) := by
  set A : Set ℂ := {z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ} \ ball 1 (3 / 4)
  set B : Set ℂ := {z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}
  have hA : IsCompact A := (isCompact_annulus 0 r ρ).diff isOpen_ball
  have hB : IsCompact B := isCompact_annulus 1 r (3 / 4)
  have hAfar {z : ℂ} (hz : z ∈ A) : 3 / 4 ≤ ‖z - 1‖ := by
    have := hz.2
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  rw [truncation_eq_union hr_def hρ_def (by linarith) (by linarith),
    setIntegral_union (Set.disjoint_left.2 fun z (hzA : z ∈ A)
      (hzB : z ∈ B ∩ ball (1 : ℂ) (3 / 4)) ↦ hzA.2 hzB.2)
      (hB.measurableSet.inter measurableSet_ball)
      (integrableOn_fderiv_apply_of_contDiffAt ω hA fun z hz ↦
        (hu z (Metric.ne_of_mem_annulus hr₀ hz.1) fun h ↦ by
          subst h
          have := hAfar hz
          norm_num at this).of_le (by norm_num))
      ((integrableOn_fderiv_apply_of_contDiffAt ω hB fun z hz ↦
        (hu z (ne_zero_ne_one_of_mem_annulus hr₀ hz).1
          (ne_zero_ne_one_of_mem_annulus hr₀ hz).2).of_le (by norm_num)).mono_set
        inter_subset_left),
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hB.measurableSet.nullMeasurableSet
      inter_subset_left ?_]
  filter_upwards [ae_notMem_sphere] with z hz hz'
  refine absurd (mem_sphere.2 ?_) hz
  rw [dist_eq_norm]
  exact le_antisymm hz'.1.2 (not_lt.1 fun h ↦ hz'.2 ⟨hz'.1, by rwa [mem_ball, dist_eq_norm]⟩)

omit [FiniteDimensional ℝ V] in
/-- The boundary circles of the truncation are the circles of the end loops. -/
private theorem sum_endSign_loopArea (ω : SymplecticForm V) (u : ℂ → V) {R r ρ : ℝ}
    (hr_def : r = Real.exp (-(2 * π * R)) / 2) (hρ_def : ρ = 2 * Real.exp (2 * π * R)) :
    ∑ q : Puncture, q.endSign *
      ω.loopArea (fun t ↦ u (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))) =
        ω.circleArea u 0 ρ - ω.circleArea u 0 r - ω.circleArea u 1 r := by
  have e₀ : ‖zero.endScale‖ * Real.exp (-(2 * π * (zero.endSign * R))) = r := by
    rw [hr_def, endScale_zero, endSign_zero, one_mul]
    norm_num
    ring
  have e₁ : ‖one.endScale‖ * Real.exp (-(2 * π * (one.endSign * R))) = r := by
    rw [hr_def, endScale_one, endSign_one, one_mul]
    norm_num
    ring
  have e₂ : ‖inf.endScale‖ * Real.exp (-(2 * π * (inf.endSign * R))) = ρ := by
    rw [hρ_def, endScale_inf, endSign_inf, show -(2 * π * (-1 * R)) = 2 * π * R by ring]
    norm_num
  simp only [loopArea_cylindricalEndLift]
  rw [sum_univ, e₀, e₁, e₂, endSign_zero, endSign_one, endSign_inf, endCenter_zero, endCenter_one,
    endCenter_inf]
  ring

/-- **Stokes' formula for symplectic area on the truncated thrice-punctured sphere.** Let `u` be
`C²` on `S = ℂ ∖ {0, 1}`. For `R ≥ 1` the symplectic area of `u` over the truncation `S_R` is the
signed sum of the loop areas of the restrictions of `u` to the three boundary circles `±s = R`,
parametrized by the end coordinates:

`∫_{S_R} u^*ω = ∑ q, ±a(t ↦ u(φ_q(±R + i t)))`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. -/
theorem integral_fderiv_apply_truncation (ω : SymplecticForm V) {u : ℂ → V}
    (hu : ContDiffOn ℝ 2 u {w : ℂ | w ≠ 0 ∧ w ≠ 1}) {R : ℝ} (hR : 1 ≤ R) :
    ∫ w in truncation R, ω (fderiv ℝ u w 1) (fderiv ℝ u w I) =
      ∑ q : Puncture, q.endSign *
        ω.loopArea (fun t ↦ u (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))) := by
  -- The radii of the boundary circles: `r` about `0` and `1`, and `ρ` about `0`.
  obtain ⟨r, hr_def⟩ : ∃ r, r = Real.exp (-(2 * π * R)) / 2 := ⟨_, rfl⟩
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ, ρ = 2 * Real.exp (2 * π * R) := ⟨_, rfl⟩
  have hexp : 5 ≤ Real.exp (2 * π * R) := by
    have := Real.add_one_le_exp (2 * π * R)
    nlinarith [Real.two_le_pi]
  have hexp' : Real.exp (-(2 * π * R)) * Real.exp (2 * π * R) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hr₀ : 0 < r := by rw [hr_def]; positivity
  have hr : r ≤ 1 / 10 := by
    rw [hr_def]
    nlinarith [Real.exp_pos (-(2 * π * R))]
  have hρ : 10 ≤ ρ := by rw [hρ_def]; linarith
  have hS : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} :=
    (isOpen_ne_fun continuous_id continuous_const).inter
      (isOpen_ne_fun continuous_id continuous_const)
  have hu' (w : ℂ) (h₀ : w ≠ 0) (h₁ : w ≠ 1) : ContDiffAt ℝ 2 u w :=
    hu.contDiffAt (hS.mem_nhds ⟨h₀, h₁⟩)
  -- Cut `u` off near `1`: `uc` vanishes near `1` and equals `u` away from it.
  obtain ⟨uc, huc_eq, huc_zero, huc_near_zero, huc_near_eq, huc⟩ := exists_cutoff hu'
  rw [sum_endSign_loopArea ω u hr_def hρ_def,
    integral_truncation_eq ω hr_def hρ_def hr₀ hr hρ hu',
    integral_annulus_one ω hr₀ hr hu']
  linarith [integral_cutoff_sdiff ω hr₀ hr hρ huc huc_eq huc_near_eq,
    integral_ball_cutoff ω huc huc_eq huc_zero huc_near_zero]

end TauCeti.SymplecticForm
