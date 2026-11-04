/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.Basic
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
import TauCeti.Geometry.Symplectic.Duality
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
  have hu' {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 1) : ContDiffAt ℝ 2 u w :=
    hu.contDiffAt (hS.mem_nhds ⟨h₀, h₁⟩)
  -- Cut `u` off near `1`: `uc = (1 - χ) u` vanishes near `1` and equals `u` away from it.
  let χ : ContDiffBump (1 : ℂ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let uc : ℂ → V := fun w ↦ (1 - χ w) • u w
  have huc_eq {w : ℂ} (hw : 1 / 2 ≤ ‖w - 1‖) : uc w = u w := by
    simp [uc, χ.zero_of_le_dist (by rw [dist_eq_norm]; exact hw)]
  have huc_zero {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 4) : uc w = 0 := by
    simp [uc, χ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hw)]
  have huc_near_eq {w : ℂ} (hw : 1 / 2 < ‖w - 1‖) : uc =ᶠ[𝓝 w] u := by
    filter_upwards [(isOpen_lt continuous_const
      (continuous_id.sub continuous_const).norm).mem_nhds hw] with z hz using huc_eq hz.le
  have huc_near_zero {w : ℂ} (hw : ‖w - 1‖ < 1 / 4) : uc =ᶠ[𝓝 w] fun _ ↦ 0 := by
    filter_upwards [(isOpen_lt (continuous_id.sub continuous_const).norm
      continuous_const).mem_nhds hw] with z hz using huc_zero hz.le
  have huc {w : ℂ} (h₀ : w ≠ 0) : ContDiffAt ℝ 2 uc w := by
    by_cases h₁ : w = 1
    · subst h₁
      exact contDiffAt_const.congr_of_eventuallyEq (huc_near_zero (by norm_num))
    · exact (contDiffAt_const.sub χ.contDiffAt).smul (hu' h₀ h₁)
  -- Norms of points on the circles and in the annuli.
  have hcircle (c : ℂ) {a : ℝ} (ha : 0 ≤ a) (θ : ℝ) : ‖circleMap c a θ - c‖ = a := by
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg ha]
  have htri (z : ℂ) : ‖z‖ - 1 ≤ ‖z - 1‖ ∧ 1 - ‖z‖ ≤ ‖z - 1‖ := by
    have t₁ := norm_sub_norm_le z 1
    have t₂ := norm_sub_norm_le 1 z
    rw [norm_one] at t₁ t₂
    rw [norm_sub_rev] at t₂
    exact ⟨t₁, t₂⟩
  have hne₀ {z : ℂ} (hz : ‖z - 1‖ < 1) : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hann (c : ℂ) (a b : ℝ) : IsCompact {z : ℂ | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b} :=
    (isCompact_closedBall c b).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        (isClosed_le (continuous_id.sub continuous_const).norm continuous_const))
      fun z hz ↦ by rw [mem_closedBall, dist_eq_norm]; exact hz.2
  -- The area density of a map which is `C²` near a compact set is integrable on it.
  have hint {v : ℂ → V} {K : Set ℂ} (hK : IsCompact K) (hv : ∀ z ∈ K, ContDiffAt ℝ 2 v z) :
      IntegrableOn (fun z ↦ ω (fderiv ℝ v z 1) (fderiv ℝ v z I)) K := by
    have hcont : ContinuousOn (fderiv ℝ v) K := fun z hz ↦
      ((hv z hz).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
    exact (ω.continuousOn_apply_comp (hcont.clm_apply continuousOn_const)
      (hcont.clm_apply continuousOn_const)).integrableOn_compact hK
  -- The pieces of the decomposition.
  set A₀ : Set ℂ := {z : ℂ | r ≤ ‖z - 0‖ ∧ ‖z - 0‖ ≤ ρ}
  set A : Set ℂ := A₀ \ ball 1 (3 / 4)
  set B : Set ℂ := {z : ℂ | r ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}
  set C : Set ℂ := {z : ℂ | 1 / 8 ≤ ‖z - 1‖ ∧ ‖z - 1‖ ≤ 3 / 4}
  have hA₀ : IsCompact A₀ := hann 0 r ρ
  have hA : IsCompact A := hA₀.diff isOpen_ball
  have hB : IsCompact B := hann 1 r (3 / 4)
  have hA₀ne {z : ℂ} (hz : z ∈ A₀) : z ≠ 0 := by
    rintro rfl
    have := hz.1
    simp only [sub_self, norm_zero] at this
    linarith
  have hAfar {z : ℂ} (hz : z ∈ A) : 3 / 4 ≤ ‖z - 1‖ := by
    have := hz.2
    rwa [mem_ball, dist_eq_norm, not_lt] at this
  have hballA₀ : ball (1 : ℂ) (3 / 4) ⊆ A₀ := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    have := htri z
    refine ⟨?_, ?_⟩ <;> simp only [sub_zero] <;> linarith
  have hsphere : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ sphere (1 : ℂ) (3 / 4) :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere (μ := volume) (1 : ℂ) (3 / 4))
  -- The annulus about `0`, for the cut-off map.
  have hI₀ : ∫ z in A₀, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ω.circleArea u 0 ρ - ω.circleArea u 0 r := by
    rw [integral_annulus ω 0 hr₀ (by linarith) fun z hz ↦ huc (hA₀ne hz)]
    congr 1 <;> refine circleArea_congr ω fun θ ↦ huc_eq ?_
    · have := (htri (circleMap 0 ρ θ)).1
      rw [← sub_zero (circleMap 0 ρ θ), hcircle 0 (by linarith) θ] at this
      simp only [sub_zero] at this
      linarith
    · have := (htri (circleMap 0 r θ)).2
      rw [← sub_zero (circleMap 0 r θ), hcircle 0 hr₀.le θ] at this
      simp only [sub_zero] at this
      linarith
  -- The disc about `1`, for the cut-off map: it vanishes near `1`.
  have hball : ∫ z in ball (1 : ℂ) (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ω.circleArea u 1 (3 / 4) := by
    have hC : ∫ z in C, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
        ω.circleArea u 1 (3 / 4) := by
      rw [integral_annulus ω 1 (by norm_num) (by norm_num)
        fun z hz ↦ huc (hne₀ (by linarith [hz.2])),
        circleArea_eq_zero ω (c := 1) (r := 1 / 8) fun θ ↦
          huc_zero (by rw [hcircle 1 (by norm_num)]; norm_num),
        sub_zero]
      exact circleArea_congr ω fun θ ↦ huc_eq (by rw [hcircle 1 (by norm_num)]; norm_num)
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
    · filter_upwards [hsphere] with z hz hz'
      exact absurd (mem_sphere.2 (le_antisymm hz'.1 (not_lt.1 hz'.2))) hz
  -- The annulus about `1`, for `u` itself.
  have hI₁ : ∫ z in B, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      ω.circleArea u 1 (3 / 4) - ω.circleArea u 1 r :=
    integral_annulus ω 1 hr₀ (by linarith) fun z hz ↦
      hu' (hne₀ (by linarith [hz.2])) fun h ↦ by
        subst h
        have := hz.1
        simp only [sub_self, norm_zero] at this
        linarith
  -- Outside the disc about `1` the cut-off map is `u`.
  have hAu : ∫ z in A, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      ∫ z in A, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) :=
    setIntegral_congr_fun hA.measurableSet fun z hz ↦ by
      rw [(huc_near_eq (by linarith [hAfar hz])).fderiv_eq]
  have hAsplit : ∫ z in A₀, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) =
      (∫ z in A, ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I)) +
        ∫ z in ball (1 : ℂ) (3 / 4), ω (fderiv ℝ uc z 1) (fderiv ℝ uc z I) := by
    conv_lhs => rw [← sdiff_union_of_subset hballA₀]
    exact setIntegral_union disjoint_sdiff_left measurableSet_ball
      (hint hA fun z hz ↦ huc (hA₀ne hz.1))
      ((hint (isCompact_closedBall 1 (3 / 4))
        fun z hz ↦ huc (hne₀ (by rw [mem_closedBall, dist_eq_norm] at hz; linarith))).mono_set
        ball_subset_closedBall)
  -- The truncation is the part of `A₀` outside the disc about `1`, and the part of `B` inside.
  have hsplit : ∫ w in truncation R, ω (fderiv ℝ u w 1) (fderiv ℝ u w I) =
      (∫ z in A, ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) +
        ∫ z in B, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) := by
    have hBu : ∀ z ∈ B, ContDiffAt ℝ 2 u z := fun z hz ↦
      hu' (hne₀ (by linarith [hz.2])) fun h ↦ by
        subst h
        have := hz.1
        simp only [sub_self, norm_zero] at this
        linarith
    rw [truncation_eq_union hr_def hρ_def (by linarith) (by linarith),
      setIntegral_union (Set.disjoint_left.2 fun z (hzA : z ∈ A)
        (hzB : z ∈ B ∩ ball (1 : ℂ) (3 / 4)) ↦ hzA.2 hzB.2)
        (hB.measurableSet.inter measurableSet_ball)
        (hint hA fun z hz ↦
          hu' (hA₀ne hz.1) fun h ↦ by subst h; have := hAfar hz; norm_num at this)
        ((hint hB hBu).mono_set inter_subset_left),
      setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hB.measurableSet.nullMeasurableSet
        inter_subset_left ?_]
    filter_upwards [hsphere] with z hz hz'
    refine absurd (mem_sphere.2 ?_) hz
    rw [dist_eq_norm]
    exact le_antisymm hz'.1.2 (not_lt.1 fun h ↦ hz'.2 ⟨hz'.1, by rwa [mem_ball, dist_eq_norm]⟩)
  -- The boundary circles of the truncation are the circles of the end loops.
  have hloops : ∑ q : Puncture, q.endSign *
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
  rw [hloops, hsplit, ← hAu, hI₁]
  linarith [hAsplit, hI₀, hball]

end TauCeti.SymplecticForm
