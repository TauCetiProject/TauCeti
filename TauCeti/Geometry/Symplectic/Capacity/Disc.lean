/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Capacity.HoferZehnder
public import TauCeti.Geometry.Symplectic.Hamiltonian.RadialTwist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The `π₁`-sensitive capacity of a disc is at least its area

On the complex line with its standard area form (`TauCeti.stdComplexSymplecticForm`), the disc of
radius `r` has area `π r²`. This file proves the lower bound

`π r² ≤ c°_HZ(U; W)`

for every set `U` containing a disc of radius `r` and every set `W` in which contractibility is
tested (`TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`). In particular the disc `D` of radius
`r` has `π r² ≤ c°_HZ(D)`. The Hofer–Zehnder capacity of the disc is exactly `π r²`; the upper bound
rests on an existence theorem for periodic orbits and is not proved here.

The lower bound comes from radial Hamiltonians `H(w) = -G(‖w - p‖²) / 2`
(`TauCeti.radialHamiltonian`), whose flow rotates each circle about `p` at the angular speed `G'`
of its squared radius. A nonconstant periodic orbit of period `T` therefore needs `T G' ∈ 2πℤ`
with `T G' ≠ 0`, so if `|T G'| < 2π` along an orbit, the orbit is constant
(`TauCeti.eq_of_periodic_radialHamiltonian`). This is independent of any contractibility, so these
Hamiltonians are admissible in every `W`. A profile `G` with slope `G' = κ φ`, for a bump function
`φ` supported in `(0, r²)` and a constant `κ < 2π`, rises from `G(0) = -κ ∫ φ` to `0` at `r²`, so
the Hamiltonian is admissible with maximum `κ ∫ φ / 2`, which approaches `π r²` as `κ → 2π` and
`φ` approaches the indicator of `(0, r²)`.

## Main results

* `TauCeti.ofReal_pi_mul_sq_le_contractibleHZCapacity`: a set containing a disc of radius `r` has
  `π₁`-sensitive capacity at least `π r²`, whatever set contractibility is tested in.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (radial Hamiltonians and the capacity of the ball).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 12.3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 6.1 and the remarks after it.
-/

public section

noncomputable section

open Complex Filter Function Metric Set Topology
open scoped ContDiff

namespace TauCeti

/-! ### A slow radial profile -/

namespace DiscCapacity

variable {R t : ℝ}

/-- The bump function on `ℝ` with centre `R / 2`, equal to `1` within `t R / 2` of the centre and
supported within `(1 + t) R / 4` of it, so that its support lies in `(0, R)`. -/
private def bump (hR : 0 < R) (ht₀ : 0 < t) (ht₁ : t < 1) : ContDiffBump (R / 2) :=
  ⟨t * R / 2, (1 + t) * R / 4, by positivity, by nlinarith⟩

/-- The profile `G(s) = 2π t ∫_R^s φ`, whose slope `2π t φ` is less than `2π`. -/
private def profile (hR : 0 < R) (ht₀ : 0 < t) (ht₁ : t < 1) (s : ℝ) : ℝ :=
  2 * Real.pi * t * ∫ u in R..s, bump hR ht₀ ht₁ u

variable (hR : 0 < R) (ht₀ : 0 < t) (ht₁ : t < 1)

private theorem bump_eq_zero {s : ℝ} (hs : s ∉ Ioo ((1 - t) * R / 4) ((3 + t) * R / 4)) :
    bump hR ht₀ ht₁ s = 0 := by
  rw [← notMem_support, ContDiffBump.support_eq, Real.ball_eq_Ioo]
  rintro ⟨h₁, h₂⟩
  simp only [bump] at h₁ h₂
  exact hs ⟨by linarith, by linarith⟩

private theorem hasDerivAt_profile (s : ℝ) :
    HasDerivAt (profile hR ht₀ ht₁) (2 * Real.pi * t * bump hR ht₀ ht₁ s) s :=
  (((bump hR ht₀ ht₁).continuous.integral_hasStrictDerivAt R s).hasDerivAt).const_mul _

private theorem deriv_profile : deriv (profile hR ht₀ ht₁) =
    fun s ↦ 2 * Real.pi * t * bump hR ht₀ ht₁ s :=
  funext fun s ↦ (hasDerivAt_profile hR ht₀ ht₁ s).deriv

private theorem contDiff_profile : ContDiff ℝ ∞ (profile hR ht₀ ht₁) :=
  contDiff_const.mul
    (by simpa using ((bump hR ht₀ ht₁).contDiff (n := ⊤)).contDiff_add_one_integral R)

private theorem monotone_profile : Monotone (profile hR ht₀ ht₁) :=
  monotone_of_deriv_nonneg ((contDiff_profile hR ht₀ ht₁).differentiable (by simp))
    fun s ↦ by
      rw [deriv_profile]
      exact mul_nonneg (by positivity) (bump hR ht₀ ht₁).nonneg

private theorem abs_deriv_profile_lt (s : ℝ) :
    |deriv (profile hR ht₀ ht₁) s| < 2 * Real.pi := by
  rw [deriv_profile, abs_of_nonneg (mul_nonneg (by positivity) (bump hR ht₀ ht₁).nonneg)]
  calc 2 * Real.pi * t * bump hR ht₀ ht₁ s ≤ 2 * Real.pi * t :=
        mul_le_of_le_one_right (by positivity) (bump hR ht₀ ht₁).le_one
    _ < 2 * Real.pi := by nlinarith [Real.pi_pos]

/-- The bump integrates to `0` over an interval on which it vanishes. -/
private theorem integral_bump_eq_zero {a b : ℝ}
    (hab : ∀ u ∈ uIcc a b, u ∉ Ioo ((1 - t) * R / 4) ((3 + t) * R / 4)) :
    ∫ u in a..b, bump hR ht₀ ht₁ u = 0 := by
  rw [intervalIntegral.integral_congr (g := 0) fun u hu ↦ bump_eq_zero hR ht₀ ht₁ (hab u hu)]
  simp

/-- The profile vanishes from `(3 + t) R / 4 < R` on. -/
private theorem profile_eq_zero {s : ℝ} (hs : (3 + t) * R / 4 ≤ s) : profile hR ht₀ ht₁ s = 0 := by
  have hmin : (3 + t) * R / 4 ≤ min R s := le_min (by nlinarith) hs
  rw [profile, integral_bump_eq_zero hR ht₀ ht₁ fun u hu h ↦ ?_, mul_zero]
  rw [uIcc, mem_Icc] at hu
  linarith [h.2, hu.1]

private theorem profile_nonpos (s : ℝ) : profile hR ht₀ ht₁ s ≤ 0 :=
  (monotone_profile hR ht₀ ht₁ (le_max_left s ((3 + t) * R / 4))).trans
    (profile_eq_zero hR ht₀ ht₁ (le_max_right _ _)).le

/-- Near `0` the profile is constant: below `(1 - t) R / 4` the bump vanishes. -/
private theorem profile_eq_profile_zero {s : ℝ} (hs₀ : 0 ≤ s) (hs : s ≤ (1 - t) * R / 4) :
    profile hR ht₀ ht₁ s = profile hR ht₀ ht₁ 0 := by
  have hint (a b : ℝ) := (bump hR ht₀ ht₁).continuous.intervalIntegrable (μ := MeasureTheory.volume)
    a b
  have h0 : ∫ u in (0 : ℝ)..s, bump hR ht₀ ht₁ u = 0 := integral_bump_eq_zero hR ht₀ ht₁
    fun u hu h ↦ by
      rw [uIcc_of_le hs₀, mem_Icc] at hu
      linarith [h.1]
  rw [profile, profile, ← intervalIntegral.integral_add_adjacent_intervals (hint R 0) (hint 0 s),
    h0, add_zero]

/-- The integral of the profile's bump over `(0, R)` is at least `t R`, the length of the interval
on which the bump equals `1`. -/
private theorem mul_le_integral_bump : t * R ≤ ∫ u in (0 : ℝ)..R, bump hR ht₀ ht₁ u := by
  have h1 : ∫ u in (R / 2 - t * R / 2)..(R / 2 + t * R / 2), bump hR ht₀ ht₁ u = t * R := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 1) fun u hu ↦ ?_]
    · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      ring
    · refine (bump hR ht₀ ht₁).one_of_mem_closedBall ?_
      rw [Real.closedBall_eq_Icc]
      rwa [uIcc_of_le (by nlinarith)] at hu
  rw [← h1]
  exact intervalIntegral.integral_mono_interval (by nlinarith) (by nlinarith) (by nlinarith)
    (MeasureTheory.ae_of_all _ fun _ ↦ (bump hR ht₀ ht₁).nonneg)
    ((bump hR ht₀ ht₁).continuous.intervalIntegrable _ _)

/-- The radial Hamiltonian of the profile is at least `π t² R` at the centre. -/
private theorem pi_mul_sq_le_radialHamiltonian (p : ℂ) :
    Real.pi * t ^ 2 * R ≤ radialHamiltonian (profile hR ht₀ ht₁) p p := by
  rw [radialHamiltonian_apply, sub_self, norm_zero, zero_pow two_ne_zero, profile,
    intervalIntegral.integral_symm]
  calc Real.pi * t ^ 2 * R = Real.pi * t * (t * R) := by ring
    _ ≤ Real.pi * t * ∫ u in (0 : ℝ)..R, bump hR ht₀ ht₁ u := by
      gcongr
      exact mul_le_integral_bump hR ht₀ ht₁
    _ = _ := by ring

/-- The disc of radius `√R` about `p` is the set of points at squared distance less than `R`. -/
private theorem mem_ball_sqrt_iff {p w : ℂ} : w ∈ ball p √R ↔ ‖w - p‖ ^ 2 < R := by
  rw [mem_ball, dist_eq_norm, ← Real.sqrt_lt_sqrt_iff (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The radial Hamiltonian of the profile is `HZ°`-admissible for the disc of radius `√R` in every
set: its slope is less than `2π`, so it has no nonconstant periodic orbit of period at most `1`. -/
private theorem isContractibleHZAdmissible (p : ℂ) (W : Set ℂ) :
    stdComplexSymplecticForm.constSmooth.IsContractibleHZAdmissible W (ball p √R)
      (radialHamiltonian (profile hR ht₀ ht₁) p) := by
  have hEc : Continuous fun w : ℂ ↦ ‖w - p‖ ^ 2 := by fun_prop
  have hG := contDiff_profile hR ht₀ ht₁
  have hG0 (s : ℝ) (hs : (3 + t) * R / 4 ≤ s) := profile_eq_zero hR ht₀ ht₁ hs
  have hR' : (3 + t) * R / 4 < R := by nlinarith
  obtain ⟨K, hX⟩ := exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian (hG.of_le
    (by norm_cast)) hG0 p
  -- The support lies where the squared distance is at most `(3 + t) R / 4`.
  have hsupp : tsupport (radialHamiltonian (profile hR ht₀ ht₁) p) ⊆
      (fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Iic ((3 + t) * R / 4) := by
    refine closure_minimal (fun w hw ↦ ?_) (isClosed_Iic.preimage hEc)
    by_contra h
    exact hw (by simp [hG0 _ (not_le.1 h).le])
  refine
    { contMDiff := (contDiff_radialHamiltonian hG p).contMDiff
      isCompact_tsupport := (hasCompactSupport_radialHamiltonian hG0 p).isCompact
      tsupport_subset_interior := hsupp.trans fun w hw ↦ by
        rw [isOpen_ball.interior_eq, mem_ball_sqrt_iff]
        exact (mem_Iic.1 hw).trans_lt hR'
      tsupport_subset_interior_manifold := by
        rw [ModelWithCorners.interior_eq_univ]
        exact subset_univ _
      nonneg := fun w ↦ by
        rw [radialHamiltonian_apply]
        linarith [profile_nonpos hR ht₀ ht₁ (‖w - p‖ ^ 2)]
      exists_isOpen_eqOn_zero := ⟨(fun w ↦ ‖w - p‖ ^ 2) ⁻¹' Ioo ((3 + t) * R / 4) R,
        isOpen_Ioo.preimage hEc, ⟨p + (√((7 + t) * R / 8) : ℂ), ?_⟩,
        fun w hw ↦ mem_ball_sqrt_iff.2 hw.2, fun w hw ↦ ?_⟩
      exists_isOpen_isMaxOn := ⟨ball p √((1 - t) * R / 4), isOpen_ball,
        nonempty_ball.2 (Real.sqrt_pos.2 (by nlinarith)), fun w hw ↦ isMaxOn_iff.2 fun v _ ↦ ?_⟩
      eq_of_isMIntegralCurve := fun T γ hT hT₁ hγ hper _ ↦
        eq_of_periodic_radialHamiltonian hX (fun s ↦ ?_)
          ((hG.differentiable (by simp)) _) hT.ne' hper ?_ }
  · have h78 : 0 ≤ (7 + t) * R / 8 := by nlinarith
    simp only [mem_preimage, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt h78, mem_Ioo]
    constructor <;> nlinarith
  · simp [hG0 _ hw.1.le]
  · rw [mem_ball_sqrt_iff] at hw
    simp only [radialHamiltonian_apply]
    rw [profile_eq_profile_zero hR ht₀ ht₁ (sq_nonneg _) hw.le]
    linarith [monotone_profile hR ht₀ ht₁ (sq_nonneg ‖v - p‖)]
  · -- An integral curve of the Hamiltonian vector field solves Hamilton's equations.
    have h := hγ s
    rw [SymplecticForm.hamiltonianVectorField_constSmooth] at h
    exact hasDerivAt_iff_hasFDerivAt.2 (hasMFDerivAt_iff_hasFDerivAt.1 h)
  · rw [abs_mul, abs_of_pos hT]
    exact (mul_le_of_le_one_left (abs_nonneg _) hT₁).trans_lt (abs_deriv_profile_lt hR ht₀ ht₁ _)

end DiscCapacity

/-! ### The capacity of a disc -/

/-- **The `π₁`-sensitive capacity of a disc is at least its area.** On the complex line with its
standard area form, a set `U` containing the disc of radius `r ≥ 0` about some point has
`c°_HZ(U; W) ≥ π r²`, whatever set `W` contractibility is tested in. In particular the disc `D` of
radius `r` has `c°_HZ(D) ≥ π r²`. -/
theorem ofReal_pi_mul_sq_le_contractibleHZCapacity {p : ℂ} {r : ℝ} (hr : 0 ≤ r) {W U : Set ℂ}
    (hU : ball p r ⊆ U) :
    ENNReal.ofReal (Real.pi * r ^ 2) ≤
      stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hR : 0 < r ^ 2 := by positivity
  have hball : ball p √(r ^ 2) = ball p r := by rw [Real.sqrt_sq hr.le]
  -- For each `t ∈ (0, 1)` the profile gives an admissible Hamiltonian of height `π t² r²`.
  have hle : ∀ᶠ t in 𝓝[<] (1 : ℝ), ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) ≤
      stdComplexSymplecticForm.constSmooth.contractibleHZCapacity W U := by
    filter_upwards [Ioo_mem_nhdsLT one_pos] with t ht
    have hF := (DiscCapacity.isContractibleHZAdmissible hR ht.1 ht.2 p W).mono subset_rfl
      (hball.symm ▸ hU)
    refine (ENNReal.ofReal_le_ofReal ?_).trans hF.ofReal_iSup_le_contractibleHZCapacity
    obtain ⟨O, -, ⟨w, hw⟩, hmax⟩ := hF.exists_isOpen_isMaxOn
    refine (DiscCapacity.pi_mul_sq_le_radialHamiltonian hR ht.1 ht.2 p).trans
      (le_ciSup ⟨radialHamiltonian (DiscCapacity.profile hR ht.1 ht.2) p w, ?_⟩ p)
    rintro _ ⟨v, rfl⟩
    exact isMaxOn_iff.1 (hmax w hw) v (mem_univ v)
  refine le_of_tendsto ?_ hle
  have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (Real.pi * t ^ 2 * r ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds

end TauCeti
