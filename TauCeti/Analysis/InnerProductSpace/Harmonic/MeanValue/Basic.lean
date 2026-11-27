/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.Calculus.ContDiff.Translation
import TauCeti.Analysis.Calculus.RadialPrimitive
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The mean-value property and the sub-mean-value inequality

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `u : E → F` be harmonic on a neighbourhood of the closed ball `closedBall x₀ R`. This file
proves the **mean-value property**: `u x₀` is the average of `u` over the sphere of radius `R`
about `x₀`, and the average of `u` over the ball of radius `R` about `x₀`,

`⨍ θ ∈ S, u (x₀ + R • θ) ∂μ.toSphere = u x₀` and `⨍ x in ball x₀ R, u x ∂μ = u x₀`.

The sphere of radius `R` about `x₀` is parametrized by the unit sphere `S` through
`θ ↦ x₀ + R • θ`, and carries Mathlib's surface measure `μ.toSphere`, the measure that makes
`μ` the product of the surface and radial measures in polar coordinates. Only the sphere average
needs `E ≠ 0`: in the trivial space the unit sphere is empty, and the integral identities hold
with both sides zero.

## The argument

Write `Φ s = ∫ θ ∈ S, u (s • θ) ∂μ.toSphere` for the sphere integral at radius `s` about the
origin. The classical proof differentiates `Φ` in `s` and evaluates `Φ'` by the divergence theorem
on the ball; the proof here instead shows that the *distributional* derivative of `Φ` on `(0, R)`
vanishes, and then applies the du Bois-Reymond lemma
`ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`. No divergence theorem is
needed.

A harmonic function is weakly harmonic
(`InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero`): `∫ Δχ • u ∂μ = 0` for every
test function `χ` supported in the ball. Taking `χ` radial, `χ x = ρ (‖x‖ ^ 2)`, the Laplacian
`Δχ x = 4 ‖x‖² ρ'' (‖x‖²) + 2 n ρ' (‖x‖²)` is radial too (`ContDiffAt.laplacian_comp_norm_sq`),
and integrating in polar coordinates with the radial variable
outermost (`TauCeti.integral_eq_integral_Ioi_integral_toSphere`) turns the identity into

`∫ s in (0, ∞), s ^ (n - 1) (4 s² ρ'' (s²) + 2 n ρ' (s²)) • Φ s = 0`,

whose weight is `2 (s ^ n ρ' (s ^ 2))'`. Every test function `ψ` on `(0, R)` is of the form
`ψ s = s ^ n ρ' (s ^ 2)` for such a `ρ`, namely the primitive of `t ↦ ψ (√t) / (√t) ^ n`, so
`∫ ψ' • Φ = 0` for all of them, and `Φ` is constant on `(0, R)`. Continuity of `Φ` on `[0, R]`
gives `Φ R = Φ 0 = μ.toSphere(S) • u 0`; integrating the sphere identity over the radii `s < R`, in
polar coordinates once more, gives the ball version.

The same computation applies to any `C²` function, with Green's identity
`∫ Δχ • u = ∫ χ • Δu` (`ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`) in place
of weak harmonicity: `2 ∫ ψ' • Φ = ∫ χ • Δu`, and the radial `χ` is nonpositive when `ψ` is
nonnegative. So if `Δ f ≥ 0` on the ball, the distributional derivative of `Φ` is nonnegative,
`Φ` is nondecreasing by the monotone du Bois-Reymond lemma
`ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos`, and `Φ 0 ≤ Φ R` is the **sub-mean-value
inequality** `μ.toSphere(S) * f 0 ≤ ∫ θ ∈ S, f (R • θ) ∂μ.toSphere`, with its ball version
`μ (ball 0 R) * f 0 ≤ ∫ x in ball 0 R, f x ∂μ`. These hold for `f` of class `C²` on the open ball
and continuous on its closure, with no regularity assumed on the boundary sphere. Monotonicity of
`Φ` also bounds the integral over the ball by the last sphere integral,
`μ.toSphere(S) * ∫ x in ball 0 R, f x ∂μ ≤ μ (ball 0 R) * Φ R`.

The same identity bounds the growth of `Φ` from above by the mass of `Δ f`. The radial `χ`
attached to a nonnegative `ψ` supported in `(a, R)` is bounded by `2 (∫ ψ) / a ^ (n - 1)`
(`TauCeti.integral_abs_div_sqrt_pow_le`), so `-∫ ψ' • Φ ≤ (∫ ψ) / a ^ (n - 1) * ∫_{ball 0 R} Δ f`,
and `s ↦ c s - Φ s` is monotone on `(a, R)` for `c = (∫_{ball 0 R} Δ f) / a ^ (n - 1)`:
`Φ r₂ - Φ r₁ ≤ (r₂ - r₁) / a ^ (n - 1) * ∫_{ball 0 R} Δ f` for `a < r₁ ≤ r₂ < R`.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`,
  `InnerProductSpace.HarmonicOnNhd.average_toSphere_eq`: **the mean-value property on spheres**,
  in integral and in average form.
* `InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq`,
  `InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`: **the mean-value property on balls**, in
  integral and in average form.
* `TauCeti.mul_le_integral_toSphere_of_laplacian_nonneg`,
  `TauCeti.le_average_toSphere_of_laplacian_nonneg`: **the sub-mean-value inequality on spheres**
  for functions with nonnegative Laplacian, in integral and in average form.
* `TauCeti.mul_le_setIntegral_ball_of_laplacian_nonneg`,
  `TauCeti.le_setAverage_ball_of_laplacian_nonneg`: **the sub-mean-value inequality on balls**,
  in integral and in average form.
* `TauCeti.integral_toSphere_le_integral_toSphere_of_laplacian_nonneg`: the sphere integrals of a
  function with nonnegative Laplacian increase with the radius.
* `TauCeti.mul_setIntegral_ball_le_mul_integral_toSphere_of_laplacian_nonneg`: its average over a
  ball is at most its average over the boundary sphere.
* `TauCeti.integral_toSphere_sub_integral_toSphere_le`: the increase of its sphere integrals
  between two radii is bounded by the integral of its Laplacian over a larger ball.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.2, Theorem 2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.1.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped Distributions ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {R : ℝ}

/-! ### The radial derivative of the sphere integrals -/

/-- The distributional derivative of the sphere integrals `Φ s = ∫ θ, u (s • θ) ∂μ.toSphere` of a
`C²` function on `ball 0 R` is computed by the Laplacian: for every test function `ψ` on `(0, R)`
there is a radial `χ`, vanishing outside the ball and nonpositive when `ψ` is nonnegative, with
`∫ χ • Δu = 2 • ∫ ψ' • Φ`. -/
private lemma exists_integral_smul_laplacian_eq_two_smul_integral_deriv_smul [Nontrivial E]
    (hu : ContDiffOn ℝ 2 u (ball (0 : E) R)) (hR : 0 < R) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∃ χ : E → ℝ, (∀ x ∉ ball (0 : E) R, χ x = 0) ∧ ((∀ s, 0 ≤ ψ s) → ∀ x, χ x ≤ 0) ∧
      ∫ x, χ x • Δ u x ∂μ =
        (2 : ℝ) • ∫ s, deriv ψ s • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere ∧
      Continuous χ ∧
      ∀ x, |χ x| ≤ ∫ τ in (0 : ℝ)..R ^ 2, |ψ (√τ) / (√τ) ^ Module.finrank ℝ E| := by
  -- `ψ s = s ^ n ρ' (s ^ 2)` for a smooth `ρ` vanishing beyond `R' ^ 2`, with `R' < R`.
  obtain ⟨R', hR'0, hR'R, ρ, hρ, hρ0, hρn, hψρ, hρb⟩ :=
    exists_contDiff_eq_pow_mul_deriv (Module.finrank ℝ E) hR hψ hψs
  have hσ : ContDiff ℝ ∞ (deriv ρ) := (contDiff_infty_iff_deriv.1 hρ).2
  -- The radial test function `χ x = ρ (‖x‖ ^ 2)` on the ball, supported in `closedBall 0 R'`.
  set Ω : Opens E := ⟨ball (0 : E) R, isOpen_ball⟩ with _
  have hχ_supp : tsupport (fun x : E ↦ ρ (‖x‖ ^ 2)) ⊆ closedBall (0 : E) R' := by
    refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
    rw [mem_ball_zero_iff]
    by_contra h
    exact hx (hρ0 _ (pow_le_pow_left₀ hR'0.le (not_lt.mp h) 2))
  have hχΩ : tsupport (fun x : E ↦ ρ (‖x‖ ^ 2)) ⊆ Ω :=
    hχ_supp.trans (closedBall_subset_ball hR'R)
  let χ : 𝓓(Ω, ℝ) := ⟨fun x ↦ ρ (‖x‖ ^ 2), hρ.comp (contDiff_norm_sq ℝ),
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hχ_supp, hχΩ⟩
  have hχ : (χ : E → ℝ) = fun x ↦ ρ (‖x‖ ^ 2) := rfl
  refine ⟨χ, fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχΩ h),
    fun hψn x ↦ hρn hψn _, ?_, by rw [hχ]; exact (hρ.comp (contDiff_norm_sq ℝ)).continuous,
    fun x ↦ by rw [hχ]; exact hρb _⟩
  have hΔ : Δ (χ : E → ℝ) = fun x ↦ 4 * ‖x‖ ^ 2 * deriv (deriv ρ) (‖x‖ ^ 2) +
      2 * (Module.finrank ℝ E : ℝ) * deriv ρ (‖x‖ ^ 2) := by
    funext x
    rw [hχ, (hρ.of_le (by simp)).contDiffAt.laplacian_comp_norm_sq]
  -- Green's identity against `χ`, in polar coordinates.
  -- `Ω` is the ball, as a set.
  have hu' : ContDiffOn ℝ 2 u Ω := hu
  rw [← hu'.integral_laplacian_smul_eq_integral_smul_laplacian (μ := μ) χ]
  have hΔcont : Continuous (Δ (χ : E → ℝ)) :=
    ((hρ.comp (contDiff_norm_sq ℝ)).of_le (by simp)).continuous_laplacian
  have hf_cont : Continuous fun x ↦ Δ (χ : E → ℝ) x • u x :=
    (hΔcont.continuousOn.smul hu'.continuousOn).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left _ _).trans
        ((tsupport_laplacian_subset _).trans χ.tsupport_subset))
  have hf_supp : HasCompactSupport fun x ↦ Δ (χ : E → ℝ) x • u x :=
    (HasCompactSupport.intro χ.hasCompactSupport fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_laplacian_subset _ h)).smul_right
  rw [integral_eq_integral_Ioi_integral_toSphere _
    (hf_cont.integrable_of_hasCompactSupport hf_supp)]
  -- On the sphere of radius `s`, the weight is `2 ψ' s`.
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, Δ (χ : E → ℝ) (s • (θ : E)) • u (s • (θ : E)) ∂μ.toSphere =
        (2 * deriv ψ s) • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere := by
    intro s hs
    have hs : 0 < s := hs
    have hnorm : ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun θ ↦ by
      rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    simp_rw [hΔ, hnorm]
    rw [MeasureTheory.integral_smul, smul_smul, pow_mul_add_eq_two_mul_deriv
      Module.finrank_pos.ne' (hσ.differentiable (by simp) (s ^ 2)) hψρ hs]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_]
  · simp_rw [mul_smul]
    rw [MeasureTheory.integral_smul]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψs (tsupport_deriv_subset h)).1]

/-! ### The mean-value property -/

section MeanValue

variable [CompleteSpace F]

/-- The mean-value property on spheres about the origin. -/
private lemma integral_toSphere_eq_of_harmonicOnNhd_zero [Nontrivial E]
    (hu : HarmonicOnNhd u (closedBall (0 : E) R)) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u 0 := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [integral_const]
  set Φ : ℝ → F := fun s ↦ ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere with hΦ_def
  have hΦc : ContinuousOn Φ (Icc 0 R) := hu.contDiffOn.continuousOn.integral_toSphere_smul
  -- The distributional derivative of `Φ` vanishes, since `Δ u = 0` on the ball.
  obtain ⟨c, hc⟩ :=
    (hΦc.mono Ioo_subset_Icc_self).exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero
      fun ψ hψ hψs ↦ by
        obtain ⟨χ, hχ0, -, hχ, -⟩ := exists_integral_smul_laplacian_eq_two_smul_integral_deriv_smul
          (μ := μ) (hu.contDiffOn.mono ball_subset_closedBall) hR hψ hψs
        have hzero : ∫ x, χ x • Δ u x ∂μ = 0 := by
          refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
          by_cases hx : x ∈ ball (0 : E) R
          · simp [(hu x (ball_subset_closedBall hx)).2.eq_of_nhds]
          · simp [hχ0 x hx]
        rw [hzero] at hχ
        exact (smul_eq_zero.mp hχ.symm).resolve_left two_ne_zero
  have hIcc : EqOn Φ (fun _ ↦ c) (Icc 0 R) :=
    hc.of_subset_closure hΦc continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hR.ne])
  calc Φ R = c := hIcc ⟨hR.le, le_rfl⟩
    _ = Φ 0 := (hIcc ⟨le_rfl, hR.le⟩).symm
    _ = μ.toSphere.real univ • u 0 := by simp [hΦ_def, integral_const]

/-- **The mean-value property on spheres.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, `0 ≤ R`, then the integral of `u` over the sphere of radius `R` about `x₀`,
parametrized by the unit sphere with the surface measure `μ.toSphere`, is the total surface
measure times `u x₀`. (In the trivial space the unit sphere is empty and both sides vanish.) -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u x₀ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [integral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  have h := integral_toSphere_eq_of_harmonicOnNhd_zero (μ := μ)
    ((harmonicOnNhd_comp_add_right_closedBall_zero_iff x₀ R).mpr hu) hR
  simpa [add_comm] using h

/-- **The mean-value property on spheres, average form.** A function harmonic on a neighbourhood
of the closed ball `closedBall x₀ R`, `0 ≤ R`, in a nontrivial space has value `u x₀` at the
centre equal to its average over the sphere of radius `R` about `x₀`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.average_toSphere_eq [Nontrivial E] {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 ≤ R) :
    ⨍ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = u x₀ := by
  have : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  rw [average_eq, hu.integral_toSphere_eq hR, smul_smul, inv_mul_cancel₀ measureReal_univ_ne_zero,
    one_smul]

/-- The mean-value property on balls about the origin. -/
private lemma setIntegral_ball_eq_of_harmonicOnNhd_zero [Nontrivial E]
    (hu : HarmonicOnNhd u (closedBall (0 : E) R)) :
    ∫ x in ball (0 : E) R, u x ∂μ = μ.real (ball (0 : E) R) • u 0 := by
  rw [setIntegral_ball_zero_eq_integral_Ioo ((hu.contDiffOn.continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall),
    setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ by
      rw [integral_toSphere_eq_of_harmonicOnNhd_zero
        (hu.mono (closedBall_subset_closedBall hs.2.le)) hs.1.le],
    integral_smul_const, smul_smul, integral_Ioo_pow_mul_toSphere_real_univ]

/-- **The mean-value property on balls.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, then the integral of `u` over the open ball of radius `R` about `x₀` is
the measure of the ball times `u x₀`. (For `R ≤ 0` the ball is empty and both sides vanish.) -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) :
    ∫ x in ball x₀ R, u x ∂μ = μ.real (ball x₀ R) • u x₀ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space `u` is constant, with value `u x₀`.
    rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ u x₀)
      fun x _ ↦ congrArg u (Subsingleton.elim x x₀), setIntegral_const]
  have h := setIntegral_ball_eq_of_harmonicOnNhd_zero (μ := μ)
    ((harmonicOnNhd_comp_add_right_closedBall_zero_iff x₀ R).mpr hu)
  rw [zero_add] at h
  rw [Measure.addHaar_real_ball_center, ← h, setIntegral_ball_eq_setIntegral_ball_zero_add]

/-- **The mean-value property on balls, average form.** A function harmonic on a neighbourhood
of the closed ball `closedBall x₀ R`, `0 < R`, has value `u x₀` at the centre equal to its average
over the open ball of radius `R` about `x₀`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq {x₀ : E}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 < R) :
    ⨍ x in ball x₀ R, u x ∂μ = u x₀ := by
  have hpos : 0 < μ.real (ball x₀ R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ x₀ hR).ne' measure_ball_lt_top.ne
  rw [setAverage_eq, hu.setIntegral_ball_eq, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

end MeanValue

/-! ### An `L¹` bound on harmonic values -/

/-- A harmonic value is bounded by the `L¹` norm on any containing open set, using a ball
of fixed radius around the evaluation point. Completeness of `F` is not needed. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.norm_le_inv_measureReal_mul_integral_norm
    {s : Set E} (hu : HarmonicOnNhd u s) (hi : IntegrableOn u s μ) {x : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : closedBall x ρ ⊆ s) :
    ‖u x‖ ≤ (μ.real (ball (0 : E) ρ))⁻¹ * ∫ z in s, ‖u z‖ ∂μ := by
  have hV : 0 < μ.real (ball (0 : E) ρ) := measureReal_ball_pos μ 0 hρ
  -- Pass to the completion `F̂`, where Bochner integrals are not junk.
  set L : F →L[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have hL (y : F) : ‖L y‖ = ‖y‖ := UniformSpace.Completion.norm_coe y
  have hu' : HarmonicOnNhd (L ∘ u) s := hu.comp_CLM L
  have hmean := (hu'.mono hx).setIntegral_ball_eq (μ := μ)
  simp only [Function.comp_apply] at hmean
  have hbound : μ.real (ball (0 : E) ρ) * ‖u x‖ ≤ ∫ z in s, ‖u z‖ ∂μ := by
    calc
      _ = ‖∫ z in ball x ρ, L (u z) ∂μ‖ := by
        rw [hmean, norm_smul, Real.norm_of_nonneg measureReal_nonneg,
          Measure.addHaar_real_ball_center μ x ρ, hL]
      _ ≤ ∫ z in ball x ρ, ‖L (u z)‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ z in ball x ρ, ‖u z‖ ∂μ := by simp only [hL]
      _ ≤ ∫ z in s, ‖u z‖ ∂μ := setIntegral_mono_set hi.norm
        (ae_of_all _ fun _ ↦ norm_nonneg _) (ball_subset_closedBall.trans hx).eventuallySubset
  rw [inv_mul_eq_div, le_div_iff₀ hV, mul_comm]
  exact hbound

/-! ### The sub-mean-value inequality -/

section SubMeanValue

variable {f : E → ℝ}

/-- The sphere integrals of a subharmonic function about the origin increase with the radius. -/
private lemma integral_toSphere_le_of_laplacian_nonneg_zero [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hfc : ContinuousOn f (closedBall (0 : E) R))
    (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x) {s : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R) :
    ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere ≤
      ∫ θ : sphere (0 : E) 1, f (R • (θ : E)) ∂μ.toSphere := by
  rcases hsR.eq_or_lt with rfl | hsR
  · exact le_rfl
  have hR : 0 < R := hs.trans_lt hsR
  set Φ : ℝ → ℝ := fun s ↦ ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere
  have hΦc : ContinuousOn Φ (Icc 0 R) := hfc.integral_toSphere_smul
  -- The distributional derivative of `Φ` is nonnegative, since `Δ f ≥ 0` on the ball.
  have hmono : MonotoneOn Φ (Ioo 0 R) :=
    (hΦc.mono Ioo_subset_Icc_self).monotoneOn_of_integral_deriv_mul_nonpos fun ψ hψ hψs hψn ↦ by
      obtain ⟨χ, hχ0, hχn, hχ, -⟩ :=
        exists_integral_smul_laplacian_eq_two_smul_integral_deriv_smul (μ := μ) hf hR hψ hψs
      have hle : ∫ x, χ x • Δ f x ∂μ ≤ 0 := integral_nonpos fun x ↦ by
        by_cases hx : x ∈ ball (0 : E) R
        · exact mul_nonpos_of_nonpos_of_nonneg (hχn hψn x) (hΔ x hx)
        · simp [hχ0 x hx]
      rw [hχ, smul_eq_mul] at hle
      simpa only [smul_eq_mul] using nonpos_of_mul_nonpos_right hle two_pos
  -- By continuity, `Φ s ≤ Φ m ≤ Φ R` for the midpoint `m` of `s` and `R`.
  set m := (s + R) / 2
  have hm : m ∈ Ioo 0 R := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have h₁ : Φ s ≤ Φ m := by
    have ht : Tendsto Φ (𝓝[>] s) (𝓝 (Φ s)) :=
      ((continuousWithinAt_Ioo_iff_Ioi hsR).mp ((hΦc s ⟨hs, hsR.le⟩).mono
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc hs le_rfl)))).tendsto
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show s < m by simp only [m]; linarith)] with t ht
    exact hmono ⟨hs.trans_lt ht.1, ht.2.trans hm.2⟩ hm ht.2.le
  have h₂ : Φ m ≤ Φ R := by
    have ht : Tendsto Φ (𝓝[<] R) (𝓝 (Φ R)) :=
      ((continuousWithinAt_Ioo_iff_Iio hR).mp
        ((hΦc R ⟨hR.le, le_rfl⟩).mono Ioo_subset_Icc_self)).tendsto
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hm.2] with t ht
    exact hmono hm ⟨hm.1.trans ht.1, ht.2⟩ ht.1.le
  exact h₁.trans h₂

/-- The sub-mean-value inequality on spheres about the origin. -/
private lemma mul_le_integral_toSphere_of_laplacian_nonneg_zero [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hfc : ContinuousOn f (closedBall (0 : E) R))
    (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x) (hR : 0 ≤ R) :
    μ.toSphere.real univ * f 0 ≤ ∫ θ : sphere (0 : E) 1, f (R • (θ : E)) ∂μ.toSphere := by
  have h := integral_toSphere_le_of_laplacian_nonneg_zero (μ := μ) hf hfc hΔ le_rfl hR
  simpa [integral_const] using h

/-- **The sub-mean-value inequality on spheres.** If `f` is `C²` on the ball `ball x₀ R`,
continuous on its closure, and has nonnegative Laplacian on the ball, then `f x₀` times the total
surface measure is at most the integral of `f` over the sphere of radius `R` about `x₀`,
parametrized by the unit sphere with the surface measure `μ.toSphere`. -/
theorem mul_le_integral_toSphere_of_laplacian_nonneg {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) (hR : 0 ≤ R) :
    μ.toSphere.real univ * f x₀ ≤ ∫ θ : sphere (0 : E) 1, f (x₀ + R • (θ : E)) ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [integral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  have h := mul_le_integral_toSphere_of_laplacian_nonneg_zero (μ := μ)
    (sub_self x₀ ▸ hf.comp_add_right_ball x₀ :
      ContDiffOn ℝ 2 (fun y ↦ f (y + x₀)) (ball 0 R))
    (hfc.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ by
      simpa [mem_closedBall, dist_eq_norm] using hy)
    (fun y hy ↦ by
      rw [laplacian_comp_add_right]
      exact hΔ _ (by simpa [mem_ball, dist_eq_norm] using hy)) hR
  simpa [add_comm] using h

/-- **The sub-mean-value inequality on spheres, average form.** A function which is `C²` on the
ball `ball x₀ R`, continuous on its closure, and has nonnegative Laplacian on the ball, is at most
its average over the sphere of radius `R` about `x₀` at the centre. -/
theorem le_average_toSphere_of_laplacian_nonneg [Nontrivial E] {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) (hR : 0 ≤ R) :
    f x₀ ≤ ⨍ θ : sphere (0 : E) 1, f (x₀ + R • (θ : E)) ∂μ.toSphere := by
  have : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  rw [average_eq, smul_eq_mul, le_inv_mul_iff₀ measureReal_univ_pos]
  exact mul_le_integral_toSphere_of_laplacian_nonneg hf hfc hΔ hR

/-- The sub-mean-value inequality on balls about the origin. -/
private lemma mul_le_setIntegral_ball_of_laplacian_nonneg_zero [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hfc : ContinuousOn f (closedBall (0 : E) R))
    (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x) :
    μ.real (ball (0 : E) R) * f 0 ≤ ∫ x in ball (0 : E) R, f x ∂μ := by
  have hcont : ContinuousOn (fun s : ℝ ↦ s ^ (Module.finrank ℝ E - 1) *
      ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere) (Icc 0 R) :=
    (continuousOn_pow _).mul hfc.integral_toSphere_smul
  rw [setIntegral_ball_zero_eq_integral_Ioo ((hfc.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall),
    ← integral_Ioo_pow_mul_toSphere_real_univ,
    mul_assoc, ← integral_mul_const]
  have hpow : IntegrableOn (fun s : ℝ ↦ s ^ (Module.finrank ℝ E - 1)) (Ioo 0 R) :=
    (continuous_pow _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine setIntegral_mono_on (hpow.mul_const _)
    ((hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self) measurableSet_Ioo
    fun s hs ↦ mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs.1.le _)
  exact mul_le_integral_toSphere_of_laplacian_nonneg_zero
    (hf.mono (ball_subset_ball hs.2.le)) (hfc.mono (closedBall_subset_closedBall hs.2.le))
    (fun x hx ↦ hΔ x (ball_subset_ball hs.2.le hx)) hs.1.le

/-- **The sub-mean-value inequality on balls.** If `f` is `C²` on the ball `ball x₀ R`,
continuous on its closure, and has nonnegative Laplacian on the ball, then the measure of the ball
times `f x₀` is at most the integral of `f` over the ball. -/
theorem mul_le_setIntegral_ball_of_laplacian_nonneg {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) :
    μ.real (ball x₀ R) * f x₀ ≤ ∫ x in ball x₀ R, f x ∂μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space `f` is constant, with value `f x₀`.
    rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ f x₀)
      fun x _ ↦ congrArg f (Subsingleton.elim x x₀), setIntegral_const, smul_eq_mul]
  have h := mul_le_setIntegral_ball_of_laplacian_nonneg_zero (μ := μ)
    (sub_self x₀ ▸ hf.comp_add_right_ball x₀ :
      ContDiffOn ℝ 2 (fun y ↦ f (y + x₀)) (ball 0 R))
    (hfc.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ by
      simpa [mem_closedBall, dist_eq_norm] using hy)
    (fun y hy ↦ by
      rw [laplacian_comp_add_right]
      exact hΔ _ (by simpa [mem_ball, dist_eq_norm] using hy))
  rw [zero_add] at h
  rw [Measure.addHaar_real_ball_center, setIntegral_ball_eq_setIntegral_ball_zero_add]
  exact h

/-- **The sub-mean-value inequality on balls, average form.** A function which is `C²` on the
ball `ball x₀ R`, `0 < R`, continuous on its closure, and has nonnegative Laplacian on the ball,
is at most its average over the ball at the centre. -/
theorem le_setAverage_ball_of_laplacian_nonneg {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) (hR : 0 < R) :
    f x₀ ≤ ⨍ x in ball x₀ R, f x ∂μ := by
  have hpos : 0 < μ.real (ball x₀ R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ x₀ hR).ne' measure_ball_lt_top.ne
  rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hpos]
  exact mul_le_setIntegral_ball_of_laplacian_nonneg hf hfc hΔ

/-! ### Growth of the sphere integrals -/

/-- **The sphere integrals of a subharmonic function increase with the radius.** If `f` is `C²`
on the ball `ball x₀ R`, continuous on its closure, and has nonnegative Laplacian on the ball,
then its integral over the sphere of radius `s` about `x₀` is at most its integral over the
sphere of radius `R`, for `0 ≤ s ≤ R`. -/
theorem integral_toSphere_le_integral_toSphere_of_laplacian_nonneg {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) {s : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R) :
    ∫ θ : sphere (0 : E) 1, f (x₀ + s • (θ : E)) ∂μ.toSphere ≤
      ∫ θ : sphere (0 : E) 1, f (x₀ + R • (θ : E)) ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [integral_of_isEmpty]
  have h := integral_toSphere_le_of_laplacian_nonneg_zero (μ := μ)
    (sub_self x₀ ▸ hf.comp_add_right_ball x₀ :
      ContDiffOn ℝ 2 (fun y ↦ f (y + x₀)) (ball 0 R))
    (hfc.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ by
      simpa [mem_closedBall, dist_eq_norm] using hy)
    (fun y hy ↦ by
      rw [laplacian_comp_add_right]
      exact hΔ _ (by simpa [mem_ball, dist_eq_norm] using hy)) hs hsR
  simpa [add_comm] using h

/-- The integral of a subharmonic function over a ball about the origin is at most the measure of
the ball times its average over the boundary sphere. -/
private lemma mul_setIntegral_ball_le_of_laplacian_nonneg_zero [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hfc : ContinuousOn f (closedBall (0 : E) R))
    (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x) :
    μ.toSphere.real univ * ∫ x in ball (0 : E) R, f x ∂μ ≤
      μ.real (ball (0 : E) R) * ∫ θ : sphere (0 : E) 1, f (R • (θ : E)) ∂μ.toSphere := by
  have hcont : ContinuousOn (fun s : ℝ ↦ s ^ (Module.finrank ℝ E - 1) *
      ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere) (Icc 0 R) :=
    (continuousOn_pow _).mul hfc.integral_toSphere_smul
  have hpow : IntegrableOn (fun s : ℝ ↦ s ^ (Module.finrank ℝ E - 1)) (Ioo 0 R) :=
    (continuous_pow _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- In polar coordinates, every sphere integral below the radius `R` is at most the last one.
  have hle : ∫ s in Ioo 0 R, s ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere ≤
      ∫ s in Ioo 0 R, s ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, f (R • (θ : E)) ∂μ.toSphere :=
    setIntegral_mono_on ((hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self)
      (hpow.mul_const _) measurableSet_Ioo fun s hs ↦ mul_le_mul_of_nonneg_left
        (integral_toSphere_le_of_laplacian_nonneg_zero hf hfc hΔ hs.1.le hs.2.le)
        (pow_nonneg hs.1.le _)
  rw [integral_mul_const] at hle
  rw [setIntegral_ball_zero_eq_integral_Ioo ((hfc.integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall),
    ← integral_Ioo_pow_mul_toSphere_real_univ]
  simp only [smul_eq_mul]
  calc μ.toSphere.real univ * ∫ s in Ioo 0 R, s ^ (Module.finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere
      ≤ μ.toSphere.real univ * ((∫ s in Ioo 0 R, s ^ (Module.finrank ℝ E - 1)) *
        ∫ θ : sphere (0 : E) 1, f (R • (θ : E)) ∂μ.toSphere) :=
        mul_le_mul_of_nonneg_left hle measureReal_nonneg
    _ = _ := by ring

/-- **The integral over a ball is bounded by the sphere integral.** If `f` is `C²` on the ball
`ball x₀ R`, continuous on its closure, and has nonnegative Laplacian on the ball, then the total
surface measure times the integral of `f` over the ball is at most the measure of the ball times
the integral of `f` over the boundary sphere: the average of `f` over the ball is at most its
average over the sphere. -/
theorem mul_setIntegral_ball_le_mul_integral_toSphere_of_laplacian_nonneg {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) :
    μ.toSphere.real univ * ∫ x in ball x₀ R, f x ∂μ ≤
      μ.real (ball x₀ R) * ∫ θ : sphere (0 : E) 1, f (x₀ + R • (θ : E)) ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [integral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  have h := mul_setIntegral_ball_le_of_laplacian_nonneg_zero (μ := μ)
    (sub_self x₀ ▸ hf.comp_add_right_ball x₀ :
      ContDiffOn ℝ 2 (fun y ↦ f (y + x₀)) (ball 0 R))
    (hfc.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ by
      simpa [mem_closedBall, dist_eq_norm] using hy)
    (fun y hy ↦ by
      rw [laplacian_comp_add_right]
      exact hΔ _ (by simpa [mem_ball, dist_eq_norm] using hy))
  rw [Measure.addHaar_real_ball_center, setIntegral_ball_eq_setIntegral_ball_zero_add]
  simpa [add_comm] using h

/-- For a nonnegative test function `ψ` on `(a, R)`, `a > 0`, the sphere integrals
`Φ s = ∫ θ, f (s • θ) ∂μ.toSphere` of a subharmonic function about the origin satisfy
`-∫ ψ' Φ ≤ (∫ ψ) / a ^ (n - 1) * ∫_{ball 0 R} Δ f`: the distributional derivative of `Φ` is at
most `(∫_{ball 0 R} Δ f) / a ^ (n - 1)` on `(a, R)`. -/
private lemma neg_integral_deriv_mul_integral_toSphere_le [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x)
    (hΔi : IntegrableOn (Δ f) (ball (0 : E) R) μ) (hR : 0 < R) {a : ℝ} (ha : 0 < a)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo a R) (hψn : ∀ s, 0 ≤ ψ s) :
    -∫ s, deriv ψ s * ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere ≤
      (∫ s, ψ s) / a ^ (Module.finrank ℝ E - 1) * ∫ x in ball (0 : E) R, Δ f x ∂μ := by
  set D := ∫ x in ball (0 : E) R, Δ f x ∂μ
  have hD : 0 ≤ D := setIntegral_nonneg measurableSet_ball hΔ
  obtain ⟨χ, hχ0, -, hχ, hχc, hχb⟩ :=
    exists_integral_smul_laplacian_eq_two_smul_integral_deriv_smul (μ := μ) hf hR hψ
      (hψs.trans (Ioo_subset_Ioo_left ha.le))
  set M := ∫ τ in (0 : ℝ)..R ^ 2, |ψ (√τ) / (√τ) ^ Module.finrank ℝ E|
  -- `M ≤ 2 (∫ ψ) / a ^ (n - 1)`, by the substitution `τ = s ^ 2`.
  have hM : M ≤ 2 * (∫ s, ψ s) / a ^ (Module.finrank ℝ E - 1) := by
    have h := integral_abs_div_sqrt_pow_le ha (Module.finrank_pos (R := ℝ) (M := E)).ne'
      hψ.continuous hψs
    simpa only [abs_of_nonneg (hψn _)] using h
  -- `-∫ χ Δ f ≤ M D`, since `|χ| ≤ M` and `χ` vanishes off the ball.
  have hχΔ : IntegrableOn (fun x ↦ χ x * Δ f x) (ball (0 : E) R) μ :=
    hΔi.bdd_mul (c := M) hχc.aestronglyMeasurable (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]
      exact hχb x)
  have hle : -∫ x, χ x • Δ f x ∂μ ≤ M * D := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hχ0 x hx],
      ← integral_neg, ← integral_const_mul]
    refine setIntegral_mono_on hχΔ.neg (hΔi.const_mul M) measurableSet_ball fun x hx ↦ ?_
    simp only [smul_eq_mul, ← neg_mul]
    exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (hχb x)) (hΔ x hx)
  rw [hχ, smul_eq_mul] at hle
  simp only [smul_eq_mul] at hle
  calc -∫ s, deriv ψ s * ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere ≤ M * D / 2 := by
        linarith
    _ ≤ 2 * (∫ s, ψ s) / a ^ (Module.finrank ℝ E - 1) * D / 2 := by gcongr
    _ = (∫ s, ψ s) / a ^ (Module.finrank ℝ E - 1) * D := by ring

/-- The increment bound for the sphere integrals about the origin. -/
private lemma integral_toSphere_sub_le_zero [Nontrivial E]
    (hf : ContDiffOn ℝ 2 f (ball (0 : E) R)) (hfc : ContinuousOn f (closedBall (0 : E) R))
    (hΔ : ∀ x ∈ ball (0 : E) R, 0 ≤ Δ f x) (hΔi : IntegrableOn (Δ f) (ball (0 : E) R) μ)
    {a r₁ r₂ : ℝ} (ha : 0 < a) (har₁ : a < r₁) (hr : r₁ ≤ r₂) (hr₂R : r₂ < R) :
    ∫ θ : sphere (0 : E) 1, f (r₂ • (θ : E)) ∂μ.toSphere -
        ∫ θ : sphere (0 : E) 1, f (r₁ • (θ : E)) ∂μ.toSphere ≤
      (r₂ - r₁) / a ^ (Module.finrank ℝ E - 1) * ∫ x in ball (0 : E) R, Δ f x ∂μ := by
  set Φ : ℝ → ℝ := fun s ↦ ∫ θ : sphere (0 : E) 1, f (s • (θ : E)) ∂μ.toSphere
  set c := (∫ x in ball (0 : E) R, Δ f x ∂μ) / a ^ (Module.finrank ℝ E - 1)
  have hR : 0 < R := by linarith
  have hΦc : ContinuousOn Φ (Icc 0 R) := hfc.integral_toSphere_smul
  -- `s ↦ c s - Φ s` is monotone on `(a, R)`: its distributional derivative is nonnegative.
  have hmono : MonotoneOn (fun s ↦ c * s - Φ s) (Ioo a R) := by
    refine ContinuousOn.monotoneOn_of_integral_deriv_mul_nonpos
      ((continuousOn_const.mul continuousOn_id).sub
        (hΦc.mono fun s hs ↦ ⟨by linarith [hs.1], hs.2.le⟩)) fun ψ hψ hψs hψn ↦ ?_
    have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ)
      (hψs.trans Ioo_subset_Icc_self)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hdψ : Continuous (deriv ψ) := hψ1.continuous_deriv le_rfl
    have hI₁ : Integrable fun x ↦ x * deriv ψ x :=
      (continuous_id.mul hdψ).integrable_of_hasCompactSupport
        (hψc.deriv.mul_left (f := fun x : ℝ ↦ x))
    -- Integration by parts: `∫ x ψ' x = -∫ ψ`.
    have hparts : ∫ x, x * deriv ψ x = -∫ x, ψ x := by
      have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ ↦ x)
        (u' := fun _ ↦ 1) (v := ψ) (v' := deriv ψ) (fun x _ ↦ hasDerivAt_id x)
        (fun x _ ↦ (hψ1.differentiable one_ne_zero x).hasDerivAt) hI₁
        ((continuous_const.mul hψ.continuous).integrable_of_hasCompactSupport
          (hψc.mul_left (f := fun _ : ℝ ↦ (1 : ℝ))))
        ((continuous_id.mul hψ.continuous).integrable_of_hasCompactSupport
          (hψc.mul_left (f := fun x : ℝ ↦ x)))
      simpa using h
    have hIΦ : Integrable fun x ↦ deriv ψ x * Φ x := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport ψ)
        ((hdψ.continuousOn.mul (hΦc.mono ?_)).integrableOn_compact hψc) fun x hx ↦ ?_
      · exact hψs.trans fun s hs ↦ ⟨by linarith [hs.1], hs.2.le⟩
      · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_deriv_subset h)]
    have hneg : -∫ x, deriv ψ x * Φ x ≤
        (∫ x, ψ x) / a ^ (Module.finrank ℝ E - 1) * ∫ x in ball (0 : E) R, Δ f x ∂μ :=
      neg_integral_deriv_mul_integral_toSphere_le (μ := μ) hf hΔ hΔi hR ha hψ hψs hψn
    have hc : c * ∫ x, ψ x =
        (∫ x, ψ x) / a ^ (Module.finrank ℝ E - 1) * ∫ x in ball (0 : E) R, Δ f x ∂μ := by
      simp only [c]
      ring
    calc ∫ x, deriv ψ x * (c * x - Φ x) = c * (∫ x, x * deriv ψ x) - ∫ x, deriv ψ x * Φ x := by
          rw [← integral_const_mul, ← integral_sub (hI₁.const_mul c) hIΦ]
          congr 1
          ext x
          ring
      _ ≤ 0 := by
          rw [hparts]
          linarith
  have h := hmono ⟨har₁, by linarith⟩ ⟨by linarith, hr₂R⟩ hr
  simp only at h
  calc Φ r₂ - Φ r₁ ≤ c * (r₂ - r₁) := by linarith
    _ = _ := by
        simp only [c]
        ring

/-- **Growth of the sphere integrals of a subharmonic function.** Let `f` be `C²` on the ball
`ball x₀ R`, continuous on its closure, with nonnegative and integrable Laplacian on the ball.
For radii `0 < a < r₁ ≤ r₂ < R`, the integrals of `f` over the spheres of radii `r₁` and `r₂`
about `x₀` differ by at most `(r₂ - r₁) / a ^ (n - 1)` times the integral of `Δ f` over the
ball, `n` being the dimension. -/
theorem integral_toSphere_sub_integral_toSphere_le {x₀ : E}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R)) (hfc : ContinuousOn f (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, 0 ≤ Δ f x) (hΔi : IntegrableOn (Δ f) (ball x₀ R) μ)
    {a r₁ r₂ : ℝ} (ha : 0 < a) (har₁ : a < r₁) (hr : r₁ ≤ r₂) (hr₂R : r₂ < R) :
    ∫ θ : sphere (0 : E) 1, f (x₀ + r₂ • (θ : E)) ∂μ.toSphere -
        ∫ θ : sphere (0 : E) 1, f (x₀ + r₁ • (θ : E)) ∂μ.toSphere ≤
      (r₂ - r₁) / a ^ (Module.finrank ℝ E - 1) * ∫ x in ball x₀ R, Δ f x ∂μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp only [integral_of_isEmpty, sub_self]
    exact mul_nonneg (div_nonneg (by linarith) (pow_nonneg ha.le _))
      (setIntegral_nonneg measurableSet_ball hΔ)
  have hΔi' : IntegrableOn (fun y ↦ Δ f (y + x₀)) (ball (0 : E) R) μ := by
    have h := ((measurePreserving_add_right μ x₀).integrableOn_comp_preimage
      (measurableEmbedding_addRight x₀)).2 hΔi
    rwa [preimage_add_right_ball, sub_self] at h
  have h := integral_toSphere_sub_le_zero (μ := μ)
    (sub_self x₀ ▸ hf.comp_add_right_ball x₀ :
      ContDiffOn ℝ 2 (fun y ↦ f (y + x₀)) (ball 0 R))
    (hfc.comp (continuousOn_id.add continuousOn_const) fun y hy ↦ by
      simpa [mem_closedBall, dist_eq_norm] using hy)
    (fun y hy ↦ by
      rw [laplacian_comp_add_right]
      exact hΔ _ (by simpa [mem_ball, dist_eq_norm] using hy))
    (by rwa [laplacian_comp_add_right]) ha har₁ hr hr₂R
  rw [laplacian_comp_add_right] at h
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simpa [add_comm] using h

end SubMeanValue

end TauCeti
