/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Isoperimetric
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Analysis.Calculus.PowerGrowth
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.MeasureTheory.Integral.Disc
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Power decay of energy at a boundary puncture

Let `x₀` be a point of the real axis and let `u` solve `∂ₜu = J(u) ∂ₛu` on the punctured closed
half-disc `{0 ≤ im z} ∩ B_R(x₀) \ {x₀}`, with derivatives taken within the closed upper
half-plane, mapping the real axis into a subspace `L` on which a constant symplectic form `ω`
vanishes. Suppose that `ω` uniformly tames `J` along `u`, with constant `c`, that `‖J(u)‖ ≤ M`,
and that `u` has finite energy: `‖∂ₛu‖²` is integrable on the half-disc. The norm is that of a
fixed inner product compatible with `ω`. The bounds below hold for every `c` and carry information
when `c > 0`. Write

`E(r) = ∫_{{0 ≤ im z} ∩ B_r(x₀)} ‖∂ₛu‖²`

for the energy of the half-disc of radius `r`. No extension of `u` over the puncture is assumed.

* **Boundary control.** The energy of a punctured half-disc is controlled by the density of its
  outer half-circle alone: `2 c E(r) ≤ (1 + M)² r (r ∫₀^π ‖∂ₛu(x₀ + r e^{iθ})‖² dθ)`
  (`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderivWithin_one_sq_inter_ball_le`). The
  same bound with an inner half-circle of radius `a` in addition holds on every half-annulus
  (`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderivWithin_one_sq_upperHalfAnnulus_le`),
  by Stokes' theorem with the primitive `½ ω(x, ·)` of `ω`, which vanishes along `L`, and the
  isoperimetric inequality for arcs with endpoints in `L`. The inner term disappears in the limit:
  the energies of small half-discs tend to zero, and since `E` is finite, its radial derivative
  `E'(a) = a ∫₀^π ‖∂ₛu(x₀ + a e^{iθ})‖² dθ` has `a E'(a)` arbitrarily small at arbitrarily small
  radii (`TauCeti.exists_mem_Ioo_mul_lt_of_hasDerivAt`).
* **The Euler inequality.** Hence `2 c E(r) ≤ (1 + M)² r E'(r)`
  (`TauCeti.SymplecticForm.mul_integral_norm_fderivWithin_one_sq_inter_ball_le_mul_deriv`).
* **Power decay.** So `E(r) / r^(2μ)` is nondecreasing, with `μ = c / (1 + M)²`, and
  `E(r) ≤ E(b) (r / b)^(2μ)` for `0 < r ≤ b < R`
  (`TauCeti.SymplecticForm.integral_norm_fderivWithin_one_sq_inter_ball_le_rpow`).

These are the boundary counterparts of
`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_punctured_disc_le`,
`TauCeti.SymplecticForm.mul_integral_norm_fderiv_one_sq_ball_le_mul_deriv` and
`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_ball_le_rpow` at an interior puncture. They
are the energy-decay step in the removal of boundary punctures of finite-energy holomorphic curves
with Lagrangian boundary conditions, in the flat model of a constant taming form and a linear
boundary subspace. Pointwise decay of the derivative, continuous and smooth extension over the
puncture, and the reduction of curved boundary conditions to this model are further steps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities, including boundary punctures with totally real boundary
  conditions).
-/

public section

open Complex MeasureTheory Metric Set Filter
open scoped Real RealInnerProductSpace Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {L : Submodule ℝ V} {x₀ : ℂ} {R c M : ℝ}

omit [FiniteDimensional ℝ V] in
/-- The energy `∫_{{0 ≤ im z} ∩ B_t(x₀)} ‖∂ₛu‖²` of the half-disc of radius `t` about a point `x₀`
of the real axis has radial derivative `t ∫₀^π ‖∂ₛu(x₀ + t e^{iθ})‖² dθ`. -/
private theorem hasDerivAt_integral_norm_fderivWithin_one_sq_inter_ball (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 1 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    HasDerivAt (fun t ↦ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ t,
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      (r * ∫ θ in 0..π, ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ r θ) 1‖ ^ 2) r := by
  have hcont : ContinuousOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})) :=
    ((hu.continuousOn_fderivWithin_of_inter (uniqueDiffOn_setOfPred_le_im 0)
      (isOpen_ball.sdiff isClosed_singleton) le_rfl).clm_apply continuousOn_const).norm.pow 2
  have hH : {z : ℂ | 0 ≤ z.im} = {z | x₀.im ≤ z.im} := by rw [hx₀]
  rw [hH] at hcont henergy ⊢
  simpa only [smul_eq_mul] using henergy.hasDerivAt_integral_inter_ball hcont hr

omit [FiniteDimensional ℝ V] in
/-- At some radius `a ∈ (0, r)` the half-disc energy and its boundary density
`a (a ∫₀^π ‖∂ₛu(x₀ + a e^{iθ})‖² dθ)` are both below any `δ > 0`: the energies of small half-discs
tend to zero, and the energy has finite radial derivative. -/
private theorem exists_mem_Ioo_integral_lt_and_mul_lt (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 1 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {r δ : ℝ} (hr : r ∈ Ioo 0 R) (hδ : 0 < δ) :
    ∃ a ∈ Ioo 0 r,
      (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ a, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) < δ ∧
      a * (a * ∫ θ in 0..π, ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ a θ) 1‖ ^ 2) < δ := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hH : MeasurableSet H := (isClosed_le continuous_const continuous_im).measurableSet
  -- The energies of small half-discs tend to zero.
  obtain ⟨a₁, ha₁, hsmall⟩ := Metric.tendsto_nhds_nhds.1
    (henergy.tendsto_setIntegral_ball_nhds_zero x₀) δ hδ
  -- Below `a₁` some radius has small boundary density, since the energy is nonnegative.
  obtain ⟨a, ha, hah⟩ := exists_mem_Ioo_mul_lt_of_hasDerivAt (lt_min ha₁ hr.1) hδ
    (fun t ht ↦ hasDerivAt_integral_norm_fderivWithin_one_sq_inter_ball hx₀ hu henergy
      ⟨ht.1, ht.2.trans (min_lt_of_right_lt hr.2)⟩)
    fun t _ ↦ setIntegral_nonneg (hH.inter measurableSet_ball) fun _ _ ↦ sq_nonneg _
  refine ⟨a, ⟨ha.1, ha.2.trans_le (min_le_right _ _)⟩, ?_, hah⟩
  have h := hsmall (x := a) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos ha.1]; exact ha.2.trans_le (min_le_left _ _))
  rw [Real.dist_eq, sub_zero, Measure.restrict_restrict measurableSet_ball,
    inter_comm, inter_assoc, inter_eq_right.2 (ball_subset_ball
      (ha.2.trans (min_lt_of_right_lt hr.2)).le)] at h
  exact (le_abs_self _).trans_lt h

omit [FiniteDimensional ℝ V] in
/-- The energy of the half-disc of radius `r` is at most that of the half-disc of radius
`a ∈ (0, r)` plus that of the closed half-annulus between them. -/
private theorem integral_inter_ball_le_add_integral_upperHalfAnnulus
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {a r : ℝ} (har : a ≤ r) (hr : r < R) :
    (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
      (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ a, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) +
        ∫ z in {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ r},
          ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 := by
  set H : Set ℂ := {z | 0 ≤ z.im}
  have hH : MeasurableSet H := (isClosed_le continuous_const continuous_im).measurableSet
  have hdiff := setIntegral_sdiff (hH.inter measurableSet_ball)
    (henergy.mono_set (inter_subset_inter_right _ (ball_subset_ball hr.le)))
    (inter_subset_inter_right _ (ball_subset_ball har))
  -- The points of the larger half-disc outside the smaller one lie in the half-annulus.
  have hmono := setIntegral_mono_set (μ := volume)
    (s := (H ∩ ball x₀ r) \ (H ∩ ball x₀ a))
    (t := {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ r})
    (henergy.mono_set fun z hz ↦ ⟨hz.1, mem_ball_iff_norm.2 (hz.2.2.trans_lt hr)⟩)
    (ae_of_all _ fun _ ↦ sq_nonneg _)
    (Eventually.of_forall fun z hz ↦ ⟨hz.1.1,
      not_lt.1 fun h ↦ hz.2 ⟨hz.1.1, mem_ball_iff_norm.2 h⟩,
      (mem_ball_iff_norm.1 hz.1.2).le⟩)
  linarith

/-- **Boundary control of the energy of a punctured half-disc.** Let `u` solve
`∂ₜu = J(u) ∂ₛu` on the punctured closed half-disc `{0 ≤ im z} ∩ B_R(x₀) \ {x₀}` about a point
`x₀` of the real axis, with derivatives taken within the closed upper half-plane, and map the real
axis into a subspace `L` on which `ω` vanishes. If `u` is uniformly tamed by `ω` with constant `c`,
satisfies `‖J(u)‖ ≤ M` and has finite energy, then for `0 < r < R` twice the taming constant times
the energy of the half-disc of radius `r` is at most `(1 + M)²` times the boundary density
`r (r ∫₀^π ‖∂ₛu(x₀ + r e^{iθ})‖² dθ)` of its half-circle. The inner product is the fixed
compatible metric of `(ω, J₀)`, and the value of `u` at the puncture is unrestricted. -/
theorem two_mul_mul_integral_norm_fderivWithin_one_sq_inter_ball_le
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 2 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    2 * c * (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * (r * (r * ∫ θ in 0..π,
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ r θ) 1‖ ^ 2)) := by
  rcases le_or_gt c 0 with hc | hc
  · -- For `c ≤ 0` the left side is nonpositive and the right side nonnegative.
    have hE : 0 ≤ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r,
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
    have hb : 0 ≤ ∫ θ in 0..π, ‖fderivWithin ℝ u {z | 0 ≤ z.im} (circleMap x₀ r θ) 1‖ ^ 2 :=
      intervalIntegral.integral_nonneg Real.pi_pos.le fun _ _ ↦ sq_nonneg _
    have hrhs := mul_nonneg (sq_nonneg (1 + M)) (mul_nonneg hr.1.le (mul_nonneg hr.1.le hb))
    nlinarith
  have hden : 0 < 2 * c + (1 + M) ^ 2 := by positivity
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Choose a small radius `a` where both the energy and the boundary density are small.
  obtain ⟨a, ha, hEa, hah⟩ := exists_mem_Ioo_integral_lt_and_mul_lt hx₀ (hu.of_le one_le_two)
    henergy hr (div_pos hε hden)
  -- Bound the energy of the half-annulus between `a` and `r` by its two boundary densities.
  have hSsub : {z : ℂ | 0 ≤ z.im ∧ a ≤ ‖z - x₀‖ ∧ ‖z - x₀‖ ≤ r} ⊆
      {z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}) := fun z hz ↦
    ⟨hz.1, mem_ball_iff_norm.2 (hz.2.2.trans_lt hr.2), fun hzx ↦ by
      have h := hz.2.1
      rw [mem_singleton_iff.1 hzx, sub_self, norm_zero] at h
      linarith [ha.1]⟩
  have hannulus := ω.two_mul_mul_integral_norm_fderivWithin_one_sq_upperHalfAnnulus_le hg
    ha.1.le ha.2.le hx₀ (isOpen_ball.sdiff isClosed_singleton) (fun z hz ↦ (hSsub hz).2) hu
    (fun z hz ↦ hCR z (hSsub hz)) (fun z hz ↦ htame z (hSsub hz)) (fun z hz ↦ hJ z (hSsub hz))
    hLω huL
  have hsplit := integral_inter_ball_le_add_integral_upperHalfAnnulus henergy ha.2.le hr.2
  have hδε : (2 * c + (1 + M) ^ 2) * (ε / (2 * c + (1 + M) ^ 2)) = ε :=
    mul_div_cancel₀ _ hden.ne'
  nlinarith [mul_le_mul_of_nonneg_left hah.le (sq_nonneg (1 + M))]

/-- **The Euler inequality for the energy at a boundary puncture.** Under the hypotheses of
`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderivWithin_one_sq_inter_ball_le`, the energy
`E(r)` of the half-disc of radius `r` about the puncture satisfies `2 c E(r) ≤ (1 + M)² r E'(r)`
for `0 < r < R`. -/
theorem mul_integral_norm_fderivWithin_one_sq_inter_ball_le_mul_deriv
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 2 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    2 * c * (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * r * deriv (fun t ↦ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ t,
        ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) r := by
  rw [(hasDerivAt_integral_norm_fderivWithin_one_sq_inter_ball hx₀ (hu.of_le one_le_two)
    henergy hr).deriv]
  exact (ω.two_mul_mul_integral_norm_fderivWithin_one_sq_inter_ball_le hg hx₀ hu hCR htame hJ
    hLω huL henergy hr).trans_eq (mul_assoc _ _ _).symm

/-- **Power decay of the energy at a boundary puncture.** Under the hypotheses of
`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderivWithin_one_sq_inter_ball_le`, the energy
`E(r)` of the half-disc of radius `r` about the puncture satisfies
`E(r) ≤ E(b) (r / b)^(2c / (1 + M)²)` for `0 < r ≤ b < R`. -/
theorem integral_norm_fderivWithin_one_sq_inter_ball_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hx₀ : x₀.im = 0)
    (hu : ContDiffOn ℝ 2 u ({z | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀})))
    (hCR : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}),
      fderivWithin ℝ u {z | 0 ≤ z.im} z I = J (u z) (fderivWithin ℝ u {z | 0 ≤ z.im} z 1))
    (htame : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}), ‖J (u z)‖ ≤ M)
    (hLω : ∀ v ∈ L, ∀ w ∈ L, ω v w = 0)
    (huL : ∀ z ∈ ball x₀ R \ {x₀}, z.im = 0 → u z ∈ L)
    (henergy : IntegrableOn (fun z ↦ ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2)
      ({z | 0 ≤ z.im} ∩ ball x₀ R))
    {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) (hb : b < R) :
    (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ r, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) ≤
      (∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ b, ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2) *
        (r / b) ^ (2 * c / (1 + M) ^ 2) := by
  set E : ℝ → ℝ := fun t ↦ ∫ z in {z : ℂ | 0 ≤ z.im} ∩ ball x₀ t,
    ‖fderivWithin ℝ u {z | 0 ≤ z.im} z 1‖ ^ 2
  have hbpos := hr.trans_le hrb
  -- The point `x₀ + b` lies on the real edge of the punctured half-disc, so `M ≥ 0`.
  have hbmem : x₀ + b ∈ {z : ℂ | 0 ≤ z.im} ∩ (ball x₀ R \ {x₀}) :=
    ⟨by simp [hx₀], by simpa [dist_eq_norm, abs_of_pos hbpos] using hb,
      by simpa using hbpos.ne'⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hJ _ hbmem)
  have hden : 0 < (1 + M) ^ 2 := by positivity
  have hd (t : ℝ) (ht : t ∈ Ioo 0 R) :=
    hasDerivAt_integral_norm_fderivWithin_one_sq_inter_ball hx₀ (hu.of_le one_le_two) henergy ht
  have hmono := monotoneOn_div_rpow_of_mul_le_mul_deriv (f := E) (α := 2 * c / (1 + M) ^ 2)
    (convex_Ioo 0 R) (fun t ht ↦ ht.1) (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd t (interior_subset ht)) fun t ht ↦ by
      have h := ω.mul_integral_norm_fderivWithin_one_sq_inter_ball_le_mul_deriv hg hx₀ hu hCR
        htame hJ hLω huL henergy (interior_subset ht)
      rw [(hd t (interior_subset ht)).deriv] at h
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
  have h := hmono ⟨hr, hrb.trans_lt hb⟩ ⟨hbpos, hb⟩ hrb
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hbpos _)] at h
  simpa only [Real.div_rpow hr.le hbpos.le, ← mul_div_assoc] using
    (le_div_iff₀ (Real.rpow_pos_of_pos hbpos _)).mpr h

end TauCeti.SymplecticForm
