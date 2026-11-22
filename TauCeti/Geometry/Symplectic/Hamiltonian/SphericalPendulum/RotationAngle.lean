/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.TurningPoint
public import TauCeti.Analysis.SpecialFunctions.Integrals.ArctanSqrt
import TauCeti.Topology.Circle.Degree
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Algebra.Group.Order

/-!
# The rotation angle of the spherical pendulum

On the phase space of the spherical pendulum the vertical momentum satisfies
`p₃² = 2 (h - q₃) (1 - q₃²) - j²` on the fibre `F⁻¹(h, j)` of the energy–momentum map
`F = (H, J)` (`TauCeti.sq_snd_two_eq_of_mem_sphericalPendulumPhaseSpace`). Classically, along a
motion the height `z = q₃` moves with velocity `p₃` and the azimuth turns with angular velocity
`j / (1 - z²)`, so the azimuthal angle swept while the height runs once up and down between its
turning points `z₋ < z₊` is the **rotation angle**

`Θ(h, j) = 2 ∫_{z₋}^{z₊} j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`

(`TauCeti.sphericalPendulumRotationAngle`). It is odd in `j` and is the quadrature entering the
rotation number of the pendulum's Liouville tori and its Hamiltonian monodromy. Here it is defined
as the integral over the whole of `(-1, 1)`: the real square root vanishes on negative numbers,
so the integrand vanishes at every height that does not occur in the fibre, and `Θ(h, j)` is the
integral over the set of heights of `F⁻¹(h, j)`
(`TauCeti.sphericalPendulumRotationAngle_eq_setIntegral`).

As `j → 0` the motions approach planar oscillations through the south pole, for `-1 < h < 1`, or
planar rotations through both poles, for `h > 1`, and each passage near a pole turns the azimuth by
almost `π`. Accordingly the rotation angle has the one-sided limits, jointly in `(h, j)`,
* `Θ(h, j) → ±π` as `(h, j) → (h₀, 0)` with `±j > 0`, for `-1 < h₀ < 1`
  (`TauCeti.tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one`,
  `TauCeti.tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_lt_one`);
* `Θ(h, j) → ±2π` as `(h, j) → (h₀, 0)` with `±j > 0`, for `h₀ > 1`
  (`TauCeti.tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_one_lt`,
  `TauCeti.tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_one_lt`),

and in particular at a fixed energy `h`
(`TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one` and its three companions), while
`Θ(h, 0) = 0`.

Away from `j = 0`, the rotation angle is continuous. At a value `(h, j)` with `j ≠ 0` lying strictly
above the curve of relative equilibria, the radicand factors as
`2 (h - z) (1 - z²) - j² = 2 (z - z₋) (z₊ - z) (z₃ - z)` with turning points `-1 < z₋ < z₊ < 1` and
`z₃ = h - z₋ - z₊ > 1` (`TauCeti.two_mul_sub_mul_one_sub_sq_sub_sq_eq`). The substitution
`z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ` absorbs both inverse square root singularities:

`Θ(h, j) = 2 ∫_{-π/2}^{π/2} j dθ / ((1 - z²) √(2 (z₃ - z)))`

(`TauCeti.sphericalPendulumRotationAngle_eq_integral_sin`), an integral of a function continuous
in `θ` and in `(h, j)`, since the turning points depend continuously on `(h, j)`. Hence `Θ` is
continuous on these values (`TauCeti.continuousOn_sphericalPendulumRotationAngle`): it varies
continuously along paths of such values, while across `j = 0` it jumps by the differences of the
one-sided limits above.

These jumps are `2π` across `j = 0` at energies `-1 < h < 1` and `4π` at energies `h > 1`, so
modulo `2π` the one-sided limits agree on both rays, but the jumps of a lift do not cancel around
the focus–focus value `(1, 0)` of `F`. Precisely, along the counterclockwise circle
`γ(t) = (1 + r cos t, r sin t)`, `t ∈ [0, 2π]`, of radius `r > 0`, if it runs above the curve of
relative equilibria off the axis, every function `L` continuous on `[0, 2π]` that agrees with
`Θ ∘ γ` modulo `2π` off the axis satisfies `L(2π) = L(0) - 2π`
(`TauCeti.sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle`), and more generally a
continuous lift of `m Θ ∘ γ` for an integer `m` drops by `2πm`
(`TauCeti.sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle`).
The circles of radius `r ≤ 1` run above the curve of relative equilibria off the axis
(`TauCeti.mem_sphericalPendulumTurningPointDomain_of_le_one`,
`TauCeti.sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle_of_le_one`).
This drop of the rotation angle is the input to the classical computation of the Hamiltonian
monodromy of the pendulum around `(1, 0)`.

## Implementation notes

The proof of the limits splits `(-1, 1)` at heights close to the zeros of
`f_h(z) = 2 (h - z) (1 - z²)`, uniformly for `h` near `h₀`. Near the south pole `z = -1`, where
`f_h` has a simple zero with `f_h' > 0`, the integrand is `ψ_h f_h' j / (f_h √(f_h - j²))` with
`ψ_h = 4 (h - z) / f_h'`, and this contributes `ψ_{h₀}(-1) π = π` in the limit by the concentration
lemma `TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto`. For `h₀ > 1` the reflection
`z ↦ -z` reduces the north pole `z = 1` to the same lemma, and it contributes `π` too. For
`-1 < h₀ < 1` the upper zero of `f_h` is the turning point `z = h`, which moves with `h`; the
reflected weight is at most `4 (h - c) / (-f_h')` on `[c, h]`, so a cut `c` close to `h₀` makes this
contribution small (`TauCeti.abs_integral_mul_mul_div_mul_sqrt_sub_sq_le`). Away from the zeros of
`f_h` the integrand is `O(j)` uniformly.

## Main declarations

* `TauCeti.sphericalPendulumRotationAngle`: the rotation angle `Θ(h, j)`.
* `TauCeti.sphericalPendulumRotationAngle_eq_setIntegral`: `Θ(h, j)` as an integral over the
  heights of the fibre `F⁻¹(h, j)`.
* `TauCeti.sphericalPendulumRotationAngle_neg_right`: `Θ(h, -j) = -Θ(h, j)`.
* `TauCeti.sphericalPendulumRotationAngle_eq_integral`: `Θ(h, j)` as an integral between the
  turning points.
* `TauCeti.tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one` and its
  three companions: the one-sided limits of `Θ(h, j)` as `(h, j) → (h₀, 0)`.
* `TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one` and its three companions: the
  one-sided limits of `Θ(h, j)` as `j → 0` at a fixed energy.
* `TauCeti.sphericalPendulumRotationAngle_eq_integral_sin`: `Θ(h, j)` as an integral of a
  continuous function over `[-π/2, π/2]`.
* `TauCeti.continuousOn_sphericalPendulumRotationAngle`: `Θ` is continuous on the values with
  `j ≠ 0` above the curve of relative equilibria.
* `TauCeti.sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle`: a continuous lift of `Θ`
  modulo `2π` decreases by `2π` once around the focus–focus value.
* `TauCeti.sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle`:
  a continuous lift of `m Θ` modulo `2π` decreases by `2πm`.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
* K. Efstathiou, A. Giacobbe, P. Mardešić and D. Sugny, *Rotation forms and local Hamiltonian
  monodromy*, arXiv:1608.01579, Sections II–III.
-/

public section

open Filter Real Set MeasureTheory
open scoped Topology

namespace TauCeti

/-- The **rotation angle** `Θ(h, j) = 2 ∫ j dz / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` of the
spherical pendulum at energy `h` and vertical angular momentum `j`. The integral runs over
`(-1, 1)`, but the integrand vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ j²`, so for a
regular value it is the integral between the two turning points of the height. -/
noncomputable def sphericalPendulumRotationAngle (h j : ℝ) : ℝ :=
  2 * ∫ z in (-1)..1, j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))

theorem sphericalPendulumRotationAngle_def (h j : ℝ) :
    sphericalPendulumRotationAngle h j =
      2 * ∫ z in (-1)..1, j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) :=
  (rfl)

/-- The rotation angle is the integral over the set
`{z ∈ [-1, 1] | z ≤ h ∧ j² ≤ 2 (h - z) (1 - z²)}`, which is the set of heights `q₃` of the points
of the fibre `F⁻¹(h, j)` of the energy–momentum map
(`TauCeti.image_apply_two_preimage_sphericalPendulumEnergyMomentum`). -/
theorem sphericalPendulumRotationAngle_eq_setIntegral (h j : ℝ) :
    sphericalPendulumRotationAngle h j =
      2 * ∫ z in {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)},
        j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) := by
  rw [sphericalPendulumRotationAngle_def, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (s := {z | z ∈ Icc (-1) 1 ∧ z ≤ h ∧ j ^ 2 ≤ 2 * (h - z) * (1 - z ^ 2)}) fun _ hz ↦ hz.1]
  rintro z ⟨hz, hzS⟩
  simp only [mem_ofPred_eq, hz, true_and, not_and, not_le] at hzS
  have hP : 2 * (h - z) * (1 - z ^ 2) - j ^ 2 ≤ 0 := by
    have hz2 : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    by_cases hzh : z ≤ h
    · linarith [hzS hzh]
    · nlinarith [sq_nonneg j]
  rw [Real.sqrt_eq_zero'.2 hP, mul_zero, div_zero]

/-- The rotation angle is odd in the angular momentum. -/
@[simp]
theorem sphericalPendulumRotationAngle_neg_right (h j : ℝ) :
    sphericalPendulumRotationAngle h (-j) = -sphericalPendulumRotationAngle h j := by
  simp only [sphericalPendulumRotationAngle_def, neg_sq, neg_div, intervalIntegral.integral_neg,
    mul_neg]

@[simp]
theorem sphericalPendulumRotationAngle_zero_right (h : ℝ) :
    sphericalPendulumRotationAngle h 0 = 0 := by
  simp [sphericalPendulumRotationAngle_def]

/-- Above the curve of relative equilibria, the rotation angle is twice the integral of
`j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` between the turning points `z₋ < z₊`. -/
theorem sphericalPendulumRotationAngle_eq_integral {h j z₀ : ℝ} (hj : j ≠ 0)
    (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumRotationAngle h j =
      2 * ∫ z in (sphericalPendulumLowerTurningPoint h j)..(sphericalPendulumUpperTurningPoint h j),
        j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)) := by
  simp only [sphericalPendulumRotationAngle_def, ← div_div]
  rw [integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV fun z ↦ j / (1 - z ^ 2)]

/-! ### The limits of the rotation angle as `j → 0` -/

/-- The derivative of `2 (h - σ z) (1 - z²)` in `z`. -/
private theorem hasDerivAt_two_mul_sub_mul_mul_one_sub_sq (h σ z : ℝ) :
    HasDerivAt (fun z ↦ 2 * (h - σ * z) * (1 - z ^ 2))
      (6 * σ * z ^ 2 - 4 * h * z - 2 * σ) z := by
  have := (((hasDerivAt_id z).const_mul σ).const_sub h).const_mul 2 |>.mul
    ((hasDerivAt_pow 2 z).const_sub 1)
  convert this using 1
  · funext y
    simp only [Pi.mul_apply, id]
  · simp only [id]
    ring

/-- The pointwise identity behind the comparison with the kernel of
`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto`. -/
private theorem two_mul_div_mul_sqrt_eq {u v j d : ℝ} (hd : d ≠ 0) :
    2 * (j / (v * √(2 * u * v - j ^ 2))) =
      4 * u / d * (d * j / (2 * u * v * √(2 * u * v - j ^ 2))) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [Real.sqrt_eq_zero'.2 (neg_nonpos.2 (sq_nonneg j))]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne √(2 * u * v - j ^ 2) 0 with hs | _
  · simp [hs]
  field_simp
  ring

/-- The integrand vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ 0`. -/
private theorem two_mul_div_mul_sqrt_eq_zero {h j z : ℝ} (hz : 2 * (h - z) * (1 - z ^ 2) ≤ 0) :
    2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))) = 0 := by
  rw [Real.sqrt_eq_zero'.2 (by nlinarith [sq_nonneg j]), mul_zero, div_zero, mul_zero]

/-- For `h ≥ -1` the integrand `2 j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` vanishes on `[h, 1]`,
where `2 (h - z) (1 - z²) ≤ 0`. -/
private theorem eqOn_two_mul_div_mul_sqrt_zero {h j : ℝ} (hh : -1 ≤ h) :
    EqOn (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) 0
      (Icc h 1) := fun z hz ↦ by
  refine two_mul_div_mul_sqrt_eq_zero ?_
  have h₁ : 0 ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hz.1) h₁]

/-- A continuous function on `ℝ × ℝ` that is positive at `(h₀, z₀)` is positive on a square
`[h₀ - δ, h₀ + δ] × [z₀ - δ, z₀ + δ]`. -/
private theorem exists_forall_Icc_pos {F : ℝ × ℝ → ℝ} (hF : Continuous F) {h₀ z₀ : ℝ}
    (h : 0 < F (h₀, z₀)) : ∃ δ > 0, ∀ h ∈ Icc (h₀ - δ) (h₀ + δ), ∀ z ∈ Icc (z₀ - δ) (z₀ + δ),
      0 < F (h, z) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (hF.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h))
  rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc] at hsub
  exact ⟨δ, hδ, fun h hh z hz ↦ hsub ⟨hh, hz⟩⟩

/-- Along the values `(h, j)` with `j > 0` tending to `(h₀, 0)`, the momentum `j` tends to `0⁺`. -/
private theorem tendsto_snd_nhdsWithin_snd_pos (h₀ : ℝ) :
    Tendsto Prod.snd (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝[>] 0) :=
  continuous_snd.continuousWithinAt.tendsto_nhdsWithin fun _ hc ↦ hc

/-- Along the values `(h, j)` with `j > 0` tending to `(h₀, 0)`, the energy eventually lies in
every interval `[h₀ - δ, h₀ + δ]` with `δ > 0`. -/
private theorem eventually_fst_mem_Icc_nhdsWithin_snd_pos {h₀ δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), c.1 ∈ Icc (h₀ - δ) (h₀ + δ) :=
  ((continuous_fst.tendsto (h₀, 0)).mono_left nhdsWithin_le_nhds).eventually
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The weight `ψ_h(z) = 4 (h - σ z) / f_h'(z)` at the pole `z = -1` of
`f_h(z) = 2 (h - σ z) (1 - z²)` tends to `ψ_{h₀}(-1) = 1` as `(h, j) → (h₀, 0)` with `j > 0` and
`z → -1⁺`, when `f_{h₀}'(-1) = 4 (h₀ + σ)` is positive. -/
private theorem tendsto_uncurry_poleWeight {σ h₀ : ℝ}
    (hD0 : 0 < 6 * σ * (-1) ^ 2 - 4 * h₀ * -1 - 2 * σ) :
    Tendsto (Function.uncurry fun (c : ℝ × ℝ) (z : ℝ) ↦
      4 * (c.1 - σ * z) / (6 * σ * z ^ 2 - 4 * c.1 * z - 2 * σ))
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0) ×ˢ 𝓝[≥] (-1)) (𝓝 1) := by
  have hcont : ContinuousAt (fun p : (ℝ × ℝ) × ℝ ↦
      4 * (p.1.1 - σ * p.2) / (6 * σ * p.2 ^ 2 - 4 * p.1.1 * p.2 - 2 * σ)) ((h₀, 0), -1) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hD0.ne'
  have h1 : 4 * (h₀ - σ * -1) / (6 * σ * (-1) ^ 2 - 4 * h₀ * -1 - 2 * σ) = 1 := by
    rw [div_eq_one_iff_eq hD0.ne']
    ring
  refine (hcont.tendsto.mono_left ?_).mono_right (le_of_eq (congrArg 𝓝 h1))
  rw [nhds_prod_eq]
  exact prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds

/-- If `f_{h₀}(z) = 2 (h₀ - σ z) (1 - z²)`, which vanishes at `z = -1`, has positive derivative on
`[-1, q]`, then at each `x ∈ (-1, q]` the value `f_h(x)` stays above a positive constant as
`(h, j) → (h₀, 0)` with `j > 0`. -/
private theorem exists_pos_eventually_le_pole {σ h₀ q : ℝ} (hq : -1 < q)
    (hd : ∀ z ∈ Icc (-1) q, 0 < 6 * σ * z ^ 2 - 4 * h₀ * z - 2 * σ) {x : ℝ}
    (hx : x ∈ Ioc (-1) q) :
    ∃ m > 0, ∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), m ≤ 2 * (c.1 - σ * x) * (1 - x ^ 2) := by
  have hmono := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (-1) q)
    (f := fun z ↦ 2 * (h₀ - σ * z) * (1 - z ^ 2)) (by fun_prop)
    (fun z _ ↦ (hasDerivAt_two_mul_sub_mul_mul_one_sub_sq h₀ σ z).hasDerivWithinAt)
    fun z hz ↦ hd z (interior_subset hz)
  have hpos : 0 < 2 * (h₀ - σ * x) * (1 - x ^ 2) := by
    simpa using hmono ⟨le_rfl, hq.le⟩ (Ioc_subset_Icc_self hx) hx.1
  refine ⟨_, half_pos hpos, ?_⟩
  exact (((by fun_prop : Continuous fun c : ℝ × ℝ ↦ 2 * (c.1 - σ * x) * (1 - x ^ 2)).tendsto
    (h₀, 0)).mono_left nhdsWithin_le_nhds).eventually (le_mem_nhds (half_lt_self hpos))

/-- **The contribution of a pole.** Let `f_h(z) = 2 (h - σ z) (1 - z²)`, which vanishes at
`z = -1`, have positive derivative on `[-1, q]` for every `h` in `[h₀ - δ, h₀ + δ]`. Then the
integral of `2 j / ((1 - z²) √(f_h(z) - j²))` over `[-1, q]` is eventually defined and tends to
`π` as `(h, j) → (h₀, 0)` with `j > 0`. This is the concentration lemma
`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto` for the weight
`ψ_h = 4 (h - σ z) / f_h'`, whose value at the pole is `1`. -/
private theorem tendsto_integral_pole {σ h₀ q δ : ℝ} (hq : -1 < q) (hδ : 0 < δ)
    (hd : ∀ h ∈ Icc (h₀ - δ) (h₀ + δ), ∀ z ∈ Icc (-1) q,
      0 < 6 * σ * z ^ 2 - 4 * h * z - 2 * σ) :
    (∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), IntervalIntegrable (fun z ↦
      2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - σ * z) * (1 - z ^ 2) - c.2 ^ 2)))) volume (-1) q) ∧
    Tendsto (fun c : ℝ × ℝ ↦ ∫ z in (-1)..q,
        2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - σ * z) * (1 - z ^ 2) - c.2 ^ 2))))
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 π) := by
  have hbox := eventually_fst_mem_Icc_nhdsWithin_snd_pos (h₀ := h₀) hδ
  have hh₀ : h₀ ∈ Icc (h₀ - δ) (h₀ + δ) := ⟨by linarith, by linarith⟩
  have hqIcc : q ∈ Icc (-1) q := ⟨hq.le, le_rfl⟩
  have hf : ∀ h : ℝ, ContinuousOn (fun z ↦ 2 * (h - σ * z) * (1 - z ^ 2)) (Icc (-1) q) :=
    fun _ ↦ by fun_prop
  have hfa : ∀ h : ℝ, 2 * (h - σ * -1) * (1 - (-1) ^ 2) = 0 := fun _ ↦ by norm_num
  have hderiv : ∀ (h : ℝ), ∀ z ∈ Ioo (-1) q, HasDerivAt (fun z ↦ 2 * (h - σ * z) * (1 - z ^ 2))
      (6 * σ * z ^ 2 - 4 * h * z - 2 * σ) z := fun h z _ ↦
    hasDerivAt_two_mul_sub_mul_mul_one_sub_sq h σ z
  have hψ : ∀ h ∈ Icc (h₀ - δ) (h₀ + δ), ContinuousOn
      (fun z ↦ 4 * (h - σ * z) / (6 * σ * z ^ 2 - 4 * h * z - 2 * σ)) (Icc (-1) q) :=
    fun h hh ↦ ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz ↦ (hd h hh z hz).ne'
  -- On `[-1, q]` the integrand is the weight `ψ_h` times the kernel of `f_h`.
  have heq : ∀ c : ℝ × ℝ, c.1 ∈ Icc (h₀ - δ) (h₀ + δ) → EqOn
      (fun z ↦ 2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - σ * z) * (1 - z ^ 2) - c.2 ^ 2))))
      (fun z ↦ 4 * (c.1 - σ * z) / (6 * σ * z ^ 2 - 4 * c.1 * z - 2 * σ) *
        ((6 * σ * z ^ 2 - 4 * c.1 * z - 2 * σ) * c.2 /
          (2 * (c.1 - σ * z) * (1 - z ^ 2) * √(2 * (c.1 - σ * z) * (1 - z ^ 2) - c.2 ^ 2))))
      (uIcc (-1) q) := fun c hc z hz ↦ by
    rw [uIcc_of_le hq.le] at hz
    exact two_mul_div_mul_sqrt_eq (hd c.1 hc z hz).ne'
  refine ⟨?_, ?_⟩
  · filter_upwards [hbox, tendsto_snd_nhdsWithin_snd_pos h₀ self_mem_nhdsWithin] with c hc hc2
    have hint := intervalIntegrable_mul_div_mul_sqrt_sub_sq (hf c.1) (hfa c.1) (hderiv c.1)
      (fun z hz ↦ hd c.1 hc z (Ioo_subset_Icc_self hz)) hc2 hqIcc
    rw [intervalIntegrable_congr ((heq c hc).mono Ioc_subset_Icc_self)]
    exact hint.continuousOn_mul (by rw [uIcc_of_le hq.le]; exact hψ c.1 hc)
  -- The weight is bounded on the compact box and tends to `1` at `(h₀, -1)`.
  have hψK : ContinuousOn
      (fun p : ℝ × ℝ ↦ 4 * (p.1 - σ * p.2) / (6 * σ * p.2 ^ 2 - 4 * p.1 * p.2 - 2 * σ))
      (Icc (h₀ - δ) (h₀ + δ) ×ˢ Icc (-1) q) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ (hd p.1 hp.1 p.2 hp.2).ne'
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hψK
  have hlim := tendsto_integral_mul_mul_div_mul_sqrt_sub_sq_of_tendsto
    (f := fun c z ↦ 2 * (c.1 - σ * z) * (1 - z ^ 2))
    (f' := fun c z ↦ 6 * σ * z ^ 2 - 4 * c.1 * z - 2 * σ) (j := Prod.snd) hq
    (.of_forall fun c ↦ hf c.1) (.of_forall fun c ↦ hfa c.1) (.of_forall fun c ↦ hderiv c.1)
    (hbox.mono fun c hc z hz ↦ hd c.1 hc z (Ioo_subset_Icc_self hz))
    (fun x hx ↦ exists_pos_eventually_le_pole hq (hd h₀ hh₀) hx)
    (tendsto_snd_nhdsWithin_snd_pos h₀) (hbox.mono fun c hc ↦ hψ c.1 hc)
    ⟨M, hbox.mono fun c hc z hz ↦ by
      simpa only [Real.norm_eq_abs] using hM (c.1, z) ⟨hc, hz⟩⟩
    (tendsto_uncurry_poleWeight (hd h₀ hh₀ (-1) ⟨le_rfl, hq.le⟩))
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hbox] with c hc
  exact (intervalIntegral.integral_congr (heq c hc)).symm

/-- **The regular part.** If `1 - z²` and `h - z` are positive for `z ∈ [p, q]` and `h` in
`[h₀ - δ, h₀ + δ]`, the integral of `2 j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` over `[p, q]` is
eventually defined and tends to `0` as `(h, j) → (h₀, 0)` with `j > 0`. -/
private theorem tendsto_integral_regular {h₀ p q δ : ℝ} (hpq : p ≤ q) (hδ : 0 < δ)
    (hpos : ∀ h ∈ Icc (h₀ - δ) (h₀ + δ), ∀ z ∈ Icc p q, 0 < 1 - z ^ 2 ∧ 0 < h - z) :
    (∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), IntervalIntegrable (fun z ↦
      2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2)))) volume p q) ∧
    Tendsto (fun c : ℝ × ℝ ↦ ∫ z in p..q,
        2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))))
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 0) := by
  have hbox := eventually_fst_mem_Icc_nhdsWithin_snd_pos (h₀ := h₀) hδ
  have hh₀ : h₀ ∈ Icc (h₀ - δ) (h₀ + δ) := ⟨by linarith, by linarith⟩
  -- `2 (h - z) (1 - z²) ≥ m` and `1 - z² ≥ n` on the compact box.
  obtain ⟨w, hw, hmin₁⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (⟨(h₀, p), hh₀, ⟨le_rfl, hpq⟩⟩ : (Icc (h₀ - δ) (h₀ + δ) ×ˢ Icc p q).Nonempty)
    (by fun_prop : Continuous fun w : ℝ × ℝ ↦ 2 * (w.1 - w.2) * (1 - w.2 ^ 2)).continuousOn
  obtain ⟨z₂, hz₂, hmin₂⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq)
    (by fun_prop : Continuous fun z : ℝ ↦ 1 - z ^ 2).continuousOn
  set m := 2 * (w.1 - w.2) * (1 - w.2 ^ 2)
  set n := 1 - z₂ ^ 2
  have hm0 : 0 < m :=
    mul_pos (mul_pos two_pos (hpos w.1 hw.1 w.2 hw.2).2) (hpos w.1 hw.1 w.2 hw.2).1
  have hn0 : 0 < n := (hpos h₀ hh₀ z₂ hz₂).1
  have hj : Tendsto Prod.snd (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 0) :=
    (continuous_snd.tendsto (h₀, 0)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), 0 < c.2 ∧ c.2 ^ 2 < m / 2 := by
    filter_upwards [tendsto_snd_nhdsWithin_snd_pos h₀ self_mem_nhdsWithin,
      (by simpa using hj.pow 2 : Tendsto (fun c : ℝ × ℝ ↦ c.2 ^ 2) _ (𝓝 0)).eventually
        (gt_mem_nhds (half_pos hm0))] with c hc hc2 using ⟨hc, hc2⟩
  -- For small `j > 0` the denominator is at least `n √(m / 2)` on `[p, q]`.
  have hden : ∀ c : ℝ × ℝ, c.1 ∈ Icc (h₀ - δ) (h₀ + δ) → c.2 ^ 2 < m / 2 → ∀ z ∈ Icc p q,
      n * √(m / 2) ≤ (1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2) := by
    intro c hc hc2 z hz
    have h₁ : m ≤ 2 * (c.1 - z) * (1 - z ^ 2) := hmin₁ (show (c.1, z) ∈ _ from ⟨hc, hz⟩)
    gcongr
    · exact (hpos c.1 hc z hz).1.le
    · exact hmin₂ hz
    · linarith
  have hden_pos : 0 < n * √(m / 2) := by positivity
  refine ⟨?_, ?_⟩
  · filter_upwards [hbox, hsmall] with c hc ⟨_, hc2⟩
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact continuousOn_const.mul (continuousOn_const.div (by fun_prop) fun z hz ↦
      (hden_pos.trans_le (hden c hc hc2 z hz)).ne')
  · have hbound : Tendsto (fun c : ℝ × ℝ ↦ 2 * c.2 / (n * √(m / 2)) * |q - p|)
        (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 0) := by
      simpa using ((by fun_prop : Continuous fun c : ℝ × ℝ ↦
        2 * c.2 / (n * √(m / 2)) * |q - p|).tendsto (h₀, 0)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hbox, hsmall] with c hc ⟨hc0, hc2⟩
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun z hz ↦ ?_
    have hz' : z ∈ Icc p q := by
      rw [uIoc_of_le hpq] at hz
      exact Ioc_subset_Icc_self hz
    have hden_z := hden_pos.trans_le (hden c hc hc2 z hz')
    rw [Real.norm_of_nonneg (mul_nonneg two_pos.le (div_nonneg hc0.le hden_z.le)),
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos (hden c hc hc2 z hz')

/-- **The contribution of the turning point `z = h`.** Let `-1 ≤ c < h ≤ 1` and let the derivative
`6 z² - 4 h z - 2` of `f_h(z) = 2 (h - z) (1 - z²)` be at most `-m < 0` on `[c, h]`. For `j > 0`
the integrand `2 j / ((1 - z²) √(f_h(z) - j²))` vanishes on `[h, 1]`, and on `[c, h]` it is the
weight `4 (h - z) / (-f_h'(z))`, at most `4 (h - c) / m`, against the kernel of `f_h` reflected at
`z = h`. So its integral over `[c, 1]` is defined and at most `4 (h - c) / m · π` in absolute
value. -/
private theorem abs_integral_turningPoint_le {h j c m : ℝ} (hj : 0 < j) (hc : -1 ≤ c)
    (hch : c < h) (hh : h ≤ 1) (hm : 0 < m)
    (hd : ∀ z ∈ Icc c h, 6 * z ^ 2 - 4 * h * z - 2 ≤ -m) :
    IntervalIntegrable (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))))
        volume c 1 ∧
      |∫ z in c..1, 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))| ≤
        4 * (h - c) / m * π := by
  set I : ℝ → ℝ := fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))
    with hI
  have hzero : EqOn I 0 (uIcc h 1) := by
    rw [uIcc_of_le hh]
    exact eqOn_two_mul_div_mul_sqrt_zero (by linarith)
  have hint₂ : IntervalIntegrable I volume h 1 :=
    (intervalIntegrable_congr (hzero.mono Ioc_subset_Icc_self)).2 intervalIntegrable_const
  -- After the reflection `z = -w`, the zero `z = h` of `f_h` becomes the zero `w = -h` of
  -- `g(w) = 2 (h + w) (1 - w²)`, which has derivative `-f_h'(-w) ≥ m` on `[-h, -c]`.
  have hgd : ∀ w ∈ Icc (-h) (-c), m ≤ 6 * -1 * w ^ 2 - 4 * h * w - 2 * -1 := fun w hw ↦ by
    have := hd (-w) ⟨le_neg.1 hw.2, neg_le.1 hw.1⟩
    linarith
  have hg : ContinuousOn (fun w ↦ 2 * (h - -1 * w) * (1 - w ^ 2)) (Icc (-h) (-c)) := by fun_prop
  have hga : 2 * (h - -1 * -h) * (1 - (-h) ^ 2) = 0 := by ring
  have hgderiv : ∀ w ∈ Ioo (-h) (-c), HasDerivAt (fun w ↦ 2 * (h - -1 * w) * (1 - w ^ 2))
      (6 * -1 * w ^ 2 - 4 * h * w - 2 * -1) w := fun w _ ↦
    hasDerivAt_two_mul_sub_mul_mul_one_sub_sq h (-1) w
  have hgpos : ∀ w ∈ Ioo (-h) (-c), 0 < 6 * -1 * w ^ 2 - 4 * h * w - 2 * -1 := fun w hw ↦
    hm.trans_le (hgd w (Ioo_subset_Icc_self hw))
  have hcIcc : -c ∈ Icc (-h) (-c) := ⟨neg_le_neg hch.le, le_rfl⟩
  have heq : EqOn (fun w ↦ I (-w))
      (fun w ↦ 4 * (h - -1 * w) / (6 * -1 * w ^ 2 - 4 * h * w - 2 * -1) *
        ((6 * -1 * w ^ 2 - 4 * h * w - 2 * -1) * j /
          (2 * (h - -1 * w) * (1 - w ^ 2) * √(2 * (h - -1 * w) * (1 - w ^ 2) - j ^ 2))))
      (uIcc (-h) (-c)) := fun w hw ↦ by
    rw [uIcc_of_le (neg_le_neg hch.le)] at hw
    beta_reduce
    rw [← two_mul_div_mul_sqrt_eq (hm.trans_le (hgd w hw)).ne']
    simp only [hI, neg_sq, neg_one_mul]
  have hψ : ContinuousOn (fun w ↦ 4 * (h - -1 * w) / (6 * -1 * w ^ 2 - 4 * h * w - 2 * -1))
      (Icc (-h) (-c)) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw ↦ (hm.trans_le (hgd w hw)).ne'
  have hint₁ : IntervalIntegrable I volume c h := by
    rw [IntervalIntegrable.iff_comp_neg]
    refine IntervalIntegrable.symm ?_
    rw [intervalIntegrable_congr (heq.mono Ioc_subset_Icc_self)]
    exact (intervalIntegrable_mul_div_mul_sqrt_sub_sq hg hga hgderiv hgpos hj
      hcIcc).continuousOn_mul (by rwa [uIcc_of_le (neg_le_neg hch.le)])
  refine ⟨hint₁.trans hint₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂,
    intervalIntegral.integral_congr hzero]
  simp only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero]
  have hrefl : ∫ z in c..h, I z = ∫ w in (-h)..(-c), I (-w) := by
    rw [intervalIntegral.integral_comp_neg, neg_neg, neg_neg]
  rw [hrefl, intervalIntegral.integral_congr heq]
  refine abs_integral_mul_mul_div_mul_sqrt_sub_sq_le hg hga hgderiv hgpos hj hcIcc fun w hw ↦ ?_
  have hden := hgd w hw
  rw [abs_div, abs_of_nonneg (by linarith [hw.1]), abs_of_pos (hm.trans_le hden)]
  exact div_le_div₀ (by linarith [hw.1]) (by linarith [hw.2]) hm hden

/-- The rotation angle is the sum of the integrals of `2 j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))`
over `[-1, a]`, `[a, c]` and `[c, 1]`, when these are defined. -/
private theorem sphericalPendulumRotationAngle_eq_add {h j a c : ℝ}
    (h₁ : IntervalIntegrable (fun z ↦
      2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) volume (-1) a)
    (h₂ : IntervalIntegrable (fun z ↦
      2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) volume a c)
    (h₃ : IntervalIntegrable (fun z ↦
      2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) volume c 1) :
    sphericalPendulumRotationAngle h j =
      (∫ z in (-1)..a, 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) +
        (∫ z in a..c, 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) +
        ∫ z in c..1, 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))) := by
  rw [sphericalPendulumRotationAngle_def, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂) h₃,
    ← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

/-- **The south pole.** For `h₀ > -1` and any `a₀ > -1` there is a cut `a ∈ (-1, a₀]` such that
the integral of `2 j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` over `[-1, a]` is eventually defined
and tends to `π` as `(h, j) → (h₀, 0)` with `j > 0`. -/
private theorem exists_tendsto_integral_southPole {h₀ a₀ : ℝ} (h₁ : -1 < h₀) (ha₀ : -1 < a₀) :
    ∃ a ∈ Ioc (-1) a₀,
      (∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), IntervalIntegrable (fun z ↦
        2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2)))) volume (-1) a) ∧
      Tendsto (fun c : ℝ × ℝ ↦ ∫ z in (-1)..a,
          2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))))
        (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 π) := by
  -- A box around `(h₀, -1)` where the derivative of `2 (h - z) (1 - z²)` is positive.
  obtain ⟨δ, hδ, hb⟩ := exists_forall_Icc_pos (h₀ := h₀) (z₀ := -1)
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ 6 * 1 * p.2 ^ 2 - 4 * p.1 * p.2 - 2 * 1)
    (show (0 : ℝ) < 6 * 1 * (-1) ^ 2 - 4 * h₀ * -1 - 2 * 1 by linarith)
  have hmin : 0 < min δ (a₀ + 1) := lt_min hδ (by linarith)
  have hmin₁ := min_le_left δ (a₀ + 1)
  have hmin₂ := min_le_right δ (a₀ + 1)
  obtain ⟨hint, hlim⟩ := tendsto_integral_pole (σ := 1) (q := -1 + min δ (a₀ + 1))
    (by linarith) hδ fun h hh z hz ↦ hb h hh z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  simp only [one_mul] at hint hlim
  exact ⟨_, ⟨by linarith, by linarith⟩, hint, hlim⟩

/-- **Planar rotations.** For `h₀ > 1`, the rotation angle `Θ(h, j)` tends to `2π` as
`(h, j) → (h₀, 0)` with `j > 0`. Each of the two poles of the sphere contributes `π`. -/
theorem tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_one_lt {h₀ : ℝ}
    (h₁ : 1 < h₀) :
    Tendsto (Function.uncurry sphericalPendulumRotationAngle)
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 (2 * π)) := by
  -- The pole `z = -1`, cut at some `a ≤ -1 / 2`.
  obtain ⟨a, ⟨ha, ha'⟩, hint₁, hlim₁⟩ :=
    exists_tendsto_integral_southPole (a₀ := -1 / 2) (by linarith) (by norm_num)
  -- A box around `(h₀, 1)`, in the reflected coordinate `w = -z`, on which the derivative of
  -- `2 (h + w) (1 - w²)` is positive.
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_forall_Icc_pos (h₀ := h₀) (z₀ := -1)
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ 6 * -1 * p.2 ^ 2 - 4 * p.1 * p.2 - 2 * -1)
    (show (0 : ℝ) < 6 * -1 * (-1) ^ 2 - 4 * h₀ * -1 - 2 * -1 by linarith)
  set δ := min δ₂ ((h₀ - 1) / 2)
  have hδ : 0 < δ := lt_min hδ₂ (by linarith)
  have hδ₂' : δ ≤ δ₂ := min_le_left _ _
  have hδ₃' : δ ≤ (h₀ - 1) / 2 := min_le_right _ _
  set q := -1 + min δ₂ (1 / 2)
  have hq : -1 < q := by have := lt_min hδ₂ (one_half_pos (α := ℝ)); linarith
  have hq' : q ≤ -1 / 2 := by have := min_le_right δ₂ (1 / 2); linarith
  have hbox : ∀ h ∈ Icc (h₀ - δ) (h₀ + δ), h ∈ Icc (h₀ - δ₂) (h₀ + δ₂) :=
    fun h hh ↦ ⟨by linarith [hh.1], by linarith [hh.2]⟩
  -- The regular part `[a, -q]` and the pole `z = 1`.
  obtain ⟨hint₂, hlim₂⟩ := tendsto_integral_regular (h₀ := h₀) (p := a) (q := -q)
    (by linarith) hδ fun h hh z hz ↦
      ⟨by nlinarith [hz.1, hz.2], by linarith [hh.1, hz.2]⟩
  obtain ⟨hint₃, hlim₃⟩ := tendsto_integral_pole (σ := -1) hq hδ fun h hh z hz ↦
    hb₂ h (hbox h hh) z ⟨by linarith [hz.1], by
      linarith [hz.2, min_le_left δ₂ (1 / 2)]⟩
  -- Reflect the third integral back to `[-q, 1]`.
  have hint₃' : ∀ᶠ c in 𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0), IntervalIntegrable (fun z ↦
      2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2)))) volume (-q) 1 := by
    filter_upwards [hint₃] with c hc
    rw [IntervalIntegrable.iff_comp_neg, neg_neg]
    exact hc.symm.congr fun z _ ↦ by simp
  have hlim₃' : Tendsto (fun c : ℝ × ℝ ↦ ∫ z in (-q)..1,
      2 * (c.2 / ((1 - z ^ 2) * √(2 * (c.1 - z) * (1 - z ^ 2) - c.2 ^ 2))))
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 π) := by
    refine hlim₃.congr fun c ↦ ?_
    rw [← neg_neg (1 : ℝ), ← intervalIntegral.integral_comp_neg, neg_neg]
    simp
  have hsum := (hlim₁.add hlim₂).add hlim₃'
  rw [add_zero, ← two_mul] at hsum
  refine hsum.congr' ?_
  filter_upwards [hint₁, hint₂, hint₃'] with c hc₁ hc₂ hc₃
  exact (sphericalPendulumRotationAngle_eq_add hc₁ hc₂ hc₃).symm

/-- **Planar oscillations.** For `-1 < h₀ < 1`, the rotation angle `Θ(h, j)` tends to `π` as
`(h, j) → (h₀, 0)` with `j > 0`. The south pole contributes `π` and the turning point near
`z = h` contributes nothing. -/
theorem tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one {h₀ : ℝ}
    (h₁ : -1 < h₀) (h₂ : h₀ < 1) :
    Tendsto (Function.uncurry sphericalPendulumRotationAngle)
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) (𝓝 π) := by
  -- The pole `z = -1`, cut at some `a < h₀`.
  obtain ⟨a, ⟨ha, hah⟩, hint₁, hlim₁⟩ :=
    exists_tendsto_integral_southPole (a₀ := (h₀ - 1) / 2) h₁ (by linarith)
  replace hah : a < h₀ := by linarith
  -- A box around `(h₀, h₀)` where the derivative of `2 (h - z) (1 - z²)` is at most `-(1 - h₀²)`.
  set m := 1 - h₀ ^ 2 with hm_def
  have hm : 0 < m := by nlinarith
  obtain ⟨ρ, hρ, hb₂⟩ := exists_forall_Icc_pos (h₀ := h₀) (z₀ := h₀)
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ -(6 * p.2 ^ 2 - 4 * p.1 * p.2 - 2) - m)
    (show (0 : ℝ) < -(6 * h₀ ^ 2 - 4 * h₀ * h₀ - 2) - m by linarith [hm_def])
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Cut at `c = h₀ - t` for a small `t`, and take `h` within `t / 2` of `h₀`.
  set t := min (min (ρ / 2) ((h₀ - a) / 2)) (min ((1 - h₀) / 2) (ε * m / (24 * π)))
  have ht : 0 < t := lt_min (lt_min (half_pos hρ) (by linarith))
    (lt_min (by linarith) (by positivity))
  have htρ : t ≤ ρ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hta : t ≤ (h₀ - a) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have ht1 : t ≤ (1 - h₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htε : t ≤ ε * m / (24 * π) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hint₂, hlim₂⟩ := tendsto_integral_regular (h₀ := h₀) (p := a) (q := h₀ - t)
    (by linarith) (half_pos ht) fun h hh z hz ↦
      ⟨by nlinarith [hz.1, hz.2], by linarith [hh.1, hz.2]⟩
  filter_upwards [hint₁, hint₂, Metric.tendsto_nhds.1 hlim₁ (ε / 4) (by positivity),
    Metric.tendsto_nhds.1 hlim₂ (ε / 4) (by positivity),
    eventually_fst_mem_Icc_nhdsWithin_snd_pos (h₀ := h₀) (half_pos ht),
    tendsto_snd_nhdsWithin_snd_pos h₀ self_mem_nhdsWithin] with c hc₁ hc₂ hl₁ hl₂ hc hc0
  obtain ⟨hc₃, hb₃⟩ := abs_integral_turningPoint_le (h := c.1) (c := h₀ - t) hc0
    (by linarith) (by linarith [hc.1]) (by linarith [hc.2]) hm fun z hz ↦ by
      have := hb₂ c.1 ⟨by linarith [hc.1], by linarith [hc.2]⟩ z
        ⟨by linarith [hz.1], by linarith [hz.2, hc.2]⟩
      linarith
  have hb₃' : 4 * (c.1 - (h₀ - t)) / m * π ≤ ε / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    have : c.1 - (h₀ - t) ≤ 3 / 2 * t := by linarith [hc.2]
    have : t * (24 * π) ≤ ε * m := (le_div_iff₀ (by positivity)).1 htε
    nlinarith [pi_pos]
  rw [Function.uncurry_apply_pair, sphericalPendulumRotationAngle_eq_add hc₁ hc₂ hc₃]
  simp only [Real.dist_eq, sub_zero] at hl₁ hl₂ ⊢
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hl₁
  obtain ⟨h₃, h₄⟩ := abs_lt.1 hl₂
  obtain ⟨h₅, h₆⟩ := abs_le.1 hb₃
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩

/-- Along the values `(h, j)` with `j < 0` tending to `(h₀, 0)`, the reflection `j ↦ -j` tends to
`(h₀, 0)` with `j > 0`. -/
private theorem tendsto_prodMk_neg_nhdsWithin_snd_neg (h₀ : ℝ) :
    Tendsto (fun c : ℝ × ℝ ↦ (c.1, -c.2)) (𝓝[{c : ℝ × ℝ | c.2 < 0}] (h₀, 0))
      (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h₀, 0)) := by
  simpa using (by fun_prop : Continuous fun c : ℝ × ℝ ↦ (c.1, -c.2)).continuousWithinAt
    |>.tendsto_nhdsWithin (x := (h₀, 0)) fun _ hc ↦ neg_pos.2 hc

/-- For `h₀ > 1`, the rotation angle `Θ(h, j)` tends to `-2π` as `(h, j) → (h₀, 0)` with
`j < 0`. -/
theorem tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_one_lt {h₀ : ℝ}
    (h₁ : 1 < h₀) :
    Tendsto (Function.uncurry sphericalPendulumRotationAngle)
      (𝓝[{c : ℝ × ℝ | c.2 < 0}] (h₀, 0)) (𝓝 (-(2 * π))) :=
  ((tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_one_lt h₁).comp
    (tendsto_prodMk_neg_nhdsWithin_snd_neg h₀)).neg.congr fun c ↦ by
      simp [Function.uncurry_def]

/-- For `-1 < h₀ < 1`, the rotation angle `Θ(h, j)` tends to `-π` as `(h, j) → (h₀, 0)` with
`j < 0`. -/
theorem tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_lt_one {h₀ : ℝ}
    (h₁ : -1 < h₀) (h₂ : h₀ < 1) :
    Tendsto (Function.uncurry sphericalPendulumRotationAngle)
      (𝓝[{c : ℝ × ℝ | c.2 < 0}] (h₀, 0)) (𝓝 (-π)) :=
  ((tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one h₁ h₂).comp
    (tendsto_prodMk_neg_nhdsWithin_snd_neg h₀)).neg.congr fun c ↦ by
      simp [Function.uncurry_def]

/-- As `j → 0⁺` at a fixed energy `h`, the value `(h, j)` tends to `(h, 0)` with `j > 0`. -/
private theorem tendsto_prodMk_nhdsGT (h : ℝ) :
    Tendsto (fun j : ℝ ↦ (h, j)) (𝓝[>] 0) (𝓝[{c : ℝ × ℝ | 0 < c.2}] (h, 0)) :=
  (by fun_prop : Continuous fun j : ℝ ↦ (h, j)).continuousWithinAt.tendsto_nhdsWithin
    fun _ hj ↦ hj

/-- As `j → 0⁻` at a fixed energy `h`, the value `(h, j)` tends to `(h, 0)` with `j < 0`. -/
private theorem tendsto_prodMk_nhdsLT (h : ℝ) :
    Tendsto (fun j : ℝ ↦ (h, j)) (𝓝[<] 0) (𝓝[{c : ℝ × ℝ | c.2 < 0}] (h, 0)) :=
  (by fun_prop : Continuous fun j : ℝ ↦ (h, j)).continuousWithinAt.tendsto_nhdsWithin
    fun _ hj ↦ hj

/-- For `-1 < h < 1`, the rotation angle tends to `π` as `j → 0⁺`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one {h : ℝ} (h₁ : -1 < h)
    (h₂ : h < 1) : Tendsto (sphericalPendulumRotationAngle h) (𝓝[>] 0) (𝓝 π) :=
  (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one h₁ h₂).comp
    (tendsto_prodMk_nhdsGT h)

/-- For `h > 1`, the rotation angle tends to `2π` as `j → 0⁺`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsGT_of_one_lt {h : ℝ} (h₁ : 1 < h) :
    Tendsto (sphericalPendulumRotationAngle h) (𝓝[>] 0) (𝓝 (2 * π)) :=
  (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_one_lt h₁).comp
    (tendsto_prodMk_nhdsGT h)

/-- For `-1 < h < 1`, the rotation angle tends to `-π` as `j → 0⁻`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsLT_of_lt_one {h : ℝ} (h₁ : -1 < h)
    (h₂ : h < 1) : Tendsto (sphericalPendulumRotationAngle h) (𝓝[<] 0) (𝓝 (-π)) :=
  (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_lt_one h₁ h₂).comp
    (tendsto_prodMk_nhdsLT h)

/-- For `h > 1`, the rotation angle tends to `-2π` as `j → 0⁻`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsLT_of_one_lt {h : ℝ} (h₁ : 1 < h) :
    Tendsto (sphericalPendulumRotationAngle h) (𝓝[<] 0) (𝓝 (-(2 * π))) :=
  (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_one_lt h₁).comp
    (tendsto_prodMk_nhdsLT h)

/-! ### Continuity of the rotation angle away from `j = 0` -/

section Continuity

variable {h j z₀ : ℝ}

/-- The regular integrand of the spherical pendulum rotation angle after the sine substitution
between turning points `a` and `b`, with third root `h - a - b`. -/
noncomputable def sphericalPendulumRotationAngleSinIntegrand (a b h j θ : ℝ) : ℝ :=
  j / ((1 - ((a + b) / 2 + (b - a) / 2 * sin θ) ^ 2) *
    √(2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * sin θ))))

/-- The formula for the regular sine-substitution integrand. -/
theorem sphericalPendulumRotationAngleSinIntegrand_def (a b h j θ : ℝ) :
    sphericalPendulumRotationAngleSinIntegrand a b h j θ =
      j / ((1 - ((a + b) / 2 + (b - a) / 2 * sin θ) ^ 2) *
        √(2 * (h - a - b - ((a + b) / 2 + (b - a) / 2 * sin θ)))) := (rfl)

/-- **The rotation angle as a regular integral.** For `j ≠ 0` and `(h, j)` strictly above the
curve of relative equilibria, the substitution `z = (z₋ + z₊) / 2 + (z₊ - z₋) / 2 · sin θ` between
the turning points `z₋ < z₊` turns the rotation angle into the integral
`Θ(h, j) = 2 ∫_{-π/2}^{π/2} j dθ / ((1 - z²) √(2 (z₃ - z)))`, where `z₃ = h - z₋ - z₊` is the
third root of the radicand. Its integrand is continuous, since `-1 < z₋ ≤ z ≤ z₊ < 1 < z₃`. -/
theorem sphericalPendulumRotationAngle_eq_integral_sin (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1)
    (hV : sphericalPendulumEffectivePotential j z₀ < h) :
    sphericalPendulumRotationAngle h j =
      2 * ∫ θ in (-(π / 2))..(π / 2),
        sphericalPendulumRotationAngleSinIntegrand (sphericalPendulumLowerTurningPoint h j)
          (sphericalPendulumUpperTurningPoint h j) h j θ := by
  have := integral_div_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq_eq_integral_sin hj hz₀ hV
    fun z ↦ j / (1 - z ^ 2)
  simp only [div_div] at this
  rw [sphericalPendulumRotationAngle_def, this]
  simp only [sphericalPendulumRotationAngleSinIntegrand_def]

/-- **Joint continuity of the regular integrand.** With the turning points `z₋(h, j)`,
`z₊(h, j)` substituted, the integrand of `sphericalPendulumRotationAngle_eq_integral_sin` is jointly
continuous in `((h, j), θ)` for `(h, j)` in `sphericalPendulumTurningPointDomain`, since its
denominator is positive there. -/
theorem continuousOn_sphericalPendulumRotationAngleSinIntegrand :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ ↦ sphericalPendulumRotationAngleSinIntegrand
        (sphericalPendulumLowerTurningPoint p.1.1 p.1.2)
        (sphericalPendulumUpperTurningPoint p.1.1 p.1.2) p.1.1 p.1.2 p.2)
      (sphericalPendulumTurningPointDomain ×ˢ univ) := by
  have ha : ContinuousOn (fun p : (ℝ × ℝ) × ℝ ↦ sphericalPendulumLowerTurningPoint p.1.1 p.1.2)
      (sphericalPendulumTurningPointDomain ×ˢ univ) :=
    continuousOn_sphericalPendulumLowerTurningPoint.comp continuousOn_fst fun p hp ↦ hp.1
  have hb : ContinuousOn (fun p : (ℝ × ℝ) × ℝ ↦ sphericalPendulumUpperTurningPoint p.1.1 p.1.2)
      (sphericalPendulumTurningPointDomain ×ˢ univ) :=
    continuousOn_sphericalPendulumUpperTurningPoint.comp continuousOn_fst fun p hp ↦ hp.1
  simp only [sphericalPendulumRotationAngleSinIntegrand_def]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun p hp ↦ ?_
  obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 hp.1
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz hV
  have ha₁ := neg_one_lt_sphericalPendulumLowerTurningPoint hj hz hV
  have hb₁ := sphericalPendulumUpperTurningPoint_lt_one hj hz hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz hV
  exact (one_sub_sq_mul_sqrt_sub_add_mul_sin_pos ha₁ hab.le hb₁ (by linarith) p.2).ne'

/-- **Continuity of the rotation angle.** The rotation angle `Θ(h, j)` is continuous on the
values `(h, j)` with `j ≠ 0` lying strictly above the curve of relative equilibria, that is, with
`V_j(z) < h` for some height `z ∈ (-1, 1)`. -/
theorem continuousOn_sphericalPendulumRotationAngle :
    ContinuousOn (fun c : ℝ × ℝ ↦ sphericalPendulumRotationAngle c.1 c.2)
      sphericalPendulumTurningPointDomain := by
  let R := sphericalPendulumTurningPointDomain
  let G : R → ℝ → ℝ := fun c θ ↦
    sphericalPendulumRotationAngleSinIntegrand
      (sphericalPendulumLowerTurningPoint (c : ℝ × ℝ).1 (c : ℝ × ℝ).2)
      (sphericalPendulumUpperTurningPoint (c : ℝ × ℝ).1 (c : ℝ × ℝ).2) (c : ℝ × ℝ).1
      (c : ℝ × ℝ).2 θ
  have hG : Continuous (Function.uncurry G) :=
    continuousOn_sphericalPendulumRotationAngleSinIntegrand.comp_continuous
      (by fun_prop : Continuous fun p : R × ℝ ↦ ((p.1 : ℝ × ℝ), p.2)) fun p ↦ ⟨p.1.property,
          trivial⟩
  rw [continuousOn_iff_continuous_domRestrict]
  refine ((continuous_const (y := (2 : ℝ))).mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hG
      (-(π / 2)) (π / 2))).congr fun c ↦ ?_
  obtain ⟨hj, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 c.property
  simp only [G, domRestrict_apply]
  exact (sphericalPendulumRotationAngle_eq_integral_sin hj hz hV).symm

end Continuity

/-! ### The rotation angle around the focus–focus value -/

/-- The one-sided limits of the rotation angle along the circle `γ(t) = (1 + r cos t, r sin t)`, at
the points `γ(0) = γ(2π) = (1 + r, 0)` and `γ(π) = (1 - r, 0)` where it crosses the axis `j = 0`. -/
private theorem tendsto_sphericalPendulumRotationAngle_circle {r : ℝ} (hr : 0 < r) (hr₂ : r < 2) :
    Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))
        (𝓝[Ioo 0 π] 0) (𝓝 (2 * π)) ∧
      Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))
        (𝓝[Ioo 0 π] π) (𝓝 π) ∧
      Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))
        (𝓝[Ioo π (2 * π)] π) (𝓝 (-π)) ∧
      Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))
        (𝓝[Ioo π (2 * π)] (2 * π)) (𝓝 (-(2 * π))) := by
  set γ : ℝ → ℝ × ℝ := fun t ↦ (1 + r * cos t, r * sin t) with hγdef
  have hγ : ∀ {s : Set ℝ} {t₀ : ℝ} {S : Set (ℝ × ℝ)}, (∀ t ∈ s, γ t ∈ S) →
      Tendsto γ (𝓝[s] t₀) (𝓝[S] (γ t₀)) := fun hs ↦
    (by fun_prop : Continuous γ).continuousWithinAt.tendsto_nhdsWithin hs
  have hup : ∀ t ∈ Ioo 0 π, γ t ∈ {c : ℝ × ℝ | 0 < c.2} := fun t ht ↦
    mul_pos hr (sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  have hdown : ∀ t ∈ Ioo π (2 * π), γ t ∈ {c : ℝ × ℝ | c.2 < 0} := fun t ht ↦
    mul_neg_of_pos_of_neg hr (sin_neg_of_pi_lt_of_lt_two_pi ht.1 ht.2)
  have hγ0 : γ 0 = (1 + r, 0) := by simp [hγdef]
  have hγπ : γ π = (1 - r, 0) := by simp [hγdef, sub_eq_add_neg]
  have hγ2π : γ (2 * π) = (1 + r, 0) := by simp [hγdef]
  have h₁ := hγ (t₀ := 0) hup
  have h₂ := hγ (t₀ := π) hup
  have h₃ := hγ (t₀ := π) hdown
  have h₄ := hγ (t₀ := 2 * π) hdown
  rw [hγ0] at h₁
  rw [hγπ] at h₂ h₃
  rw [hγ2π] at h₄
  exact ⟨(tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_one_lt
      (by linarith)).comp h₁,
    (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_pos_of_lt_one (by linarith)
      (by linarith)).comp h₂,
    (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_lt_one (by linarith)
      (by linarith)).comp h₃,
    (tendsto_uncurry_sphericalPendulumRotationAngle_nhdsWithin_snd_neg_of_one_lt
      (by linarith)).comp h₄⟩

/-- The value `(1, r)` lies above the curve of relative equilibria only for `r < 2`: for
`z ∈ (-1, 1)` the effective potential satisfies `V_r(z) ≥ |r| - 1`. -/
private theorem lt_two_of_mem_sphericalPendulumTurningPointDomain {r : ℝ}
    (h : (1, r) ∈ sphericalPendulumTurningPointDomain) : r < 2 := by
  obtain ⟨_, z, hz, hV⟩ := mem_sphericalPendulumTurningPointDomain_iff.1 h
  rw [sphericalPendulumEffectivePotential_def] at hV
  have hu : 0 < 1 + z := by linarith [hz.1]
  have hw : 0 < 1 - z := by linarith [hz.2]
  have hzz : 0 < 2 * (1 - z ^ 2) := by nlinarith
  rw [div_add' _ _ _ hzz.ne', div_lt_iff₀ hzz] at hV
  -- `r² < 2 (1 - z)² (1 + z)`, and `(1 + z) (1 - z) ≤ 1` with `1 - z < 2`.
  have hle : (1 + z) * (1 - z) ≤ 1 := by nlinarith [sq_nonneg z]
  nlinarith [mul_le_mul_of_nonneg_right hle hw.le]

/-- **A continuous lift of an integer multiple of the rotation angle drops around the focus–focus
value.** Let `γ(t) = (1 + r cos t, r sin t)`, for `t ∈ [0, 2π]`, be the counterclockwise circle of
radius `r > 0` about the focus–focus value `(1, 0)` of the energy–momentum map, and suppose that off
the axis `j = 0` it runs strictly above the curve of relative equilibria. Let `m` be an integer. If
`L` is continuous on `[0, 2π]` and agrees modulo `2π` with `m Θ(γ(t))` at every `t` with
`sin t ≠ 0`, then `L(2π) - L(0) = -2πm`. The circle can only run above that curve when `r < 2`.

The difference `L - m Θ ∘ γ` is constant on each of the two open half-circles, where it is
continuous with values in `2πℤ`. The one-sided limits of `Θ` at the axis, `±2π` at `(1 + r, 0)` and
`±π` at `(1 - r, 0)`, then force the two constants to differ by `2πm` and the lift to drop by
`2πm`. -/
theorem sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle
    {r : ℝ} (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    (m : ℤ) {L : ℝ → ℝ} (hL : ContinuousOn L (Icc 0 (2 * π)))
    (hLΘ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      (L t : Real.Angle) = ↑(m * sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t))) :
    L (2 * π) - L 0 = -(m * (2 * π)) := by
  have hpi : 0 < π := pi_pos
  have h2pi : π < 2 * π := by linarith
  have hr₂ := lt_two_of_mem_sphericalPendulumTurningPointDomain
    (by simpa using hγ (π / 2) (by simp))
  set Θ : ℝ → ℝ := fun t ↦ m * sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)
  obtain ⟨l₀, lπ₁, lπ₂, l₂π⟩ := tendsto_sphericalPendulumRotationAngle_circle hr hr₂
  have hΘ : ∀ {s : Set ℝ}, (∀ t ∈ s, sin t ≠ 0) → ContinuousOn Θ s :=
    fun hs ↦ continuousOn_const.mul <| continuousOn_sphericalPendulumRotationAngle.comp
      (by fun_prop : Continuous fun t : ℝ ↦ (1 + r * cos t, r * sin t)).continuousOn
      fun t ht ↦ hγ t (hs t ht)
  have hIcc₁ : Ioo 0 π ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨ht.1.le, by linarith [ht.2]⟩
  have hIcc₂ : Ioo π (2 * π) ⊆ Icc 0 (2 * π) := fun t ht ↦ ⟨by linarith [ht.1], ht.2.le⟩
  have hsin₁ : ∀ t ∈ Ioo 0 π, sin t ≠ 0 := fun t ht ↦ (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have hsin₂ : ∀ t ∈ Ioo π (2 * π), sin t ≠ 0 := fun t ht ↦
    (sin_neg_of_pi_lt_of_lt_two_pi ht.1 ht.2).ne
  -- On each open half-circle the lift differs from `m Θ ∘ γ` by a constant.
  obtain ⟨C₁, hC₁⟩ := isPreconnected_Ioo.exists_forall_sub_eq_of_coe_eq (hL.mono hIcc₁)
    (hΘ hsin₁) fun t ht ↦ hLΘ t (hIcc₁ ht) (hsin₁ t ht)
  obtain ⟨C₂, hC₂⟩ := isPreconnected_Ioo.exists_forall_sub_eq_of_coe_eq (hL.mono hIcc₂)
    (hΘ hsin₂) fun t ht ↦ hLΘ t (hIcc₂ ht) (hsin₂ t ht)
  -- A one-sided limit of `m Θ ∘ γ` at an endpoint of a half-circle identifies its constant.
  have key : ∀ {s : Set ℝ} {t₀ C θ : ℝ}, (𝓝[s] t₀).NeBot → s ⊆ Icc 0 (2 * π) →
      t₀ ∈ Icc 0 (2 * π) → (∀ t ∈ s, L t - Θ t = C) →
      Tendsto (fun t ↦ sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)) (𝓝[s] t₀)
        (𝓝 θ) → L t₀ - m * θ = C := fun _ hs ht₀ hC hθ ↦
    tendsto_nhds_unique (((hL _ ht₀).tendsto.mono_left (nhdsWithin_mono _ hs)).sub
        (hθ.const_mul _))
      (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht ↦ (hC t ht).symm))
  have h₀ := key (left_nhdsWithin_Ioo_neBot hpi) hIcc₁ ⟨le_rfl, by linarith⟩ hC₁ l₀
  have h₁ := key (right_nhdsWithin_Ioo_neBot hpi) hIcc₁ ⟨hpi.le, by linarith⟩ hC₁ lπ₁
  have h₂ := key (left_nhdsWithin_Ioo_neBot h2pi) hIcc₂ ⟨hpi.le, by linarith⟩ hC₂ lπ₂
  have h₃ := key (right_nhdsWithin_Ioo_neBot h2pi) hIcc₂ ⟨by linarith, le_rfl⟩ hC₂ l₂π
  linear_combination h₃ - h₂ + h₁ - h₀

/-- **A continuous lift of the rotation angle decreases by `2π` around the focus–focus value.**
Let `γ(t) = (1 + r cos t, r sin t)`, for `t ∈ [0, 2π]`, be the counterclockwise circle of radius
`r > 0` about the focus–focus value `(1, 0)` of the energy–momentum map, and suppose that off the
axis `j = 0` it runs strictly above the curve of relative equilibria. If `L` is continuous on
`[0, 2π]` and agrees modulo `2π` with the rotation angle `Θ(γ(t))` at every `t` with `sin t ≠ 0`,
then `L(2π) - L(0) = -2π`. This is the case `m = 1` of
`TauCeti.sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle`. -/
theorem sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle {r : ℝ} (hr : 0 < r)
    (hγ : ∀ t, sin t ≠ 0 → (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain)
    {L : ℝ → ℝ} (hL : ContinuousOn L (Icc 0 (2 * π)))
    (hLΘ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      (L t : Real.Angle) = sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)) :
    L (2 * π) - L 0 = -(2 * π) := by
  simpa using sub_eq_neg_intCast_mul_two_mul_pi_of_coe_eq_intCast_mul_sphericalPendulumRotationAngle
    hr hγ 1 hL (by simpa using hLΘ)

/-- The counterclockwise circles of radius `0 < r ≤ 1` about the focus–focus value `(1, 0)` run
above the curve of relative equilibria off the axis `j = 0`. -/
theorem mem_sphericalPendulumTurningPointDomain_of_le_one {r t : ℝ} (hr : 0 < r) (hr₂ : r ≤ 1)
    (ht : sin t ≠ 0) : (1 + r * cos t, r * sin t) ∈ sphericalPendulumTurningPointDomain := by
  refine mem_sphericalPendulumTurningPointDomain_of_sq_lt (mul_ne_zero hr.ne' ht) ?_
  -- `2 (1 + r cos t) - r² sin² t = (1 + r cos t)² + 1 - r²`, and `cos t > -1` off the axis.
  have hc : 0 < 1 + cos t := by
    rcases (neg_one_le_cos t).lt_or_eq with hc | hc
    · linarith
    · exact absurd (by linear_combination sin_sq_add_cos_sq t + (cos t - 1) * hc)
        (pow_ne_zero 2 ht)
  have hrc : 0 < r * (1 + cos t) := mul_pos hr hc
  have key : 2 * (1 + r * cos t) - (r * sin t) ^ 2 = (1 + r * cos t) ^ 2 + (1 - r ^ 2) := by
    linear_combination -r ^ 2 * sin_sq_add_cos_sq t
  nlinarith [mul_pos hrc (by linarith : 0 < 2 - r + r * cos t)]

/-- The counterclockwise circles of radius `0 < r ≤ 1` about the focus–focus value `(1, 0)`
run above the curve of relative equilibria off the axis `j = 0`
(`TauCeti.mem_sphericalPendulumTurningPointDomain_of_le_one`), so a continuous lift `L` of the
rotation angle along such a circle satisfies `L(2π) - L(0) = -2π`
(`TauCeti.sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle`). -/
theorem sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle_of_le_one {r : ℝ}
    (hr : 0 < r) (hr₂ : r ≤ 1) {L : ℝ → ℝ} (hL : ContinuousOn L (Icc 0 (2 * π)))
    (hLΘ : ∀ t ∈ Icc 0 (2 * π), sin t ≠ 0 →
      (L t : Real.Angle) = sphericalPendulumRotationAngle (1 + r * cos t) (r * sin t)) :
    L (2 * π) - L 0 = -(2 * π) :=
  sub_eq_neg_two_mul_pi_of_coe_eq_sphericalPendulumRotationAngle hr
    (fun _ ht ↦ mem_sphericalPendulumTurningPointDomain_of_le_one hr hr₂ ht) hL hLΘ

end TauCeti
