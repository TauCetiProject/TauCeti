/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum
public import TauCeti.Analysis.SpecialFunctions.Integrals.ArctanSqrt
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
almost `π`. Accordingly the rotation angle has the one-sided limits
* `Θ(h, j) → ±π` as `j → 0±` for `-1 < h < 1`
  (`TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one`,
  `TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsLT_of_lt_one`);
* `Θ(h, j) → ±2π` as `j → 0±` for `h > 1`
  (`TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsGT_of_one_lt`,
  `TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsLT_of_one_lt`),

while `Θ(h, 0) = 0`. These one-sided limits are the input to the classical computation of the
Hamiltonian monodromy of the pendulum around the focus–focus value `(1, 0)` of `F`.

## Implementation notes

The proof splits `(-1, 1)` at heights close to the zeros of `f(z) = 2 (h - z) (1 - z²)`. Near the
south pole `z = -1`, where `f` has a simple zero with `f' > 0`, the integrand is
`ψ f' j / (f √(f - j²))` with `ψ = 4 (h - z) / f'` continuous, and this contributes
`π ψ(-1) = π` in the limit by the concentration lemma
`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq`. Near the upper zero `e` of `f`, where
`f' < 0`, the reflection `z ↦ -z` reduces to the same lemma with `ψ = 4 (h - z) / (-f')`: at the
north pole `e = 1`, for `h > 1`, this contributes `π ψ(1) = π`, while at the turning point `e = h`
of the oscillations, for `-1 < h < 1`, it contributes `π ψ(h) = 0`. Away from the zeros of `f` the
integrand is `O(j)` uniformly.

## Main declarations

* `TauCeti.sphericalPendulumRotationAngle`: the rotation angle `Θ(h, j)`.
* `TauCeti.sphericalPendulumRotationAngle_eq_setIntegral`: `Θ(h, j)` as an integral over the
  heights of the fibre `F⁻¹(h, j)`.
* `TauCeti.sphericalPendulumRotationAngle_neg_right`: `Θ(h, -j) = -Θ(h, j)`.
* `TauCeti.tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one` and its three companions: the
  one-sided limits of `Θ(h, j)` as `j → 0`.

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
`TauCeti.tendsto_integral_mul_mul_div_mul_sqrt_sub_sq`. -/
private theorem two_mul_div_mul_sqrt_eq {u v j d : ℝ} (hd : d ≠ 0) :
    2 * (j / (v * √(2 * u * v - j ^ 2))) =
      4 * u / d * (d * j / (2 * u * v * √(2 * u * v - j ^ 2))) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [Real.sqrt_eq_zero'.2 (neg_nonpos.2 (sq_nonneg j))]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rcases eq_or_ne √(2 * u * v - j ^ 2) 0 with hs | hs
  · simp [hs]
  field_simp
  ring

/-- **The contribution of a simple zero.** Let `f(z) = 2 (h - σ z) (1 - z²)` vanish at `p` and
have positive derivative on `[p, q]`. The integral of `2 j / ((1 - z²) √(f(z) - j²))` over `[p, q]`
tends to `π ψ(p)` as `j → 0⁺`, where `ψ = 4 (h - σ z) / f'`. -/
private theorem tendsto_integral_of_hasDerivAt_pos {h σ p q : ℝ} (hpq : p < q)
    (hp : 2 * (h - σ * p) * (1 - p ^ 2) = 0)
    (hd : ∀ z ∈ Icc p q, 0 < 6 * σ * z ^ 2 - 4 * h * z - 2 * σ) :
    (∀ j, 0 < j → IntervalIntegrable
      (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - σ * z) * (1 - z ^ 2) - j ^ 2)))) volume p q) ∧
    Tendsto (fun j ↦ ∫ z in p..q,
        2 * (j / ((1 - z ^ 2) * √(2 * (h - σ * z) * (1 - z ^ 2) - j ^ 2))))
      (𝓝[>] 0) (𝓝 (π * (4 * (h - σ * p) / (6 * σ * p ^ 2 - 4 * h * p - 2 * σ)))) := by
  have hf : ContinuousOn (fun z ↦ 2 * (h - σ * z) * (1 - z ^ 2)) (Icc p q) := by fun_prop
  have hderiv : ∀ z ∈ Ioo p q, HasDerivAt (fun z ↦ 2 * (h - σ * z) * (1 - z ^ 2))
      (6 * σ * z ^ 2 - 4 * h * z - 2 * σ) z := fun z _ ↦
    hasDerivAt_two_mul_sub_mul_mul_one_sub_sq h σ z
  have hpos : ∀ z ∈ Ioo p q, 0 < 6 * σ * z ^ 2 - 4 * h * z - 2 * σ := fun z hz ↦
    hd z (Ioo_subset_Icc_self hz)
  have hψ : ContinuousOn (fun z ↦ 4 * (h - σ * z) / (6 * σ * z ^ 2 - 4 * h * z - 2 * σ))
      (Icc p q) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz ↦ (hd z hz).ne'
  have heq : ∀ j, EqOn
      (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - σ * z) * (1 - z ^ 2) - j ^ 2))))
      (fun z ↦ 4 * (h - σ * z) / (6 * σ * z ^ 2 - 4 * h * z - 2 * σ) *
        ((6 * σ * z ^ 2 - 4 * h * z - 2 * σ) * j /
          (2 * (h - σ * z) * (1 - z ^ 2) * √(2 * (h - σ * z) * (1 - z ^ 2) - j ^ 2))))
      (uIcc p q) := fun j z hz ↦ by
    rw [uIcc_of_le hpq.le] at hz
    exact two_mul_div_mul_sqrt_eq (hd z hz).ne'
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · have hint := intervalIntegrable_mul_div_mul_sqrt_sub_sq hf hp hderiv hpos hj
      ⟨hpq.le, le_rfl⟩
    rw [intervalIntegrable_congr ((heq j).mono Ioc_subset_Icc_self)]
    exact hint.continuousOn_mul (by rwa [uIcc_of_le hpq.le])
  · refine (tendsto_integral_mul_mul_div_mul_sqrt_sub_sq hf hp hderiv hpos hpq hψ).congr fun j ↦ ?_
    exact (intervalIntegral.integral_congr (heq j)).symm

/-- **The regular part.** On an interval of heights where `1 - z²` and `h - z` are positive, the
integral of `2 j / ((1 - z²) √(2 (h - z) (1 - z²) - j²))` is eventually defined and tends to `0`
as `j → 0⁺`. -/
private theorem tendsto_integral_of_pos {h p q : ℝ} (hpq : p ≤ q)
    (hpos : ∀ z ∈ Icc p q, 0 < 1 - z ^ 2 ∧ 0 < h - z) :
    (∀ᶠ j in 𝓝[>] 0, IntervalIntegrable
      (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) volume p q) ∧
    Tendsto (fun j ↦ ∫ z in p..q,
        2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨z₁, hz₁, hmin₁⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq)
    (by fun_prop : Continuous fun z : ℝ ↦ 2 * (h - z) * (1 - z ^ 2)).continuousOn
  obtain ⟨z₂, hz₂, hmin₂⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpq)
    (by fun_prop : Continuous fun z : ℝ ↦ 1 - z ^ 2).continuousOn
  set m := 2 * (h - z₁) * (1 - z₁ ^ 2)
  set n := 1 - z₂ ^ 2
  have hm0 : 0 < m := mul_pos (mul_pos two_pos (hpos z₁ hz₁).2) (hpos z₁ hz₁).1
  have hn0 : 0 < n := (hpos z₂ hz₂).1
  have hsmall : ∀ᶠ j in 𝓝[>] (0 : ℝ), 0 < j ∧ j ^ 2 < m / 2 := by
    have : Tendsto (fun j : ℝ ↦ j ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, this.eventually (gt_mem_nhds (half_pos hm0))]
      with j hj hj2 using ⟨hj, hj2⟩
  -- For small `j > 0` the denominator is at least `n √(m / 2)` on `[p, q]`.
  have hden : ∀ j, j ^ 2 < m / 2 → ∀ z ∈ Icc p q,
      n * √(m / 2) ≤ (1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2) := by
    intro j hj z hz
    have h₁ : m ≤ 2 * (h - z) * (1 - z ^ 2) := hmin₁ hz
    gcongr
    · exact (hpos z hz).1.le
    · exact hmin₂ hz
    · linarith
  have hden_pos : 0 < n * √(m / 2) := by positivity
  refine ⟨?_, ?_⟩
  · filter_upwards [hsmall] with j ⟨hj, hj2⟩
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hpq]
    exact continuousOn_const.mul (continuousOn_const.div (by fun_prop) fun z hz ↦
      (hden_pos.trans_le (hden j hj2 z hz)).ne')
  · have hbound : Tendsto (fun j : ℝ ↦ 2 * j / (n * √(m / 2)) * |q - p|) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun j : ℝ ↦ 2 * j / (n * √(m / 2)) * |q - p| := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hsmall] with j ⟨hj, hj2⟩
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun z hz ↦ ?_
    have hz' : z ∈ Icc p q := by
      rw [uIoc_of_le hpq] at hz
      exact Ioc_subset_Icc_self hz
    have hden_z := hden_pos.trans_le (hden j hj2 z hz')
    rw [Real.norm_of_nonneg (mul_nonneg two_pos.le (div_nonneg hj.le hden_z.le)),
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) hden_pos (hden j hj2 z hz')

/-- **The contribution of a simple zero at the right end.** Let `f(z) = 2 (h - z) (1 - z²)`
vanish at `q` and have negative derivative on `[p, q]`. The integral of
`2 j / ((1 - z²) √(f(z) - j²))` over `[p, q]` tends to `π ψ(q)` as `j → 0⁺`, where
`ψ = 4 (h - z) / (-f')`. This is `tendsto_integral_of_hasDerivAt_pos` after the reflection
`z ↦ -z`. -/
private theorem tendsto_integral_of_hasDerivAt_neg {h p q : ℝ} (hpq : p < q)
    (hq : 2 * (h - q) * (1 - q ^ 2) = 0) (hd : ∀ z ∈ Icc p q, 6 * z ^ 2 - 4 * h * z - 2 < 0) :
    (∀ j, 0 < j → IntervalIntegrable
      (fun z ↦ 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2)))) volume p q) ∧
    Tendsto (fun j ↦ ∫ z in p..q, 2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))))
      (𝓝[>] 0) (𝓝 (π * (4 * (h - q) / (2 + 4 * h * q - 6 * q ^ 2)))) := by
  obtain ⟨hint, hlim⟩ := tendsto_integral_of_hasDerivAt_pos (h := h) (σ := -1)
    (neg_lt_neg hpq) (by linear_combination hq) fun y hy ↦ by
      linarith [hd (-y) ⟨le_neg_of_le_neg hy.2, neg_le_of_neg_le hy.1⟩]
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [IntervalIntegrable.iff_comp_neg]
    exact (hint j hj).symm.congr fun y _ ↦ by simp
  · rw [show h - -1 * -q = h - q by ring,
      show (6 : ℝ) * -1 * (-q) ^ 2 - 4 * h * -q - 2 * -1 = 2 + 4 * h * q - 6 * q ^ 2 by ring]
      at hlim
    refine hlim.congr fun j ↦ ?_
    rw [← intervalIntegral.integral_comp_neg]
    simp

/-- The integrand vanishes at every height `z` with `2 (h - z) (1 - z²) ≤ 0`. -/
private theorem two_mul_div_mul_sqrt_eq_zero {h j z : ℝ} (hz : 2 * (h - z) * (1 - z ^ 2) ≤ 0) :
    2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))) = 0 := by
  rw [Real.sqrt_eq_zero'.2 (by nlinarith [sq_nonneg j]), mul_zero, div_zero, mul_zero]

/-- The rotation angle near `j = 0⁺`, for an energy `h > -1` and a height `e ∈ (-1, 1]` with
`e ≤ h` at which `f(z) = 2 (h - z) (1 - z²)` vanishes with negative derivative. The pole `z = -1`
contributes `π`, the zero `z = e` contributes `π ψ(e)` with `ψ = 4 (h - z) / (-f')`, and the
integrand vanishes on `[e, 1]`. -/
private theorem tendsto_sphericalPendulumRotationAngle_nhdsGT {h e : ℝ} (hh : -1 < h)
    (he : -1 < e) (he1 : e ≤ 1) (heh : e ≤ h) (hfe : (h - e) * (1 - e ^ 2) = 0)
    (hde : 6 * e ^ 2 - 4 * h * e - 2 < 0) :
    Tendsto (sphericalPendulumRotationAngle h) (𝓝[>] 0)
      (𝓝 (π + π * (4 * (h - e) / (2 + 4 * h * e - 6 * e ^ 2)))) := by
  set I : ℝ → ℝ → ℝ := fun j z ↦
    2 * (j / ((1 - z ^ 2) * √(2 * (h - z) * (1 - z ^ 2) - j ^ 2))) with hI
  have hf' : Continuous fun z : ℝ ↦ 6 * z ^ 2 - 4 * h * z - 2 := by fun_prop
  -- Choose `-1 < a < c < e` such that `f' = 6 z² - 4 h z - 2` is positive on `[-1, a]` and
  -- negative on `[c, e]`.
  obtain ⟨a, ha₁, ha⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 (nhdsWithin_le_nhds
    (inter_mem (hf'.continuousAt.eventually (lt_mem_nhds (by linarith : (0 : ℝ) <
      6 * (-1) ^ 2 - 4 * h * (-1) - 2))) (Iio_mem_nhds he)))
  have ha₂ : a < e := (ha ⟨ha₁.le, le_rfl⟩).2
  obtain ⟨c, hc₂, hc⟩ := mem_nhdsLE_iff_exists_Icc_subset.1 (nhdsWithin_le_nhds
    (inter_mem (hf'.continuousAt.eventually (gt_mem_nhds hde)) (Ioi_mem_nhds ha₂)))
  have hc₁ : a < c := (hc ⟨le_rfl, hc₂.le⟩).2
  -- The pole at `-1`, the regular part `[a, c]` and the zero at `e`.
  obtain ⟨hint₁, hlim₁⟩ := tendsto_integral_of_hasDerivAt_pos (h := h) (σ := 1) ha₁
    (by norm_num) fun z hz ↦ by simpa using (ha hz).1
  obtain ⟨hint₂, hlim₂⟩ := tendsto_integral_of_pos (h := h) hc₁.le fun z hz ↦
    ⟨by nlinarith [hz.1, hz.2], by linarith [hz.2]⟩
  obtain ⟨hint₃, hlim₃⟩ := tendsto_integral_of_hasDerivAt_neg (h := h) hc₂
    (by linear_combination 2 * hfe) fun z hz ↦ (hc hz).1
  simp only [one_mul] at hint₁ hlim₁
  -- The integrand vanishes on `[e, 1]`.
  have hzero : ∀ j, EqOn (I j) 0 (uIcc e 1) := fun j z hz ↦ by
    rw [uIcc_of_le he1] at hz
    refine two_mul_div_mul_sqrt_eq_zero ?_
    rcases mul_eq_zero.1 hfe with h' | h'
    · have h₁ : h - z ≤ 0 := by linarith [hz.1]
      have h₂ : 0 ≤ 1 - z ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hz.2) (by linarith [hz.1] : (0 : ℝ) ≤ 1 + z)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg h₁ h₂]
    · obtain rfl : z = 1 := le_antisymm hz.2 (by nlinarith [hz.1])
      norm_num
  have hsplit : ∀ᶠ j in 𝓝[>] 0, sphericalPendulumRotationAngle h j =
      (∫ z in (-1)..a, I j z) + (∫ z in a..c, I j z) + ∫ z in c..e, I j z := by
    filter_upwards [self_mem_nhdsWithin, hint₂] with j hj hint₂j
    have hint₄j : IntervalIntegrable (I j) volume e 1 :=
      (intervalIntegrable_congr ((hzero j).mono Ioc_subset_Icc_self)).2 intervalIntegrable_const
    rw [sphericalPendulumRotationAngle_def, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add_adjacent_intervals
        (((hint₁ j hj).trans hint₂j).trans (hint₃ j hj)) hint₄j,
      intervalIntegral.integral_congr (hzero j),
      ← intervalIntegral.integral_add_adjacent_intervals ((hint₁ j hj).trans hint₂j) (hint₃ j hj),
      ← intervalIntegral.integral_add_adjacent_intervals (hint₁ j hj) hint₂j]
    simp [hI]
  refine Tendsto.congr' (EventuallyEq.symm hsplit) ?_
  convert (hlim₁.add hlim₂).add hlim₃ using 2
  rw [show (6 : ℝ) * 1 * (-1) ^ 2 - 4 * h * -1 - 2 * 1 = 4 * (h - -1) by ring,
    div_self (by linarith)]
  ring

/-- For `-1 < h < 1`, the rotation angle tends to `π` as `j → 0⁺`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one {h : ℝ} (h₁ : -1 < h)
    (h₂ : h < 1) : Tendsto (sphericalPendulumRotationAngle h) (𝓝[>] 0) (𝓝 π) := by
  have := tendsto_sphericalPendulumRotationAngle_nhdsGT h₁ h₁ h₂.le le_rfl (by ring)
    (by nlinarith)
  simpa using this

/-- For `h > 1`, the rotation angle tends to `2π` as `j → 0⁺`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsGT_of_one_lt {h : ℝ} (h₁ : 1 < h) :
    Tendsto (sphericalPendulumRotationAngle h) (𝓝[>] 0) (𝓝 (2 * π)) := by
  have := tendsto_sphericalPendulumRotationAngle_nhdsGT (e := 1) (by linarith) (by norm_num)
    le_rfl h₁.le (by ring) (by linarith)
  rwa [show (2 : ℝ) + 4 * h * 1 - 6 * 1 ^ 2 = 4 * (h - 1) by ring, div_self (by linarith),
    mul_one, ← two_mul] at this

/-- For `-1 < h < 1`, the rotation angle tends to `-π` as `j → 0⁻`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsLT_of_lt_one {h : ℝ} (h₁ : -1 < h)
    (h₂ : h < 1) : Tendsto (sphericalPendulumRotationAngle h) (𝓝[<] 0) (𝓝 (-π)) := by
  have := ((tendsto_sphericalPendulumRotationAngle_nhdsGT_of_lt_one h₁ h₂).comp
    (by simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))).neg
  simpa [Function.comp_def, sphericalPendulumRotationAngle_neg_right] using this

/-- For `h > 1`, the rotation angle tends to `-2π` as `j → 0⁻`. -/
theorem tendsto_sphericalPendulumRotationAngle_nhdsLT_of_one_lt {h : ℝ} (h₁ : 1 < h) :
    Tendsto (sphericalPendulumRotationAngle h) (𝓝[<] 0) (𝓝 (-(2 * π))) := by
  have := ((tendsto_sphericalPendulumRotationAngle_nhdsGT_of_one_lt h₁).comp
    (by simpa using (tendsto_neg_nhdsLT (a := (0 : ℝ))))).neg
  simpa [Function.comp_def, sphericalPendulumRotationAngle_neg_right] using this

end TauCeti
