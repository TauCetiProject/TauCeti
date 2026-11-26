/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Distribution
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Newtonian potential of a ball

Let `Gₙ = TauCeti.newtonianKernel n` be the Newtonian kernel of `ℝⁿ`, `n = 1` or `n ≥ 3`. This
file computes the Newtonian potential of a uniform ball,

`v(x) = ∫_{B(c, R)} Gₙ(x - y) dy`,

the potential `Gₙ ⋆ 1_{B(c, R)}` of the indicator of the ball. Inside the ball it is the quadratic

`v(x) = (n R² - (n - 2) ‖x - c‖²) / (2 n (n - 2))`

(`TauCeti.setIntegral_ball_newtonianKernel_sub_of_norm_sub_le`), so `-Δv = 1` there
(`TauCeti.laplacian_setIntegral_ball_newtonianKernel_sub`), and on the sphere `‖x - c‖ = R` it
takes the constant value `R² / (n (n - 2))`. Outside the ball it is the potential of a point mass
`|B(c, R)|` at the centre, `v(x) = |B(c, R)| Gₙ(x - c)`
(`TauCeti.setIntegral_ball_newtonianKernel_sub_of_le_norm_sub`). For the unit ball of `ℝ³` this
is `v(x) = (3 - ‖x‖²) / 6` inside, with the value `1 / 3` on the unit sphere and `1 / (3 ‖x‖)`
outside; in dimension one it is `-(1 + x²) / 2` on `[-1, 1]`, the integral of `-|x - y| / 2`.

These are **Newton's theorems** on the attraction of spherical shells. For the uniform measure on
the sphere of radius `s` about the origin, parametrized by the unit sphere with the surface measure
`μ.toSphere`, the potential at a point `x` outside the sphere is that of the total mass placed at
the centre (`TauCeti.integral_toSphere_newtonianKernel_sub_smul_of_lt_norm`), and inside the sphere
it is constant, equal to its value at the centre
(`TauCeti.integral_toSphere_newtonianKernel_sub_smul_of_norm_lt`). The ball formulas follow by
integrating over the shells in polar coordinates
(`TauCeti.setIntegral_ball_zero_eq_integral_Ioo`).

## The argument

Outside the sphere, `y ↦ Gₙ(x - y)` is harmonic on a neighbourhood of the closed ball of radius
`s`, and the mean-value property on spheres
(`InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`) evaluates its sphere integral. Inside the
sphere, write `x = ρ η` with `ρ = ‖x‖ < s` and `η` a unit vector. For unit vectors `η` and `θ` the
distances `‖ρ η - s θ‖` and `‖s η - ρ θ‖` agree, as both squares are `ρ² - 2 ρ s ⟪η, θ⟫ + s²`.
So the sphere integral of radius `s` of `y ↦ Gₙ(x - y)` is the sphere integral of radius `ρ` of
`y ↦ Gₙ(s η - y)`, which is harmonic on a neighbourhood of the closed ball of radius `ρ`; the
mean-value property gives `|S| Gₙ(s η)`, which is also the value at the centre.

## Main declarations

* `TauCeti.integral_toSphere_newtonianKernel_sub_smul_of_lt_norm`,
  `TauCeti.integral_toSphere_newtonianKernel_sub_smul_of_norm_lt`: Newton's theorems for a
  spherical shell, outside and inside.
* `TauCeti.setIntegral_ball_newtonianKernel_sub_of_le_norm_sub`: outside a ball its Newtonian
  potential is that of a point mass at the centre.
* `TauCeti.setIntegral_ball_newtonianKernel_sub_of_norm_sub_le`: the Newtonian potential of a ball
  on the closed ball.
* `TauCeti.laplacian_setIntegral_ball_newtonianKernel_sub`: it solves `-Δv = 1` in the ball.

## References

* I. Newton, *Philosophiæ Naturalis Principia Mathematica*, Book I, Section XII, Propositions 70
  and 71.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., Theorem 9.7 (Newton's theorem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 2.2.1.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set

variable {n : ℕ}

/-! ### Newton's theorems for a spherical shell -/

section Shell

variable {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

/-- **Newton's theorem outside a spherical shell.** For `0 ≤ s < ‖x‖`, the Newtonian potential at
`x` of the uniform measure on the sphere of radius `s` about the origin, parametrized by the unit
sphere with the surface measure `μ.toSphere`, is that of its total mass placed at the origin:
`∫_S Gₙ(x - s θ) dθ = |S| Gₙ(x)`. -/
theorem integral_toSphere_newtonianKernel_sub_smul_of_lt_norm {x : EuclideanSpace ℝ (Fin n)}
    {s : ℝ} (hs : 0 ≤ s) (hsx : s < ‖x‖) :
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, newtonianKernel n (x - s • (θ : _))
        ∂μ.toSphere = μ.toSphere.real univ * newtonianKernel n x := by
  have hu : HarmonicOnNhd (fun y ↦ newtonianKernel n (y - x)) (closedBall 0 s) := fun y hy ↦
    harmonicOnNhd_newtonianKernel_sub n x y fun hyx : y = x ↦ by
      rw [hyx, mem_closedBall_zero_iff] at hy
      exact hy.not_gt hsx
  simpa [newtonianKernel_sub_comm n _ x, newtonianKernel_eq_of_norm_eq n (norm_neg x)] using
    hu.integral_toSphere_eq (μ := μ) (x₀ := 0) hs

/-- **Newton's theorem inside a spherical shell.** For `‖x‖ < s`, the Newtonian potential at `x`
of the uniform measure on the sphere of radius `s` about the origin, parametrized by the unit
sphere with the surface measure `μ.toSphere`, does not depend on `x`: it equals its value at the
centre, `∫_S Gₙ(x - s θ) dθ = ∫_S Gₙ(s θ) dθ`. -/
theorem integral_toSphere_newtonianKernel_sub_smul_of_norm_lt {x : EuclideanSpace ℝ (Fin n)}
    {s : ℝ} (hxs : ‖x‖ < s) :
    ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, newtonianKernel n (x - s • (θ : _))
        ∂μ.toSphere =
      ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, newtonianKernel n (s • (θ : _))
        ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hE | hE
  · have : IsEmpty (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : EuclideanSpace ℝ (Fin n)) 0] using
        norm_eq_of_mem_sphere θ⟩
    simp [Measure.eq_zero_of_isEmpty]
  -- Write `x = ρ η` with `ρ = ‖x‖` and `η` a unit vector.
  obtain ⟨η, hη, hxη⟩ : ∃ η : EuclideanSpace ℝ (Fin n), ‖η‖ = 1 ∧ x = ‖x‖ • η := by
    rcases eq_or_ne x 0 with rfl | hx
    · obtain ⟨η, hη⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) zero_le_one
      exact ⟨η, hη, by simp⟩
    · exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx], by simp [smul_smul, hx]⟩
  have hs : 0 < s := (norm_nonneg x).trans_lt hxs
  -- For unit vectors `η` and `θ`, `‖ρ η - s θ‖ = ‖s η - ρ θ‖`.
  have hswap : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      newtonianKernel n (x - s • (θ : _)) = newtonianKernel n ((0 + ‖x‖ • (θ : _)) - s • η) := by
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere θ
    refine newtonianKernel_eq_of_norm_eq n ?_
    rw [zero_add, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real,
      norm_sub_sq_real]
    conv_lhs => rw [hxη]
    simp only [norm_smul, norm_norm, hη, hθ, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm η]
  have hu : HarmonicOnNhd (fun y ↦ newtonianKernel n (y - s • η)) (closedBall 0 ‖x‖) :=
    fun y hy ↦ harmonicOnNhd_newtonianKernel_sub n (s • η) y fun hyη : y = s • η ↦ by
      rw [hyη, mem_closedBall_zero_iff, norm_smul, hη, mul_one, Real.norm_of_nonneg hs.le] at hy
      exact hy.not_gt hxs
  have hconst : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      newtonianKernel n (s • (θ : _)) = newtonianKernel n (0 - s • η) := fun θ ↦
    newtonianKernel_eq_of_norm_eq n <| by
      rw [zero_sub, norm_neg, norm_smul, norm_smul, hη, norm_eq_of_mem_sphere θ]
  simp_rw [hswap, hconst, hu.integral_toSphere_eq (μ := μ) (norm_nonneg x), integral_const]

end Shell

/-! ### The Newtonian potential of a ball -/

section Ball

/-- The kernel `y ↦ Gₙ(x - y)` with pole `x` is integrable on every ball. -/
private theorem integrableOn_ball_newtonianKernel_sub (x c : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    IntegrableOn (fun y ↦ newtonianKernel n (x - y)) (ball c R) := by
  have h := (locallyIntegrable_newtonianKernel n).integrableOn_isCompact
    (isCompact_closedBall (x - c) R)
  refine (((volume.measurePreserving_sub_left x).integrableOn_comp_preimage
    (MeasurableEquiv.subLeft x).measurableEmbedding).2 h).mono_set fun y hy ↦ ?_
  rw [mem_preimage, mem_closedBall, dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm]
  exact (mem_ball'.1 hy).le

/-- The Newtonian potential of a ball centred at the origin, in polar coordinates: the integral
over the radii `s ∈ (r, R)` of the potentials of the spheres of radius `s`. -/
private theorem setIntegral_ball_sdiff_closedBall_newtonianKernel_sub
    [Nontrivial (EuclideanSpace ℝ (Fin n))] (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r)
    (R : ℝ) :
    ∫ y in ball (0 : EuclideanSpace ℝ (Fin n)) R \ closedBall 0 r, newtonianKernel n (x - y) =
      ∫ s in Ioo r R, s ^ (n - 1) * ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        newtonianKernel n (x - s • (θ : _)) ∂volume.toSphere := by
  simpa [finrank_euclideanSpace_fin] using setIntegral_ball_sdiff_closedBall_zero_eq_integral_Ioo
    (μ := volume) hr ((integrableOn_ball_newtonianKernel_sub x 0 R).mono_set sdiff_subset)

/-- **The Newtonian potential of a ball, outside the ball.** At a point `x` with
`R ≤ ‖x - c‖`, the Newtonian potential of the ball `B(c, R)` is that of its total mass placed at
the centre: `∫_{B(c, R)} Gₙ(x - y) dy = |B(c, R)| Gₙ(x - c)`. -/
theorem setIntegral_ball_newtonianKernel_sub_of_le_norm_sub {x c : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : R ≤ ‖x - c‖) :
    ∫ y in ball c R, newtonianKernel n (x - y) =
      volume.real (ball c R) * newtonianKernel n (x - c) := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hE | hE
  · simp [fun y : EuclideanSpace ℝ (Fin n) ↦ Subsingleton.elim (x - y) 0]
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add, Measure.addHaar_real_ball_center]
  simp_rw [sub_add_eq_sub_sub_swap]
  rw [setIntegral_ball_zero_eq_integral_Ioo (integrableOn_ball_newtonianKernel_sub (x - c) 0 R),
    setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ by
      rw [integral_toSphere_newtonianKernel_sub_smul_of_lt_norm hs.1.le (hs.2.trans_le hR)],
    integral_smul_const, smul_eq_mul, ← mul_assoc, integral_Ioo_pow_mul_toSphere_real_univ]

/-- The Newtonian kernel at `x` times the volume `‖x‖ⁿ |B(0, 1)|` of the ball through `x` is
`‖x‖² / (n (n - 2))`: the potential at `x` of the ball `B(0, ‖x‖)`, whose mass is placed at the
centre. -/
theorem pow_norm_mul_measureReal_ball_mul_newtonianKernel (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * newtonianKernel n x =
      ‖x‖ ^ 2 / (n * (n - 2)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 2 with rfl | hn2
  · norm_num
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hn2' : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn2)
  have hω := (volume_real_unitBall_pos n).ne'
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx, zero_pow hn0, zero_pow two_ne_zero, zero_mul, zero_mul, zero_div]
  rw [newtonianKernel_def]
  calc ‖x‖ ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ((n * (n - 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
          ‖x‖ ^ (2 - (n : ℝ)))
      = (‖x‖ ^ n * ‖x‖ ^ (2 - (n : ℝ))) / (n * (n - 2)) := by field_simp
    _ = ‖x‖ ^ 2 / (n * (n - 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx]
      norm_num

/-- The surface measure of the unit sphere times the Newtonian kernel at radius `s > 0`, weighted
by the radial Jacobian `s ^ (n - 1)`, is `s / (n - 2)`: the integrand of the potential of a ball
at its centre. -/
private theorem pow_mul_integral_toSphere_newtonianKernel_smul (hn : n ≠ 0) {s : ℝ} (hs : 0 < s) :
    s ^ (n - 1) * ∫ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        newtonianKernel n (s • (θ : _)) ∂volume.toSphere = s / ((n : ℝ) - 2) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsθ : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ‖s • (θ : EuclideanSpace ℝ (Fin n))‖ = s := fun θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
  have hω := (volume_real_unitBall_pos n).ne'
  have hθ : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, newtonianKernel n (s • (θ : _)) =
      s ^ 2 / (n * (n - 2)) / (s ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    fun θ ↦ by
      rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hs.ne') hω), mul_comm]
      simpa [hsθ θ] using pow_norm_mul_measureReal_ball_mul_newtonianKernel
        (s • (θ : EuclideanSpace ℝ (Fin n)))
  have hpow : s ^ n = s ^ (n - 1) * s := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
  simp_rw [hθ, integral_const, smul_eq_mul, Measure.toSphere_real_apply_univ,
    finrank_euclideanSpace_fin, hpow]
  rcases eq_or_ne ((n : ℝ) - 2) 0 with h2 | h2
  · simp [h2]
  field_simp

/-- **The Newtonian potential of a ball, inside the ball.** For `n ≠ 2` and a point `x` of the
closed ball `‖x - c‖ ≤ R`, the Newtonian potential of the ball `B(c, R)` is

`∫_{B(c, R)} Gₙ(x - y) dy = R² / (n (n - 2)) + (R² - ‖x - c‖²) / (2 n)`.

The first term is the constant value of the potential on the sphere `‖x - c‖ = R`, the second is
the torsion function of the ball, which solves `-Δu = 1` with zero boundary values. For the unit
ball of `ℝ³` the potential is `(3 - ‖x‖²) / 6`; in dimension one it is `-(1 + x²) / 2`. -/
theorem setIntegral_ball_newtonianKernel_sub_of_norm_sub_le (hn : n ≠ 2)
    {x c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hx : ‖x - c‖ ≤ R) :
    ∫ y in ball c R, newtonianKernel n (x - y) =
      R ^ 2 / (n * (n - 2)) + (R ^ 2 - ‖x - c‖ ^ 2) / (2 * n) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have : NeZero n := ⟨hn0⟩
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hn2 : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add]
  simp_rw [sub_add_eq_sub_sub_swap]
  set z := x - c
  -- The potential of the inner ball `B(0, ‖z‖)`, on whose sphere `z` lies, is that of a point mass.
  have hinner : ∫ y in ball (0 : EuclideanSpace ℝ (Fin n)) ‖z‖, newtonianKernel n (z - y) =
      ‖z‖ ^ 2 / (n * (n - 2)) := by
    rw [setIntegral_ball_newtonianKernel_sub_of_le_norm_sub (by rw [sub_zero]), sub_zero,
      Measure.addHaar_real_ball _ _ (norm_nonneg z), finrank_euclideanSpace_fin,
      pow_norm_mul_measureReal_ball_mul_newtonianKernel]
  rcases hx.eq_or_lt with hzR | hzR
  · rw [← hzR, hinner, sub_self, zero_div, add_zero]
  -- Split the ball into the closed inner ball and the shell `‖z‖ < ‖y‖ < R`.
  rw [← union_sdiff_cancel (closedBall_subset_ball hzR),
    setIntegral_union disjoint_sdiff_right (measurableSet_ball.diff measurableSet_closedBall)
      (integrableOn_ball_newtonianKernel_sub z 0 R |>.mono_set (closedBall_subset_ball hzR))
      (integrableOn_ball_newtonianKernel_sub z 0 R |>.mono_set sdiff_subset),
    setIntegral_congr_set (Measure.addHaar_closedBall_ae_eq_ball volume 0 ‖z‖), hinner,
    setIntegral_ball_sdiff_closedBall_newtonianKernel_sub z (norm_nonneg z) R,
    setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ by
      rw [integral_toSphere_newtonianKernel_sub_smul_of_norm_lt hs.1,
        pow_mul_integral_toSphere_newtonianKernel_smul hn0 ((norm_nonneg z).trans_lt hs.1)],
    integral_div, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hzR.le,
    integral_id]
  field_simp
  ring

/-- **The Newtonian potential of a ball solves Poisson's equation in the ball.** For `n = 1` or
`n ≥ 3`, the Newtonian potential `v(x) = ∫_{B(c, R)} Gₙ(x - y) dy` of the ball `B(c, R)` satisfies
`-Δv = 1` at every point of the ball. -/
theorem laplacian_setIntegral_ball_newtonianKernel_sub (hn : n ≠ 2) (hn0 : n ≠ 0)
    {x c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hx : x ∈ ball c R) :
    Δ (fun x ↦ ∫ y in ball c R, newtonianKernel n (x - y)) x = -1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  -- In the ball the potential is the quadratic `a + b ‖y - c‖²` with `b = -1 / (2 n)`.
  set a : ℝ := R ^ 2 / (n * (n - 2)) + R ^ 2 / (2 * n) with ha
  set b : ℝ := -(2 * (n : ℝ))⁻¹ with hb
  have hq : ContDiff ℝ 2 fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y - c‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hΔq : Δ (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y - c‖ ^ 2) x = 2 * n := by
    have h := congrFun (laplacian_comp_add_right (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ 2)
      (-c)) x
    simp only [← sub_eq_add_neg] at h
    rw [h, laplacian_norm_sq, finrank_euclideanSpace_fin]
  have heq : (fun x ↦ ∫ y in ball c R, newtonianKernel n (x - y)) =ᶠ[nhds x]
      fun y ↦ a + b * ‖y - c‖ ^ 2 :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy ↦ by
      dsimp only
      rw [setIntegral_ball_newtonianKernel_sub_of_norm_sub_le hn (mem_ball_iff_norm.1 hy).le, ha,
        hb]
      ring
  have hsmul : Δ (fun y : EuclideanSpace ℝ (Fin n) ↦ b * ‖y - c‖ ^ 2) x =
      b * Δ (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y - c‖ ^ 2) x :=
    laplacian_smul b hq.contDiffAt
  have hadd : Δ (fun y : EuclideanSpace ℝ (Fin n) ↦ a + b * ‖y - c‖ ^ 2) x =
      Δ (fun _ : EuclideanSpace ℝ (Fin n) ↦ a) x +
        Δ (fun y : EuclideanSpace ℝ (Fin n) ↦ b * ‖y - c‖ ^ 2) x :=
    contDiffAt_const.laplacian_add (contDiffAt_const.mul hq.contDiffAt)
  rw [(laplacian_congr_nhds heq).eq_of_nhds, hadd, laplacian_const, Pi.zero_apply, zero_add,
    hsmul, hΔq, hb]
  field_simp

end Ball

end TauCeti
