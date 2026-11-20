/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Analysis.InnerProductSpace.NormPow
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The Newtonian kernel away from dimension two

For `n = 1` and `3 ≤ n`, this file defines the Newtonian kernel for the negative Laplacian on
`EuclideanSpace ℝ (Fin n)`:

`Gₙ(x) = (n (n - 2) ωₙ)⁻¹ ‖x‖²⁻ⁿ`,

where `ωₙ` is the volume of the Euclidean unit ball.  It proves the full Fréchet derivative
formula and the pointwise equation `Δ Gₙ = 0` away from the pole, together with translated
versions for a pole at an arbitrary point.  The dimension-one specialization is `-|x| / 2` and
the dimension-three specialization recovers the classical kernel `1 / (4π‖x‖)`.  The planar
kernel is the logarithmic one, `TauCeti.planarNewtonianKernel`.

The normalization and formulas follow Evans, *Partial Differential Equations*, Section 2.2.
The distributional identity `-Δ Gₙ = δ₀` is proved from the derivative formula here in
`TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.DistributionalLaplacian`.

## Main declarations

* `TauCeti.newtonianKernel`: the normalized kernel in dimension `n = 1` or `n ≥ 3`.
* `TauCeti.hasFDerivAt_newtonianKernel`: its derivative away from the origin.
* `TauCeti.norm_fderiv_newtonianKernel`: the `‖x‖ ^ (1 - n)` operator norm of that derivative.
* `TauCeti.laplacian_newtonianKernel`: the pointwise equation `Δ Gₙ = 0` away from the origin.
* `TauCeti.harmonicAt_newtonianKernel_sub`: harmonicity of the kernel with a translated pole.
* `TauCeti.newtonianKernel_one`, `TauCeti.newtonianKernel_three`: the familiar one- and
  three-dimensional formulas.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Topology

open scoped RealInnerProductSpace

/-- The Newtonian kernel for the negative Laplacian on `ℝⁿ`.

For `n = 1` and `3 ≤ n`, this normalization is the fundamental solution.  For `3 ≤ n` the
exponent `2 - n` is negative, and Lean's convention for a negative real power of zero makes the
kernel take the value zero at the pole.  In dimensions zero and two the normalizing constant is
`0⁻¹ = 0`, so the kernel vanishes identically.  Results that need a particular dimensional
regime state it as a hypothesis rather than carrying it in the definition. -/
def newtonianKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
    ‖x‖ ^ (2 - (n : ℝ))

/-- The defining formula for the Newtonian kernel.  The body of `TauCeti.newtonianKernel` is not
`@[expose]`d, so this is the form in which other modules reach the definition. -/
theorem newtonianKernel_def (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n x =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖x‖ ^ (2 - (n : ℝ)) := by
  rw [newtonianKernel]

/-- The totalized Newtonian kernel takes the value zero at its pole. -/
@[simp]
theorem newtonianKernel_zero (n : ℕ) :
    newtonianKernel n 0 = 0 := by
  rcases eq_or_ne n 2 with rfl | hn
  · norm_num [newtonianKernel]
  · have hexp : 2 - (n : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hn.symm)
    simp [newtonianKernel, Real.zero_rpow hexp]

/-- In dimension two the normalizing constant of the Newtonian kernel is `0⁻¹ = 0`, so the totalized
kernel `TauCeti.newtonianKernel 2` is the zero function. -/
@[simp]
theorem newtonianKernel_two : newtonianKernel 2 = 0 :=
  funext fun y ↦ by simp [newtonianKernel_def]

/-- In dimension zero the Euclidean space is a single point, the pole, so the totalized kernel
`TauCeti.newtonianKernel 0` is the zero function. -/
@[simp]
theorem newtonianKernel_dim_zero : newtonianKernel 0 = 0 :=
  funext fun x ↦ by rw [Subsingleton.elim x 0, newtonianKernel_zero, Pi.zero_apply]

/-- The Newtonian kernel is radial, hence invariant under orthogonal transformations. -/
@[simp]
theorem newtonianKernel_map_linearIsometryEquiv (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (e x) = newtonianKernel n x := by
  simp [newtonianKernel]

/-- The Newtonian kernel is symmetric under exchanging a point and its pole. -/
theorem newtonianKernel_sub_comm (n : ℕ) (x a : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (x - a) = newtonianKernel n (a - x) := by
  simp [newtonianKernel, norm_sub_rev]

/-- Real dilation scales the Newtonian kernel with radial homogeneity `2 - n`. -/
theorem newtonianKernel_smul (n : ℕ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (r • x) = ‖r‖ ^ (2 - (n : ℝ)) * newtonianKernel n x := by
  rw [newtonianKernel_def, newtonianKernel_def, norm_smul,
    Real.mul_rpow (norm_nonneg r) (norm_nonneg x)]
  ring

/-- The Euclidean unit ball has positive real volume in every dimension. -/
theorem volume_real_unitBall_pos (n : ℕ) :
    0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  exact ENNReal.toReal_pos
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
    measure_ball_ne_top

/-- Away from its pole, and outside dimension two, the Newtonian kernel does not vanish. -/
theorem newtonianKernel_ne_zero (n : ℕ) (hn : n ≠ 2) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    newtonianKernel n x ≠ 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; exact hx (Subsingleton.elim _ _))
  have hn2 : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hn)
  have hvol := (volume_real_unitBall_pos n).ne'
  rw [newtonianKernel_def]
  positivity

/-- Away from the pole, the normalized Newtonian kernel is strictly positive. -/
theorem newtonianKernel_pos (n : ℕ) (hn : 3 ≤ n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < newtonianKernel n x := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnsub : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  rw [newtonianKernel_def]
  exact mul_pos (inv_pos.mpr (mul_pos (mul_pos hnpos hnsub)
      (volume_real_unitBall_pos n)))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)

/-- The radial expression for the Newtonian kernel strictly decreases as the squared radius
increases, in every nondegenerate positive dimension. -/
theorem newtonianKernel_rpow_sq_lt (n : ℕ) (hn : n ≠ 2) (hn0 : 0 < n)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        b ^ ((2 - (n : ℝ)) / 2) <
    ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        a ^ ((2 - (n : ℝ)) / 2) := by
  obtain hn1 | hn3 : n = 1 ∨ 3 ≤ n := by omega
  · have hn1ℝ : (n : ℝ) = 1 := by exact_mod_cast hn1
    have hc : (n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) < 0 := by
      rw [hn1ℝ]
      linarith [volume_real_unitBall_pos n]
    have hexp : (0 : ℝ) < (2 - (n : ℝ)) / 2 := by
      rw [hn1ℝ]
      norm_num
    exact mul_lt_mul_of_neg_left
      (Real.rpow_lt_rpow ha.le hab hexp) (inv_lt_zero.mpr hc)
  · have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hc : 0 < ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ := by
      have hnpos : (0 : ℝ) < n := by linarith
      have hnsub : (0 : ℝ) < (n : ℝ) - 2 := by linarith
      exact inv_pos.mpr (mul_pos (mul_pos hnpos hnsub)
        (volume_real_unitBall_pos n))
    have hexp : (2 - (n : ℝ)) / 2 < 0 := by linarith
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg ha hab hexp) hc

/-- In a positive dimension other than two, the Newtonian kernel strictly decreases with
distance from the origin. -/
theorem newtonianKernel_lt_newtonianKernel_of_norm_lt (n : ℕ) (hn : n ≠ 2)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (h : ‖x‖ < ‖y‖) :
    newtonianKernel n y < newtonianKernel n x := by
  rw [newtonianKernel_def, newtonianKernel_def,
    ← Real.sq_rpow_div_two (norm_nonneg y), ← Real.sq_rpow_div_two (norm_nonneg x)]
  exact newtonianKernel_rpow_sq_lt n hn (pos_of_ne_euclideanSpace hx)
    (by positivity) (by nlinarith [norm_nonneg x, norm_nonneg y])

/-- The Fréchet derivative of the Newtonian kernel away from its pole. -/
theorem hasFDerivAt_newtonianKernel (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt (newtonianKernel n)
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x) x := by
  have hfun : newtonianKernel n = fun y ↦
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖y‖ ^ (2 - (n : ℝ)) := by rfl
  rw [hfun]
  refine ((hasFDerivAt_norm_rpow_of_ne (2 - (n : ℝ)) hx).const_mul
    (((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹)).congr_fderiv ?_
  have hn0 : (n : ℝ) ≠ 0 := by
    cases n with
    | zero => exact (hx (Subsingleton.elim x 0)).elim
    | succ n => positivity
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hn)
  have hvol := (volume_real_unitBall_pos n).ne'
  have hexp : (2 - (n : ℝ)) - 2 = -(n : ℝ) := by ring
  rw [hexp]
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

/-- Away from dimension two and dimension zero, the Newtonian kernel is not differentiable at its
pole: it is unbounded there in dimensions `n ≥ 3`, but takes the value `0` at the origin, and it is
a multiple of the norm in dimension one. -/
theorem not_differentiableAt_newtonianKernel_zero (n : ℕ) (hn : n ≠ 2) (hn0 : n ≠ 0) :
    ¬DifferentiableAt ℝ (newtonianKernel n) (0 : EuclideanSpace ℝ (Fin n)) := by
  intro h
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn0⟩⟩
  have hω := volume_real_unitBall_pos n
  rcases (by omega : n = 1 ∨ 3 ≤ n) with rfl | h3
  · obtain ⟨c, hc0, hfun⟩ : ∃ c : ℝ, c ≠ 0 ∧
        newtonianKernel 1 = fun y : EuclideanSpace ℝ (Fin 1) ↦ c * ‖y‖ := by
      refine ⟨(((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 1)) 1))⁻¹, ?_, ?_⟩
      · norm_num
        exact hω.ne'
      · funext y
        rw [newtonianKernel_def]
        norm_num
    rw [hfun] at h
    refine not_differentiableAt_norm_zero (EuclideanSpace ℝ (Fin 1)) ?_
    simpa only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] using h.const_mul c⁻¹
  · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h3
    have hC : 0 < ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ :=
      inv_pos.2 (by have : 0 < (n : ℝ) - 2 := by linarith
                    positivity)
    have hc : Tendsto (newtonianKernel n) (𝓝[≠] (0 : EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
      simpa using h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    have hpow : Tendsto (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)))
        (𝓝[≠] 0) atTop :=
      (tendsto_rpow_neg_nhdsGT_zero (by linarith)).comp tendsto_norm_nhdsNE_zero
    have hatTop : Tendsto (newtonianKernel n) (𝓝[≠] (0 : EuclideanSpace ℝ (Fin n))) atTop := by
      rw [funext (newtonianKernel_def n)]
      exact hpow.const_mul_atTop hC
    exact not_tendsto_nhds_of_tendsto_atTop hatTop _ hc

/-- The Fréchet derivative of the Newtonian kernel as a continuous linear functional. At the pole,
where the kernel is not differentiable (or the space is trivial), both sides are `0`. -/
theorem fderiv_newtonianKernel (n : ℕ) (hn : n ≠ 2) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (newtonianKernel n) x =
      (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn0
    · ext v
      rw [Subsingleton.elim v 0]
      simp
    · rw [fderiv_zero_of_not_differentiableAt (not_differentiableAt_newtonianKernel_zero n hn hn0)]
      simp
  · exact (hasFDerivAt_newtonianKernel n hn hx).fderiv

/-- The derivative of the Newtonian kernel evaluated in a direction. -/
theorem fderiv_newtonianKernel_apply (n : ℕ) (hn : n ≠ 2)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (newtonianKernel n) x v =
      -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (-(n : ℝ)) * ⟪x, v⟫_ℝ) := by
  rw [fderiv_newtonianKernel n hn x]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The gradient of the Newtonian kernel at its pole is zero, by the junk-value conventions: in
dimension two the kernel is `0`, and otherwise the gradient formula holds at `0` with value `0`. -/
@[simp]
theorem fderiv_newtonianKernel_zero (n : ℕ) : fderiv ℝ (newtonianKernel n) 0 = 0 := by
  rcases eq_or_ne n 2 with rfl | hn
  · simp
  · ext v
    simp [fderiv_newtonianKernel_apply n hn 0 v]

/-- The operator norm of the derivative of the Newtonian kernel decays like `‖x‖ ^ (1 - n)`. -/
@[simp]
theorem norm_fderiv_newtonianKernel (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖fderiv ℝ (newtonianKernel n) x‖ =
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (1 - (n : ℝ)) := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    exact hx (Subsingleton.elim x 0)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsplit : ‖x‖ ^ (1 - (n : ℝ)) = ‖x‖ ^ (-(n : ℝ)) * ‖x‖ := by
    rw [sub_eq_add_neg, add_comm, Real.rpow_add hnorm, Real.rpow_one]
  rw [fderiv_newtonianKernel n hn x, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_mul, abs_neg, abs_inv, abs_of_pos (mul_pos hnpos (volume_real_unitBall_pos n)),
    abs_of_pos (Real.rpow_pos_of_pos hnorm _), hsplit]
  ring

/-- The operator norm of the derivative of the Newtonian kernel is at most
`(n ωₙ)⁻¹ r ^ (1 - n)` at every point of norm at least `r > 0`. -/
theorem norm_fderiv_newtonianKernel_le (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hx : r ≤ ‖x‖) :
    ‖fderiv ℝ (newtonianKernel n) x‖ ≤
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        r ^ (1 - (n : ℝ)) := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (hr.trans_le hx)
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact (hx0 (Subsingleton.elim _ _)).elim
    · exact_mod_cast h
  rw [norm_fderiv_newtonianKernel n hn hx0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hx (by linarith))
    (inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg n) (volume_real_unitBall_pos n).le))

/-- Away from its pole, the Newtonian kernel is twice continuously differentiable. -/
theorem contDiffAt_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (newtonianKernel n) x := by
  have hfun : newtonianKernel n =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)) := by
    funext y
    simp only [newtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  have hpow : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ (2 - (n : ℝ))) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  exact hpow.const_smul (((n : ℝ) * ((n : ℝ) - 2) *
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹)

/-- The Newtonian kernel solves the homogeneous Laplace equation pointwise away from its pole. -/
@[simp]
theorem laplacian_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Δ (newtonianKernel n) x = 0 := by
  have hfun : newtonianKernel n =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)) := by
    funext y
    simp only [newtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  have hpow : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ (2 - (n : ℝ))) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  rw [hfun, laplacian_smul _ hpow]
  rw [laplacian_norm_rpow_of_ne (2 - (n : ℝ)) hx]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  ring

/-- The Newtonian kernel is harmonic at every point away from its pole at the origin. -/
theorem harmonicAt_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HarmonicAt (newtonianKernel n) x := by
  refine ⟨contDiffAt_newtonianKernel n hx, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact laplacian_newtonianKernel n hy

/-- The Newtonian kernel is harmonic on the punctured Euclidean space. -/
theorem harmonicOnNhd_newtonianKernel (n : ℕ) :
    HarmonicOnNhd (newtonianKernel n) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  intro x hx
  exact harmonicAt_newtonianKernel n (Set.mem_compl_singleton_iff.mp hx)

/-- A Newtonian kernel with pole at `a` is harmonic away from that pole. -/
theorem harmonicAt_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    HarmonicAt (fun y ↦ newtonianKernel n (y - a)) x := by
  simpa [sub_eq_add_neg] using
    (harmonicAt_comp_add_right_iff (f := newtonianKernel n) (x := x) (a := -a)).2
      (harmonicAt_newtonianKernel n (sub_ne_zero.mpr hxa))

/-- A Newtonian kernel with pole at `a` is twice continuously differentiable away from `a`. -/
theorem contDiffAt_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    ContDiffAt ℝ 2 (fun y ↦ newtonianKernel n (y - a)) x :=
  (harmonicAt_newtonianKernel_sub n hxa).1

/-- A Newtonian kernel with pole at `a` has the translated Fréchet derivative. -/
theorem hasFDerivAt_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    HasFDerivAt (fun y ↦ newtonianKernel n (y - a))
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x - a‖ ^ (-(n : ℝ))) • innerSL ℝ (x - a)) x := by
  rw [hasFDerivAt_comp_sub]
  exact hasFDerivAt_newtonianKernel n hn (sub_ne_zero.mpr hxa)

/-- The Fréchet derivative of a Newtonian kernel with pole at `a`. -/
theorem fderiv_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    (x a : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x =
      (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x - a‖ ^ (-(n : ℝ))) • innerSL ℝ (x - a) := by
  rw [fderiv_comp_sub]
  exact fderiv_newtonianKernel n hn (x - a)

/-- The derivative of the Newtonian kernel with a translated pole. -/
theorem fderiv_newtonianKernel_sub_apply (n : ℕ) (hn : n ≠ 2)
    (x a v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x v =
      -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x - a‖ ^ (-(n : ℝ)) * ⟪x - a, v⟫_ℝ) := by
  rw [fderiv_newtonianKernel_sub n hn x a]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The operator norm of the derivative of a Newtonian kernel with pole at `a`. -/
@[simp]
theorem norm_fderiv_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    ‖fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x‖ =
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x - a‖ ^ (1 - (n : ℝ)) := by
  rw [fderiv_comp_sub]
  exact norm_fderiv_newtonianKernel n hn (sub_ne_zero.mpr hxa)

/-- A translated Newtonian kernel solves the homogeneous Laplace equation away from its pole. -/
@[simp]
theorem laplacian_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    Δ (fun y ↦ newtonianKernel n (y - a)) x = 0 :=
  (harmonicAt_newtonianKernel_sub n hxa).2.self_of_nhds

/-- A Newtonian kernel with pole at `a` is harmonic on the complement of the pole. -/
theorem harmonicOnNhd_newtonianKernel_sub (n : ℕ)
    (a : EuclideanSpace ℝ (Fin n)) :
    HarmonicOnNhd (fun x ↦ newtonianKernel n (x - a)) ({a}ᶜ : Set _) := by
  intro x hx
  exact harmonicAt_newtonianKernel_sub n (Set.mem_compl_singleton_iff.mp hx)

/-- In dimension one the Newtonian kernel is `-|x| / 2`, whose second derivative is `-δ₀`. -/
theorem newtonianKernel_one (x : EuclideanSpace ℝ (Fin 1)) :
    newtonianKernel 1 x = -‖x‖ / 2 := by
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = 2 := by
    rw [Measure.real_def, InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp)]
    norm_num
  rw [newtonianKernel_def, hvol]
  norm_num
  ring

/-- In dimension three the Newtonian kernel is the classical function `1 / (4π‖x‖)`. -/
theorem newtonianKernel_three (x : EuclideanSpace ℝ (Fin 3)) :
    newtonianKernel 3 x = (4 * Real.pi * ‖x‖)⁻¹ := by
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Real.pi * 4 / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    simp only [one_pow, ENNReal.ofReal_one, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [newtonianKernel_def, hvol]
  norm_num [Real.rpow_neg_one]
  field_simp [Real.pi_ne_zero]

end TauCeti

end
