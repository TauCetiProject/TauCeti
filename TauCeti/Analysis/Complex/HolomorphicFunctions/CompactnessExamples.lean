/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The hypotheses of compactness for holomorphic sequences

The compactness theorem for pseudoholomorphic curves (McDuff–Salamon, *J-holomorphic Curves and
Symplectic Topology*, Theorem B.4.2 and Theorem 4.1.1) extracts a `C^∞`-convergent subsequence
from a sequence of solutions whose derivatives are uniformly bounded on compact sets, whose
images of compact sets stay in a fixed compact set, and, for discs with boundary on a totally
real `L`, whose boundary values lie in a closed `L`. This file records, for holomorphic maps
(`J = i`, `η = 0`), that dropping the closedness of `L` or the image bound breaks the conclusion,
that a sequence violating the gradient bound has no convergent subsequence, and that maps
satisfying all of the hypotheses do converge in the expected example. For holomorphic maps into
`ℂ` the image bound already implies interior gradient bounds by the Cauchy estimates, so no
example of this kind isolates the gradient bound: the sequence below violates the gradient and
image bounds simultaneously.

* Closedness of the boundary condition. Boundary values in a closed set pass to pointwise
  limits (`TauCeti.mapsTo_of_tendsto_of_isClosed`). For `L = (0, 1) ⊆ ℝ ⊆ ℂ` the constant maps
  `u m = 1 / (m + 2)` take values in `L` and have derivative zero, but converge uniformly to the
  constant `0 ∉ L`; for the closed `L = ℝ` the general statement keeps the boundary values of
  the limit in `L`.
* The gradient bound. The maps `u m z = m z` are holomorphic with `‖deriv (u m)‖ = m`, so their
  `L^p` norms on `D_{1/2}` equal `m · vol(D_{1/2})^{1/p}` and are unbounded, and no subsequence
  converges locally uniformly on `D_1`. They send `D_1` onto `D_m`, so they violate the image
  bound as well. The maps `u m z = z / m` satisfy `‖deriv (u m)‖ ≤ 1`, send `D_1` into the
  closed unit disc, and every iterated derivative tends to `0` locally uniformly on `ℂ`.
* The image bound. The constant maps `u m = m` have derivative zero (`deriv_const'`), so the
  gradient bound holds with constant `0`, but no subsequence converges locally uniformly.

The non-convergence statements all come from one observation: a sequence whose values at one
point have norms tending to infinity has no subsequence converging pointwise there
(`TauCeti.not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop`).

## Main results

* `TauCeti.HolomorphicCompactness.ofReal_inv_add_two_mem_image_Ioo`,
  `TauCeti.HolomorphicCompactness.tendstoUniformly_ofReal_inv_add_two`: the closedness witness.
* `TauCeti.HolomorphicCompactness.eLpNorm_deriv_natCast_mul`,
  `TauCeti.HolomorphicCompactness.not_exists_eLpNorm_deriv_natCast_mul_le`,
  `TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast_mul`: the maps
  `u m z = m z`, which violate the gradient and image bounds simultaneously.
* `TauCeti.HolomorphicCompactness.tendstoLocallyUniformly_iteratedDeriv_div_natCast`: the maps
  `z / m` converge to `0` with all derivatives.
* `TauCeti.HolomorphicCompactness.not_tendstoLocallyUniformlyOn_natCast`: the image-bound
  witness `u m = m`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 4.1.1 and Theorem B.4.2.
-/

public section

noncomputable section

open Complex Filter Metric MeasureTheory Set Topology

namespace TauCeti.HolomorphicCompactness

/-! ### Closedness of the boundary condition -/

/-- The values `1 / (m + 2)` lie in `(0, 1) ⊆ ℝ ⊆ ℂ`, so the constant maps with these values
satisfy the boundary condition for `L = (0, 1)`. -/
theorem ofReal_inv_add_two_mem_image_Ioo (m : ℕ) :
    (((m + 2 : ℝ)⁻¹ : ℝ) : ℂ) ∈ ofReal '' Ioo 0 1 :=
  ⟨_, ⟨by positivity, inv_lt_one_of_one_lt₀ (by linarith [m.cast_nonneg (α := ℝ)])⟩, rfl⟩

/-- The constant maps `1 / (m + 2)` converge uniformly to the constant `0`. -/
theorem tendstoUniformly_ofReal_inv_add_two :
    TendstoUniformly (fun (m : ℕ) (_ : ℂ) ↦ (((m + 2 : ℝ)⁻¹ : ℝ) : ℂ)) (fun _ ↦ 0) atTop := by
  have h : Tendsto (fun m : ℕ ↦ (((m + 2 : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2
        tendsto_natCast_atTop_atTop))
  exact h.tendstoUniformly_const

/-- The limit `0` of the constant maps `1 / (m + 2)` violates the boundary condition for
`L = (0, 1)`: closedness of `L` cannot be dropped. -/
theorem zero_notMem_ofReal_image_Ioo : (0 : ℂ) ∉ ofReal '' Ioo 0 1 := by
  rintro ⟨x, hx, h⟩
  exact hx.1.ne' (ofReal_eq_zero.1 h)

/-! ### The gradient bound -/

/-- The derivative of `z ↦ m z` has norm `m` everywhere, so it violates any pointwise gradient
bound on `D_{1/2}` once `m` is large. -/
theorem norm_deriv_natCast_mul (m : ℕ) (z : ℂ) : ‖deriv (fun z : ℂ ↦ m * z) z‖ = m := by
  simp

/-- The `L^p` norm of the derivative of `z ↦ m z` on `D_{1/2}` is `m · vol(D_{1/2})^{1/p}`. -/
theorem eLpNorm_deriv_natCast_mul (m : ℕ) {p : ENNReal} (hp : p ≠ 0) :
    eLpNorm (deriv (fun z : ℂ ↦ m * z)) p (volume.restrict (ball 0 (1 / 2))) =
      m * volume (ball (0 : ℂ) (1 / 2)) ^ (1 / p.toReal) := by
  have hμ : volume.restrict (ball (0 : ℂ) (1 / 2)) ≠ 0 := by
    simpa [Measure.restrict_eq_zero] using (measure_ball_pos volume (0 : ℂ) one_half_pos).ne'
  rw [deriv_const_mul_id' (m : ℂ), eLpNorm_const _ hp hμ, Measure.restrict_apply_univ]
  simp [eNorm_eq_nnNorm]

/-- The `L^p` norms on `D_{1/2}` of the derivatives of `z ↦ m z` admit no finite bound, so this
sequence violates the gradient bound. -/
theorem not_exists_eLpNorm_deriv_natCast_mul_le {p : ENNReal} (hp : p ≠ 0) :
    ¬ ∃ C : NNReal, ∀ m : ℕ,
      eLpNorm (deriv (fun z : ℂ ↦ m * z)) p (volume.restrict (ball 0 (1 / 2))) ≤ C := by
  rintro ⟨C, hC⟩
  simp only [eLpNorm_deriv_natCast_mul _ hp] at hC
  set V := volume (ball (0 : ℂ) (1 / 2)) ^ (1 / p.toReal)
  have hV0 : V ≠ 0 :=
    (ENNReal.rpow_pos (measure_ball_pos volume _ one_half_pos) measure_ball_lt_top.ne).ne'
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_ball_lt_top.ne
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top ENNReal.coe_ne_top hV0).ne
  exact ((ENNReal.div_lt_iff (Or.inl hV0) (Or.inl hVt)).1 hm).not_ge (hC m)

/-- No subsequence of `z ↦ m z` converges locally uniformly on `D_1`. -/
theorem not_tendstoLocallyUniformlyOn_natCast_mul {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (g : ℂ → ℂ) :
    ¬ TendstoLocallyUniformlyOn (fun m (z : ℂ) ↦ (φ m : ℂ) * z) g atTop (ball 0 1) := by
  refine not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop (F := fun m (z : ℂ) ↦ m * z)
    (z := 1 / 2) (by simp; norm_num) ?_ hφ g
  simp only [norm_mul, Complex.norm_natCast]
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (by norm_num)

/-- The maps `z ↦ z / m` satisfy the gradient bound: their derivatives have norm at most `1`. -/
theorem norm_deriv_div_natCast_le_one (m : ℕ) (z : ℂ) :
    ‖deriv (fun z : ℂ ↦ z / m) z‖ ≤ 1 := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · simpa using inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hm)

/-- The maps `z ↦ z / m` satisfy the image bound: they send `D_1` into the closed unit disc. -/
theorem mapsTo_div_natCast_ball (m : ℕ) :
    MapsTo (fun z : ℂ ↦ z / m) (ball 0 1) (closedBall 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_natCast]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  · exact (div_le_one (Nat.cast_pos.2 hm)).2 (hz.le.trans (Nat.one_le_cast.2 hm))

/-- The maps `z ↦ z / m` converge to `0` in `C^∞` on compact sets: every iterated derivative
tends to `0` locally uniformly on `ℂ`. -/
theorem tendstoLocallyUniformly_iteratedDeriv_div_natCast (k : ℕ) :
    TendstoLocallyUniformly (fun (m : ℕ) ↦ iteratedDeriv k (fun z : ℂ ↦ z / m))
      (fun _ ↦ 0) atTop :=
  (tendstoLocallyUniformly_div_natCast (contDiff_id.continuous_iteratedDeriv' k)).congr
    fun _ _ ↦ (iteratedDeriv_div_const _ _).symm

/-! ### The image bound -/

/-- No subsequence of the constant maps `m` converges locally uniformly on `D_1`: their images
lie in no fixed compact set. -/
theorem not_tendstoLocallyUniformlyOn_natCast {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → ℂ) :
    ¬ TendstoLocallyUniformlyOn (fun m (_ : ℂ) ↦ (φ m : ℂ)) g atTop (ball 0 1) :=
  not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop (F := fun m (_ : ℂ) ↦ (m : ℂ))
    (z := 0) (mem_ball_self one_pos) (by simpa using tendsto_natCast_atTop_atTop) hφ g

end TauCeti.HolomorphicCompactness
