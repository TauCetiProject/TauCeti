/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Analytic
public import TauCeti.Analysis.Quaternion.Cauchy.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Star
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Universal Cauchy–Fueter derivative estimates

Combining the differentiated Cauchy–Fueter box representation from
`TauCeti.Analysis.Quaternion.Cauchy.IteratedFDeriv` on an inscribed four-dimensional coordinate
cube with the homogeneous decay bound `‖D^m G(w)‖ ≤ C_m / ‖w‖^(3 + m)` yields universal interior
Cauchy–Fueter estimates on cubes and Euclidean balls.

## Universal Cauchy–Fueter estimates and reflection

On the coordinate cube of half-side `r > 0` centred at `x₀`, each of the eight three-dimensional
faces has Euclidean distance at least `r` from `dq x₀` and three-dimensional Lebesgue measure
`(2 r)³ = 8 r³`. Whereas harmonicity (`InnerProductSpace.HarmonicOnNhd`) already bounds interior
derivatives on open balls from a solid-ball bound, estimating each differentiated Cauchy–Fueter face
integral gives a boundary-only supremum bound
`‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ C_m * r⁻¹ ^ m * M` requiring only continuity on the closed cube,
Fueter regularity on the open cube, and `‖f‖ ≤ M` on the eight three-dimensional boundary faces.
Taking `r = R / 2` inscribes the cube in `Metric.closedBall q₀ R` (since `√4 · (R / 2) = R`),
yielding universal ball bounds `TauCeti.exists_leftFueter_iteratedFDeriv_ball_bound`,
`TauCeti.leftFueter_iteratedFDeriv_bound`, and—by isometric reflection invariance
(`TauCeti.norm_iteratedFDeriv_star`, `TauCeti.norm_iteratedFDeriv_comp_star`)—their right-regular
counterparts with the identical dimension-only constants.

## Main declarations

* `TauCeti.norm_iteratedFDeriv_cauchyFueterKernel_mul_right_le`,
  `TauCeti.norm_iteratedFDeriv_mul_cauchyFueterKernel_right_le`: operator-norm bounds for weighted
  pole derivatives of `cauchyFueterKernel`.
* `TauCeti.exists_leftFueter_iteratedFDeriv_cube_boundary_bound`,
  `TauCeti.exists_rightFueter_iteratedFDeriv_cube_boundary_bound`,
  `TauCeti.exists_leftFueter_iteratedFDeriv_ball_bound`,
  `TauCeti.exists_rightFueter_iteratedFDeriv_ball_bound`,
  `TauCeti.leftFueter_iteratedFDeriv_bound`,
  `TauCeti.rightFueter_iteratedFDeriv_bound`: universal Cauchy–Fueter derivative estimates on cubes
  and balls.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology TauCeti.Quaternion
open scoped ContDiff

namespace TauCeti

/-! ### Pointwise pole derivatives of weighted Cauchy–Fueter kernels -/

/-- Operator-norm bound for the `m`-th pole derivative of `y ↦ cauchyFueterKernel w y * c`. -/
theorem norm_iteratedFDeriv_cauchyFueterKernel_mul_right_le {w q : ℍ} (h : w ≠ q) (c : ℍ)
    (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ cauchyFueterKernel w y * c) q‖ ≤
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel w) q‖ * ‖c‖ := by
  have hop : ‖(ContinuousLinearMap.mul ℝ ℍ).flip c‖ ≤ ‖c‖ :=
    (((ContinuousLinearMap.mul ℝ ℍ).flip.le_opNorm c).trans_eq
      (by rw [ContinuousLinearMap.opNorm_flip])).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℍ)
        (norm_nonneg c)).trans_eq (one_mul _))
  exact ((((ContinuousLinearMap.mul ℝ ℍ).flip c).norm_iteratedFDeriv_comp_left
      (analyticAt_cauchyFueterKernel_right h).contDiffAt le_top).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg _))).trans_eq (mul_comm _ _)

/-- Operator-norm bound for the `m`-th pole derivative of `y ↦ c * cauchyFueterKernel w y`. -/
theorem norm_iteratedFDeriv_mul_cauchyFueterKernel_right_le {w q : ℍ} (h : w ≠ q) (c : ℍ)
    (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ c * cauchyFueterKernel w y) q‖ ≤
      ‖c‖ * ‖iteratedFDeriv ℝ m (cauchyFueterKernel w) q‖ :=
  (((ContinuousLinearMap.mul ℝ ℍ) c).norm_iteratedFDeriv_comp_left
      (analyticAt_cauchyFueterKernel_right h).contDiffAt le_top).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℍ c) (norm_nonneg _))

/-! ### Universal Cauchy–Fueter derivative bounds on cubes and balls -/

/-- Norm estimate for `(1 / (2π²)) • boxBoundarySum` on the four-dimensional cube of half-side
`r > 0` centred at `x₀`: each of the eight three-dimensional faces has volume `8 r³`, cancelling
`r⁻³` against a pointwise bound `C_K / r ^ (3 + m) * M`. -/
private theorem norm_smul_boxBoundarySum_cube_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x₀ : Fin 4 → ℝ} {r C_K M : ℝ} (hr : 0 < r) (m : ℕ)
    (H : Fin 4 → (Fin 4 → ℝ) → E)
    (hH : ∀ (i : Fin 4) {c : ℝ}, (c = x₀ i - r ∨ c = x₀ i + r) →
      ∀ u ∈ Icc (fun k ↦ x₀ (i.succAbove k) - r) (fun k ↦ x₀ (i.succAbove k) + r),
        ‖H i (i.insertNth c u)‖ ≤ C_K / r ^ (3 + m) * M) :
    ‖(1 / (2 * Real.pi ^ 2)) •
        boxBoundarySum (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r) H‖ ≤
      (64 * C_K / (2 * Real.pi ^ 2)) * r⁻¹ ^ m * M := by
  set a : Fin 4 → ℝ := fun j ↦ x₀ j - r
  set b : Fin 4 → ℝ := fun j ↦ x₀ j + r
  have hface_bound (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i) :
      ‖∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth c u)‖ ≤
        8 * C_K * r⁻¹ ^ m * M := by
    have hlo_hi : (a ∘ i.succAbove) ≤ (b ∘ i.succAbove) := fun k ↦ by
      simp only [Function.comp_apply, a, b]; linarith
    have hvol : volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) = 8 * r ^ 3 := by
      rw [Measure.real_def, Real.volume_Icc_pi_toReal hlo_hi]
      have hdiff (k : Fin 3) : (b ∘ i.succAbove) k - (a ∘ i.succAbove) k = 2 * r := by
        simp only [Function.comp_apply, a, b]; ring
      simp_rw [hdiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring
    calc ‖∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth c u)‖
        ≤ (C_K / r ^ (3 + m) * M) * volume.real (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :=
          norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top (hH i hc')
      _ = 8 * C_K * r⁻¹ ^ m * M := by
          rw [hvol, pow_add, inv_pow]
          have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr.ne'
          field_simp [hr3]
  rw [norm_smul, Real.norm_of_nonneg (by positivity), boxBoundarySum_def]
  have hsum : ‖∑ i : Fin 4,
      ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth (a i) x))‖ ≤
      64 * C_K * r⁻¹ ^ m * M := by
    calc ‖∑ i : Fin 4, _‖
        ≤ ∑ i : Fin 4,
            ‖(∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth (b i) x)) -
              ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H i (i.insertNth (a i) x)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin 4, (8 * C_K * r⁻¹ ^ m * M + 8 * C_K * r⁻¹ ^ m * M) := by
          refine Finset.sum_le_sum fun i _ ↦ (norm_sub_le _ _).trans ?_
          exact add_le_add (hface_bound i (Or.inr rfl)) (hface_bound i (Or.inl rfl))
      _ = 64 * C_K * r⁻¹ ^ m * M := by
          simp [Finset.sum_const]
          ring
  calc (1 / (2 * Real.pi ^ 2)) * ‖∑ i : Fin 4, _‖
      ≤ (1 / (2 * Real.pi ^ 2)) * (64 * C_K * r⁻¹ ^ m * M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (64 * C_K / (2 * Real.pi ^ 2)) * r⁻¹ ^ m * M := by ring

/-- Shared cube-boundary estimate from a differentiated `boxBoundarySum` representation whose
integrand satisfies `‖H i x‖ ≤ ‖D^m G(dq x, dq x₀)‖ * ‖f (dq x)‖` away from `dq x₀`. -/
private theorem norm_iteratedFDeriv_cube_boundary_le {x₀ : Fin 4 → ℝ} {r C_K M : ℝ}
    (hr : 0 < r) (hC_K : 0 ≤ C_K) (m : ℕ) {f : ℍ → ℍ}
    (hK : ∀ {w q : ℍ}, r ≤ ‖w - q‖ →
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel w) q‖ ≤ C_K / r ^ (3 + m))
    (H : Fin 4 → (Fin 4 → ℝ) → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ ℍ) ℍ)
    (hrep : iteratedFDeriv ℝ m f (dq x₀) =
      (1 / (2 * Real.pi ^ 2)) • boxBoundarySum (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r) H)
    (hH : ∀ (i : Fin 4) (x : Fin 4 → ℝ), dq x ≠ dq x₀ →
      ‖H i x‖ ≤ ‖iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)‖ * ‖f (dq x)‖)
    (hM : ∀ (i : Fin 4) {c : ℝ}, (c = x₀ i - r ∨ c = x₀ i + r) →
      ∀ u ∈ Icc (fun k ↦ x₀ (i.succAbove k) - r) (fun k ↦ x₀ (i.succAbove k) + r),
        ‖f (dq (i.insertNth c u))‖ ≤ M) :
    ‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ (64 * C_K / (2 * Real.pi ^ 2)) * r⁻¹ ^ m * M := by
  rw [hrep]
  refine norm_smul_boxBoundarySum_cube_le hr m _ fun i {c} hc' u hu ↦ ?_
  have hsep : r ≤ ‖dq (i.insertNth c u) - dq x₀‖ :=
    le_norm_dq_insertNth_sub x₀ hr.le i hc' u
  have hne : dq (i.insertNth c u) ≠ dq x₀ := sub_ne_zero.1 (norm_pos_iff.1 (hr.trans_le hsep))
  exact (hH i _ hne).trans
    (mul_le_mul (hK hsep) (hM i hc' u hu) (norm_nonneg _) (by positivity))

/-- Universal cube-boundary Cauchy–Fueter estimate for left regular functions: for every order `m`,
there is `C > 0` depending on `m` alone such that if `f` is continuous on the closed coordinate
cube of half-side `r > 0` centred at `x₀`, left Fueter regular on the open cube, and bounded by `M`
on the eight boundary faces, then `‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ C * r⁻¹ ^ m * M`. -/
theorem exists_leftFueter_iteratedFDeriv_cube_boundary_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x₀ : Fin 4 → ℝ} {r : ℝ}, 0 < r →
      ∀ {f : ℍ → ℍ},
      ContinuousOn f (dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r)) →
      LeftFueterOn f (dq '' pi univ fun j ↦ Ioo (x₀ j - r) (x₀ j + r)) →
      ∀ {M : ℝ},
      (∀ (i : Fin 4) {c : ℝ}, (c = x₀ i - r ∨ c = x₀ i + r) →
        ∀ u ∈ Icc (fun k ↦ x₀ (i.succAbove k) - r) (fun k ↦ x₀ (i.succAbove k) + r),
          ‖f (dq (i.insertNth c u))‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ C * r⁻¹ ^ m * M := by
  obtain ⟨C_K, hC_K, hK⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub m
  refine ⟨64 * C_K / (2 * Real.pi ^ 2), by positivity, fun {x₀ r} hr {f} hc hf {M} hM ↦
    norm_iteratedFDeriv_cube_boundary_le hr hC_K.le m (fun hsep ↦ hK m le_rfl hr hsep) _
      (iteratedFDeriv_left_cauchyFueter_box hc hf (fun _ ↦ by linarith) (fun _ ↦ by linarith) m)
      (fun i x hne ↦ by
        simpa only [mul_assoc, norm_mul, norm_dq, PiLp.toLp_single, PiLp.norm_single,
          norm_one, one_mul] using
          norm_iteratedFDeriv_cauchyFueterKernel_mul_right_le hne
            (dq (Pi.single i 1) * f (dq x)) m)
      hM⟩

/-- Universal cube-boundary Cauchy–Fueter estimate for right regular functions: for every order
`m`, there is `C > 0` depending on `m` alone such that if `f` is continuous on the closed
coordinate cube of half-side `r > 0` centred at `x₀`, right Fueter regular on the open cube, and
bounded by `M` on the eight boundary faces, then
`‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ C * r⁻¹ ^ m * M`. -/
theorem exists_rightFueter_iteratedFDeriv_cube_boundary_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x₀ : Fin 4 → ℝ} {r : ℝ}, 0 < r →
      ∀ {f : ℍ → ℍ},
      ContinuousOn f (dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r)) →
      RightFueterOn f (dq '' pi univ fun j ↦ Ioo (x₀ j - r) (x₀ j + r)) →
      ∀ {M : ℝ},
      (∀ (i : Fin 4) {c : ℝ}, (c = x₀ i - r ∨ c = x₀ i + r) →
        ∀ u ∈ Icc (fun k ↦ x₀ (i.succAbove k) - r) (fun k ↦ x₀ (i.succAbove k) + r),
          ‖f (dq (i.insertNth c u))‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f (dq x₀)‖ ≤ C * r⁻¹ ^ m * M := by
  obtain ⟨C_K, hC_K, hK⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub m
  refine ⟨64 * C_K / (2 * Real.pi ^ 2), by positivity, fun {x₀ r} hr {f} hc hf {M} hM ↦
    norm_iteratedFDeriv_cube_boundary_le hr hC_K.le m (fun hsep ↦ hK m le_rfl hr hsep) _
      (iteratedFDeriv_right_cauchyFueter_box hc hf (fun _ ↦ by linarith) (fun _ ↦ by linarith) m)
      (fun i x hne ↦ by
        simpa only [norm_mul, norm_dq, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] using
          (norm_iteratedFDeriv_mul_cauchyFueterKernel_right_le hne
            (f (dq x) * dq (Pi.single i 1)) m).trans_eq (mul_comm _ _))
      hM⟩

/-- Universal ball Cauchy–Fueter estimate for functions continuous on `closedBall q₀ R` and left
Fueter regular on `ball q₀ R`: for every order `m`, there is `C > 0` depending on `m` alone such
that `‖f‖ ≤ M` on `closedBall q₀ R` (`R > 0`) implies
`‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`. -/
theorem exists_leftFueter_iteratedFDeriv_ball_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ}, 0 < R →
      ContinuousOn f (closedBall q₀ R) →
      LeftFueterOn f (ball q₀ R) →
      ∀ {M : ℝ}, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C₀, hC₀, hcube⟩ := exists_leftFueter_iteratedFDeriv_cube_boundary_bound m
  refine ⟨C₀ * 2 ^ m, by positivity, fun {f q₀ R} hR hc hf {M} hM ↦ ?_⟩
  let x₀ := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1) q₀
  have hqx₀ : dq x₀ = q₀ := by simp [x₀, coe_dq]
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have h2r : 2 * r = R := by ring
  have hclosed_sub : dq '' Icc (fun j ↦ x₀ j - r) (fun j ↦ x₀ j + r) ⊆ closedBall q₀ R :=
    (dq_image_Icc_subset_closedBall x₀ hr.le).trans (by rw [hqx₀, h2r])
  have hopen_sub : dq '' pi univ (fun j ↦ Ioo (x₀ j - r) (x₀ j + r)) ⊆ ball q₀ R :=
    (dq_image_pi_Ioo_subset_ball x₀ hr).trans (by rw [hqx₀, h2r])
  have hbd : ∀ (i : Fin 4) {c : ℝ}, (c = x₀ i - r ∨ c = x₀ i + r) →
      ∀ u ∈ Icc (fun k ↦ x₀ (i.succAbove k) - r) (fun k ↦ x₀ (i.succAbove k) + r),
        ‖f (dq (i.insertNth c u))‖ ≤ M := by
    intro i c hc' u hu
    have hc_mem : c ∈ Icc (x₀ i - r) (x₀ i + r) := by
      rcases hc' with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
    exact hM _ (hclosed_sub (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc_mem, hu⟩)))
  rw [← hqx₀]
  calc ‖iteratedFDeriv ℝ m f (dq x₀)‖
      ≤ C₀ * r⁻¹ ^ m * M := hcube hr (hc.mono hclosed_sub) (hf.mono hopen_sub) hbd
    _ = (C₀ * 2 ^ m) * R⁻¹ ^ m * M := by
        have hr_inv : r⁻¹ = 2 * R⁻¹ := by
          dsimp [r]
          field_simp [hR.ne']
        rw [hr_inv, mul_pow]
        ring

/-- Universal ball Cauchy–Fueter estimate for functions continuous on `closedBall q₀ R` and right
Fueter regular on `ball q₀ R`: for every order `m`, there is `C > 0` depending on `m` alone such
that `‖f‖ ≤ M` on `closedBall q₀ R` (`R > 0`) implies
`‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`. -/
theorem exists_rightFueter_iteratedFDeriv_ball_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℍ → ℍ} {q₀ : ℍ} {R : ℝ}, 0 < R →
      ContinuousOn f (closedBall q₀ R) →
      RightFueterOn f (ball q₀ R) →
      ∀ {M : ℝ}, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C, hC, hleft⟩ := exists_leftFueter_iteratedFDeriv_ball_bound m
  refine ⟨C, hC, fun {f q₀ R} hR hc hf {M} hM ↦ ?_⟩
  have hnorm_star (q : ℍ) : ‖star q - q₀‖ = ‖q - star q₀‖ := by
    rw [← _root_.norm_star (q - star q₀), star_sub, star_star]
  have hcb_star : ∀ q ∈ closedBall (star q₀) R, star q ∈ closedBall q₀ R := fun q hq ↦ by
    rwa [mem_closedBall, dist_eq_norm, hnorm_star, ← dist_eq_norm, ← mem_closedBall]
  have hb_star : ball (star q₀) R ⊆ star '' ball q₀ R := fun q hq ↦ by
    refine ⟨star q, ?_, star_star q⟩
    rwa [mem_ball, dist_eq_norm, hnorm_star, ← dist_eq_norm, ← mem_ball]
  have hc_refl : ContinuousOn (fun x ↦ star (f (star x))) (closedBall (star q₀) R) :=
    continuous_star.comp_continuousOn (hc.comp continuous_star.continuousOn hcb_star)
  have hf_refl : LeftFueterOn (fun x ↦ star (f (star x))) (ball (star q₀) R) :=
    hf.star_star.mono hb_star
  have hM_refl : ∀ q ∈ closedBall (star q₀) R, ‖star (f (star q))‖ ≤ M := fun q hq ↦ by
    rw [_root_.norm_star]
    exact hM (star q) (hcb_star q hq)
  have hbound := hleft hR hc_refl hf_refl hM_refl
  rwa [norm_iteratedFDeriv_star, norm_iteratedFDeriv_comp_star, star_star] at hbound

/-- Universal interior derivative estimate for left Fueter regular functions on a domain containing
`closedBall q₀ R` (`R > 0`): for each order `m`, a constant `C > 0` depending only on `m` bounds
`‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M` whenever `‖f‖ ≤ M` on `closedBall q₀ R`. -/
theorem leftFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), LeftFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C, hC, hball⟩ := exists_leftFueter_iteratedFDeriv_ball_bound m
  exact ⟨C, hC, fun f Ω hf q₀ R hR hsub M hM ↦
    hball hR (hf.mono hsub).differentiableOn.continuousOn
      (hf.mono (ball_subset_closedBall.trans hsub)) hM⟩

/-- Universal interior derivative estimate for right Fueter regular functions on a domain containing
`closedBall q₀ R` (`R > 0`), with a constant depending on `m` alone. -/
theorem rightFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), RightFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C, hC, hball⟩ := exists_rightFueter_iteratedFDeriv_ball_bound m
  exact ⟨C, hC, fun f Ω hf q₀ R hR hsub M hM ↦
    hball hR (hf.mono hsub).differentiableOn.continuousOn
      (hf.mono (ball_subset_closedBall.trans hsub)) hM⟩

end TauCeti
