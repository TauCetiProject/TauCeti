/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Calculus.IteratedFDeriv.ParametricIntegral
public import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
public import TauCeti.Analysis.Quaternion.Cauchy.Representation
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Differentiated Cauchy–Fueter representations and universal derivative estimates

Differentiating the Cauchy–Fueter kernel `G(q - q₀) = (q - q₀)⁻¹ / ‖q - q₀‖²` in its second
argument `q₀` produces a continuous multilinear jet of homogeneous degree `-3 - m`. Away from the
support of a boundary measure, the pole separation `δ ≤ ‖φ z - q₀‖` gives a common closed-ball
bound on `‖D^m_q G(φ z - q)‖`, so dominated differentiation under the Bochner integral commutes
`iteratedFDeriv ℝ m` with potential integration at every order `m`.

Combining this kernel-potential differentiation with the box and affine Cauchy–Fueter integral
formulas expresses every iterated real Fréchet derivative `iteratedFDeriv ℝ m f (dq x₀)` of a left
or right Fueter regular function as an explicit boundary integral over the eight three-dimensional
faces of the box or positively oriented affine parallelepiped. Quaternion coefficients act on the
continuous multilinear kernel jet `D^m[q ↦ G(z - q)](q₀) : ℍ [×m]→L[ℝ] ℍ` on the left via `•` and
on the right via `MulOpposite.op _ • _`, preserving the noncommutative factor orders
`D^m G * Dq * f` (left regular) and `f * Dq * D^m G` (right regular).

Specializing the differentiated box representation to the axis-aligned cube of side `R` centred at
`q₀` — whose closed body lies inside `closedBall q₀ R` because `√(4 (R / 2)²) = R`, whose eight
faces lie at distance at least `R / 2` from `q₀`, and whose three-dimensional faces each have
volume `R³` — yields the universal Cauchy-type derivative estimates
`TauCeti.leftFueter_iteratedFDeriv_bound` and `TauCeti.rightFueter_iteratedFDeriv_bound`: for each
`m : ℕ` there is a constant `C > 0`, depending on `m` alone, such that whenever `f` is left (or
right) Fueter regular on a set `Ω` containing `closedBall q₀ R` (`R > 0`) and bounded in norm by
`M` on `closedBall q₀ R`,

`‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`.

## Main results

* `TauCeti.iteratedFDeriv_integral_bilinear_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_integral_cauchyFueterKernel_mul`,
  `TauCeti.iteratedFDeriv_integral_mul_cauchyFueterKernel`: iterated derivatives of general
  bilinear-paired, left, and right Cauchy–Fueter kernel potentials at a positively separated point.
* `TauCeti.left_cauchyFueter_iteratedFDeriv_box`,
  `TauCeti.right_cauchyFueter_iteratedFDeriv_box`: differentiated Cauchy–Fueter formulas on an
  axis-aligned box.
* `TauCeti.left_cauchyFueter_iteratedFDeriv_affine`,
  `TauCeti.right_cauchyFueter_iteratedFDeriv_affine`: differentiated Cauchy–Fueter formulas over
  the unit-cube face charts of a positively oriented affine parallelepiped.
* `TauCeti.iteratedFDeriv_star_star_apply`, `TauCeti.norm_iteratedFDeriv_star_star`: behavior of
  iterated real derivatives under the quaternionic reflection `q ↦ star (f (star q))`.
* `TauCeti.leftFueter_iteratedFDeriv_bound`, `TauCeti.rightFueter_iteratedFDeriv_bound`: universal
  `C_m R⁻ᵐ M` Cauchy estimates on closed balls for left and right Fueter regular functions.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 2 and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set TauCeti.Quaternion
open scoped ContDiff Quaternion Topology

namespace TauCeti

/-! ### Differentiating Cauchy–Fueter kernel potentials -/

section KernelPotentials

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an a.e. strongly measurable pole map `φ : X → ℍ`, the `m`-th derivative of
`cauchyFueterKernel (φ z)` at any point `p : ℍ` is a.e. strongly measurable. No pole-avoidance
hypothesis is needed because the kernel jet is continuous away from the single point `0`. -/
theorem aestronglyMeasurable_iteratedFDeriv_cauchyFueterKernel_right
    {φ : X → ℍ} (hφ : AEStronglyMeasurable φ μ) (m : ℕ) (p : ℍ) :
    AEStronglyMeasurable (fun z ↦ iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) p) μ := by
  let e : ℍ ≃L[ℝ] (Fin 4 → ℝ) :=
    (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).toContinuousLinearEquiv
  have hdq (q : ℍ) : dq (e q) = q := by
    rw [congrFun coe_dq (e q)]
    exact (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm_apply_apply q
  have : TopologicalSpace.PseudoMetrizableSpace (ℍ [×m]→L[ℝ] ℍ) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (ℍ [×m]→L[ℝ] ℍ) _
  let K₀ : (Fin 4 → ℝ) → (ℍ [×m]→L[ℝ] ℍ) :=
    fun u ↦ iteratedFDeriv ℝ m (fun y ↦ cauchyFueterKernel y 0) (dq u)
  have hK₀_cont : ContinuousOn K₀ {0}ᶜ := by
    intro u hu
    have hdu : dq u ≠ 0 := by
      intro h0
      apply hu
      have hu' : e (dq u) = u := by
        simpa [e, coe_dq] using
          (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).apply_symm_apply u
      simpa [h0] using hu'.symm
    exact (((contDiffAt_cauchyFueterKernel (q₀ := 0) (by simpa using hdu)
      (n := m)).continuousAt_iteratedFDeriv le_rfl).comp dq.continuous.continuousAt
      |>.continuousWithinAt)
  have hK₀_meas : StronglyMeasurable K₀ :=
    hK₀_cont.stronglyMeasurable_of_countable_compl (by simp)
  have hcoord : AEMeasurable (fun z ↦ e (φ z - p)) μ :=
    (e.continuous.comp_aestronglyMeasurable
      ((continuous_sub_right p).comp_aestronglyMeasurable hφ)).aemeasurable
  have hcomp : AEStronglyMeasurable (fun z ↦ (-1 : ℝ) ^ m • K₀ (e (φ z - p))) μ :=
    ContinuousConstSMul.continuous_const_smul ((-1 : ℝ) ^ m) |>.comp_aestronglyMeasurable
      (hK₀_meas.aestronglyMeasurable.comp_aemeasurable hcoord)
  refine hcomp.congr (ae_of_all _ fun z ↦ ?_)
  simp only [K₀, hdq, iteratedFDeriv_cauchyFueterKernel_right]

private theorem aestronglyMeasurable_bilinear_comp_iteratedFDeriv_cauchyFueterKernel
    {B : G × ℍ → E} (hB : IsBoundedBilinearMap ℝ B)
    {φ : X → ℍ} {g : X → G} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (k : ℕ) (q : ℍ) :
    AEStronglyMeasurable
      (fun z ↦ (hB.toContinuousLinearMap (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (cauchyFueterKernel (φ z)) q)) μ := by
  have hc : Continuous (fun p : G × (ℍ [×k]→L[ℝ] ℍ) ↦
      (hB.toContinuousLinearMap p.1).compContinuousMultilinearMap p.2) :=
    isBoundedBilinearMap_compMultilinear.continuous.comp
      (hB.toContinuousLinearMap.continuous.prodMap continuous_id)
  exact hc.comp_aestronglyMeasurable
    (hg.aestronglyMeasurable.prodMk
      (aestronglyMeasurable_iteratedFDeriv_cauchyFueterKernel_right hφ k q))

private theorem norm_bilinear_comp_multilinear_le {B : G × ℍ → E}
    (hB : IsBoundedBilinearMap ℝ B) {K : ℝ} (hK₀ : 0 ≤ K)
    (hK : ∀ x y, ‖B (x, y)‖ ≤ K * ‖x‖ * ‖y‖) (x : G) {k : ℕ} (J : ℍ [×k]→L[ℝ] ℍ) :
    ‖(hB.toContinuousLinearMap x).compContinuousMultilinearMap J‖ ≤ K * ‖x‖ * ‖J‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  calc ‖((hB.toContinuousLinearMap x).compContinuousMultilinearMap J) v‖
      = ‖B (x, J v)‖ := rfl
    _ ≤ K * ‖x‖ * ‖J v‖ := hK x (J v)
    _ ≤ K * ‖x‖ * (‖J‖ * ∏ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm v) (by positivity)
    _ = K * ‖x‖ * ‖J‖ * ∏ i, ‖v i‖ := (mul_assoc _ _ _).symm

/-- A bilinearly weighted Cauchy–Fueter kernel potential
`q ↦ ∫ z, B (g z, cauchyFueterKernel (φ z) q)` is smooth (`C^n` for any `n : ℕ∞`) at every point
`q₀` positively separated almost everywhere from `φ`. -/
theorem contDiffAt_integral_bilinear_cauchyFueterKernel {B : G × ℍ → E}
    (hB : IsBoundedBilinearMap ℝ B) {φ : X → ℍ} {g : X → G}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, B (g z, cauchyFueterKernel (φ z) q) ∂μ) q₀ := by
  -- Work on the open ball of radius `δ / 2`, where `contDiffOn_iff_forall_nat_le` reduces `n : ℕ∞`
  -- to each finite order `N : ℕ`.
  suffices ContDiffOn ℝ n (fun q ↦ ∫ z, B (g z, cauchyFueterKernel (φ z) q) ∂μ)
      (ball q₀ (δ / 2)) from
    this.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hδ₀)))
  rw [contDiffOn_iff_forall_nat_le]
  intro N _
  obtain ⟨K, hK_pos, hK⟩ := hB.bound
  obtain ⟨C, _, hC⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_mem_closedBall N
  have hsep : ∀ᵐ z ∂μ, ∀ q ∈ ball q₀ (δ / 2), φ z ≠ q := by
    filter_upwards [hδ] with z hz q hq heq
    have hq' : ‖q - q₀‖ < δ / 2 := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  refine contDiffOn_integral_of_dominated
    (bound := fun k z ↦ K * ‖g z‖ * (C / (δ - δ / 2) ^ (3 + k)))
    isOpen_ball ?_ ?_ ?_ (fun k _ ↦ (hg.norm.const_mul K).mul_const _)
  · filter_upwards [hsep] with z hz q hq
    exact (hB.toContinuousLinearMap (g z)).contDiff.contDiffOn.comp
      (fun p hp ↦ (contDiffAt_cauchyFueterKernel_right (hz p hp)).contDiffWithinAt)
      (mapsTo_univ _ _) q hq
  · intro q hq k hk
    have hk' : k ≤ N := Nat.cast_le.mp hk
    refine (aestronglyMeasurable_bilinear_comp_iteratedFDeriv_cauchyFueterKernel
      hB hφ hg k q).congr ?_
    filter_upwards [hsep] with z hz
    exact ((hB.toContinuousLinearMap (g z)).iteratedFDeriv_comp_left
      (contDiffAt_cauchyFueterKernel_right (hz q hq) (n := N)) (mod_cast hk')).symm
  · filter_upwards [hδ, hsep] with z hz hzne q hq k hk
    have hk' : k ≤ N := Nat.cast_le.mp hk
    have hcomp := (hB.toContinuousLinearMap (g z)).iteratedFDeriv_comp_left
      (contDiffAt_cauchyFueterKernel_right (hzne q hq) (n := N)) (mod_cast hk')
    dsimp only [Function.comp_def, IsBoundedBilinearMap.toContinuousLinearMap_apply] at hcomp
    rw [hcomp]
    exact (norm_bilinear_comp_multilinear_le hB hK_pos.le hK (g z) _).trans
      (mul_le_mul_of_nonneg_left
        (hC k hk' (half_lt_self hδ₀) hz (ball_subset_closedBall hq)) (by positivity))

/-- **Iterated derivatives of a bilinearly weighted Cauchy–Fueter kernel potential.** If `φ` is
positively separated from `q₀` almost everywhere and `g : X → G` is Bochner integrable,
`iteratedFDeriv ℝ m` commutes with integration of `B (g z, cauchyFueterKernel (φ z) q)`. -/
theorem iteratedFDeriv_integral_bilinear_cauchyFueterKernel {B : G × ℍ → E}
    (hB : IsBoundedBilinearMap ℝ B) {φ : X → ℍ} {g : X → G}
    {q₀ : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, B (g z, cauchyFueterKernel (φ z) q) ∂μ) q₀ =
      ∫ z, (hB.toContinuousLinearMap (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀) ∂μ := by
  obtain ⟨K, hK_pos, hK⟩ := hB.bound
  obtain ⟨C, _, hC⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_mem_closedBall m
  set s := closedBall q₀ (δ / 2)
  have hs : s ∈ 𝓝 q₀ := closedBall_mem_nhds q₀ (half_pos hδ₀)
  have hsep : ∀ᵐ z ∂μ, ∀ q ∈ s, φ z ≠ q := by
    filter_upwards [hδ] with z hz q hq heq
    have hq' : ‖q - q₀‖ ≤ δ / 2 := by simpa [s, mem_closedBall, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hcomm := iteratedFDeriv_integral_of_dominated (n := (m : ℕ∞))
    (f := fun z q ↦ B (g z, cauchyFueterKernel (φ z) q))
    (bound := fun k z ↦ K * ‖g z‖ * (C / (δ - δ / 2) ^ (3 + k))) hs
    (hsep.mono fun z hz q hq ↦ (hB.toContinuousLinearMap (g z)).contDiff.contDiffAt.comp q
      (contDiffAt_cauchyFueterKernel_right (hz q hq)))
    (fun q hq k hk ↦ by
      have hk' : k ≤ m := Nat.cast_le.mp hk
      refine (aestronglyMeasurable_bilinear_comp_iteratedFDeriv_cauchyFueterKernel
        hB hφ hg k q).congr ?_
      filter_upwards [hsep] with z hz
      exact ((hB.toContinuousLinearMap (g z)).iteratedFDeriv_comp_left
        (contDiffAt_cauchyFueterKernel_right (hz q hq) (n := m)) (mod_cast hk')).symm)
    (by
      filter_upwards [hδ, hsep] with z hz hzne q hq k hk
      have hk' : k ≤ m := Nat.cast_le.mp hk
      have hcomp := (hB.toContinuousLinearMap (g z)).iteratedFDeriv_comp_left
        (contDiffAt_cauchyFueterKernel_right (hzne q hq) (n := m)) (mod_cast hk')
      dsimp only [Function.comp_def, IsBoundedBilinearMap.toContinuousLinearMap_apply] at hcomp
      rw [hcomp]
      exact (norm_bilinear_comp_multilinear_le hB hK_pos.le hK (g z) _).trans
        (mul_le_mul_of_nonneg_left (hC k hk' (half_lt_self hδ₀) hz hq) (by positivity)))
    (fun k _ ↦ (hg.norm.const_mul K).mul_const _) (k := m) le_rfl
  rw [hcomm]
  refine integral_congr_ae ?_
  filter_upwards [hsep] with z hz
  exact (hB.toContinuousLinearMap (g z)).iteratedFDeriv_comp_left
    (contDiffAt_cauchyFueterKernel_right (hz q₀ (mem_closedBall_self (half_pos hδ₀).le)) (n := m))
    le_rfl

variable (X) in
/-- Uniform decay bound on the `m`-th derivative of a bilinearly weighted Cauchy–Fueter kernel
potential in terms of the separation scale `δ` and the `L¹` norm of `g`. The constant depends only
on the bilinear pairing `B` and the maximum order `N`, uniformly across all measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le
    {B : G × ℍ → E} (hB : IsBoundedBilinearMap ℝ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {μ : Measure X} {φ : X → ℍ} {g : X → G}
      {q₀ : ℍ} {δ : ℝ},
        AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
        ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, B (g z, cauchyFueterKernel (φ z) q) ∂μ) q₀‖ ≤
          C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ := by
  obtain ⟨K, hK_pos, hK⟩ := hB.bound
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub N
  refine ⟨K * C, mul_pos hK_pos hC, fun m hm {μ φ g q₀ δ} hφ hg hδ₀ hδ ↦ ?_⟩
  rw [iteratedFDeriv_integral_bilinear_cauchyFueterKernel hB m hφ hg hδ₀ hδ]
  refine (norm_integral_le_of_norm_le (hg.norm.const_mul (K * C / δ ^ (3 + m))) ?_).trans_eq
    (integral_const_mul _ _)
  filter_upwards [hδ] with z hz
  calc ‖(hB.toContinuousLinearMap (g z)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀)‖
      ≤ K * ‖g z‖ * ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀‖ :=
        norm_bilinear_comp_multilinear_le hB hK_pos.le hK (g z) _
    _ ≤ K * ‖g z‖ * (C / δ ^ (3 + m)) :=
        mul_le_mul_of_nonneg_left (hbound m hm hδ₀ hz) (by positivity)
    _ = K * C / δ ^ (3 + m) * ‖g z‖ := by ring

/-- Smoothness at `q₀` of a left Cauchy–Fueter kernel potential
`q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`. -/
theorem contDiffAt_integral_cauchyFueterKernel_mul {φ : X → ℍ} {g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀ :=
  contDiffAt_integral_bilinear_cauchyFueterKernel
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)).symm hφ hg hδ₀ hδ

/-- Smoothness at `q₀` of a right Cauchy–Fueter kernel potential
`q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`. -/
theorem contDiffAt_integral_mul_cauchyFueterKernel {φ : X → ℍ} {g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀ :=
  contDiffAt_integral_bilinear_cauchyFueterKernel
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)) hφ hg hδ₀ hδ

/-- **Iterated derivatives of a left Cauchy–Fueter kernel potential.** Right multiplication by
`g z` acts on each kernel jet through `MulOpposite.op (g z)`. -/
theorem iteratedFDeriv_integral_cauchyFueterKernel_mul {φ : X → ℍ} {g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀ =
      ∫ z, MulOpposite.op (g z) • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀ ∂μ :=
  iteratedFDeriv_integral_bilinear_cauchyFueterKernel
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)).symm m hφ hg hδ₀ hδ

/-- **Iterated derivatives of a right Cauchy–Fueter kernel potential.** Left multiplication by
`g z` acts on each kernel jet through the left `ℍ`-action `•`. -/
theorem iteratedFDeriv_integral_mul_cauchyFueterKernel {φ : X → ℍ} {g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀ =
      ∫ z, g z • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀ ∂μ :=
  iteratedFDeriv_integral_bilinear_cauchyFueterKernel
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)) m hφ hg hδ₀ hδ

variable (X) in
/-- Uniform decay bound on the `m`-th derivative of a left Cauchy–Fueter kernel potential
`q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`, uniform across all measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {μ : Measure X} {φ g : X → ℍ} {q₀ : ℍ} {δ : ℝ},
      AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
      ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀‖ ≤
        C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ :=
  exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le X
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)).symm N

variable (X) in
/-- Uniform decay bound on the `m`-th derivative of a right Cauchy–Fueter kernel potential
`q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`, uniform across all measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_mul_cauchyFueterKernel_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {μ : Measure X} {φ g : X → ℍ} {q₀ : ℍ} {δ : ℝ},
      AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
      ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀‖ ≤
        C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ :=
  exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le X
    (isBoundedBilinearMap_mul (𝕜 := ℝ) (A := ℍ)) N

end KernelPotentials

/-! ### Differentiated Cauchy–Fueter representations on boxes and affine parallelepipeds -/

section BoundaryRepresentations

/-- Positive separation of the eight extended face planes of a box from an interior point `x₀`,
together with an open ball inside the open box image. -/
private theorem exists_ball_subset_and_le_norm_box_face {a b x₀ : Fin 4 → ℝ}
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ∃ δ > 0, ball (dq x₀) δ ⊆ dq '' pi univ (fun i ↦ Ioo (a i) (b i)) ∧
      ∀ (i : Fin 4) (c : ℝ), (c = a i ∨ c = b i) → ∀ u : Fin 3 → ℝ,
        δ ≤ ‖dq (i.insertNth c u) - dq x₀‖ := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  have he (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  let U := pi univ (fun i ↦ Ioo (a i) (b i))
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hx₀ : x₀ ∈ U := mem_pi.mpr fun i _ ↦ ⟨ha i, hb i⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap U hU) (e x₀) (mem_image_of_mem e hx₀)
  refine ⟨δ, hδ, ?_, fun i c hc u ↦ ?_⟩
  · simpa only [← he] using hball
  · by_contra hn
    obtain ⟨y, hy, heq⟩ :=
      hball (by simpa only [mem_ball, dist_eq_norm, he] using lt_of_not_ge hn)
    have hy' : y = i.insertNth c u := e.injective heq
    have hi := mem_pi.mp hy i (mem_univ i)
    rw [hy', Fin.insertNth_apply_same] at hi
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hi.1
    · exact lt_irrefl _ hi.2

/-- Smoothness at any interior point `dq x₀` of the left Cauchy–Fueter box boundary potential of a
density `g` continuous on the closed box. -/
theorem contDiffAt_boxBoundarySum_cauchyFueterKernel_left
    {a b x₀ : Fin 4 → ℝ} {g : ℍ → ℍ} {n : ℕ∞}
    (hg : ContinuousOn g (dq '' Icc a b))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * g (dq x))) (dq x₀) := by
  obtain ⟨δ, hδ₀, _, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  simp only [boxBoundarySum_def, mul_assoc]
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hface (c : ℝ) (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ n
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          cauchyFueterKernel (dq (i.insertNth c u)) q *
            (dq (Pi.single i 1) * g (dq (i.insertNth c u)))) (dq x₀) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    refine contDiffAt_integral_cauchyFueterKernel_mul
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
      (ContinuousOn.integrableOn_compact isCompact_Icc ?_) hδ₀ (ae_of_all _ (hdist i c hc))
    exact continuousOn_const.mul (hg.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
  exact (hface (b i) (Or.inr rfl)).sub (hface (a i) (Or.inl rfl))

/-- Smoothness at any interior point `dq x₀` of the right Cauchy–Fueter box boundary potential of a
density `g` continuous on the closed box. -/
theorem contDiffAt_boxBoundarySum_cauchyFueterKernel_right
    {a b x₀ : Fin 4 → ℝ} {g : ℍ → ℍ} {n : ℕ∞}
    (hg : ContinuousOn g (dq '' Icc a b))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ g (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) (dq x₀) := by
  obtain ⟨δ, hδ₀, _, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  simp only [boxBoundarySum_def]
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hface (c : ℝ) (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ n
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (g (dq (i.insertNth c u)) * dq (Pi.single i 1)) *
            cauchyFueterKernel (dq (i.insertNth c u)) q) (dq x₀) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    refine contDiffAt_integral_mul_cauchyFueterKernel
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
      (ContinuousOn.integrableOn_compact isCompact_Icc ?_) hδ₀ (ae_of_all _ (hdist i c hc))
    exact (hg.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩)).mul continuousOn_const
  exact (hface (b i) (Or.inr rfl)).sub (hface (a i) (Or.inl rfl))

/-- Differentiating the left Cauchy–Fueter box boundary potential at an interior point `dq x₀`, for
any boundary density `g` continuous on the closed box. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left
    {a b x₀ : Fin 4 → ℝ} {g : ℍ → ℍ} (m : ℕ)
    (hg : ContinuousOn g (dq '' Icc a b))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * g (dq x))) (dq x₀) =
      boxBoundarySum a b
        (fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * g (dq x)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, _, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_int (i : Fin 4) {c : ℝ} (hc : c ∈ Icc (a i) (b i)) :
      IntegrableOn (fun u ↦ dq (Pi.single i 1) * g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact continuousOn_const.mul (hg.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc, hu⟩))
  have hface_cd (i : Fin 4) {c : ℝ} (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ m
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          cauchyFueterKernel (dq (i.insertNth c u)) q *
            (dq (Pi.single i 1) * g (dq (i.insertNth c u)))) (dq x₀) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    exact (contDiffAt_integral_cauchyFueterKernel_mul (n := m)
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
      (hface_int i hcIcc) hδ₀ (ae_of_all _ (hdist i c hc))).of_le le_rfl
  simp only [boxBoundarySum_def, mul_assoc]
  rw [iteratedFDeriv_fun_sum_apply fun i _ ↦
    (hface_cd i (Or.inr rfl)).sub (hface_cd i (Or.inl rfl))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Pi.sub_def, iteratedFDeriv_sub_apply (hface_cd i (Or.inr rfl)) (hface_cd i (Or.inl rfl)),
    iteratedFDeriv_integral_cauchyFueterKernel_mul m
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth (b i) u)).aestronglyMeasurable
      (hface_int i ⟨hab i, le_rfl⟩) hδ₀ (ae_of_all _ (hdist i (b i) (Or.inr rfl))),
    iteratedFDeriv_integral_cauchyFueterKernel_mul m
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth (a i) u)).aestronglyMeasurable
      (hface_int i ⟨le_rfl, hab i⟩) hδ₀ (ae_of_all _ (hdist i (a i) (Or.inl rfl)))]

/-- Differentiating the right Cauchy–Fueter box boundary potential at an interior point `dq x₀`,
for any boundary density `g` continuous on the closed box. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right
    {a b x₀ : Fin 4 → ℝ} {g : ℍ → ℍ} (m : ℕ)
    (hg : ContinuousOn g (dq '' Icc a b))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ g (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) (dq x₀) =
      boxBoundarySum a b
        (fun i x ↦ (g (dq x) * dq (Pi.single i 1)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, _, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_int (i : Fin 4) {c : ℝ} (hc : c ∈ Icc (a i) (b i)) :
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)) * dq (Pi.single i 1))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact (hg.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc, hu⟩)).mul continuousOn_const
  have hface_cd (i : Fin 4) {c : ℝ} (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ m
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (g (dq (i.insertNth c u)) * dq (Pi.single i 1)) *
            cauchyFueterKernel (dq (i.insertNth c u)) q) (dq x₀) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    exact (contDiffAt_integral_mul_cauchyFueterKernel (n := m)
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
      (hface_int i hcIcc) hδ₀ (ae_of_all _ (hdist i c hc))).of_le le_rfl
  simp only [boxBoundarySum_def]
  rw [iteratedFDeriv_fun_sum_apply fun i _ ↦
    (hface_cd i (Or.inr rfl)).sub (hface_cd i (Or.inl rfl))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Pi.sub_def, iteratedFDeriv_sub_apply (hface_cd i (Or.inr rfl)) (hface_cd i (Or.inl rfl)),
    iteratedFDeriv_integral_mul_cauchyFueterKernel m
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth (b i) u)).aestronglyMeasurable
      (hface_int i ⟨hab i, le_rfl⟩) hδ₀ (ae_of_all _ (hdist i (b i) (Or.inr rfl))),
    iteratedFDeriv_integral_mul_cauchyFueterKernel m
      (by fun_prop : Continuous fun u ↦ dq (i.insertNth (a i) u)).aestronglyMeasurable
      (hface_int i ⟨le_rfl, hab i⟩) hδ₀ (ae_of_all _ (hdist i (a i) (Or.inl rfl)))]

/-- **Differentiated left Cauchy–Fueter formula on a box.** For `f` continuous on the closed box
and left Fueter regular in its open interior, the `m`-th iterated Fréchet derivative at every
interior point `dq x₀` is `1 / (2π²)` times the boundary flux of the kernel `m`-jets multiplied on
the right by `eᵢ * f (dq x)`. -/
theorem left_cauchyFueter_iteratedFDeriv_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * f (dq x)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, _⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, hy, rfl⟩ := hball hq
    exact left_cauchyFueter_box hc (hf.mono sdiff_subset)
      (fun i ↦ (mem_pi.mp hy i (mem_univ i)).1) (fun i ↦ (mem_pi.mp hy i (mem_univ i)).2)
  have hsum_cd :=
    (contDiffAt_boxBoundarySum_cauchyFueterKernel_left (n := m) hc ha hb).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left m hc ha hb]

/-- **Differentiated right Cauchy–Fueter formula on a box.** For `f` continuous on the closed box
and right Fueter regular in its open interior, the `m`-th iterated Fréchet derivative at every
interior point `dq x₀` is `1 / (2π²)` times the boundary flux of `f (dq x) * eᵢ` acting on the left
of the kernel `m`-jets. -/
theorem right_cauchyFueter_iteratedFDeriv_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ (f (dq x) * dq (Pi.single i 1)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, _⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, hy, rfl⟩ := hball hq
    exact right_cauchyFueter_box hc (hf.mono sdiff_subset)
      (fun i ↦ (mem_pi.mp hy i (mem_univ i)).1) (fun i ↦ (mem_pi.mp hy i (mem_univ i)).2)
  have hsum_cd :=
    (contDiffAt_boxBoundarySum_cauchyFueterKernel_right (n := m) hc ha hb).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right m hc ha hb]

/-- Positive separation of the eight parametrized faces of an invertible affine parallelepiped
`u ↦ p + L u` from an interior point `dq x₀`, together with an open ball inside the open
parallelepiped image. -/
private theorem exists_ball_subset_and_le_norm_affine_face
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ}
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    ∃ δ > 0,
      ball (dq x₀) δ ⊆ dq '' ((fun u ↦ p + L u) '' pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) ∧
      ∀ (j : Fin 4) (c : ℝ), (c = 0 ∨ c = 1) → ∀ u : Fin 3 → ℝ,
        δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖ := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  let A := L.toHomeomorph.trans (Homeomorph.addLeft p)
  let U := pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)
  have he (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hpole : x₀ ∈ A '' U := ⟨L.symm (x₀ - p), hx₀, by simp [A]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap _ (A.isOpenMap _ hU))
    (e x₀) (mem_image_of_mem e hpole)
  have hA : (A : (Fin 4 → ℝ) → Fin 4 → ℝ) = fun u ↦ p + L u := by
    funext u
    simp [A]
  refine ⟨δ, hδ, ?_, fun j c hc u ↦ ?_⟩
  · simpa only [← he, hA] using hball
  · by_contra hn
    obtain ⟨y, hy, hyq⟩ :=
      hball (by simpa only [mem_ball, dist_eq_norm, he] using lt_of_not_ge hn)
    have hy' : y = p + L (j.insertNth c u) := e.injective hyq
    obtain ⟨v, hv, hvq⟩ := hy
    have hv' : v = j.insertNth c u := A.injective (by simpa [A, hy'] using hvq)
    have hj := mem_pi.mp hv j (mem_univ j)
    rw [hv', Fin.insertNth_apply_same] at hj
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hj.1
    · exact lt_irrefl _ hj.2

/-- **Differentiated left Cauchy–Fueter formula over unit-cube affine face charts.** On a positively
oriented affine parallelepiped `u ↦ p + L u`, every iterated derivative `iteratedFDeriv ℝ m f` at an
interior point `dq x₀` is `1 / (2π²)` times the front-minus-back sum of `Icc 0 1` face integrals of
`D^m[q ↦ G(φ_F(u) - q)](dq x₀)` multiplied on the right by the oriented face normal
`affineFaceNormal L j` and `f (φ_F(u))`. -/
theorem left_cauchyFueter_iteratedFDeriv_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1), LeftFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            MulOpposite.op (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 1 u)))) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 1 u)))) (dq x₀)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            MulOpposite.op (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 0 u)))) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 0 u)))) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ := exists_ball_subset_and_le_norm_affine_face hx₀
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) •
      ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
          (cauchyFueterKernel (dq x) q) (f (dq x))) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, ⟨u, hu, rfl⟩, rfl⟩ := hball hq
    exact left_cauchyFueter_affine hL hc (fun v hv _ ↦ hf v hv) (by simpa using hu)
  have hface_int (j : Fin 4) {c : ℝ} (hc' : c ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun u ↦ ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
        f (dq (p + L (j.insertNth c u)))) (Icc (0 : Fin 3 → ℝ) 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuousOn_const.mul (hc.comp (by fun_prop) fun u hu ↦ ?_)
    exact mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩))
  have hface_cd (j : Fin 4) {c : ℝ} (hc' : c = 0 ∨ c = 1) :
      ContDiffAt ℝ m
        (fun q ↦ ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          cauchyFueterKernel (dq (p + L (j.insertNth c u))) q *
            (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
              f (dq (p + L (j.insertNth c u))))) (dq x₀) := by
    have hcIcc : c ∈ Icc (0 : ℝ) 1 := by rcases hc' with rfl | rfl <;> simp
    exact (contDiffAt_integral_cauchyFueterKernel_mul (n := m)
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth c u))).aestronglyMeasurable
      (hface_int j hcIcc) hδ₀ (ae_of_all _ (hdist j c hc'))).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds]
  simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe, mul_assoc]
  have hsum_cd : ContDiffAt ℝ m
      (fun q ↦ ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) q *
              (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 1 u))))) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) q *
              (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 0 u)))))) (dq x₀) :=
    ContDiffAt.sum fun j _ ↦ (hface_cd j (Or.inr rfl)).sub (hface_cd j (Or.inl rfl))
  rw [iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_fun_sum_apply fun j _ ↦
      (hface_cd j (Or.inr rfl)).sub (hface_cd j (Or.inl rfl))]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Pi.sub_def, iteratedFDeriv_sub_apply (hface_cd j (Or.inr rfl)) (hface_cd j (Or.inl rfl)),
    iteratedFDeriv_integral_cauchyFueterKernel_mul m
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth 1 u))).aestronglyMeasurable
      (hface_int j (by simp)) hδ₀ (ae_of_all _ (hdist j 1 (Or.inr rfl))),
    iteratedFDeriv_integral_cauchyFueterKernel_mul m
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth 0 u))).aestronglyMeasurable
      (hface_int j (by simp)) hδ₀ (ae_of_all _ (hdist j 0 (Or.inl rfl)))]

/-- **Differentiated right Cauchy–Fueter formula over unit-cube affine face charts.** On a
positively oriented affine parallelepiped `u ↦ p + L u`, every iterated derivative
`iteratedFDeriv ℝ m f` of a right Fueter regular function at an interior point `dq x₀` retains `f`
to the left of `affineFaceNormal L j` and the kernel `m`-jet to its right. -/
theorem right_cauchyFueter_iteratedFDeriv_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1), RightFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 1 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 1 u)))) (dq x₀)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 0 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 0 u)))) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ := exists_ball_subset_and_le_norm_affine_face hx₀
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) •
      ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
        (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
          (f (dq x)) (cauchyFueterKernel (dq x) q)) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, ⟨u, hu, rfl⟩, rfl⟩ := hball hq
    exact right_cauchyFueter_affine hL hc (fun v hv _ ↦ hf v hv) (by simpa using hu)
  have hface_int (j : Fin 4) {c : ℝ} (hc' : c ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun u ↦ f (dq (p + L (j.insertNth c u))) *
        ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j)
        (Icc (0 : Fin 3 → ℝ) 1) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine (hc.comp (by fun_prop) fun u hu ↦ ?_).mul continuousOn_const
    exact mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hc', hu⟩))
  have hface_cd (j : Fin 4) {c : ℝ} (hc' : c = 0 ∨ c = 1) :
      ContDiffAt ℝ m
        (fun q ↦ ∫ u in Icc (0 : Fin 3 → ℝ) 1,
          (f (dq (p + L (j.insertNth c u))) *
              ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) *
            cauchyFueterKernel (dq (p + L (j.insertNth c u))) q) (dq x₀) := by
    have hcIcc : c ∈ Icc (0 : ℝ) 1 := by rcases hc' with rfl | rfl <;> simp
    exact (contDiffAt_integral_mul_cauchyFueterKernel (n := m)
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth c u))).aestronglyMeasurable
      (hface_int j hcIcc) hδ₀ (ae_of_all _ (hdist j c hc'))).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds]
  simp only [ContinuousLinearMap.rawAffineBoundary_eq, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearEquiv.coe_coe]
  have hsum_cd : ContDiffAt ℝ m
      (fun q ↦ ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 1 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) *
              cauchyFueterKernel (dq (p + L (j.insertNth 1 u))) q) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 0 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) *
              cauchyFueterKernel (dq (p + L (j.insertNth 0 u))) q)) (dq x₀) :=
    ContDiffAt.sum fun j _ ↦ (hface_cd j (Or.inr rfl)).sub (hface_cd j (Or.inl rfl))
  rw [iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_fun_sum_apply fun j _ ↦
      (hface_cd j (Or.inr rfl)).sub (hface_cd j (Or.inl rfl))]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Pi.sub_def, iteratedFDeriv_sub_apply (hface_cd j (Or.inr rfl)) (hface_cd j (Or.inl rfl)),
    iteratedFDeriv_integral_mul_cauchyFueterKernel m
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth 1 u))).aestronglyMeasurable
      (hface_int j (by simp)) hδ₀ (ae_of_all _ (hdist j 1 (Or.inr rfl))),
    iteratedFDeriv_integral_mul_cauchyFueterKernel m
      (by fun_prop : Continuous fun u ↦ dq (p + L (j.insertNth 0 u))).aestronglyMeasurable
      (hface_int j (by simp)) hδ₀ (ae_of_all _ (hdist j 0 (Or.inl rfl)))]

end BoundaryRepresentations

/-! ### Reflection of iterated derivatives and universal Cauchy-type derivative estimates -/

section UniversalEstimates

/-- Quaternionic reflection `x ↦ star (f (star x))` conjugates every iterated real Fréchet
derivative in both each input slot and the output, without any differentiability hypothesis. -/
theorem iteratedFDeriv_star_star_apply (f : ℍ → ℍ) (m : ℕ) (q : ℍ) (v : Fin m → ℍ) :
    iteratedFDeriv ℝ m (fun x ↦ star (f (star x))) (star q) v =
      star (iteratedFDeriv ℝ m f q (fun i ↦ star (v i))) := by
  let σ : ℍ ≃L[ℝ] ℍ := starL' ℝ
  have hcomp : (fun x ↦ star (f (star x))) = σ ∘ (f ∘ σ) := by
    funext x
    simp [σ]
  rw [hcomp, σ.iteratedFDeriv_comp_left, σ.iteratedFDeriv_comp_right,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [σ]

/-- Quaternionic reflection preserves the operator norm of every iterated real Fréchet derivative,
without any differentiability hypothesis. -/
@[simp]
theorem norm_iteratedFDeriv_star_star (f : ℍ → ℍ) (m : ℕ) (q : ℍ) :
    ‖iteratedFDeriv ℝ m (fun x ↦ star (f (star x))) (star q)‖ =
      ‖iteratedFDeriv ℝ m f q‖ := by
  let σ : ℍ ≃ₗᵢ[ℝ] ℍ := { starLinearEquiv ℝ with norm_map' := Quaternion.norm_star }
  have hcomp : (fun x ↦ star (f (star x))) = σ ∘ (f ∘ σ) := rfl
  have hσq : σ (star q) = q := star_star q
  rw [hcomp, σ.norm_iteratedFDeriv_comp_left, σ.norm_iteratedFDeriv_comp_right, hσq]

/-- The closed coordinate cube of side `R` centred at `x₀` has Euclidean half-diagonal
`√(4 (R / 2)²) = R`, hence maps into `closedBall (dq x₀) R`. -/
private theorem closedCube_subset_closedBall (x₀ : Fin 4 → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    dq '' Icc (fun i ↦ x₀ i - R / 2) (fun i ↦ x₀ i + R / 2) ⊆ closedBall (dq x₀) R := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall, dist_eq_norm, ← map_sub]
  have hcoord (i : Fin 4) : (x - x₀) i * (x - x₀) i ≤ (R / 2) * (R / 2) := by
    have hx1 : x₀ i - R / 2 ≤ x i := hx.1 i
    have hx2 : x i ≤ x₀ i + R / 2 := hx.2 i
    have hi : |(x - x₀) i| ≤ R / 2 := by
      rw [Pi.sub_apply, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    simpa [abs_mul_abs_self] using mul_self_le_mul_self (abs_nonneg _) hi
  have hnsq := normSq_eq_norm_mul_self (dq (x - x₀))
  simp only [normSq_def', re_dq, imI_dq, imJ_dq, imK_dq] at hnsq
  nlinarith [hcoord 0, hcoord 1, hcoord 2, hcoord 3, norm_nonneg (dq (x - x₀)), hR]

/-- Norm estimate on a single three-dimensional face of the cube of side `R` centred at `x₀`, given
a potential-decay constant `K` from `exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le`.
Each face lies at distance at least `R / 2` from `dq x₀` and has volume `R³`. -/
private theorem norm_cube_face_iteratedFDeriv_cauchyFueterKernel_left_le
    {x₀ : Fin 4 → ℝ} {R M K : ℝ} {f : ℍ → ℍ} (m : ℕ) (hR : 0 < R) (hK : 0 ≤ K)
    (hKbound : ∀ {μ : Measure (Fin 3 → ℝ)} {φ g : (Fin 3 → ℝ) → ℍ} {q₀ : ℍ} {δ : ℝ},
      AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
      ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀‖ ≤
        K / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ)
    (hc : ContinuousOn f (dq '' Icc (fun j ↦ x₀ j - R / 2) (fun j ↦ x₀ j + R / 2)))
    (hM : ∀ q ∈ dq '' Icc (fun j ↦ x₀ j - R / 2) (fun j ↦ x₀ j + R / 2), ‖f q‖ ≤ M)
    (i : Fin 4) {c : ℝ} (hc' : c = x₀ i - R / 2 ∨ c = x₀ i + R / 2) :
    ‖∫ u in Icc ((fun j ↦ x₀ j - R / 2) ∘ i.succAbove) ((fun j ↦ x₀ j + R / 2) ∘ i.succAbove),
        MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth c u))) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth c u))) (dq x₀)‖ ≤
      K / (R / 2) ^ (3 + m) * (R ^ 3 * M) := by
  let a : Fin 4 → ℝ := fun j ↦ x₀ j - R / 2
  let b : Fin 4 → ℝ := fun j ↦ x₀ j + R / 2
  have hab : a ≤ b := fun j ↦ by dsimp [a, b]; linarith [half_pos hR]
  have hcIcc : c ∈ Icc (a i) (b i) := by
    rcases hc' with rfl | rfl
    · exact ⟨le_rfl, hab i⟩
    · exact ⟨hab i, le_rfl⟩
  set F := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)
  have hg_int : IntegrableOn (fun u ↦ dq (Pi.single i 1) * f (dq (i.insertNth c u))) F :=
    ContinuousOn.integrableOn_compact isCompact_Icc <| continuousOn_const.mul
      (hc.comp (by fun_prop) fun u hu ↦
        mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
  have hsep (u : Fin 3 → ℝ) : R / 2 ≤ ‖dq (i.insertNth c u) - dq x₀‖ := by
    rw [← map_sub, norm_dq]
    have hle := PiLp.norm_apply_le (WithLp.toLp 2 (i.insertNth c u - x₀)) i
    have hval : |c - x₀ i| = R / 2 := by
      rcases hc' with rfl | rfl
      · simp [abs_of_neg (neg_lt_zero.mpr (half_pos hR))]
      · simp [abs_of_pos (half_pos hR)]
    simpa [Pi.sub_apply, Fin.insertNth_apply_same, hval] using hle
  have hpot := hKbound (μ := volume.restrict F)
    (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
    hg_int (half_pos hR) (ae_of_all _ hsep)
  rw [iteratedFDeriv_integral_cauchyFueterKernel_mul m
    (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
    hg_int (half_pos hR) (ae_of_all _ hsep)] at hpot
  refine hpot.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hunit : ‖dq (Pi.single i 1)‖ = 1 := by
    rw [← mul_self_inj (norm_nonneg _) zero_le_one, mul_one, ← normSq_eq_norm_mul_self]
    fin_cases i <;> simp [normSq_def', dq_apply]
  have hlen (r : Fin 3) : b (i.succAbove r) - a (i.succAbove r) = R := by
    dsimp [a, b]; ring
  calc ∫ u in F, ‖dq (Pi.single i 1) * f (dq (i.insertNth c u))‖
      ≤ ∫ _ in F, M := setIntegral_mono_on hg_int.norm
        (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc fun u hu ↦ by
          rw [norm_mul, hunit, one_mul]
          exact hM _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
    _ = R ^ 3 * M := by
        rw [setIntegral_const, smul_eq_mul, Measure.real]
        dsimp only [F]
        rw [Real.volume_Icc_pi_toReal (a := a ∘ i.succAbove) (b := b ∘ i.succAbove)
          fun r ↦ hab (i.succAbove r)]
        simp [Function.comp_apply, hlen, pow_three]

/-- **Universal Cauchy-type derivative estimate for left Fueter regular functions.** For every
order `m` there is a constant `C > 0`, depending on `m` alone, such that whenever `f` is left
Fueter regular on a set `Ω` containing `closedBall q₀ R` (`R > 0`) and `‖f q‖ ≤ M` on that closed
ball, `‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`. -/
theorem leftFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), LeftFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le (Fin 3 → ℝ) m
  -- Eight faces, each of separation `R / 2` and volume `R³`, normalized by `1 / (2π²)`.
  refine ⟨8 * 2 ^ (3 + m) * K / (2 * Real.pi ^ 2), by positivity,
    fun f Ω hf q₀ R hR hΩ M hM ↦ ?_⟩
  let x₀ : Fin 4 → ℝ := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)) q₀
  have hx₀ : dq x₀ = q₀ := by
    rw [congrFun coe_dq x₀]
    exact (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm_apply_apply q₀
  let a : Fin 4 → ℝ := fun i ↦ x₀ i - R / 2
  let b : Fin 4 → ℝ := fun i ↦ x₀ i + R / 2
  have ha (i : Fin 4) : a i < x₀ i := by dsimp [a]; linarith [half_pos hR]
  have hb (i : Fin 4) : x₀ i < b i := by dsimp [b]; linarith [half_pos hR]
  have hcube : dq '' Icc a b ⊆ closedBall q₀ R := hx₀ ▸ closedCube_subset_closedBall x₀ hR.le
  have hc : ContinuousOn f (dq '' Icc a b) :=
    hf.differentiableOn.continuousOn.mono (hcube.trans hΩ)
  have hIoo : pi univ (fun i ↦ Ioo (a i) (b i)) ⊆ Icc a b := fun _ hx ↦
    ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2.le⟩
  have hf_open : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))) :=
    hf.mono ((image_mono hIoo).trans (hcube.trans hΩ))
  rw [← hx₀, left_cauchyFueter_iteratedFDeriv_box m hc hf_open ha hb,
    norm_smul, Real.norm_of_nonneg (by positivity), boxBoundarySum_def]
  have hface (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i) :=
    norm_cube_face_iteratedFDeriv_cauchyFueterKernel_left_le m hR hK.le (hKbound m le_rfl)
      hc (fun q hq ↦ hM q (hcube hq)) i hc'
  have hsum : ‖∑ i : Fin 4,
      ((∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth (b i) u))) •
            iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth (b i) u))) (dq x₀)) -
        ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth (a i) u))) •
            iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth (a i) u))) (dq x₀))‖ ≤
      8 * (K / (R / 2) ^ (3 + m) * (R ^ 3 * M)) := by
    refine (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (g := fun _ ↦ 2 * (K / (R / 2) ^ (3 + m) * (R ^ 3 * M)))
        fun i _ ↦ (norm_sub_le _ _).trans ?_).trans_eq ?_)
    · linarith [hface i (Or.inr rfl), hface i (Or.inl rfl)]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  have hpi : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hR₀ : R ≠ 0 := hR.ne'
  rw [div_pow, pow_add R 3 m, inv_pow]
  field_simp [hpi, hR₀]

/-- **Universal Cauchy-type derivative estimate for right Fueter regular functions.** Obtained from
`leftFueter_iteratedFDeriv_bound` by the norm-preserving reflection `q ↦ star (f (star q))`. -/
theorem rightFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), RightFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C, hC, hleft⟩ := leftFueter_iteratedFDeriv_bound m
  refine ⟨C, hC, fun f Ω hf q₀ R hR hΩ M hM ↦ ?_⟩
  have hball : closedBall (star q₀) R ⊆ star '' Ω := by
    intro p hp
    refine ⟨star p, hΩ ?_, star_star p⟩
    rw [mem_closedBall, dist_eq_norm, ← Quaternion.norm_star, star_sub, star_star]
    simpa [mem_closedBall, dist_eq_norm] using hp
  have hbound := hleft (fun q ↦ star (f (star q))) (star '' Ω)
    hf.star_star (star q₀) R hR hball M
    (fun p hp ↦ by
      rw [Quaternion.norm_star]
      refine hM (star p) ?_
      rw [mem_closedBall, dist_eq_norm, ← Quaternion.norm_star, star_sub, star_star]
      simpa [mem_closedBall, dist_eq_norm] using hp)
  simpa only [norm_iteratedFDeriv_star_star] using hbound

end UniversalEstimates

end TauCeti
