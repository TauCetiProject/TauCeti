/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple

/-!
# Maps with constant conjugate Wirtinger derivative

Let `u : ℂ → E` take values in a complex Banach space and satisfy the inhomogeneous
Cauchy–Riemann equation with constant right-hand side, `\bar∂u = b`, that is,
`∂ₛu + i ∂ₜu = 2 b` in the coordinate `z = s + i t`. Then `u w - conj (w - c) • b` is holomorphic,
since `\bar∂ (conj (w - c) • b) = b`. This file draws two consequences.

* **The mean identity.** If `\bar∂u = b` on a disc `|z - c| < R` and `u` is continuous on its
  closure, then Cauchy's theorem for the holomorphic part, together with
  `∮ conj (z - c) dz = 2 π i R²`, gives `∮_{|z - c| = R} u(z) dz = 2 π i R² b`. Written out in the
  angle, this is `π R² (2 b) = R ∫₀^{2π} e^{iθ} u(c + R e^{iθ}) dθ`. Bounding the integral gives
  `R ‖b‖ ≤ M` whenever `‖u‖ ≤ M` on the circle. In particular, for `R ‖b‖ > M` there is no
  solution of `\bar∂u = b` on the disc whose boundary values stay in the ball of radius `M`.
* **The image bound.** A solution of `\bar∂u = b` is harmonic. Hence if `u` is continuous on a
  compact set `K`, satisfies `\bar∂u = b` at the interior points where `‖u‖ > C`, and satisfies
  `‖u‖ ≤ C` on the frontier of `K`, then `‖u‖ ≤ C` on all of `K`. This is the weak maximum
  principle applied to the harmonic functions `ℓ ∘ u` for the continuous real functionals `ℓ` of
  norm at most one, followed by Hahn–Banach.

Both are the a priori estimates for holomorphic discs with a Hamiltonian perturbation that is
linear far out. In Gromov's proof that a compact Lagrangian submanifold `L` of `ℂⁿ` bounds a
nonconstant holomorphic disc, one deforms the Cauchy–Riemann equation by a forcing term that equals
a constant vector `a` wherever `|u|` is large. The mean identity on the unit disc shows that for
`|a| > 2 max_L |z|` no disc with boundary on `L` solves the fully forced equation, and the image
bound confines all solutions of the intermediate equations to a fixed ball.

## Main results

* `TauCeti.conjWirtingerDeriv_conj_sub_smul_apply_one`: `\bar∂ (conj (w - c) • b) = b`.
* `DifferentiableAt.sub_conj_sub_smul`: if `\bar∂u = b` at `z`, then
  `u w - conj (w - c) • b` is complex differentiable at `z`.
* `TauCeti.harmonicOnNhd_of_conjWirtingerDeriv_apply_one_eq`: a solution of `\bar∂u = b` on an
  open set is harmonic there.
* `TauCeti.circleIntegral_eq_of_conjWirtingerDeriv_apply_one_eq`: the mean identity
  `∮_{|z - c| = R} u(z) dz = 2 π i R² b`.
* `TauCeti.mul_norm_le_of_conjWirtingerDeriv_apply_one_eq`: the exclusion estimate `R ‖b‖ ≤ M`.
* `TauCeti.norm_le_of_conjWirtingerDeriv_apply_one_eq_of_norm_le_frontier`: the image bound.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347 (the theorem that a compact Lagrangian submanifold of `ℂⁿ` bounds a nonconstant
  holomorphic disc).
-/

public section

open Complex Metric Set Real InnerProductSpace
open scoped ComplexConjugate Laplacian Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real derivative of the antiholomorphic affine map `w ↦ conj (w - c) • b`. -/
theorem hasFDerivAt_conj_sub_smul (c : ℂ) (b : E) (z : ℂ) :
    HasFDerivAt (fun w : ℂ ↦ conj (w - c) • b)
      ((conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.smulRight b) z := by
  have h : HasFDerivAt (fun w : ℂ ↦ conj (w - c))
      ((conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) z := by
    simpa [Function.comp_def] using
      (conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  exact h.smul_const b

/-- The map `w ↦ conj (w - c) • b` has conjugate Wirtinger derivative `b`: it solves
`\bar∂u = b`. -/
theorem conjWirtingerDeriv_conj_sub_smul_apply_one (c : ℂ) (b : E) (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ conj (w - c) • b) z 1 = b := by
  rw [conjWirtingerDeriv_apply, (hasFDerivAt_conj_sub_smul c b z).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
    map_one, smul_eq_mul, mul_one, conj_I, smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]
  module

/-- If `u` is real differentiable at `z` with `\bar∂u(z) = b`, then removing the antiholomorphic
affine part, `w ↦ u w - conj (w - c) • b` is complex differentiable at `z`. -/
theorem _root_.DifferentiableAt.sub_conj_sub_smul {u : ℂ → E} {c z : ℂ} {b : E}
    (hu : DifferentiableAt ℝ u z) (hb : conjWirtingerDeriv u z 1 = b) :
    DifferentiableAt ℂ (fun w ↦ u w - conj (w - c) • b) z := by
  have hl := (hasFDerivAt_conj_sub_smul c b z).differentiableAt
  refine (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hu.sub hl)).2 ?_
  rw [conjWirtingerDeriv_sub hu hl, sub_apply, hb,
    conjWirtingerDeriv_conj_sub_smul_apply_one, sub_self]

/-- A solution of `\bar∂u = b` with constant `b` on an open set is harmonic there: it is the sum
of a holomorphic map and the real-affine map `w ↦ conj w • b`. -/
theorem harmonicOnNhd_of_conjWirtingerDeriv_apply_one_eq [CompleteSpace E] {u : ℂ → E}
    {U : Set ℂ} {b : E} (hU : IsOpen U) (hd : ∀ z ∈ U, DifferentiableAt ℝ u z)
    (hb : ∀ z ∈ U, conjWirtingerDeriv u z 1 = b) :
    HarmonicOnNhd u U := by
  intro z hz
  have hg : DifferentiableOn ℂ (fun w ↦ u w - conj w • b) U := fun w hw ↦ by
    simpa using ((hd w hw).sub_conj_sub_smul (c := 0) (hb w hw)).differentiableWithinAt
  have hgh : HarmonicAt (fun w ↦ u w - conj w • b) z :=
    ((hg.contDiffOn (n := 2) hU).contDiffAt (hU.mem_nhds hz)).harmonicAt
  have hconj : HarmonicAt (fun w : ℂ ↦ conj w) z :=
    analyticAt_id.harmonicAt_conj
  have hlin : HarmonicAt (fun w : ℂ ↦ conj w • b) z := by
    simpa [Function.comp_def] using
      hconj.comp_CLM ((ContinuousLinearMap.toSpanSingleton ℂ b).restrictScalars ℝ)
  convert hgh.add hlin using 1
  ext w
  simp

variable [CompleteSpace E]

/-- **The mean identity for `\bar∂u = b`.** If `u` is continuous on the closed disc
`|z - c| ≤ R` and real differentiable with `\bar∂u = b` on the open disc, then
`∮_{|z - c| = R} u(z) dz = 2 π i R² b`. In the angle `θ`, with `a = 2 b = ∂ₛu + i ∂ₜu`, this
reads `π R² a = R ∫₀^{2π} e^{iθ} u(c + R e^{iθ}) dθ`. -/
theorem circleIntegral_eq_of_conjWirtingerDeriv_apply_one_eq {u : ℂ → E} {c : ℂ} {R : ℝ}
    {b : E} (hR : 0 ≤ R) (hc : ContinuousOn u (closedBall c R))
    (hd : ∀ z ∈ ball c R, DifferentiableAt ℝ u z)
    (hb : ∀ z ∈ ball c R, conjWirtingerDeriv u z 1 = b) :
    (∮ z in C(c, R), u z) = (2 * π * R ^ 2 * I : ℂ) • b := by
  rcases hR.eq_or_lt with rfl | hR'
  · simp
  have hlc : Continuous fun w : ℂ ↦ conj (w - c) • b := by fun_prop
  -- Cauchy's theorem for the holomorphic part `u w - conj (w - c) • b`.
  have hg : (∮ z in C(c, R), (u z - conj (z - c) • b)) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      (hc.sub hlc.continuousOn) fun z hz ↦
        (hd z hz.1).sub_conj_sub_smul (hb z hz.1)
  -- On the circle `conj (z - c) = R² (z - c)⁻¹`, whose integral is `2 π i R²`.
  have hconj : (∮ z in C(c, R), conj (z - c)) = 2 * π * R ^ 2 * I := by
    have heq : EqOn (fun z ↦ conj (z - c)) (fun z ↦ (R ^ 2 : ℂ) • (z - c)⁻¹) (sphere c R) := by
      intro z hz
      have hzc : z - c ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hz hR'.ne')
      have hn : ‖z - c‖ = R := by simpa [dist_eq_norm] using hz
      simp only [smul_eq_mul]
      rw [eq_mul_inv_iff_mul_eq₀ hzc, mul_comm, mul_conj, normSq_eq_norm_sq, hn]
      push_cast
      ring
    rw [circleIntegral.integral_congr hR heq, circleIntegral.integral_smul,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR'), smul_eq_mul]
    ring
  rw [circleIntegral.integral_sub ((hc.mono sphere_subset_closedBall).circleIntegrable hR)
    (hlc.continuousOn.circleIntegrable hR), circleIntegral.integral_smul_const, hconj,
    sub_eq_zero] at hg
  exact hg

/-- **The exclusion estimate for `\bar∂u = b`.** If `u` is continuous on the closed disc
`|z - c| ≤ R`, real differentiable with `\bar∂u = b` on the open disc, and `‖u‖ ≤ M` on the
boundary circle, then `R ‖b‖ ≤ M`. So for `R ‖b‖ > M` the equation `\bar∂u = b` has no solution
on the disc with boundary values in the closed ball of radius `M`. -/
theorem mul_norm_le_of_conjWirtingerDeriv_apply_one_eq {u : ℂ → E} {c : ℂ} {R M : ℝ} {b : E}
    (hR : 0 ≤ R) (hc : ContinuousOn u (closedBall c R))
    (hd : ∀ z ∈ ball c R, DifferentiableAt ℝ u z)
    (hb : ∀ z ∈ ball c R, conjWirtingerDeriv u z 1 = b)
    (hM : ∀ z ∈ sphere c R, ‖u z‖ ≤ M) :
    R * ‖b‖ ≤ M := by
  rcases hR.eq_or_lt with rfl | hR'
  · simpa using (norm_nonneg _).trans (hM c (by simp))
  have h := circleIntegral.norm_integral_le_of_norm_le_const hR hM
  rw [circleIntegral_eq_of_conjWirtingerDeriv_apply_one_eq hR hc hd hb, norm_smul] at h
  have hn : ‖(2 * π * R ^ 2 * I : ℂ)‖ = 2 * π * R * R := by
    simp only [norm_mul, Complex.norm_ofNat, norm_real, norm_I, norm_pow, Real.norm_eq_abs,
      abs_of_pos pi_pos, abs_of_pos hR', mul_one]
    ring
  rw [hn] at h
  have h2πR : 0 < 2 * π * R := by positivity
  nlinarith

/-- **The image bound for `\bar∂u = b`.** Let `K ⊆ ℂ` be compact and `u` continuous on `K`.
Suppose that at every interior point of `K` where `‖u‖ > C`, `u` is real differentiable with
`\bar∂u = b`, for one constant `b`, and that `‖u‖ ≤ C` on the frontier of `K`. Then `‖u‖ ≤ C` on
all of `K`. Nothing is assumed at interior points where `‖u‖ ≤ C`. -/
theorem norm_le_of_conjWirtingerDeriv_apply_one_eq_of_norm_le_frontier {u : ℂ → E} {K : Set ℂ}
    {b : E} {C : ℝ} (hK : IsCompact K) (hu : ContinuousOn u K)
    (hd : ∀ z ∈ interior K, C < ‖u z‖ → DifferentiableAt ℝ u z)
    (hb : ∀ z ∈ interior K, C < ‖u z‖ → conjWirtingerDeriv u z 1 = b)
    (hfr : ∀ z ∈ frontier K, ‖u z‖ ≤ C) :
    ∀ z ∈ K, ‖u z‖ ≤ C := by
  -- `u` is harmonic on the open set of interior points where `‖u‖ > C`.
  set U := interior K ∩ u ⁻¹' {y | C < ‖y‖}
  have hU : IsOpen U := (hu.mono interior_subset).isOpen_inter_preimage isOpen_interior
    (isOpen_lt continuous_const continuous_norm)
  have hharm : HarmonicOnNhd u U :=
    harmonicOnNhd_of_conjWirtingerDeriv_apply_one_eq hU (fun z hz ↦ hd z hz.1 hz.2)
      fun z hz ↦ hb z hz.1 hz.2
  -- The weak maximum principle bounds `ℓ ∘ u` by `C` for every real functional `‖ℓ‖ ≤ 1`.
  have hℓ : ∀ ℓ : StrongDual ℝ E, ‖ℓ‖ ≤ 1 → ∀ z ∈ K, ℓ (u z) ≤ C := by
    intro ℓ hℓ
    have hle : ∀ y, ℓ y ≤ ‖y‖ := fun y ↦ (le_abs_self _).trans <|
      (ℓ.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg y) hℓ)
    have hUℓ : ∀ ⦃z⦄, z ∈ interior K → C < ℓ (u z) → HarmonicAt (fun w ↦ ℓ (u w)) z :=
      fun z hz hlt ↦ (hharm z ⟨hz, hlt.trans_le (hle _)⟩).comp_CLM ℓ
    exact le_of_laplacian_nonneg_of_lt_le_frontier hK (ℓ.continuous.comp_continuousOn hu)
      (fun z hz hlt ↦ (hUℓ hz hlt).1)
      (fun z hz hlt ↦ (hUℓ hz hlt).2.self_of_nhds.symm.le)
      (fun z hz ↦ (hle _).trans (hfr z hz))
  intro z hz
  obtain ⟨g, hg, hgu⟩ := exists_dual_vector'' ℝ (u z)
  simpa [hgu] using hℓ g hg z hz

end TauCeti
