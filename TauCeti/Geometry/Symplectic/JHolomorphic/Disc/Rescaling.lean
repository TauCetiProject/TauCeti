/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Disc.Existence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Algebra.Ring.CayleyChart
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# Pseudoholomorphic discs for structures of class `C²`

Let `F` be a finite-dimensional complex normed space and `J : F → (F →L[ℝ] F)` a field of real
endomorphisms of class `C²` near `0` with `J(0) v = i v`, such as an almost complex structure
written in coordinates centred at a point where it is standard. The discs of
`TauCeti.Geometry.Symplectic.JHolomorphic.Disc.Existence` solve `∂ₛu + J(u) ∂ₜu = 0` when the
derivative of `J` and its Lipschitz constant are small on the ball of radius `4`. Rescaling the
argument, `x ↦ J(t x)` with small `t > 0`, makes them so, and rescaling the disc back,
`z ↦ t v(z / (t μ))`, gives solutions near `0` of the original equation.

* Through the centre `0` there is a solution in every complex direction: for every `ξ ∈ F` there
  is a `C¹` solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`
  (`TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`).
* If moreover `J(x)² = -1` near `0`, the Beltrami coefficient `Q = -cayleyCoord i J` of `J` is of
  class `C²` near `0`, vanishes at `0` and takes conjugate-linear values, and the Beltrami equation
  `\bar∂u = Q(u) ∂u` is equivalent to `∂ₛu + J(u) ∂ₜu = 0`. The rotation-equivariant discs of the
  Beltrami equation then give a family of discs `u_ξ` through `0` in every direction `‖ξ‖ ≤ 1`, on
  a common disc, with `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`
  (`TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq`).
  This equivariance is the `U(1)` normal-frame equivariance of the normal disc families used to
  foliate a neighbourhood of a pseudoholomorphic curve in the large-parameter analysis of the
  Seiberg–Witten equations.
* The discs are close to complex lines. In the rescaled coordinates the Beltrami coefficient is
  of size `O(t)` in the `C¹` norm, and the disc of a small coefficient is close in `C¹` to the
  disc `w ↦ w ξ` of the zero coefficient. So, for any `κ > 0`, the family can be chosen on a disc
  small enough that `‖du_ξ - (w ↦ w ξ)‖ ≤ κ` there. With `κ = 1/2` and `‖ξ‖ = 1`, `u_ξ` is
  `2`-antilipschitz on that disc and so is its derivative at every point: each disc is an
  embedding, injective with injective derivative.

## Main results

* `TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`: for a structure of class
  `C²` near `0`, a solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`, for every `ξ`.
* `TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq`: for
  an almost complex structure of class `C²` near `0` and any `κ > 0`, a family of such discs
  `u_ξ`, `‖ξ‖ ≤ 1`, on a common disc, with `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1` and derivatives
  within `κ` of the derivative of `w ↦ w ξ`.
* `TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_antilipschitzWith`:
  such a family in which every disc with a unit first jet, and its derivative at every point, is
  `2`-antilipschitz, so that the discs are embedded.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public noncomputable section

open Complex Metric Set Function
open scoped NNReal Topology

namespace TauCeti

/-! ### Rescaling -/

section Rescaling

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Rescaling the argument of a structure by `t` multiplies its derivative by `t` and the
Lipschitz constant of the derivative by `t²`: bounds `A` and `L` on the ball of radius `r ≥ 4 t`
give bounds `t A` and `t² L` for `x ↦ J (t x)` on the ball of radius `4`. -/
private theorem rescale_bounds (J : F → F →L[ℝ] F) {r A L t : ℝ} (ht : 0 < t) (htr : 4 * t ≤ r)
    (hd : ∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ J x)
    (hA : ∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ A)
    (hL : ∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ L * ‖x - y‖) :
    (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ (fun x ↦ J (t • x)) x) ∧
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (fun x ↦ J (t • x)) x‖ ≤ t * A) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ J (t • x)) x - fderiv ℝ (fun x ↦ J (t • x)) y‖ ≤
          t ^ 2 * L * ‖x - y‖ := by
  have hmem : ∀ x ∈ closedBall (0 : F) 4, t • x ∈ closedBall (0 : F) r := fun x hx ↦ by
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_smul, Real.norm_of_nonneg ht.le]
    nlinarith
  have hfd : ∀ x ∈ closedBall (0 : F) 4, HasFDerivAt (fun x ↦ J (t • x))
      ((fderiv ℝ J (t • x)).comp (t • ContinuousLinearMap.id ℝ F)) x := fun x hx ↦
    (hd _ (hmem x hx)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have hsmul : ‖t • ContinuousLinearMap.id ℝ F‖ ≤ t :=
    (norm_smul_le t (ContinuousLinearMap.id ℝ F)).trans (by
      rw [Real.norm_of_nonneg ht.le]
      exact mul_le_of_le_one_right ht.le ContinuousLinearMap.norm_id_le)
  refine ⟨fun x hx ↦ (hfd x hx).differentiableAt, fun x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · rw [(hfd x hx).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul hsmul (hA _ (hmem x hx)) (norm_nonneg _) ht.le
  · rw [(hfd x hx).fderiv, (hfd y hy).fderiv, ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hxy := hL _ (hmem x hx) _ (hmem y hy)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le] at hxy
    calc ‖fderiv ℝ J (t • x) - fderiv ℝ J (t • y)‖ * ‖t • ContinuousLinearMap.id ℝ F‖
        ≤ L * (t * ‖x - y‖) * t := mul_le_mul hxy hsmul (norm_nonneg _)
          ((norm_nonneg (fderiv ℝ J (t • x) - fderiv ℝ J (t • y))).trans hxy)
      _ = t ^ 2 * L * ‖x - y‖ := by ring

/-- The derivative of the rescaled disc `z ↦ t v(z / κ)`. -/
private theorem fderiv_rescale_apply {v : ℂ → F} {z : ℂ} (t κ : ℝ)
    (hv : DifferentiableAt ℝ v (κ⁻¹ • z)) (w : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ t • v (κ⁻¹ • z)) z w = (t * κ⁻¹) • fderiv ℝ v (κ⁻¹ • z) w := by
  have h : HasFDerivAt (fun z : ℂ ↦ t • v (κ⁻¹ • z)) _ z :=
    (hv.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul κ⁻¹)).const_smul t
  rw [h.fderiv]
  simp [smul_smul]

/-- A disc `v`, `C¹` on the disc of radius `2` with `v(0) = 0` and `∂ₛv(0) = μ ξ`, rescales to
the disc `u(z) = t v(z / (t μ))`, `C¹` on the disc of radius `t μ / 2` with `u(0) = 0` and
`∂ₛu(0) = ξ`; there `Du(z) = μ⁻¹ Dv(z / (t μ))`. -/
private theorem rescale_props {ξ : F} {t μ : ℝ} (ht : 0 < t) (hμ : 0 < μ) {v : ℂ → F}
    (hvC : ContDiffOn ℝ 1 v (ball 0 2)) (hv0 : v 0 = 0) (hv1 : fderiv ℝ v 0 1 = μ • ξ) :
    ContDiffOn ℝ 1 (fun z ↦ t • v ((t * μ)⁻¹ • z)) (ball 0 (t * μ / 2)) ∧
      (fun z ↦ t • v ((t * μ)⁻¹ • z)) 0 = 0 ∧
      fderiv ℝ (fun z ↦ t • v ((t * μ)⁻¹ • z)) 0 1 = ξ ∧
      ∀ z ∈ ball (0 : ℂ) (t * μ / 2), (t * μ)⁻¹ • z ∈ ball (0 : ℂ) 2⁻¹ ∧
        ∀ w, fderiv ℝ (fun z ↦ t • v ((t * μ)⁻¹ • z)) z w =
          (t * (t * μ)⁻¹) • fderiv ℝ v ((t * μ)⁻¹ • z) w := by
  set κ := t * μ
  have hκ : 0 < κ := mul_pos ht hμ
  have hmaps : ∀ z ∈ ball (0 : ℂ) (κ / 2), κ⁻¹ • z ∈ ball (0 : ℂ) 2⁻¹ := fun z hz ↦ by
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hκ.le), inv_mul_lt_iff₀ hκ]
    linarith
  have hvd : ∀ z ∈ ball (0 : ℂ) (κ / 2), DifferentiableAt ℝ v (κ⁻¹ • z) := fun z hz ↦
    (hvC.contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by norm_num) (hmaps z hz)))).differentiableAt one_ne_zero
  refine ⟨?_, by simp [hv0], ?_, fun z hz ↦ ⟨hmaps z hz, fderiv_rescale_apply t κ (hvd z hz)⟩⟩
  · exact (hvC.comp (contDiffOn_id.const_smul κ⁻¹) fun z hz ↦
      ball_subset_ball (by norm_num) (hmaps z hz)).const_smul t
  · rw [fderiv_rescale_apply t κ (by simpa using hvd 0 (by simpa using hκ)), smul_zero, hv1,
      smul_smul, mul_right_comm, mul_inv_cancel₀ hκ.ne', one_smul]

/-- Rescaling the argument of a map `J` whose derivative is `K`-Lipschitz on the ball of radius
`r` makes its derivative and the Lipschitz constant of its derivative as small as required on
the ball of radius `4`. -/
private theorem exists_rescale {J : F → F →L[ℝ] F} {η r : ℝ} {K : ℝ≥0} (hη : 0 < η) (hr : 0 < r)
    (hd : ∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ J x)
    (hL : ∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ K * ‖x - y‖) :
    ∃ t > 0, 4 * t ≤ r ∧
      (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ (fun x ↦ J (t • x)) x) ∧
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (fun x ↦ J (t • x)) x‖ ≤ η) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ J (t • x)) x - fderiv ℝ (fun x ↦ J (t • x)) y‖ ≤ η * ‖x - y‖ := by
  -- On the ball of radius `r`, `DJ` is bounded by `A = ‖DJ(0)‖ + K r`.
  have hA : ∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + K * r := fun x hx ↦ by
    have h := hL x hx 0 (mem_closedBall_self hr.le)
    rw [sub_zero] at h
    rw [mem_closedBall, dist_zero_right] at hx
    calc ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + ‖fderiv ℝ J x - fderiv ℝ J 0‖ :=
          norm_le_insert' (fderiv ℝ J x) (fderiv ℝ J 0)
      _ ≤ _ := by gcongr; exact h.trans (by gcongr)
  -- Rescale by `t ≤ min (r / 4) 1` small enough for the bounds `η`.
  set A := ‖fderiv ℝ J 0‖ + K * r
  have hA0 : 0 ≤ A := by positivity
  set t := min (min (r / 4) 1) (η / (A + K + 1))
  have ht : 0 < t := lt_min (lt_min (by positivity) one_pos) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have htr : 4 * t ≤ r := by
    have : t ≤ r / 4 := (min_le_left _ _).trans (min_le_left (r / 4) 1)
    linarith
  have htη : t * A + t * K + t ≤ η := by
    have h : t * (A + K + 1) ≤ η := by
      rw [← le_div_iff₀ (by positivity)]
      exact min_le_right _ _
    linarith [mul_add t (A + K) 1, mul_add t A K]
  obtain ⟨hdt, hAt, hLt⟩ := rescale_bounds J ht htr hd hA hL
  have htK : 0 ≤ t * K := mul_nonneg ht.le K.coe_nonneg
  have hAη : t * A ≤ η := by linarith
  have hLη : t ^ 2 * K ≤ η := by
    have h := mul_le_mul_of_nonneg_right ht1 htK
    rw [one_mul, ← mul_assoc, ← pow_two] at h
    linarith [mul_nonneg ht.le hA0]
  exact ⟨t, ht, htr, hdt, fun x hx ↦ (hAt x hx).trans hAη,
    fun x hx y hy ↦ (hLt x hx y hy).trans (mul_le_mul_of_nonneg_right hLη (norm_nonneg _))⟩

/-- **Discs solving `∂ₛu + J(u) ∂ₜu = 0` with a prescribed first jet.** Let
`J : F → (F →L[ℝ] F)` be of class `C²` near `0` with `J(0) v = i v`. For every `ξ ∈ F` there is a
`C¹` map `u` from a disc about `0` in `ℂ` to `F` with `u(0) = 0` and `∂ₛu(0) = ξ` which solves
`∂ₛu + J(u) ∂ₜu = 0`. -/
theorem exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt [FiniteDimensional ℂ F]
    {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0) (hJ0 : ∀ v, J 0 v = I • v) (ξ : F) :
    ∃ ε > 0, ∃ u : ℂ → F, ContDiffOn ℝ 1 u (ball 0 ε) ∧ u 0 = 0 ∧ fderiv ℝ u 0 1 = ξ ∧
      ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0 := by
  obtain ⟨η, hη, hdisc⟩ := exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero (F := F)
  -- Near `0`, `J` is differentiable and `DJ` is Lipschitz, hence bounded.
  obtain ⟨r, hr, K, hd, hL⟩ := hJ.exists_closedBall_differentiableAt_lipschitz_fderiv
  obtain ⟨t, ht, -, hdt, hAt, hLt⟩ := exists_rescale hη hr hd hL
  set μ := (‖ξ‖ + 1)⁻¹
  have hμ : 0 < μ := by positivity
  obtain ⟨v, hvC, hv0, hv1, -, hveq⟩ := hdisc (fun x ↦ J (t • x)) (μ • ξ)
    (by
      rw [norm_smul, Real.norm_of_nonneg hμ.le, inv_mul_le_one₀ (by positivity)]
      linarith)
    (by simpa using hJ0) hdt hAt hLt
  obtain ⟨huC, hu0, hu1, hu⟩ := rescale_props ht hμ hvC hv0 hv1
  refine ⟨t * μ / 2, by positivity, _, huC, hu0, hu1, fun z hz ↦ ?_⟩
  obtain ⟨hz', hDu⟩ := hu z hz
  rw [hDu, hDu, map_smul, ← smul_add, hveq _ hz', smul_zero]

end Rescaling

/-! ### Rotation-equivariant families of `J`-holomorphic discs -/

/-! #### The Beltrami coefficient of a structure near `i`

The Beltrami coefficient of a real endomorphism `A` of `F` is `-cayleyCoord i A`, minus its
Cayley coordinate (`TauCeti.cayleyCoord`) relative to the standard structure `i`, in the normed
ring `F →L[ℝ] F`, where it depends smoothly on `A`. For `A² = -1` it is `(A + i)⁻¹ (i - A)`
(`TauCeti.add_mul_cayleyCoord`) and conjugate linear (`TauCeti.cayleyCoord_mul_eq_neg_mul`). -/

section EquivariantFamily

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem mul_self_eq_neg_one {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v) : A * A = -1 := by
  ext v
  simp [hAA]

/-- `(A + i) Q v = (i - A) v` for the Beltrami coefficient `Q` of `A`, when `A² = -1` and `i + A`
is invertible. -/
private theorem add_apply_neg_cayleyCoord {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v)
    (hA : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + A)) (v : F) :
    A ((-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) v) +
        I • (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) v = I • v - A v := by
  have h := congrArg (fun T : F →L[ℝ] F ↦ T v) (add_mul_cayleyCoord
    ((mul_self_eq_neg_one hAA).trans ContinuousLinearMap.lsmul_I_mul_lsmul_I.symm) hA)
  simp only [add_mul, mul_apply_eq_comp, add_apply, sub_apply,
    ContinuousLinearMap.lsmul_apply] at h
  simp only [neg_apply, map_neg, smul_neg]
  rw [← neg_add, h, neg_sub]

/-- **The Beltrami form of the Cauchy–Riemann equation.** If `A² = -1`, `i + A` is invertible and
the real-linear map `L : ℂ → F` satisfies `\bar∂L = Q ∂L` for the Beltrami coefficient `Q` of
`A`, then `L 1 + A (L i) = 0`. -/
private theorem apply_one_add_apply_apply_I_eq_zero {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v)
    (hA : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + A)) {L : ℂ →L[ℝ] F}
    (hL : L.complexAntilinearPart 1 =
      (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) (L.complexLinearPart 1)) :
    L 1 + A (L I) = 0 := by
  have hII : ∀ w : F, I • I • w = -w := fun w ↦ by rw [smul_smul, I_mul_I, neg_one_smul]
  rw [ContinuousLinearMap.complexAntilinearPart_apply, ContinuousLinearMap.complexLinearPart_apply,
    smul_eq_mul, mul_one, map_smul] at hL
  have hL' : L 1 + I • L I = (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) (L 1 - I • L I) :=
    smul_right_injective F (by norm_num : (2⁻¹ : ℝ) ≠ 0) hL
  -- The equation `(A + i) \bar∂L = (i - A) ∂L` reduces to `A (L 1) = L i`.
  have h := add_apply_neg_cayleyCoord hAA hA (L 1 - I • L I)
  rw [← hL'] at h
  simp only [map_add, map_sub, smul_add, smul_sub, hII] at h
  have hq : A (L 1) = L I := by
    linear_combination (norm := module) (2⁻¹ : ℝ) • h
  rw [← hq, hAA, add_neg_cancel]

/-- For a structure `J` of class `C²` near `0` with `J(0) = i` and `J² = -1` near `0`, the Beltrami
coefficient `Q = -cayleyCoord i J` vanishes at `0`, and on a small ball it is differentiable with
Lipschitz derivative, `J² = -1` and `i + J` is invertible. -/
private theorem exists_neg_cayleyCoord_local [CompleteSpace F] {J : F → F →L[ℝ] F}
    (hJ : ContDiffAt ℝ 2 J 0) (hJ0 : ∀ v, J 0 v = I • v)
    (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) :
    ∃ r > 0, ∃ K : ℝ≥0, -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J 0) = 0 ∧
      (∀ x ∈ closedBall (0 : F) r,
        DifferentiableAt ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) x) ∧
      (∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
        ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) x -
          fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) y‖ ≤
            K * ‖x - y‖) ∧
      ∀ x ∈ closedBall (0 : F) r,
        (∀ v, J x (J x v) = -v) ∧ IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J x) := by
  have hI0 : J 0 = ContinuousLinearMap.lsmul ℝ ℂ I := by
    ext v
    simp [hJ0]
  -- `Q` is `C²` near `0`, since `i + J(0) = 2 i` is invertible.
  have hU : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J 0) := by
    have h2 := (IsUnit.mk0 (2 : ℝ) two_ne_zero).map (algebraMap ℝ (F →L[ℝ] F))
    rw [map_ofNat] at h2
    rw [hI0, ← two_mul]
    exact isUnit_two_mul_of_mul_self_eq_neg_one h2 ContinuousLinearMap.lsmul_I_mul_lsmul_I
  have hAC : ContDiffAt ℝ 2 (fun x ↦ ContinuousLinearMap.lsmul ℝ ℂ I + J x) 0 :=
    contDiffAt_const.add hJ
  have hinv : ContDiffAt ℝ 2 Ring.inverse (ContinuousLinearMap.lsmul ℝ ℂ I + J 0) :=
    hU.unit_spec ▸ contDiffAt_ringInverse ℝ hU.unit
  have hQC : ContDiffAt ℝ 2 (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) 0 := by
    simp only [cayleyCoord_def]
    exact ((contDiffAt_const.sub hJ).mul (hinv.comp 0 hAC)).neg
  have hunit : ∀ᶠ x in 𝓝 0, IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J x) :=
    hAC.continuousAt.eventually (Units.isOpen.mem_nhds hU)
  obtain ⟨r₁, hr₁, K, hd, hL⟩ := hQC.exists_closedBall_differentiableAt_lipschitz_fderiv
  obtain ⟨r₂, hr₂, hr₂J⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (hJJ.and hunit)
  have h₁ : closedBall (0 : F) (min r₁ r₂) ⊆ closedBall 0 r₁ :=
    closedBall_subset_closedBall (min_le_left _ _)
  have h₂ : closedBall (0 : F) (min r₁ r₂) ⊆ closedBall 0 r₂ :=
    closedBall_subset_closedBall (min_le_right _ _)
  exact ⟨min r₁ r₂, lt_min hr₁ hr₂, K, by rw [hI0, cayleyCoord_self, neg_zero],
    fun x hx ↦ hd x (h₁ hx), fun x hx y hy ↦ hL x (h₁ hx) y (h₁ hy), fun x hx ↦ hr₂J (h₂ hx)⟩

/-- A coefficient vanishing at `0` with derivative bounded by `a` on the ball of radius `4` is
within `4 a` of the zero coefficient in the `C¹` norm there. -/
private theorem norm_sub_zero_le_of_norm_fderiv_le {P : F → F →L[ℝ] F} {a : ℝ} (ha : 0 ≤ a)
    (hP0 : P 0 = 0) (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ P x)
    (hA : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ P x‖ ≤ a) :
    (∀ x ∈ closedBall (0 : F) 4, ‖P x - (0 : F → F →L[ℝ] F) x‖ ≤ 4 * a) ∧
      ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ P x - fderiv ℝ (0 : F → F →L[ℝ] F) x‖ ≤ 4 * a := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd hA (convex_closedBall (0 : F) 4)
      (mem_closedBall_self (by norm_num)) hx
    rw [hP0, sub_zero, sub_zero] at h
    rw [Pi.zero_apply, sub_zero]
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa using hx) ha |>.trans_eq (mul_comm a 4))
  · rw [show fderiv ℝ (0 : F → F →L[ℝ] F) x = 0 from fderiv_const_apply 0, sub_zero]
    exact (hA x hx).trans (by linarith)

/-- Bounds `a` on the derivative of a coefficient and on its Lipschitz constant on the ball of
radius `4` give the bounds `b` for every `b ≥ a`. -/
private theorem fderiv_bounds_mono {P : F → F →L[ℝ] F} {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ P x‖ ≤ a)
    (hL : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ P x - fderiv ℝ P y‖ ≤ a * ‖x - y‖) :
    (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ P x‖ ≤ b) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ P x - fderiv ℝ P y‖ ≤ b * ‖x - y‖ :=
  ⟨fun x hx ↦ (hA x hx).trans hab, fun x hx y hy ↦
    (hL x hx y hy).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))⟩

/-- The derivative of a parametrization `w ↦ w ξ` of a complex line. -/
private theorem fderiv_eq_smulRight_of_eq_smul {v : ℂ → F} {ξ : F} (hv : ∀ w, v w = w • ξ)
    (z : ℂ) : fderiv ℝ v z = (ContinuousLinearMap.id ℝ ℂ).smulRight ξ := by
  rw [show v = fun w ↦ w • ξ from funext hv]
  exact ((hasFDerivAt_id _).smul_const ξ).fderiv

/-- The zero coefficient satisfies the smallness hypotheses of the Beltrami discs for every
nonnegative bound `b`. -/
private theorem zero_coeff_bounds {b : ℝ} (hb : 0 ≤ b) :
    (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ (0 : F → F →L[ℝ] F) x) ∧
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (0 : F → F →L[ℝ] F) x‖ ≤ b) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (0 : F → F →L[ℝ] F) x - fderiv ℝ (0 : F → F →L[ℝ] F) y‖ ≤ b * ‖x - y‖ := by
  -- The zero map has norm at most every nonnegative bound.
  have hz : ∀ c : ℝ, 0 ≤ c → ‖(0 : F →L[ℝ] F →L[ℝ] F)‖ ≤ c := fun c hc ↦
    ContinuousLinearMap.opNorm_le_bound _ hc fun v ↦ by
      simp only [zero_apply, norm_zero]
      exact mul_nonneg hc (norm_nonneg v)
  have hd0 : ∀ x, fderiv ℝ (0 : F → F →L[ℝ] F) x = 0 := fun x ↦ fderiv_const_apply 0
  refine ⟨fun _ _ ↦ differentiableAt_const _, fun x _ ↦ ?_, fun x _ y _ ↦ ?_⟩
  · rw [hd0]
    exact hz b hb
  · rw [hd0, hd0, sub_zero]
    exact hz _ (mul_nonneg hb (norm_nonneg _))

/-- **A rotation-equivariant family of `J`-holomorphic discs with prescribed first jets, close to
complex lines.** Let `J : F → (F →L[ℝ] F)` be of class `C²` near `0`, with `J(0) v = i v` and
`J(x)² = -1` near `0`, as for an almost complex structure in coordinates centred at a point where
it is standard, and let `κ > 0`. Then there are `ε > 0` and maps `u_ξ : ℂ → F`, for `‖ξ‖ ≤ 1`,
each `C¹` on the disc of radius `ε` with `u_ξ(0) = 0` and `∂ₛu_ξ(0) = ξ`, solving
`∂ₛu_ξ + J(u_ξ) ∂ₜu_ξ = 0` there, such that

* on the disc of radius `ε`, the derivative of `u_ξ` is within `κ` in operator norm of the
  derivative `w ↦ w ξ` of the complex line with the same first jet;
* rotating the first jet rotates the parameter: `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`. So the
  discs through `0` with first jets `ξ` and `c ξ` have the same image, parametrized differently by
  the rotation `w ↦ c w`.

The derivative bound comes from rescaling: in the coordinates `x ↦ t x` the Beltrami coefficient
of `J` is of size `O(t)` in the `C¹` norm, and the disc of a small coefficient is close to the
disc `w ↦ w ξ` of the zero coefficient. -/
theorem exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq
    [FiniteDimensional ℂ F] {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0)
    (hJ0 : ∀ v, J 0 v = I • v) (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u ξ) (ball 0 ε) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        (∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ (u ξ) z 1 + J (u ξ z) (fderiv ℝ (u ξ) z I) = 0) ∧
        ∀ z ∈ ball (0 : ℂ) ε,
          ‖fderiv ℝ (u ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
      ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w) := by
  -- Rescale the Beltrami coefficient `Q` of `J` by `t`, small enough that `Q(t ·)` is admissible
  -- for the Beltrami discs and within `4 η'` of `0` in `C¹`, with `C (4 η') ≤ κ`. The discs of
  -- `Q(t ·)`, rescaled back, solve the equation for `J`, and their derivatives are within
  -- `C (4 η')` of those of the discs `w ↦ w ξ` of the zero coefficient.
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨η, hη, C, hC, V, hdisc, hV0, hlip⟩ :=
    exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le (F := F)
  obtain ⟨r, hr, K, hQ0, hd, hL, hrJ⟩ := exists_neg_cayleyCoord_local hJ hJ0 hJJ
  set Q : F → F →L[ℝ] F := fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)
  -- Rescale until the coefficient is below both `η` and `κ / (4 (C + 1))` in the `C¹` norm.
  set η' := min η (κ / (4 * (C + 1)))
  have hη' : 0 < η' := lt_min hη (by positivity)
  obtain ⟨t, ht, htr, hdt, hAt, hLt⟩ := exists_rescale hη' hr hd hL
  have hmem : ∀ x : F, ‖x‖ ≤ 2 → t • x ∈ closedBall (0 : F) r := fun x hx ↦ by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
    nlinarith
  have hQt0 : (fun x ↦ Q (t • x)) 0 = 0 := by simp only [smul_zero]; exact hQ0
  obtain ⟨hAη, hLη⟩ := fderiv_bounds_mono (min_le_left η _) hAt hLt
  obtain ⟨hv, hveq⟩ := hdisc (fun x ↦ Q (t • x)) hQt0 hdt hAη hLη
  -- The rescaled coefficient is within `4 η'` of `0` in the `C¹` norm on the ball of radius `4`.
  obtain ⟨hQsmall, hDsmall⟩ := norm_sub_zero_le_of_norm_fderiv_le hη'.le hQt0 hdt hAt
  obtain ⟨hd0, hz0, hzL⟩ := zero_coeff_bounds (F := F) hη.le
  have hlip0 := hlip (fun x ↦ Q (t • x)) 0 hQt0 rfl hdt hd0 hAη hz0 hLη hzL
  have hCη : C * (4 * η') ≤ κ := by
    have h : η' * (4 * (C + 1)) ≤ κ := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  replace hveq := hveq fun x hx w ↦ by
    -- The Cayley coordinate of a square root of `-1` anticommutes with `i`.
    have h := congrArg (fun T : F →L[ℝ] F ↦ T w)
      (cayleyCoord_mul_eq_neg_mul ContinuousLinearMap.lsmul_I_mul_lsmul_I
        (mul_self_eq_neg_one (hrJ _ (hmem x (by simpa using hx))).1))
    simp only [mul_apply_eq_comp, neg_apply, ContinuousLinearMap.lsmul_apply] at h
    simp only [Q, neg_apply, h, smul_neg]
  set v := V (fun x ↦ Q (t • x))
  refine ⟨t / 2, by positivity, fun ξ z ↦ t • v ξ (t⁻¹ • z), fun ξ hξ ↦ ?_,
    fun ξ hξ c hc w ↦ ?_⟩
  · obtain ⟨hvC, hv0, hv1, hvb, hvbel⟩ := hv ξ hξ
    obtain ⟨huC, hu0, hu1, hu⟩ := rescale_props ht one_pos hvC hv0 (by simpa using hv1)
    rw [mul_one] at huC hu0 hu1 hu
    have hfd : ∀ z ∈ ball (0 : ℂ) (t / 2),
        fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z = fderiv ℝ (v ξ) (t⁻¹ • z) := fun z hz ↦
      ContinuousLinearMap.ext fun w ↦ by rw [(hu z hz).2, mul_inv_cancel₀ ht.ne', one_smul]
    have hz1 : ∀ z ∈ ball (0 : ℂ) (t / 2), t⁻¹ • z ∈ closedBall (0 : ℂ) 1 := fun z hz ↦
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) (hu z hz).1
    refine ⟨huC, hu0, hu1, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have hy' := hrJ _ (hmem _ (hvb _ (hz1 z hz)))
      refine apply_one_add_apply_apply_I_eq_zero hy'.1 hy'.2 ?_
      rw [hfd z hz, ← conjWirtingerDeriv_eq_complexAntilinearPart,
        ← wirtingerDeriv_eq_complexLinearPart]
      exact hvbel _ (hu z hz).1
    · have h := (hlip0 ξ ξ (4 * η') hξ hξ hQsmall hDsmall _ (hz1 z hz)).2
      rw [sub_self, norm_zero, zero_add, fderiv_eq_smulRight_of_eq_smul (hV0 ξ hξ)] at h
      rw [hfd z hz]
      exact h.trans hCη
  · dsimp only
    rw [hveq ξ hξ c hc, mul_smul_comm]

/-- **The `J`-holomorphic discs with unit first jets are embedded.** Under the hypotheses of
`TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq`, the
rotation-equivariant family of discs `u_ξ` can be chosen so that, for every unit vector `ξ`,
`u_ξ` is injective on the disc of radius `ε`, with `|w - w'| ≤ 2 ‖u_ξ(w) - u_ξ(w')‖` there, and
its derivative is injective at every point of that disc, with `|v| ≤ 2 ‖du_ξ(w) v‖`. So each
`u_ξ` is an embedding of the disc, and the discs through `0` in the directions `ξ` are embedded
`J`-holomorphic discs. -/
theorem exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_antilipschitzWith
    [FiniteDimensional ℂ F] {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0)
    (hJ0 : ∀ v, J 0 v = I • v) (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) :
    ∃ ε > 0, ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u ξ) (ball 0 ε) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ (u ξ) z 1 + J (u ξ z) (fderiv ℝ (u ξ) z I) = 0) ∧
      (∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w)) ∧
      ∀ ξ : F, ‖ξ‖ = 1 → AntilipschitzWith 2 ((ball (0 : ℂ) ε).domRestrict (u ξ)) ∧
        ∀ z ∈ ball (0 : ℂ) ε, AntilipschitzWith 2 (fderiv ℝ (u ξ) z) := by
  obtain ⟨ε, hε, u, hu, hrot⟩ :=
    exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq hJ hJ0 hJJ
      (by norm_num : (0 : ℝ) < 2⁻¹)
  refine ⟨ε, hε, u, fun ξ hξ ↦ ?_, hrot, fun ξ hξ ↦ ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hu ξ hξ
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨huC, -, -, -, hD⟩ := hu ξ hξ.le
  -- The complex line `w ↦ w ξ` is an isometry, and `u_ξ` is within `1/2` of it in `C¹`.
  set φ := (ContinuousLinearMap.id ℝ ℂ).smulRight ξ
  have hφ : AntilipschitzWith 1 φ := φ.antilipschitz_of_bound fun w ↦ by
    simp [φ, norm_smul, hξ]
  have hDnn : ∀ z ∈ ball (0 : ℂ) ε, ‖fderiv ℝ (u ξ) z - φ‖₊ ≤ 2⁻¹ := fun z hz ↦ by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_inv, NNReal.coe_ofNat]
    exact hD z hz
  have hK : (2⁻¹ : ℝ≥0) < (1 : ℝ≥0)⁻¹ := by norm_num
  have hK2 : ((1 : ℝ≥0)⁻¹ - 2⁻¹)⁻¹ = 2 := by
    have h : (1 : ℝ≥0)⁻¹ - 2⁻¹ = 2⁻¹ := by
      rw [inv_one]
      exact tsub_eq_of_eq_add (by norm_num)
    rw [h, inv_inv]
  have hdiff : ∀ z ∈ ball (0 : ℂ) ε, DifferentiableAt ℝ (u ξ) z := fun z hz ↦
    (huC.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt one_ne_zero
  refine ⟨?_, fun z hz ↦ ?_⟩
  · have hlip : LipschitzOnWith 2⁻¹ (u ξ - ⇑φ) (ball 0 ε) :=
      (convex_ball (0 : ℂ) ε).lipschitzOnWith_of_nnNorm_fderiv_le
        (fun z hz ↦ (hdiff z hz).sub φ.differentiableAt) fun z hz ↦ by
          rw [fderiv_sub (hdiff z hz) φ.differentiableAt, φ.fderiv]
          exact hDnn z hz
    have := (hφ.domRestrict (ball (0 : ℂ) ε)).add_sub_lipschitzWith
      (g := (ball (0 : ℂ) ε).domRestrict (u ξ)) hlip.to_restrict hK
    rwa [hK2] at this
  · have := hφ.add_sub_lipschitzWith (g := fderiv ℝ (u ξ) z)
      (by
        rw [← FunLike.coe_sub]
        exact (fderiv ℝ (u ξ) z - φ).lipschitzWith.weaken (hDnn z hz)) hK
    rwa [hK2] at this

end EquivariantFamily

end TauCeti
