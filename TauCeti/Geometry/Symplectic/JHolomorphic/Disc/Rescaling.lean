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
import TauCeti.Analysis.Calculus.FDeriv.Prod
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
  (`exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq`).
  This equivariance is the `U(1)` normal-frame equivariance of the normal disc families used to
  foliate a neighbourhood of a pseudoholomorphic curve in the large-parameter analysis of the
  Seiberg–Witten equations.
* The discs are close to complex lines. In the rescaled coordinates the Beltrami coefficient is
  of size `O(t)` in the `C¹` norm, and the disc of a small coefficient is close in `C¹` to the
  disc `w ↦ w ξ` of the zero coefficient. So, for any `κ > 0`, the family can be chosen on a disc
  small enough that `‖du_ξ - (w ↦ w ξ)‖ ≤ κ` there. With `κ = 1/2` and `‖ξ‖ = 1`, `u_ξ` is
  `2`-antilipschitz on that disc and so is its derivative at every point: each disc is an
  embedding, injective with injective derivative.
* The discs depend Lipschitz continuously on the structure. For a family of structures `J p`,
  jointly of class `C²` in the base point `p` and in `x`, with `J p 0 = i`, as for an almost complex
  structure written at each point of a curve in coordinates centred there, one rescaling `t` serves
  every base point near a given one, so the discs `u_{p, ξ}` are defined on a common disc. The
  Beltrami coefficients of `J p` and `J p'`, rescaled by `t`, differ by `O(‖p - p'‖)` in `C¹`, and
  the discs of two such coefficients differ by `O(‖ξ - ξ'‖ + ‖p - p'‖)` in `C¹`
  (`TauCeti.exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le`). So the
  discs `u_{p, ξ}` and their derivatives are Lipschitz in the base point and the first jet
  (`exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_mul_add`). The family
  at a single structure is the constant family.

## Main results

* `TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`: for a structure of class
  `C²` near `0`, a solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`, for every `ξ`.
* `exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq`: for
  an almost complex structure of class `C²` near `0` and any `κ > 0`, a family of such discs
  `u_ξ`, `‖ξ‖ ≤ 1`, on a common disc, with `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1` and derivatives
  within `κ` of the derivative of `w ↦ w ξ`.
* `TauCeti.exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_antilipschitzWith`:
  such a family in which every disc with a unit first jet, and its derivative at every point, is
  `2`-antilipschitz, so that the discs are embedded.
* `TauCeti.exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_mul_add`: for
  a family of such structures `J p`, jointly of class `C²` near `(p₀, 0)`, rotation-equivariant
  discs `u_{p, ξ}` on a common disc for all `p` near `p₀`, close to complex lines, with `u_{p, ξ}`
  and `Du_{p, ξ}` Lipschitz in `(p, ξ)`.

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

/-- One rescaling works for all maps with the same bounds: if the derivative of `J` is bounded by
`A` and `K`-Lipschitz on the ball of radius `r`, then for a `t ∈ (0, 1]` depending only on `η`,
`r`, `A` and `K`, the derivative of `x ↦ J (t x)` and its Lipschitz constant are at most `η` on the
ball of radius `4`. -/
private theorem exists_rescale_of_le {η r A : ℝ} {K : ℝ≥0} (hη : 0 < η) (hr : 0 < r)
    (hA0 : 0 ≤ A) :
    ∃ t > 0, t ≤ 1 ∧ 4 * t ≤ r ∧ ∀ J : F → F →L[ℝ] F,
      (∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ J x) →
      (∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ A) →
      (∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
        ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ K * ‖x - y‖) →
      (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ (fun x ↦ J (t • x)) x) ∧
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (fun x ↦ J (t • x)) x‖ ≤ η) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ J (t • x)) x - fderiv ℝ (fun x ↦ J (t • x)) y‖ ≤ η * ‖x - y‖ := by
  -- Rescale by `t ≤ min (r / 4) 1` small enough for the bounds `η`.
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
  have htK : 0 ≤ t * K := mul_nonneg ht.le K.coe_nonneg
  have hAη : t * A ≤ η := by linarith
  have hLη : t ^ 2 * K ≤ η := by
    have h := mul_le_mul_of_nonneg_right ht1 htK
    rw [one_mul, ← mul_assoc, ← pow_two] at h
    linarith [mul_nonneg ht.le hA0]
  refine ⟨t, ht, ht1, htr, fun J hd hA hL ↦ ?_⟩
  obtain ⟨hdt, hAt, hLt⟩ := rescale_bounds J ht htr hd hA hL
  exact ⟨hdt, fun x hx ↦ (hAt x hx).trans hAη,
    fun x hx y hy ↦ (hLt x hx y hy).trans (mul_le_mul_of_nonneg_right hLη (norm_nonneg _))⟩

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
  -- On the ball of radius `r`, `DJ` is bounded by `‖DJ(0)‖ + K r`.
  obtain ⟨t, ht, -, htr, h⟩ := exists_rescale_of_le (F := F) (K := K) hη hr
    (by positivity : 0 ≤ ‖fderiv ℝ J 0‖ + K * r)
  exact ⟨t, ht, htr, h J hd (fun x hx ↦ norm_le_norm_add_const_of_dist_le (a := fderiv ℝ J x) <|
    (dist_eq_norm _ _).trans_le <| (lipschitzOnWith_iff_norm_sub_le.2 hL).norm_sub_le_of_le hx
      (mem_closedBall_self hr.le) (mem_closedBall_iff_norm.1 hx)) hL⟩

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem mul_self_eq_neg_one {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v) : A * A = -1 := by
  ext v
  simp [hAA]

/-- The Beltrami coefficient `Q` of `A` takes conjugate-linear values, `Q (i v) = -i Q v`, when
`A² = -1`. -/
private theorem neg_cayleyCoord_apply_I_smul {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v) (v : F) :
    (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) (I • v) =
      -(I • (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) v) := by
  have h := congrArg (fun T : F →L[ℝ] F ↦ T v)
    (cayleyCoord_mul_eq_neg_mul ContinuousLinearMap.lsmul_I_mul_lsmul_I (mul_self_eq_neg_one hAA))
  simp only [mul_apply_eq_comp, neg_apply, ContinuousLinearMap.lsmul_apply] at h
  simp only [neg_apply, h, smul_neg]

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

/-- For a family of structures `J p`, jointly of class `C²` near `(p₀, 0)`, with `J p 0 = i` for `p`
near `p₀` and `(J p x)² = -1` near `(p₀, 0)`, the Beltrami coefficient
`Q(p, x) = -cayleyCoord i (J p x)` vanishes at `(p, 0)` for `p` near `p₀`, and on a small ball about
`(p₀, 0)` it is differentiable with Lipschitz derivative, `(J p x)² = -1` and `i + J p x` is
invertible. -/
private theorem exists_neg_cayleyCoord_local [CompleteSpace F] {J : E → F → F →L[ℝ] F} {p₀ : E}
    (hJ : ContDiffAt ℝ 2 (uncurry J) (p₀, 0)) (hJ0 : ∀ᶠ p in 𝓝 p₀, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ᶠ q in 𝓝 (p₀, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) :
    ∃ r > 0, ∃ K : ℝ≥0,
      (∀ p ∈ closedBall p₀ r, -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p 0) = 0) ∧
      (∀ q ∈ closedBall (p₀, (0 : F)) r, DifferentiableAt ℝ
        (fun q : E × F ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) q) ∧
      (∀ q ∈ closedBall (p₀, (0 : F)) r, ∀ q' ∈ closedBall (p₀, (0 : F)) r,
        ‖fderiv ℝ (fun q : E × F ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) q -
          fderiv ℝ (fun q : E × F ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2))
            q'‖ ≤ K * ‖q - q'‖) ∧
      ∀ q ∈ closedBall (p₀, (0 : F)) r,
        (∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) ∧
          IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J q.1 q.2) := by
  have hI : ∀ {p : E}, (∀ v, J p 0 v = I • v) → J p 0 = ContinuousLinearMap.lsmul ℝ ℂ I :=
    fun h ↦ ContinuousLinearMap.ext fun v ↦ by simp [h]
  have hI0 := hI hJ0.self_of_nhds
  -- `Q` is `C²` near `(p₀, 0)`, since `i + J p₀ 0 = 2 i` is invertible.
  have hU : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p₀ 0) := by
    have h2 := (IsUnit.mk0 (2 : ℝ) two_ne_zero).map (algebraMap ℝ (F →L[ℝ] F))
    rw [map_ofNat] at h2
    rw [hI0, ← two_mul]
    exact isUnit_two_mul_of_mul_self_eq_neg_one h2 ContinuousLinearMap.lsmul_I_mul_lsmul_I
  have hAC : ContDiffAt ℝ 2
      (fun q : E × F ↦ ContinuousLinearMap.lsmul ℝ ℂ I + J q.1 q.2) (p₀, 0) :=
    contDiffAt_const.add hJ
  have hinv : ContDiffAt ℝ 2 Ring.inverse (ContinuousLinearMap.lsmul ℝ ℂ I + J p₀ 0) :=
    hU.unit_spec ▸ contDiffAt_ringInverse ℝ hU.unit
  have hQC : ContDiffAt ℝ 2
      (fun q : E × F ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) (p₀, 0) := by
    simp only [cayleyCoord_def]
    exact ((contDiffAt_const.sub hJ).mul (hinv.comp (p₀, 0) hAC)).neg
  have hunit : ∀ᶠ q in 𝓝 (p₀, (0 : F)), IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J q.1 q.2) :=
    hAC.continuousAt.eventually (Units.isOpen.mem_nhds hU)
  obtain ⟨r₁, hr₁, K, hd, hL⟩ := hQC.exists_closedBall_differentiableAt_lipschitz_fderiv
  obtain ⟨r₂, hr₂, hr₂J⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (hJJ.and hunit)
  obtain ⟨r₃, hr₃, hr₃J⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hJ0
  set r := min (min r₁ r₂) r₃
  have h₁ : closedBall (p₀, (0 : F)) r ⊆ closedBall (p₀, 0) r₁ :=
    closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_left _ _))
  have h₂ : closedBall (p₀, (0 : F)) r ⊆ closedBall (p₀, 0) r₂ :=
    closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _))
  have h₃ : closedBall p₀ r ⊆ closedBall p₀ r₃ := closedBall_subset_closedBall (min_le_right _ _)
  exact ⟨r, lt_min (lt_min hr₁ hr₂) hr₃, K,
    fun p hp ↦ by rw [hI (hr₃J (h₃ hp)), cayleyCoord_self, neg_zero],
    fun q hq ↦ hd q (h₁ hq), fun q hq q' hq' ↦ hL q (h₁ hq) q' (h₁ hq'), fun q hq ↦ hr₂J (h₂ hq)⟩

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

/-! #### Families of structures over a parameter space -/

/-- The slices `x ↦ Q(p, x)` of a map `Q` on `E × F` inherit, on the ball of radius `r` about `0`,
the bounds of `Q` on the ball of radius `r` about `(p₀, 0)`: their derivative is `DQ(p, x) ∘ inr`,
so it is bounded by the bound `A` of `DQ` and `K`-Lipschitz when `DQ` is. -/
private theorem slice_bounds {Q : E × F → F →L[ℝ] F} {p₀ : E} {r A : ℝ} {K : ℝ≥0}
    (hd : ∀ q ∈ closedBall (p₀, (0 : F)) r, DifferentiableAt ℝ Q q)
    (hA : ∀ q ∈ closedBall (p₀, (0 : F)) r, ‖fderiv ℝ Q q‖ ≤ A)
    (hL : ∀ q ∈ closedBall (p₀, (0 : F)) r, ∀ q' ∈ closedBall (p₀, (0 : F)) r,
      ‖fderiv ℝ Q q - fderiv ℝ Q q'‖ ≤ K * ‖q - q'‖) {p : E} (hp : p ∈ closedBall p₀ r) :
    (∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ (fun x ↦ Q (p, x)) x) ∧
      (∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ (fun x ↦ Q (p, x)) x‖ ≤ A) ∧
      ∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
        ‖fderiv ℝ (fun x ↦ Q (p, x)) x - fderiv ℝ (fun x ↦ Q (p, x)) y‖ ≤ K * ‖x - y‖ := by
  have hmem : ∀ x ∈ closedBall (0 : F) r, (p, x) ∈ closedBall (p₀, (0 : F)) r := fun x hx ↦ by
    rw [← closedBall_prod_same]
    exact ⟨hp, hx⟩
  refine ⟨fun x hx ↦ ((hd _ (hmem x hx)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right p x)).differentiableAt, fun x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · rw [fderiv_slice_right (hd _ (hmem x hx))]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ E F)).trans
        (hA _ (hmem x hx)))
  · rw [fderiv_slice_right (hd _ (hmem x hx)), fderiv_slice_right (hd _ (hmem y hy)),
      ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_of_le_one_right
      (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ E F)).trans ?_)
    have h := hL _ (hmem x hx) _ (hmem y hy)
    simpa [Prod.norm_def] using h

omit [NormedSpace ℝ E] in
/-- For `‖p - p₀‖ ≤ r`, `‖x‖ ≤ 4`, `t ≥ 0` and `4 t ≤ r`, the point `(p, t x)` lies in the ball of
radius `r` about `(p₀, 0)`. -/
private theorem mk_smul_mem_closedBall {p₀ p : E} {x : F} {r t : ℝ} (ht : 0 ≤ t)
    (htr : 4 * t ≤ r) (hp : p ∈ closedBall p₀ r) (hx : x ∈ closedBall (0 : F) 4) :
    (p, t • x) ∈ closedBall (p₀, (0 : F)) r := by
  rw [← closedBall_prod_same]
  refine ⟨hp, ?_⟩
  rw [mem_closedBall_zero_iff] at hx ⊢
  rw [norm_smul, Real.norm_of_nonneg ht]
  nlinarith

/-- Rescaled slices at two parameters differ by `O(‖p - p'‖)` in `C¹`: if `DQ` is bounded by `A`
and `K`-Lipschitz on the ball of radius `r` about `(p₀, 0)`, and `0 < t ≤ 1` with `4 t ≤ r`, then on
the ball of radius `4` the maps `x ↦ Q(p, t x)` and `x ↦ Q(p', t x)`, and their derivatives, differ
by at most `(A + K) ‖p - p'‖`, for `p` and `p'` in the ball of radius `r` about `p₀`. -/
private theorem rescaled_slice_sub_le {Q : E × F → F →L[ℝ] F} {p₀ : E} {r A t : ℝ} {K : ℝ≥0}
    (hd : ∀ q ∈ closedBall (p₀, (0 : F)) r, DifferentiableAt ℝ Q q)
    (hA : ∀ q ∈ closedBall (p₀, (0 : F)) r, ‖fderiv ℝ Q q‖ ≤ A)
    (hL : ∀ q ∈ closedBall (p₀, (0 : F)) r, ∀ q' ∈ closedBall (p₀, (0 : F)) r,
      ‖fderiv ℝ Q q - fderiv ℝ Q q'‖ ≤ K * ‖q - q'‖) (ht : 0 < t) (ht1 : t ≤ 1) (htr : 4 * t ≤ r)
    {p p' : E} (hp : p ∈ closedBall p₀ r) (hp' : p' ∈ closedBall p₀ r) :
    (∀ x ∈ closedBall (0 : F) 4, ‖Q (p, t • x) - Q (p', t • x)‖ ≤ (A + K) * ‖p - p'‖) ∧
      ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (fun x ↦ Q (p, t • x)) x -
        fderiv ℝ (fun x ↦ Q (p', t • x)) x‖ ≤ (A + K) * ‖p - p'‖ := by
  have hmem : ∀ {p : E}, p ∈ closedBall p₀ r → ∀ x ∈ closedBall (0 : F) 4,
      (p, t • x) ∈ closedBall (p₀, (0 : F)) r := fun hp _ hx ↦
    mk_smul_mem_closedBall ht.le htr hp hx
  have hpp : ∀ x : F, ‖(p, t • x) - (p', t • x)‖ = ‖p - p'‖ := fun x ↦ by
    simp [Prod.norm_def]
  have hA0 : 0 ≤ A := (norm_nonneg (fderiv ℝ Q (p₀, 0))).trans (hA _ (mem_closedBall_self
    ((mul_nonneg zero_le_four ht.le).trans htr)))
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · -- The mean value inequality along the segment from `(p', t x)` to `(p, t x)`.
    have h := (convex_closedBall (p₀, (0 : F)) r).norm_image_sub_le_of_norm_fderiv_le hd hA
      (hmem hp' x hx) (hmem hp x hx)
    rw [hpp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right K.coe_nonneg)
      (norm_nonneg _))
  · -- The derivative of `x ↦ Q(p, t x)` is `DQ(p, t x) ∘ inr ∘ t`, and `‖inr ∘ t‖ ≤ 1`.
    have hfd : ∀ {p : E}, p ∈ closedBall p₀ r → fderiv ℝ (fun x ↦ Q (p, t • x)) x =
        (fderiv ℝ Q (p, t • x)).comp
          ((ContinuousLinearMap.inr ℝ E F).comp (t • ContinuousLinearMap.id ℝ F)) := fun hp ↦
      ((hd _ (hmem hp x hx)).hasFDerivAt.comp x ((hasFDerivAt_prodMk_right _ _).comp x
        ((hasFDerivAt_id x).const_smul t))).fderiv
    have hn : ‖(ContinuousLinearMap.inr ℝ E F).comp (t • ContinuousLinearMap.id ℝ F)‖ ≤ 1 := by
      have h : ‖t • ContinuousLinearMap.id ℝ F‖ ≤ 1 :=
        (norm_smul_le t (ContinuousLinearMap.id ℝ F)).trans (by
          rw [Real.norm_of_nonneg ht.le]
          nlinarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F),
            norm_nonneg (ContinuousLinearMap.id ℝ F)])
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        nlinarith [ContinuousLinearMap.norm_inr_le_one ℝ E F,
          norm_nonneg (t • ContinuousLinearMap.id ℝ F)])
    rw [hfd hp, hfd hp', ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hn).trans ?_)
    refine (hL _ (hmem hp x hx) _ (hmem hp' x hx)).trans ?_
    rw [hpp]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA0) (norm_nonneg _)

/-- A disc `v` of the Beltrami equation for the rescaled coefficient `x ↦ Q(t x)` of a structure
`J`, with `Q = -cayleyCoord i J`, rescales to the disc `u(z) = t v(z / t)` of the equation
`∂ₛu + J(u) ∂ₜu = 0` on the disc of radius `t / 2`, with the same centre and first jet, as long as
`J(t x)² = -1` and `i + J(t x)` is invertible for `‖x‖ ≤ 2`. There `Du(z) = Dv(z / t)`. -/
private theorem rescaled_disc {J : F → F →L[ℝ] F} {t : ℝ} (ht : 0 < t) {v : ℂ → F} {ξ : F}
    (hvC : ContDiffOn ℝ 1 v (ball 0 2)) (hv0 : v 0 = 0) (hv1 : fderiv ℝ v 0 1 = ξ)
    (hvb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖v z‖ ≤ 2)
    (hvbel : ∀ z ∈ ball (0 : ℂ) 2⁻¹, conjWirtingerDeriv v z 1 =
      -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J (t • v z)) (wirtingerDeriv v z 1))
    (hJ : ∀ x ∈ closedBall (0 : F) 2, (∀ w, J (t • x) (J (t • x) w) = -w) ∧
      IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J (t • x))) :
    ContDiffOn ℝ 1 (fun z ↦ t • v (t⁻¹ • z)) (ball 0 (t / 2)) ∧
      (fun z ↦ t • v (t⁻¹ • z)) 0 = 0 ∧ fderiv ℝ (fun z ↦ t • v (t⁻¹ • z)) 0 1 = ξ ∧
      ∀ z ∈ ball (0 : ℂ) (t / 2), t⁻¹ • z ∈ closedBall (0 : ℂ) 1 ∧
        fderiv ℝ (fun z ↦ t • v (t⁻¹ • z)) z = fderiv ℝ v (t⁻¹ • z) ∧
        fderiv ℝ (fun z ↦ t • v (t⁻¹ • z)) z 1 +
          J (t • v (t⁻¹ • z)) (fderiv ℝ (fun z ↦ t • v (t⁻¹ • z)) z I) = 0 := by
  obtain ⟨huC, hu0, hu1, hu⟩ := rescale_props ht one_pos hvC hv0 (by simpa using hv1)
  rw [mul_one] at huC hu0 hu1 hu
  refine ⟨huC, hu0, hu1, fun z hz ↦ ?_⟩
  have hfd : fderiv ℝ (fun z ↦ t • v (t⁻¹ • z)) z = fderiv ℝ v (t⁻¹ • z) :=
    ContinuousLinearMap.ext fun w ↦ by rw [(hu z hz).2, mul_inv_cancel₀ ht.ne', one_smul]
  have hz1 : t⁻¹ • z ∈ closedBall (0 : ℂ) 1 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) (hu z hz).1
  refine ⟨hz1, hfd, ?_⟩
  have hy := hJ _ (mem_closedBall_zero_iff.2 (hvb _ hz1))
  refine apply_one_add_apply_apply_I_eq_zero hy.1 hy.2 ?_
  rw [hfd, ← conjWirtingerDeriv_eq_complexAntilinearPart, ← wirtingerDeriv_eq_complexLinearPart]
  exact hvbel _ (hu z hz).1

/-- One rescaling serves all base points near `p₀`. For a family of structures `J p`, jointly of
class `C²` near `(p₀, 0)`, with `J p 0 = i` for `p` near `p₀` and `(J p x)² = -1` near `(p₀, 0)`,
and for `η > 0`, there are `r > 0`, `0 < t ≤ 1` and `L ≥ 0` such that,
for `‖p - p₀‖ ≤ r`, the rescaled Beltrami coefficient `x ↦ -cayleyCoord i (J p (t x))` vanishes at
`0`, its derivative and the Lipschitz constant of its derivative are at most `η` on the ball of
radius `4`, and `J p (t x)² = -1` with `i + J p (t x)` invertible for `‖x‖ ≤ 2`; and the rescaled
coefficients at two such base points `p`, `p'` and their derivatives differ by at most
`L ‖p - p'‖` on the ball of radius `4`. -/
private theorem exists_rescaled_beltrami_family [CompleteSpace F] {J : E → F → F →L[ℝ] F}
    {p₀ : E} (hJ : ContDiffAt ℝ 2 (uncurry J) (p₀, 0))
    (hJ0 : ∀ᶠ p in 𝓝 p₀, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ᶠ q in 𝓝 (p₀, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∃ t > (0 : ℝ), t ≤ 1 ∧ ∃ L ≥ (0 : ℝ),
      (∀ p ∈ closedBall p₀ r,
        (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) 0 = 0 ∧
        (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ
          (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x) ∧
        (∀ x ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x‖ ≤
            η) ∧
        (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x -
            fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) y‖ ≤
              η * ‖x - y‖) ∧
        ∀ x ∈ closedBall (0 : F) 2, (∀ w, J p (t • x) (J p (t • x) w) = -w) ∧
          IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p (t • x))) ∧
      ∀ p ∈ closedBall p₀ r, ∀ p' ∈ closedBall p₀ r,
        (∀ x ∈ closedBall (0 : F) 4,
          ‖-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x)) -
            -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p' (t • x))‖ ≤ L * ‖p - p'‖) ∧
        ∀ x ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x -
            fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p' (t • x))) x‖ ≤
              L * ‖p - p'‖ := by
  obtain ⟨r, hr, K, hQ0, hd, hL, hrJ⟩ := exists_neg_cayleyCoord_local hJ hJ0 hJJ
  set Q : E × F → F →L[ℝ] F :=
    fun q ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)
  -- On the ball of radius `r` about `(p₀, 0)`, `DQ` is bounded by `A = ‖DQ(p₀, 0)‖ + K r`.
  set A := ‖fderiv ℝ Q (p₀, 0)‖ + K * r
  have hA : ∀ q ∈ closedBall (p₀, (0 : F)) r, ‖fderiv ℝ Q q‖ ≤ A := fun q hq ↦
    norm_le_norm_add_const_of_dist_le (a := fderiv ℝ Q q) <| (dist_eq_norm _ _).trans_le <|
      (lipschitzOnWith_iff_norm_sub_le.2 hL).norm_sub_le_of_le hq (mem_closedBall_self hr.le)
        (mem_closedBall_iff_norm.1 hq)
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨t, ht, ht1, htr, hresc⟩ := exists_rescale_of_le (F := F) (K := K) hη hr hA0
  refine ⟨r, hr, t, ht, ht1, A + K, add_nonneg hA0 K.coe_nonneg, fun p hp ↦ ?_,
    fun p hp p' hp' ↦ rescaled_slice_sub_le hd hA hL ht ht1 htr hp hp'⟩
  obtain ⟨hd', hA', hL'⟩ := slice_bounds hd hA hL hp
  obtain ⟨hdt, hAt, hLt⟩ := hresc _ hd' hA' hL'
  exact ⟨by simpa using hQ0 p hp, hdt, hAt, hLt, fun x hx ↦ hrJ (p, t • x)
    (mk_smul_mem_closedBall ht.le htr hp (closedBall_subset_closedBall (by norm_num) hx))⟩

/-- **Families of `J`-holomorphic discs depending Lipschitz continuously on the base point.** Let
`J p : F → (F →L[ℝ] F)` be a family of structures depending on a parameter `p` in a real normed
space `E`, jointly of class `C²` near `(p₀, 0)`, with `J p 0 v = i v` for `p` near `p₀` and
`(J p x)² = -1` near `(p₀, 0)`, as for an almost complex structure written, at each point `p` of a
curve, in coordinates centred at `p` in which it is standard there. Let `κ > 0`. Then there are
`δ, ε > 0`, `C ≥ 0` and maps `u_{p, ξ} : ℂ → F`, for `‖p - p₀‖ ≤ δ` and `‖ξ‖ ≤ 1`, such that

* each `u_{p, ξ}` is `C¹` on the disc of radius `ε`, with `u_{p, ξ}(0) = 0` and
  `∂ₛu_{p, ξ}(0) = ξ`, solves `∂ₛu_{p, ξ} + J p (u_{p, ξ}) ∂ₜu_{p, ξ} = 0` there, and its derivative
  is within `κ` in operator norm of `v ↦ v ξ` there;
* rotating the first jet rotates the parameter: `u_{p, c ξ}(w) = u_{p, ξ}(c w)` for `|c| = 1`;
* the discs and their derivatives depend Lipschitz continuously on the base point and the first
  jet: on the disc of radius `ε`,
  `‖u_{p, ξ} - u_{p', ξ'}‖ ≤ C (‖p - p'‖ + ‖ξ - ξ'‖)` and
  `‖Du_{p, ξ} - Du_{p', ξ'}‖ ≤ C (‖p - p'‖ + ‖ξ - ξ'‖)`.

The radius `ε` of the discs is the same for every base point near `p₀`. -/
theorem exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_mul_add
    [FiniteDimensional ℂ F] {J : E → F → F →L[ℝ] F} {p₀ : E}
    (hJ : ContDiffAt ℝ 2 (uncurry J) (p₀, 0)) (hJ0 : ∀ᶠ p in 𝓝 p₀, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ᶠ q in 𝓝 (p₀, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ > 0, ∃ ε > 0, ∃ C ≥ 0, ∃ u : E → F → ℂ → F,
      (∀ p ∈ closedBall p₀ δ, ∀ ξ : F, ‖ξ‖ ≤ 1 →
        ContDiffOn ℝ 1 (u p ξ) (ball 0 ε) ∧ u p ξ 0 = 0 ∧ fderiv ℝ (u p ξ) 0 1 = ξ ∧
          (∀ z ∈ ball (0 : ℂ) ε,
            fderiv ℝ (u p ξ) z 1 + J p (u p ξ z) (fderiv ℝ (u p ξ) z I) = 0) ∧
          ∀ z ∈ ball (0 : ℂ) ε,
            ‖fderiv ℝ (u p ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
      (∀ p ∈ closedBall p₀ δ, ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w,
        u p (c • ξ) w = u p ξ (c * w)) ∧
      ∀ p ∈ closedBall p₀ δ, ∀ p' ∈ closedBall p₀ δ, ∀ ξ ξ' : F, ‖ξ‖ ≤ 1 → ‖ξ'‖ ≤ 1 →
        ∀ z ∈ ball (0 : ℂ) ε,
          ‖u p ξ z - u p' ξ' z‖ ≤ C * (‖p - p'‖ + ‖ξ - ξ'‖) ∧
            ‖fderiv ℝ (u p ξ) z - fderiv ℝ (u p' ξ') z‖ ≤ C * (‖p - p'‖ + ‖ξ - ξ'‖) := by
  -- One rescaling makes all `Q_p` admissible and `4 η'`-small in `C¹`, with `C (4 η') ≤ κ`; their
  -- discs, rescaled back, solve the equations of the `J p`, and are `O(‖p - p'‖)` apart in `C¹`.
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨η, hη, C, hC, V, hdisc, hV0, hlip⟩ :=
    exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le (F := F)
  obtain ⟨a, ha, haκ⟩ := exists_pos_mul_lt hκ (4 * C)
  set η' := min η a
  have hη' : 0 < η' := lt_min hη ha
  have hCη : C * (4 * η') ≤ κ := by nlinarith [mul_le_mul_of_nonneg_left (min_le_right η a) hC]
  obtain ⟨r, hr, t, ht, ht1, L, hL0, hQt, hQsub⟩ := exists_rescaled_beltrami_family hJ hJ0 hJJ hη'
  -- For each `p`, `Q_p` is bounded by `η`, so it has Beltrami discs, which rescale back.
  have hQη := fun p (hp : p ∈ closedBall p₀ r) ↦
    fderiv_bounds_mono (min_le_left η _) (hQt p hp).2.2.1 (hQt p hp).2.2.2.1
  have hV := fun p (hp : p ∈ closedBall p₀ r) ↦
    hdisc _ (hQt p hp).1 (hQt p hp).2.1 (hQη p hp).1 (hQη p hp).2
  have hres := fun p (hp : p ∈ closedBall p₀ r) ξ (hξ : ‖ξ‖ ≤ 1) ↦
    have hv := (hV p hp).1 ξ hξ
    rescaled_disc ht hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 (hQt p hp).2.2.2.2
  refine ⟨r, hr, t / 2, by positivity, C * (1 + L), by positivity, fun p ξ z ↦ t • V
    (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) ξ (t⁻¹ • z),
    fun p hp ξ hξ ↦ ?_, fun p hp ξ hξ c hc w ↦ ?_, fun p hp p' hp' ξ ξ' hξ hξ' z hz ↦ ?_⟩
  · obtain ⟨hQt0, hdt, hAt, -, -⟩ := hQt p hp
    obtain ⟨huC, hu0, hu1, hu⟩ := hres p hp ξ hξ
    refine ⟨huC, hu0, hu1, fun z hz ↦ (hu z hz).2.2, fun z hz ↦ ?_⟩
    -- `Q_p` is within `4 η'` of `0` in `C¹`, so its disc is `C (4 η')`-close to `w ↦ w ξ`.
    obtain ⟨hQsmall, hDsmall⟩ := norm_sub_zero_le_of_norm_fderiv_le hη'.le hQt0 hdt hAt
    have h0 := fderiv_bounds_mono (F := F) (P := 0) hη.le
      (by simp [ContinuousLinearMap.opNorm_zero]) (by simp [ContinuousLinearMap.opNorm_zero])
    have h := (hlip _ 0 hQt0 rfl hdt (fun _ _ ↦ differentiableAt_const _) (hQη p hp).1 h0.1
      (hQη p hp).2 h0.2 ξ ξ (4 * η') hξ hξ hQsmall hDsmall _ (hu z hz).1).2
    rw [sub_self, norm_zero, zero_add, fderiv_eq_smulRight_of_eq_smul (hV0 ξ hξ),
      ← (hu z hz).2.1] at h
    exact h.trans hCη
  · -- `Q_p` takes conjugate-linear values, so its discs are rotation equivariant.
    have hrot := (hV p hp).2 fun x hx v ↦ neg_cayleyCoord_apply_I_smul ((hQt p hp).2.2.2.2 x hx).1 v
    simp only [hrot ξ hξ c hc, mul_smul_comm]
  · obtain ⟨-, -, -, hu⟩ := hres p hp ξ hξ
    obtain ⟨-, -, -, hu'⟩ := hres p' hp' ξ' hξ'
    -- `Q_p`, `Q_p'` differ by `L ‖p - p'‖` in `C¹`, so the discs by `C (‖ξ - ξ'‖ + L ‖p - p'‖)`.
    obtain ⟨hQ₀, hQ₁⟩ := hQsub p hp p' hp'
    obtain ⟨h₀, h₁⟩ := hlip _ _ (hQt p hp).1 (hQt p' hp').1 (hQt p hp).2.1 (hQt p' hp').2.1
      (hQη p hp).1 (hQη p' hp').1 (hQη p hp).2 (hQη p' hp').2 ξ ξ' _ hξ hξ' hQ₀ hQ₁ _ (hu z hz).1
    have hb : C * (‖ξ - ξ'‖ + L * ‖p - p'‖) ≤ C * (1 + L) * (‖p - p'‖ + ‖ξ - ξ'‖) := by
      nlinarith [mul_nonneg hC (norm_nonneg (p - p')),
        mul_nonneg (mul_nonneg hC hL0) (norm_nonneg (ξ - ξ'))]
    refine ⟨?_, by rw [(hu z hz).2.1, (hu' z hz).2.1]; exact h₁.trans hb⟩
    simp only [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans (h₀.trans hb)

/-- **A rotation-equivariant family of `J`-holomorphic discs with prescribed first jets, close to
complex lines.** Let `J : F → (F →L[ℝ] F)` be of class `C²` near `0`, with `J(0) v = i v` and
`J(x)² = -1` near `0`, as for an almost complex structure in coordinates centred at a point where
it is standard, and let `κ > 0`. Then there are `ε > 0` and maps `u_ξ : ℂ → F`, for `‖ξ‖ ≤ 1`,
each `C¹` on the disc of radius `ε` with `u_ξ(0) = 0` and `∂ₛu_ξ(0) = ξ`, solving
`∂ₛu_ξ + J(u_ξ) ∂ₜu_ξ = 0` there, such that

* on the disc of radius `ε`, the derivative of `u_ξ` is within `κ` in operator norm of `v ↦ v ξ`,
  the derivative of the complex line `w ↦ w ξ` with the same first jet;
* rotating the first jet rotates the parameter: `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`. So the
  discs through `0` with first jets `ξ` and `c ξ` have the same image, parametrized differently by
  the rotation `w ↦ c w`. -/
theorem exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq
    [FiniteDimensional ℂ F] {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0)
    (hJ0 : ∀ v, J 0 v = I • v) (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u ξ) (ball 0 ε) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        (∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ (u ξ) z 1 + J (u ξ z) (fderiv ℝ (u ξ) z I) = 0) ∧
        ∀ z ∈ ball (0 : ℂ) ε,
          ‖fderiv ℝ (u ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
      ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w) := by
  -- This is the case of the constant family `p ↦ J` over `ℝ`, at `p = 0`.
  obtain ⟨δ, hδ, ε, hε, -, -, u, hu, hrot, -⟩ :=
    exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_mul_add
      (J := fun (_ : ℝ) ↦ J) (p₀ := 0) (hJ.comp ((0 : ℝ), (0 : F)) contDiffAt_snd)
      (.of_forall fun _ ↦ hJ0) ((continuousAt_snd (p := ((0 : ℝ), (0 : F)))).eventually hJJ) hκ
  exact ⟨ε, hε, u 0, fun ξ hξ ↦ hu 0 (mem_closedBall_self hδ.le) ξ hξ,
    fun ξ hξ ↦ hrot 0 (mem_closedBall_self hδ.le) ξ hξ⟩

/-- **The `J`-holomorphic discs with unit first jets are embedded.** Under the hypotheses of
`exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq`, the
rotation-equivariant family of discs `u_ξ` can be chosen so that, for every unit vector `ξ`,
`u_ξ` is injective on the disc of radius `ε`, with `|w - w'| ≤ 2 ‖u_ξ(w) - u_ξ(w')‖` there, and
its derivative is injective at every point of that disc, with `|v| ≤ 2 ‖du_ξ(w) v‖`. So each
`u_ξ` is an embedding of the disc, and the discs through `0` in the directions `ξ` are embedded
`J`-holomorphic discs. -/
theorem exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_antilipschitzWith
    [FiniteDimensional ℂ F] {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0)
    (hJ0 : ∀ v, J 0 v = I • v) (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) :
    ∃ ε > 0, ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u ξ) (ball 0 ε) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ (u ξ) z 1 + J (u ξ z) (fderiv ℝ (u ξ) z I) = 0) ∧
      (∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w)) ∧
      ∀ ξ : F, ‖ξ‖ = 1 → AntilipschitzWith 2 ((ball (0 : ℂ) ε).domRestrict (u ξ)) ∧
        ∀ z ∈ ball (0 : ℂ) ε, AntilipschitzWith 2 (fderiv ℝ (u ξ) z) := by
  obtain ⟨ε, hε, u, hu, hrot⟩ :=
    exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq
      hJ hJ0 hJJ (by norm_num : (0 : ℝ) < 2⁻¹)
  refine ⟨ε, hε, u, fun ξ hξ ↦ ?_, hrot, fun ξ hξ ↦ ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄, -⟩ := hu ξ hξ
    exact ⟨h₁, h₂, h₃, h₄⟩
  obtain ⟨huC, -, -, -, hD⟩ := hu ξ hξ.le
  -- The complex line `w ↦ w ξ` is an isometry, and `u_ξ` is within `1/2` of it in `C¹`.
  set φ := (ContinuousLinearMap.id ℝ ℂ).smulRight ξ
  have hφ : AntilipschitzWith 1 φ := φ.antilipschitz_of_bound fun w ↦ by
    simp [φ, norm_smul, hξ]
  have hDnn : ∀ z ∈ ball (0 : ℂ) ε, ‖fderiv ℝ (u ξ) z - φ‖₊ ≤ 2⁻¹ := fun z hz ↦ by
    exact_mod_cast hD z hz
  have hK : (2⁻¹ : ℝ≥0) < (1 : ℝ≥0)⁻¹ := by norm_num
  have hK2 : ((1 : ℝ≥0)⁻¹ - 2⁻¹)⁻¹ = 2 := by
    rw [← NNReal.coe_inj]
    norm_num [NNReal.coe_sub_def]
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
