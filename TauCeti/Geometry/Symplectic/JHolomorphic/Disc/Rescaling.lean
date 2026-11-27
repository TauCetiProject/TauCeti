/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Disc.Existence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Algebra.Ring.CayleyChart
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

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
* The family depends continuously on the structure. Let `J p` depend on a parameter `p` in a real
  normed space, jointly of class `C²` near `(p, 0)` for every `p` in a compact set `S`. The
  Beltrami coefficients and their derivatives are then bounded, and the derivatives uniformly
  Lipschitz, on one ball about `0` for all `p ∈ S`, so a single rescaling factor serves every
  `p ∈ S`, and the discs `u_{p, ξ}` live on a common disc. On that disc the Beltrami coefficients
  of nearby parameters are close in `C¹`, by uniform continuity on a compact set, and the discs
  depend Lipschitz continuously on the coefficient and the first jet. So `u_{p, ξ}(z)` and its
  derivative are jointly continuous in `(p, ξ, z)`
  (`exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_continuousOn`).
  For the structures `J p` read in coordinates centred at the points `p` of a pseudoholomorphic
  curve, this is the continuity in the base point of the family of normal discs. The family for a
  single structure is the case of a one-point parameter set.

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
* `exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_continuousOn`: for structures
  `J p` depending on a parameter, jointly of class `C²` near `(p, 0)` for `p` in a compact set
  `S`, such families `u_{p, ξ}` on one common disc for all `p ∈ S`, with `u_{p, ξ}(z)`
  and its derivative jointly continuous in `(p, ξ, z)`.

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

/-- Rescaling the arguments by `t ≥ 0` multiplies the distance between two derivatives by `t`. -/
private theorem norm_fderiv_comp_smul_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f g : F → E) {t : ℝ} (ht : 0 ≤ t) (x y : F) :
    ‖fderiv ℝ (fun x ↦ f (t • x)) x - fderiv ℝ (fun x ↦ g (t • x)) y‖ ≤
      t * ‖fderiv ℝ f (t • x) - fderiv ℝ g (t • y)‖ := by
  rw [fderiv_comp_smul, fderiv_comp_smul, ← smul_sub]
  refine (ContinuousLinearMap.opNorm_smul_le t _).trans_eq ?_
  rw [Real.norm_of_nonneg ht]

/-- Rescaling by `t ≥ 0` maps the ball of radius `4` into the ball of radius `r ≥ 4 t`. -/
private theorem smul_mem_closedBall_of_four_mul_le {r t : ℝ} (ht : 0 ≤ t) (htr : 4 * t ≤ r)
    {x : F} (hx : ‖x‖ ≤ 4) : t • x ∈ closedBall (0 : F) r := by
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht]
  nlinarith [norm_nonneg x]

/-- Rescaling the argument of a structure by `t` multiplies its derivative by `t` and the
Lipschitz constant of the derivative by `t²`: bounds `A` and `L` on the ball of radius `r ≥ 4 t`
with `t A ≤ η` and `t² L ≤ η` give the bounds `η` for `x ↦ J (t x)` on the ball of radius `4`. -/
private theorem rescale_bounds (J : F → F →L[ℝ] F) {r A L t η : ℝ} (ht : 0 < t) (htr : 4 * t ≤ r)
    (htA : t * A ≤ η) (htL : t ^ 2 * L ≤ η)
    (hd : ∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ J x)
    (hA : ∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ A)
    (hL : ∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ L * ‖x - y‖) :
    (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ (fun x ↦ J (t • x)) x) ∧
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ (fun x ↦ J (t • x)) x‖ ≤ η) ∧
      ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ J (t • x)) x - fderiv ℝ (fun x ↦ J (t • x)) y‖ ≤ η * ‖x - y‖ := by
  have hmem : ∀ x ∈ closedBall (0 : F) 4, t • x ∈ closedBall (0 : F) r := fun x hx ↦
    smul_mem_closedBall_of_four_mul_le ht.le htr (mem_closedBall_zero_iff.1 hx)
  refine ⟨fun x hx ↦ (hd _ (hmem x hx)).comp x (differentiableAt_id.const_smul t),
    fun x hx ↦ ?_, fun x hx y hy ↦ ?_⟩
  · calc ‖fderiv ℝ (fun x ↦ J (t • x)) x‖ = t * ‖fderiv ℝ J (t • x)‖ := by
          rw [norm_fderiv_comp_smul, abs_of_pos ht]
      _ ≤ t * A := by gcongr; exact hA _ (hmem x hx)
      _ ≤ η := htA
  · refine (norm_fderiv_comp_smul_sub_le J J ht.le x y).trans ?_
    have hxy := hL _ (hmem x hx) _ (hmem y hy)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le] at hxy
    calc t * ‖fderiv ℝ J (t • x) - fderiv ℝ J (t • y)‖ ≤ t * (L * (t * ‖x - y‖)) := by gcongr
      _ = t ^ 2 * L * ‖x - y‖ := by ring
      _ ≤ η * ‖x - y‖ := mul_le_mul_of_nonneg_right htL (norm_nonneg _)

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

/-- A rescaling factor `t ≤ 1` with `4 t ≤ r`, `t A ≤ η` and `t² L ≤ η`, for which bounds `A`
and `L` on the derivative of a structure on the ball of radius `r` and on its Lipschitz constant
give the bounds `η` for the rescaled structure (`rescale_bounds`). It depends only on `η`, `r`, `A`
and `L`. -/
private theorem exists_rescale {η r A L : ℝ} (hη : 0 < η) (hr : 0 < r) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ t > 0, t ≤ 1 ∧ 4 * t ≤ r ∧ t * A ≤ η ∧ t ^ 2 * L ≤ η := by
  set t := min (min (r / 4) 1) (η / (A + L + 1))
  have ht : 0 < t := lt_min (lt_min (by positivity) one_pos) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have htr : t ≤ r / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have htη : t * (A + L + 1) ≤ η := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have htL : t ^ 2 * L ≤ t * L := by
    rw [pow_two, mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg ht.le hL) ht1
  exact ⟨t, ht, ht1, by linarith, by nlinarith [mul_nonneg ht.le hL],
    by nlinarith [mul_nonneg ht.le hA]⟩

/-- **Discs solving `∂ₛu + J(u) ∂ₜu = 0` with a prescribed first jet.** Let
`J : F → (F →L[ℝ] F)` be of class `C²` near `0` with `J(0) v = i v`. For every `ξ ∈ F` there is a
`C¹` map `u` from a disc about `0` in `ℂ` to `F` with `u(0) = 0` and `∂ₛu(0) = ξ` which solves
`∂ₛu + J(u) ∂ₜu = 0`. -/
theorem exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt [FiniteDimensional ℂ F]
    {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0) (hJ0 : ∀ v, J 0 v = I • v) (ξ : F) :
    ∃ ε > 0, ∃ u : ℂ → F, ContDiffOn ℝ 1 u (ball 0 ε) ∧ u 0 = 0 ∧ fderiv ℝ u 0 1 = ξ ∧
      ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0 := by
  obtain ⟨η, hη, hdisc⟩ := exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero (F := F)
  -- Near `0`, `J` is differentiable and `DJ` is Lipschitz, hence bounded by `‖DJ(0)‖ + K r`.
  obtain ⟨r, hr, K, hd, hL⟩ := hJ.exists_closedBall_differentiableAt_lipschitz_fderiv
  have hA : ∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + K * r := fun x hx ↦ by
    have h := hL x hx 0 (mem_closedBall_self hr.le)
    rw [sub_zero] at h
    rw [mem_closedBall, dist_zero_right] at hx
    calc ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + ‖fderiv ℝ J x - fderiv ℝ J 0‖ :=
          norm_le_insert' (fderiv ℝ J x) (fderiv ℝ J 0)
      _ ≤ _ := by gcongr; exact h.trans (by gcongr)
  obtain ⟨t, ht, -, htr, htA, htL⟩ :=
    exists_rescale (A := ‖fderiv ℝ J 0‖ + K * r) hη hr (by positivity) K.coe_nonneg
  obtain ⟨hdt, hAt, hLt⟩ := rescale_bounds J ht htr htA htL hd hA hL
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

/-- An endomorphism acting as multiplication by `i` is `lsmul i`. -/
private theorem eq_lsmul_I {A : F →L[ℝ] F} (hA : ∀ v, A v = I • v) :
    A = ContinuousLinearMap.lsmul ℝ ℂ I := by
  ext v
  simp [hA]

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

/-- Near a point `(p, 0)` where the structures `J` are `C²` with `J p 0 = i` and square to `-1`
nearby, they are `C²`, square to `-1` and `i + J` is invertible. -/
private theorem eventually_contDiffAt_and_isUnit [CompleteSpace F] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {J : P → F → F →L[ℝ] F} {p : P}
    (hJ : ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) (p, 0)) (hJ0 : ∀ v, J p 0 v = I • v)
    (hJJ : ∀ᶠ q in 𝓝 (p, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) :
    ∀ᶠ q in 𝓝 (p, (0 : F)), ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) q ∧
      (∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) ∧
      IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J q.1 q.2) := by
  have hI0 := eq_lsmul_I hJ0
  have hU : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p 0) := by
    have h2 := (IsUnit.mk0 (2 : ℝ) two_ne_zero).map (algebraMap ℝ (F →L[ℝ] F))
    rw [map_ofNat] at h2
    rw [hI0, ← two_mul]
    exact isUnit_two_mul_of_mul_self_eq_neg_one h2 ContinuousLinearMap.lsmul_I_mul_lsmul_I
  exact (hJ.eventually (by simp)).and (hJJ.and
    ((continuousAt_const.add hJ.continuousAt).eventually (Units.isOpen.mem_nhds hU)))

/-- **Uniform bounds for the Beltrami coefficients of a compact family of structures.** Let the
structures `J p` depend on a parameter, jointly of class `C²` near `(p, 0)` with `J p 0 = i` and
`J² = -1` near `(p, 0)`, for every `p` in a compact set `S`, and let `G (p, x)` be the Beltrami
coefficient `-cayleyCoord i (J p x)`. Then on one closed ball of radius `r` about `0` and for every
`p ∈ S`, `J p x² = -1`, `i + J p x` is invertible, and `x ↦ G (p, x)` is differentiable with
derivative bounded by `A` and `A`-Lipschitz; and `G` and its derivative in `x` are jointly
continuous on `S ×ˢ closedBall 0 r`. -/
private theorem exists_uniform_bounds_neg_cayleyCoord [FiniteDimensional ℂ F] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {S : Set P} (hS : IsCompact S)
    {J : P → F → F →L[ℝ] F} (hJ : ∀ p ∈ S, ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) (p, 0))
    (hJ0 : ∀ p ∈ S, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ p ∈ S, ∀ᶠ q in 𝓝 (p, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v)
    {G : P × F → F →L[ℝ] F}
    (hG : ∀ q, G q = -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) :
    ∃ r > 0, ∃ A ≥ 0, (∀ p ∈ S, ∀ x ∈ closedBall (0 : F) r,
      ((∀ v, J p x (J p x v) = -v) ∧ IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p x)) ∧
      DifferentiableAt ℝ (fun x ↦ G (p, x)) x ∧ ‖fderiv ℝ (fun x ↦ G (p, x)) x‖ ≤ A ∧
      ∀ y ∈ closedBall (0 : F) r,
        ‖fderiv ℝ (fun x ↦ G (p, x)) x - fderiv ℝ (fun x ↦ G (p, x)) y‖ ≤ A * ‖x - y‖) ∧
      ContinuousOn G (S ×ˢ closedBall 0 r) ∧
      ContinuousOn (fun q : P × F ↦ fderiv ℝ (fun x ↦ G (q.1, x)) q.2) (S ×ˢ closedBall 0 r) := by
  have := FiniteDimensional.completeSpace ℂ F
  have : ProperSpace F := FiniteDimensional.proper_rclike ℂ F
  set ι : F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ I
  -- The open set `W` of `(p, x)` near which `J` is `C²`, squares to `-1` and `i + J` is invertible
  -- contains `S × {0}`, hence some `S × closedBall 0 r`.
  set W := interior {q : P × F | ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) q ∧
    (∀ v, J q.1 q.2 (J q.1 q.2 v) = -v) ∧ IsUnit (ι + J q.1 q.2)}
  have hSW : S ×ˢ ({0} : Set F) ⊆ W := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_interior_iff_mem_nhds.2 (eventually_contDiffAt_and_isUnit (hJ p hp) (hJ0 p hp)
      (hJJ p hp))
  obtain ⟨U, V, -, hVo, hSU, h0V, hUV⟩ :=
    generalized_tube_lemma hS isCompact_singleton isOpen_interior hSW
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hVo.mem_nhds (h0V (Set.mem_singleton 0)))
  have hTW : S ×ˢ closedBall (0 : F) r ⊆ W := (Set.prod_mono hSU hrV).trans hUV
  have hGW : ContDiffOn ℝ 2 G W := fun q hq ↦ by
    obtain ⟨hC, -, hU⟩ := interior_subset hq
    have hinv : ContDiffAt ℝ 2 Ring.inverse (ι + J q.1 q.2) :=
      hU.unit_spec ▸ contDiffAt_ringInverse ℝ hU.unit
    rw [show G = fun q ↦ -cayleyCoord ι (J q.1 q.2) from funext hG]
    simp only [cayleyCoord_def]
    exact ((contDiffAt_const.sub hC).mul (hinv.comp q (contDiffAt_const.add hC))).neg
      |>.contDiffWithinAt
  -- The derivatives of order at most two of `x ↦ G (p, x)` are bounded by one `B` on the compact
  -- set, which bounds `D_x G` and its Lipschitz constant on the ball.
  obtain ⟨B, hB0, hB⟩ := (hGW.of_le (by norm_num : ((2 : ℕ) : WithTop ℕ∞) ≤ 2)
    ).exists_nonneg_bound_iteratedFDeriv_uncurry_of_isOpen (f := fun p x ↦ G (p, x))
      isOpen_interior hS (isCompact_closedBall (0 : F) r) hTW
  have hC2 : ∀ p ∈ S, ∀ x ∈ closedBall (0 : F) r, ContDiffAt ℝ 2 (fun x ↦ G (p, x)) x :=
    fun p hp x hx ↦ by exact_mod_cast (hB p hp x hx).1
  refine ⟨r, hr, B, hB0, fun p hp x hx ↦ ⟨(interior_subset (hTW (Set.mk_mem_prod hp hx))).2,
    (hC2 p hp x hx).differentiableAt two_ne_zero, ?_, fun y hy ↦ ?_⟩,
    hGW.continuousOn.mono hTW, ?_⟩
  · rw [← norm_iteratedFDeriv_one]
    exact (hB p hp x hx).2 1 (by norm_num)
  · exact (convex_closedBall (0 : F) r).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ (fun x ↦ G (p, x)))
      (fun z hz ↦ ((hC2 p hp z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
        one_ne_zero)
      (fun z hz ↦ by
        rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
        exact (hB p hp z hz).2 2 le_rfl) hy hx
  -- The derivative in `x` is that of `G` composed with `inr`, so it is continuous.
  refine ((hGW.continuousOn_fderiv_of_isOpen isOpen_interior (by norm_num)).mono hTW
    |>.clm_comp (continuousOn_const (c := ContinuousLinearMap.inr ℝ P F))).congr fun q hq ↦ ?_
  exact (((hGW.contDiffAt (isOpen_interior.mem_nhds (hTW hq))).differentiableAt
    two_ne_zero).hasFDerivAt.comp q.2 (hasFDerivAt_prodMk_right q.1 q.2)).fderiv

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

/-- The discs `v_ξ` of the Beltrami equation `\bar∂v = Q(v) ∂v` for the rescaled Beltrami
coefficient `Q(x) = -cayleyCoord i (J (t x))` of a structure `J`, rescaled back to
`u_ξ(z) = t v_ξ(z / t)`, solve `∂ₛu + J(u) ∂ₜu = 0` on the disc of radius `t / 2`, with
`u_ξ(0) = 0`, `∂ₛu_ξ(0) = ξ` and `Du_ξ(z) = Dv_ξ(z / t)`, so that `Du_ξ` is as close to the
derivative of the complex line `w ↦ w ξ` as `Dv_ξ` is on the unit disc. -/
private theorem rescaled_disc_props {J : F → F →L[ℝ] F} {v : F → ℂ → F} {t κ : ℝ} (ht : 0 < t)
    (hJ : ∀ x : F, ‖x‖ ≤ 2 → (∀ w, J (t • x) (J (t • x) w) = -w) ∧
      IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J (t • x)))
    (hv : ∀ ξ : F, ‖ξ‖ ≤ 1 → ContDiffOn ℝ 1 (v ξ) (ball 0 2) ∧ v ξ 0 = 0 ∧
      fderiv ℝ (v ξ) 0 1 = ξ ∧ (∀ z ∈ closedBall (0 : ℂ) 1, ‖v ξ z‖ ≤ 2) ∧
      ∀ z ∈ ball (0 : ℂ) 2⁻¹, conjWirtingerDeriv (v ξ) z 1 =
        -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J (t • v ξ z)) (wirtingerDeriv (v ξ) z 1))
    (hclose : ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖fderiv ℝ (v ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ)
    {ξ : F} (hξ : ‖ξ‖ ≤ 1) :
    (ContDiffOn ℝ 1 (fun z ↦ t • v ξ (t⁻¹ • z)) (ball 0 (t / 2)) ∧
      t • v ξ (t⁻¹ • (0 : ℂ)) = 0 ∧ fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) 0 1 = ξ ∧
      (∀ z ∈ ball (0 : ℂ) (t / 2), fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z 1 +
        J (t • v ξ (t⁻¹ • z)) (fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z I) = 0) ∧
      ∀ z ∈ ball (0 : ℂ) (t / 2),
        ‖fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
    ∀ z ∈ ball (0 : ℂ) (t / 2), t⁻¹ • z ∈ closedBall (0 : ℂ) 1 ∧
      fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z = fderiv ℝ (v ξ) (t⁻¹ • z) := by
  obtain ⟨hvC, hv0, hv1, hvb, hvbel⟩ := hv ξ hξ
  obtain ⟨huC, hu0, hu1, hu⟩ := rescale_props ht one_pos hvC hv0 (by simpa using hv1)
  rw [mul_one] at huC hu0 hu1 hu
  have hfd : ∀ z ∈ ball (0 : ℂ) (t / 2),
      fderiv ℝ (fun z ↦ t • v ξ (t⁻¹ • z)) z = fderiv ℝ (v ξ) (t⁻¹ • z) := fun z hz ↦
    ContinuousLinearMap.ext fun w ↦ by rw [(hu z hz).2, mul_inv_cancel₀ ht.ne', one_smul]
  have hz1 : ∀ z ∈ ball (0 : ℂ) (t / 2), t⁻¹ • z ∈ closedBall (0 : ℂ) 1 := fun z hz ↦
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) (hu z hz).1
  refine ⟨⟨huC, hu0, hu1, fun z hz ↦ ?_, fun z hz ↦ ?_⟩, fun z hz ↦ ⟨hz1 z hz, hfd z hz⟩⟩
  · have hy' := hJ _ (hvb _ (hz1 z hz))
    refine apply_one_add_apply_apply_I_eq_zero hy'.1 hy'.2 ?_
    rw [hfd z hz, ← conjWirtingerDeriv_eq_complexAntilinearPart,
      ← wirtingerDeriv_eq_complexLinearPart]
    exact hvbel _ (hu z hz).1
  · rw [hfd z hz]
    exact hclose ξ hξ _ (hz1 z hz)

/-- **One rescaling for a compact family of structures.** Under the hypotheses of
`exists_uniform_bounds_neg_cayleyCoord` and for `η > 0`, there is one factor `t > 0` such that for
every `p ∈ S` the rescaled Beltrami coefficient `x ↦ -cayleyCoord i (J p (t x))` vanishes at `0`
and, on the ball of radius `4`, is differentiable with derivative bounded by `η` and `η`-Lipschitz,
while `J p (t x)² = -1` and `i + J p (t x)` is invertible there; and the rescaled coefficients of
parameters `p'` near `p` in `S` are uniformly close to that of `p` in `C¹` on that ball. -/
private theorem exists_rescale_neg_cayleyCoord [FiniteDimensional ℂ F] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {S : Set P} (hS : IsCompact S)
    {J : P → F → F →L[ℝ] F} (hJ : ∀ p ∈ S, ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) (p, 0))
    (hJ0 : ∀ p ∈ S, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ p ∈ S, ∀ᶠ q in 𝓝 (p, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v)
    {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ ∀ p ∈ S, (∀ x : F, ‖x‖ ≤ 4 → (∀ v, J p (t • x) (J p (t • x) v) = -v) ∧
        IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p (t • x))) ∧
      -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • 0)) = 0 ∧
      (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ
        (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x) ∧
      (∀ x ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x‖ ≤ η) ∧
      (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x -
          fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) y‖ ≤
            η * ‖x - y‖) ∧
      ∀ e > 0, ∀ᶠ p' in 𝓝[S] p, ∀ x ∈ closedBall (0 : F) 4,
        ‖-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p' (t • x)) -
          -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))‖ ≤ e ∧
        ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p' (t • x))) x -
          fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) x‖ ≤
            e := by
  obtain ⟨r, hr, A, hA, hloc, hGc, hDGc⟩ := exists_uniform_bounds_neg_cayleyCoord
    (G := fun q ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) hS hJ hJ0 hJJ
    fun _ ↦ rfl
  dsimp only at hloc hDGc
  choose hsq hdiff hbd hlip using hloc
  have : ProperSpace F := FiniteDimensional.proper_rclike ℂ F
  obtain ⟨t, ht, ht1, htr, htA, htK⟩ := exists_rescale hη hr hA hA
  have hmem : ∀ x : F, ‖x‖ ≤ 4 → t • x ∈ closedBall (0 : F) r := fun _ ↦
    smul_mem_closedBall_of_four_mul_le ht.le htr
  have hT := hS.prod (isCompact_closedBall (0 : F) r)
  refine ⟨t, ht, fun p hp ↦ ?_⟩
  obtain ⟨hdt, hAt, hLt⟩ := rescale_bounds _ ht htr htA htK (hdiff p hp) (hbd p hp) (hlip p hp)
  refine ⟨fun x hx ↦ hsq p hp _ (hmem x hx), by
    rw [smul_zero, eq_lsmul_I (hJ0 p hp), cayleyCoord_self, neg_zero], hdt, hAt, hLt,
    fun e he ↦ ?_⟩
  -- Uniform continuity of the coefficient and of its derivative on the compact `S × B(0, r)`.
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuousOn_iff.1
    (hT.uniformContinuousOn_of_continuous
      (f := fun q : P × F ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 q.2)) hGc) e he
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuousOn_iff.1
    (hT.uniformContinuousOn_of_continuous (f := fun q : P × F ↦
      fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J q.1 x)) q.2) hDGc) e he
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds p (lt_min hδ₁ hδ₂))] with p' hp' hpd x hx
  have hx' := hmem x (mem_closedBall_zero_iff.1 hx)
  have hd : dist (p', t • x) (p, t • x) < min δ₁ δ₂ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hpd
  have h₁' := h₁ _ ⟨hp', hx'⟩ _ ⟨hp, hx'⟩ (hd.trans_le (min_le_left _ _))
  have h₂' := h₂ _ ⟨hp', hx'⟩ _ ⟨hp, hx'⟩ (hd.trans_le (min_le_right _ _))
  rw [dist_eq_norm] at h₁' h₂'
  refine ⟨h₁'.le, ?_⟩
  exact (norm_fderiv_comp_smul_sub_le
    (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p' x))
    (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p x)) ht.le x x).trans
    ((mul_le_mul ht1 h₂'.le (norm_nonneg _) zero_le_one).trans_eq (one_mul e))

/-- **Beltrami discs for a compact family of rescaled structures.** Under the hypotheses of
`exists_rescale_neg_cayleyCoord` and for `κ > 0`, there are a factor `t > 0`, a constant `C ≥ 0`
and discs `v_{p, ξ}`, for `p ∈ S` and `‖ξ‖ ≤ 1`, solving the Beltrami equation of the rescaled
coefficient `x ↦ -cayleyCoord i (J p (t x))` near `0` with `v_{p, ξ}(0) = 0` and first jet `ξ`,
with derivatives within `κ` of `v ↦ v ξ` on the unit disc and rotation equivariant in `ξ`, and such
that for every `e > 0` and `p` near `p₀` in `S`, the discs and their derivatives move by at most
`C (‖ξ - ξ₀‖ + e)` on the unit disc. -/
private theorem exists_rescaled_beltrami_discs [FiniteDimensional ℂ F] {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] {S : Set P} (hS : IsCompact S)
    {J : P → F → F →L[ℝ] F} (hJ : ∀ p ∈ S, ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) (p, 0))
    (hJ0 : ∀ p ∈ S, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ p ∈ S, ∀ᶠ q in 𝓝 (p, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ t : ℝ, 0 < t ∧ ∃ C ≥ 0, ∃ v : P → F → ℂ → F,
      (∀ p ∈ S, ∀ x : F, ‖x‖ ≤ 4 → (∀ w, J p (t • x) (J p (t • x) w) = -w) ∧
        IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J p (t • x))) ∧
      (∀ p ∈ S, ∀ ξ : F, ‖ξ‖ ≤ 1 → ContDiffOn ℝ 1 (v p ξ) (ball 0 2) ∧ v p ξ 0 = 0 ∧
        fderiv ℝ (v p ξ) 0 1 = ξ ∧ (∀ z ∈ closedBall (0 : ℂ) 1, ‖v p ξ z‖ ≤ 2) ∧
        ∀ z ∈ ball (0 : ℂ) 2⁻¹, conjWirtingerDeriv (v p ξ) z 1 =
          -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • v p ξ z))
            (wirtingerDeriv (v p ξ) z 1)) ∧
      (∀ p ∈ S, ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ z ∈ closedBall (0 : ℂ) 1,
        ‖fderiv ℝ (v p ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
      (∀ p ∈ S, ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, v p (c • ξ) w = v p ξ (c * w)) ∧
      ∀ p₀ ∈ S, ∀ e > 0, ∀ᶠ p in 𝓝[S] p₀, ∀ ξ ξ₀ : F, ‖ξ‖ ≤ 1 → ‖ξ₀‖ ≤ 1 →
        ∀ z ∈ closedBall (0 : ℂ) 1, ‖v p ξ z - v p₀ ξ₀ z‖ ≤ C * (‖ξ - ξ₀‖ + e) ∧
          ‖fderiv ℝ (v p ξ) z - fderiv ℝ (v p₀ ξ₀) z‖ ≤ C * (‖ξ - ξ₀‖ + e) := by
  -- Rescale every Beltrami coefficient by one factor `t`, small enough that the rescaled
  -- coefficients are admissible for the Beltrami discs `V` and within `4 η'` of `0` in `C¹`, with
  -- `C (4 η') ≤ κ`.
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨η, hη, C, hC, V, hdisc, hV0, hlip⟩ :=
    exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le (F := F)
  set η' := min η (κ / (4 * (C + 1)))
  have hη' : 0 < η' := lt_min hη (by positivity)
  have hCη : C * (4 * η') ≤ κ := by
    have h : η' * (4 * (C + 1)) ≤ κ := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  obtain ⟨t, ht, hR⟩ := exists_rescale_neg_cayleyCoord hS hJ hJ0 hJJ hη'
  choose hsq h0 hd hA hL hnear using hR
  have hadm := fun p (hp : p ∈ S) ↦ fderiv_bounds_mono (min_le_left η _) (hA p hp) (hL p hp)
  have hV' := fun p (hp : p ∈ S) ↦ hdisc
    (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) (h0 p hp) (hd p hp)
    (hadm p hp).1 (hadm p hp).2
  refine ⟨t, ht, C, hC, fun p ↦ V (fun x ↦
      -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))), hsq,
    fun p hp ↦ (hV' p hp).1, fun p hp ξ hξ z hz ↦ ?_, fun p hp ↦ (hV' p hp).2 fun x hx w ↦ ?_,
    fun p₀ hp₀ e he ↦ ?_⟩
  · -- The disc of a coefficient within `4 η'` of `0` in `C¹` is within `C (4 η')` of `w ↦ w ξ`.
    obtain ⟨hQsmall, hDsmall⟩ := norm_sub_zero_le_of_norm_fderiv_le
      (P := fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J p (t • x))) hη'.le
      (h0 p hp) (hd p hp) (hA p hp)
    have h := (hlip _ 0 (h0 p hp) rfl (hd p hp) (fun _ _ ↦ differentiableAt_const _) (hadm p hp).1
      (fun _ _ ↦ by simpa [ContinuousLinearMap.opNorm_zero] using hη.le) (hadm p hp).2
      (fun _ _ _ _ ↦ by
        simpa [ContinuousLinearMap.opNorm_zero] using mul_nonneg hη.le (norm_nonneg _))
      ξ ξ (4 * η') hξ hξ hQsmall hDsmall z hz).2
    rw [sub_self, norm_zero, zero_add, fderiv_eq_smulRight_of_eq_smul (hV0 ξ hξ)] at h
    exact h.trans hCη
  · -- The Cayley coordinate of a square root of `-1` anticommutes with `i`.
    have h := congrArg (fun T : F →L[ℝ] F ↦ T w)
      (cayleyCoord_mul_eq_neg_mul ContinuousLinearMap.lsmul_I_mul_lsmul_I
        (mul_self_eq_neg_one (hsq p hp x (by linarith [mem_closedBall_zero_iff.1 hx])).1))
    simp only [mul_apply_eq_comp, neg_apply, ContinuousLinearMap.lsmul_apply] at h
    rw [neg_apply, neg_apply, h, smul_neg]
  · filter_upwards [hnear p₀ hp₀ e he, self_mem_nhdsWithin] with p hpG hp ξ ξ₀ hξ hξ₀ z hz
    exact hlip _ _ (h0 p hp) (h0 p₀ hp₀) (hd p hp) (hd p₀ hp₀) (hadm p hp).1
      (hadm p₀ hp₀).1 (hadm p hp).2 (hadm p₀ hp₀).2 ξ ξ₀ e hξ hξ₀ (fun x hx ↦ (hpG x hx).1)
      (fun x hx ↦ (hpG x hx).2) z hz

/-- **A family of `J`-holomorphic discs depending continuously on the structure.** Let
`J : P → F → (F →L[ℝ] F)` be structures depending on a parameter `p` in a real normed space, such
as an almost complex structure read in coordinates centred at a varying point `p` where it is
standard. Suppose that for every `p` in a compact set `S`, `(p, x) ↦ J p x` is of class `C²` near
`(p, 0)`, `J p 0 v = i v` and `J² = -1` near `(p, 0)`, and let `κ > 0`. Then there are `ε > 0`
and maps `u_{p, ξ} : ℂ → F`, for `p ∈ S` and `‖ξ‖ ≤ 1`, with the properties of
`exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_norm_sub_le_and_apply_smul_eq` for
every `p ∈ S` on the common disc of radius `ε`:

* each `u_{p, ξ}` is `C¹` on that disc with `u_{p, ξ}(0) = 0` and `∂ₛu_{p, ξ}(0) = ξ`, solves
  `∂ₛu + J p (u) ∂ₜu = 0` there, and its derivative is within `κ` of that of `w ↦ w ξ`;
* `u_{p, c ξ}(w) = u_{p, ξ}(c w)` for `|c| = 1`;

and such that `u_{p, ξ}(z)` and its derivative `Du_{p, ξ}(z)` are jointly continuous in
`(p, ξ, z)` on `S × closedBall 0 1 × ball 0 ε`. -/
theorem exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_continuousOn
    [FiniteDimensional ℂ F] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {S : Set P}
    (hS : IsCompact S) {J : P → F → F →L[ℝ] F}
    (hJ : ∀ p ∈ S, ContDiffAt ℝ 2 (fun q : P × F ↦ J q.1 q.2) (p, 0))
    (hJ0 : ∀ p ∈ S, ∀ v, J p 0 v = I • v)
    (hJJ : ∀ p ∈ S, ∀ᶠ q in 𝓝 (p, (0 : F)), ∀ v, J q.1 q.2 (J q.1 q.2 v) = -v)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε > 0, ∃ u : P → F → ℂ → F, (∀ p ∈ S, ∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u p ξ) (ball 0 ε) ∧ u p ξ 0 = 0 ∧ fderiv ℝ (u p ξ) 0 1 = ξ ∧
        (∀ z ∈ ball (0 : ℂ) ε,
          fderiv ℝ (u p ξ) z 1 + J p (u p ξ z) (fderiv ℝ (u p ξ) z I) = 0) ∧
        ∀ z ∈ ball (0 : ℂ) ε,
          ‖fderiv ℝ (u p ξ) z - (ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ ≤ κ) ∧
      (∀ p ∈ S, ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u p (c • ξ) w = u p ξ (c * w)) ∧
      ContinuousOn (fun q : (P × F) × ℂ ↦ u q.1.1 q.1.2 q.2)
        ((S ×ˢ closedBall 0 1) ×ˢ ball 0 ε) ∧
      ContinuousOn (fun q : (P × F) × ℂ ↦ fderiv ℝ (u q.1.1 q.1.2) q.2)
        ((S ×ˢ closedBall 0 1) ×ˢ ball 0 ε) := by
  obtain ⟨t, ht, C, hC, v, hJt, hv, hclose, hrot, hnear⟩ :=
    exists_rescaled_beltrami_discs hS hJ hJ0 hJJ hκ
  -- The discs `v_{p, ξ}` rescaled back, `u_{p, ξ}(z) = t v_{p, ξ}(z / t)`, are the family.
  have hfam := fun p (hp : p ∈ S) ξ (hξ : ‖ξ‖ ≤ 1) ↦ rescaled_disc_props (J := J p) ht
    (fun x hx ↦ hJt p hp x (by linarith)) (hv p hp) (hclose p hp) hξ
  have hB : ∀ ξ ∈ closedBall (0 : F) 1, ‖ξ‖ ≤ 1 := fun ξ hξ ↦ mem_closedBall_zero_iff.1 hξ
  refine ⟨t / 2, by positivity, fun p ξ z ↦ t • v p ξ (t⁻¹ • z),
    fun p hp ξ hξ ↦ (hfam p hp ξ hξ).1, fun p hp ξ hξ c hc w ↦ ?_, ?_, ?_⟩
  · dsimp only
    rw [hrot p hp ξ hξ c hc, mul_smul_comm]
  · refine continuousOn_prod_of_eventually_norm_sub_le (M := t * C) (by positivity)
      (fun a ha ↦ (hfam a.1 ha.1 a.2 (hB _ ha.2)).1.1.continuousOn)
      fun p₀ hp₀ ξ₀ hξ₀ e he ↦ ?_
    filter_upwards [hnear p₀ hp₀ e he, self_mem_nhdsWithin] with p hpv hp ξ hξ z hz
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpv ξ ξ₀ (hB _ hξ) (hB _ hξ₀) _
      ((hfam p hp ξ (hB _ hξ)).2 z hz).1).1 ht.le
  · refine continuousOn_prod_of_eventually_norm_sub_le hC (fun a ha ↦
      (hfam a.1 ha.1 a.2 (hB _ ha.2)).1.1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)
      fun p₀ hp₀ ξ₀ hξ₀ e he ↦ ?_
    filter_upwards [hnear p₀ hp₀ e he, self_mem_nhdsWithin] with p hpv hp ξ hξ z hz
    obtain ⟨hz1, hfp⟩ := (hfam p hp ξ (hB _ hξ)).2 z hz
    rw [hfp, ((hfam p₀ hp₀ ξ₀ (hB _ hξ₀)).2 z hz).2]
    exact (hpv ξ ξ₀ (hB _ hξ) (hB _ hξ₀) _ hz1).2

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
  obtain ⟨ε, hε, u, hu, hrot, -⟩ :=
    exists_pos_exists_fderiv_one_add_apply_fderiv_I_eq_zero_and_continuousOn
      (isCompact_singleton (x := (0 : ℝ))) (J := fun _ ↦ J)
      (fun p _ ↦ hJ.comp (p, (0 : F)) contDiffAt_snd) (fun _ _ ↦ hJ0)
      (fun p _ ↦ (continuous_snd.tendsto (p, (0 : F))).eventually hJJ) hκ
  exact ⟨ε, hε, u 0, hu 0 (Set.mem_singleton 0), hrot 0 (Set.mem_singleton 0)⟩

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
