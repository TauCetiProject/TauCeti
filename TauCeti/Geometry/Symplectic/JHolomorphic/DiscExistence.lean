/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Algebra.Ring.CayleyChart
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Pompeiu.Holder.Operator
import TauCeti.Analysis.Complex.Pompeiu.Rotation
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Analysis.Holder.Bilinear
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Topology.MetricSpace.Holder

/-!
# Pseudoholomorphic discs with a prescribed centre and first jet

Let `F` be a finite-dimensional complex normed space and `J : F → (F →L[ℝ] F)` a field of real
endomorphisms with `J(0) v = i v`, such as an almost complex structure written in coordinates
centred at a point where it is standard. This file solves the nonlinear Cauchy–Riemann equation

`∂ₛu + J(u) ∂ₜu = 0`

for maps `u` from a disc in `ℂ = {s + i t}` to `F`. The two non-equivariant theorems are stated
for this equation and an arbitrary field `J`; the equivariant family theorem also needs
`J(x)² = -1` near `0`, and the Beltrami theorem is stated for the equation `\bar∂u = Q(u) ∂u`
below. When every `J(x)` is an almost complex structure, `J(x)² = -1`, a solution
is `J`-holomorphic for the standard structure of `ℂ` in the sense of `TauCeti.IsJHolomorphicAt`
(`TauCeti.isJHolomorphicAt_iff_fderiv_one_add_apply_fderiv_I_eq_zero`).
Through the centre `0` there is a solution in every complex direction: for every `ξ ∈ F` there is
a `C¹` solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`
(`TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`).

The proof is a contraction for the Cauchy transform `T h(w) = π⁻¹ ∫ (w - z)⁻¹ h(z) dz`
(`TauCeti.cauchyTransform`), which satisfies `\bar∂ T h = h`. The equation is written as
`\bar∂u = K(u) ℓ(Du)` for a coefficient `K : F → (F →L[ℝ] F)` with `K(0) = 0` and a real-linear
`ℓ` of norm at most `1` applied to the derivative `Du`. Its solutions with the prescribed centre
and first jet are sought as

`u(w) = w ξ + T h(w) - T h(0) - w · ∂ₛ(T h)(0)`,

whose centre and first jet do not depend on the source `h`, because the subtracted terms are
holomorphic. The source solves the fixed-point equation `h = χ · K(u) ℓ(Du)` with the radial
cutoff `χ(z) = min 1 (max 0 (2 - 2|z|))`, equal to `1` on `|z| ≤ 1/2` and vanishing off the unit
disc. On the Banach space of `1/2`-Hölder sources supported in the unit disc the right side is a
contraction with constant `1/2` on a fixed ball of sources as soon as the first derivative of `K`
and the Lipschitz constant of that derivative are small on a fixed ball of `F`: the Cauchy
transform gains a derivative in Hölder norm (`TauCeti.cauchyDerivativeCLM`), so `Du` is Hölder,
and the Lipschitz bounds on `K` and its derivative make `h ↦ K(u)` Lipschitz in the Hölder norm.
So the source is unique in that ball. On `|w| < 1/2`, where `χ = 1`, the fixed point solves the
equation.

Two forms of the equation are used.

* With `J(x) = i + K(x)`, the equation `∂ₛu + J(u) ∂ₜu = 0` reads `\bar∂u = K(u) (-∂ₜu / 2)`
  (`TauCeti.exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero`).
* The **Beltrami form** `\bar∂u = Q(u) ∂u`, with `∂u = (∂ₛu - i ∂ₜu) / 2`
  (`TauCeti.exists_pos_forall_exists_conjWirtingerDeriv_eq_apply_wirtingerDeriv_and_apply_smul_eq`).
  For `J(x)² = -1` with `i + J(x)` invertible it is equivalent to `∂ₛu + J(u) ∂ₜu = 0` when
  `Q = (J + i)⁻¹ (i - J)` is the Beltrami coefficient of `J`, minus its Cayley coordinate
  `TauCeti.cayleyCoord i J` relative to `i`, which is conjugate linear
  (`TauCeti.cayleyCoord_mul_eq_neg_mul`). Both forms have the same solutions, and these are
  preserved by rotations `w ↦ c w` of the domain with `|c| = 1`. What the Beltrami form adds is
  that, for conjugate-linear `Q`, its right side `Q(u) ∂u` is compatible with the source rotation
  `h ↦ c⁻¹ h(c ·)`, unlike `K(u) (-∂ₜu / 2)`, so the fixed-point map commutes with it.
  The cutoff `χ` and the Cauchy transform (`TauCeti.cauchyTransform_comp_mul_left`) are rotation
  invariant too, so `z ↦ c⁻¹ h(c z)` is the source of the disc with first jet `c ξ`, and by
  uniqueness of the source the discs satisfy `u_{c ξ}(w) = u_ξ(c w)`.

A `C²` structure has the smallness properties after rescaling `x ↦ J(λ x)` with small `λ`, which
gives the local theorem for every `ξ`
(`TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`) and, through the Beltrami
form, a rotation-equivariant family of discs through `0` in every direction with a common radius
(`TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq`).
This equivariance is the `U(1)` normal-frame equivariance of the normal disc families used to
foliate a neighbourhood of a pseudoholomorphic curve in the large-parameter analysis of the
Seiberg–Witten equations.

The contraction adapts the small-coefficient Beltrami fixed point
`TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`
(`TauCeti/Analysis/Complex/Beltrami/Holder.lean`) to a nonlinear coefficient, and shares its
Cauchy transform regularity lemmas
`TauCeti.contDiff_cauchyTransform_of_mem_supportedHolderSubmodule` and
`TauCeti.conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule`. The Lipschitz bound
for `h ↦ K(u)` is the second-difference estimate
`Convex.norm_image_sub_sub_sub_le_of_norm_fderiv_le`.

## Main results

* `TauCeti.exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero`: for structures whose
  derivative and its Lipschitz constant are small on the ball of radius `4`, a solution on
  `|w| < 1/2` with `u(0) = 0`, `∂ₛu(0) = ξ` for each `‖ξ‖ ≤ 1`, which is `C¹` on `|w| < 2` and has
  values of norm at most `2` on the unit disc.
* `TauCeti.exists_pos_forall_exists_conjWirtingerDeriv_eq_apply_wirtingerDeriv_and_apply_smul_eq`:
  the same for the Beltrami equation `\bar∂u = Q(u) ∂u` with a small conjugate-linear
  coefficient, as a family `u_ξ` with `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`.
* `TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`: for a structure of class
  `C²` near `0`, a solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`, for every `ξ`.
* `TauCeti.exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq`: for
  an almost complex structure of class `C²` near `0`, a family of such discs `u_ξ`, `‖ξ‖ ≤ 1`, on a
  common disc, with `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`.

## References

* A. Nijenhuis and W. B. Woolf, *Some integration problems in almost-complex and complex
  manifolds*, Ann. of Math. (2) 77 (1963), 424–489.
* J.-C. Sikorav, *Some properties of holomorphic curves in almost complex manifolds*, in
  *Holomorphic curves in symplectic geometry*, Progr. Math. 117, Birkhäuser, 1994, 165–189.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Complex Metric Set Function
open scoped NNReal BoundedContinuousFunction Topology

namespace TauCeti

/-! ### The radial cutoff -/

/-- The radial cutoff `z ↦ min 1 (max 0 (2 - 2 ‖z‖))`, written through the projection onto
`[0, 1]`. -/
private def discCutoff (z : ℂ) : ℝ :=
  (projIcc (0 : ℝ) 1 zero_le_one (2 - 2 * ‖z‖) : ℝ)

private theorem discCutoff_eq_one {z : ℂ} (hz : ‖z‖ ≤ 2⁻¹) : discCutoff z = 1 := by
  rw [discCutoff, projIcc_of_right_le _ (by linarith)]

private theorem discCutoff_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : discCutoff z = 0 := by
  rw [discCutoff, projIcc_of_le_left _ (by linarith)]

/-- The cutoff is invariant under rotations `z ↦ c z`, `|c| = 1`. -/
private theorem discCutoff_mul_left {c : ℂ} (hc : ‖c‖ = 1) (z : ℂ) :
    discCutoff (c * z) = discCutoff z := by
  simp [discCutoff, hc]

private theorem norm_discCutoff_le (z : ℂ) : ‖discCutoff z‖ ≤ 1 := by
  have h := (projIcc (0 : ℝ) 1 zero_le_one (2 - 2 * ‖z‖)).property
  rw [discCutoff, Real.norm_of_nonneg h.1]
  exact h.2

private theorem lipschitzWith_discCutoff : LipschitzWith 2 discCutoff := by
  have hg : LipschitzWith 2 fun z : ℂ ↦ 2 - 2 * ‖z‖ :=
    LipschitzWith.of_dist_le_mul fun z w ↦ by
      rw [Real.dist_eq, dist_eq_norm]
      have := abs_norm_sub_norm_le z w
      rw [show 2 - 2 * ‖z‖ - (2 - 2 * ‖w‖) = -(2 * (‖z‖ - ‖w‖)) by ring, abs_neg, abs_mul,
        abs_two]
      push_cast
      linarith
  have h := (LipschitzWith.subtypeVal _).comp ((LipschitzWith.projIcc (zero_le_one' ℝ)).comp hg)
  rw [one_mul, one_mul] at h
  exact h

variable {α : ℝ≥0}

/-- The radial cutoff as a bounded continuous function. -/
private def cutoffBCF : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup discCutoff lipschitzWith_discCutoff.continuous 1
    norm_discCutoff_le

private theorem coe_cutoffBCF : ⇑cutoffBCF = discCutoff :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

private theorem memHolder_cutoffBCF (hα1 : α ≤ 1) : MemHolder α ⇑cutoffBCF := by
  rw [coe_cutoffBCF]
  exact ⟨_, holderOnWith_univ.mp <| lipschitzWith_discCutoff.lipschitzOnWith.holderOnWith_of_norm_le
    (M := 1) (fun z _ ↦ (norm_discCutoff_le z).trans_eq NNReal.coe_one.symm) hα1⟩

/-- The radial cutoff as a Hölder function supported in the unit disc. -/
private def cutoffHolder (hα1 : α ≤ 1) :
    supportedHolderSubmodule (Y := ℝ) α (closedBall (0 : ℂ) 1) :=
  ⟨HolderSpace.ofBoundedContinuousFunction cutoffBCF (memHolder_cutoffBCF hα1),
    mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ by
      simp only [mem_closedBall, dist_zero_right, not_le] at hz
      rw [HolderSpace.ofBoundedContinuousFunction_apply, coe_cutoffBCF]
      exact discCutoff_eq_zero hz.le⟩

private theorem cutoffHolder_apply (hα1 : α ≤ 1) (z : ℂ) :
    (cutoffHolder hα1 : HolderSpace α ℂ ℝ) z = discCutoff z := by
  rw [cutoffHolder, HolderSpace.ofBoundedContinuousFunction_apply, coe_cutoffBCF]

/-! ### The normalized disc of a source -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The disc `w ↦ w ξ + T h(w) - T h(0) - w ∂ₛ(T h)(0)` with source `h`. Its centre is `0`, and
the subtracted terms are holomorphic, so its conjugate Wirtinger derivative is that of `T h`. -/
private def discMap (ξ : F) (h : ℂ → F) (w : ℂ) : F :=
  w • ξ + cauchyTransform h w - cauchyTransform h 0 - w • fderiv ℝ (cauchyTransform h) 0 1

private theorem discMap_zero (ξ : F) (h : ℂ → F) : discMap ξ h 0 = 0 := by
  simp [discMap]

private theorem hasFDerivAt_discMap (ξ : F) {h : ℂ → F} {z : ℂ}
    (hT : DifferentiableAt ℝ (cauchyTransform h) z) :
    HasFDerivAt (discMap ξ h)
      ((ContinuousLinearMap.id ℝ ℂ).smulRight ξ + fderiv ℝ (cauchyTransform h) z -
        (ContinuousLinearMap.id ℝ ℂ).smulRight (fderiv ℝ (cauchyTransform h) 0 1)) z :=
  ((((hasFDerivAt_id z).smul_const ξ).add hT.hasFDerivAt).sub_const _).sub
    ((hasFDerivAt_id z).smul_const _)

/-- The terms of the disc other than `T h` are complex linear in `w`, so the disc has the
conjugate Wirtinger derivative of `T h`. -/
private theorem conjWirtingerDeriv_discMap (ξ : F) {h : ℂ → F} {z : ℂ}
    (hT : DifferentiableAt ℝ (cauchyTransform h) z) :
    conjWirtingerDeriv (discMap ξ h) z 1 = conjWirtingerDeriv (cauchyTransform h) z 1 := by
  rw [conjWirtingerDeriv_apply, conjWirtingerDeriv_apply, (hasFDerivAt_discMap ξ hT).fderiv]
  congr 1
  simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, smul_eq_mul, mul_one, smul_add, smul_sub, smul_smul,
    I_mul_I, neg_one_smul]
  abel

private theorem norm_id_smulRight_le (a : F) :
    ‖(ContinuousLinearMap.id ℝ ℂ).smulRight a‖ ≤ ‖a‖ :=
  (ContinuousLinearMap.norm_smulRight_le _ a).trans
    (mul_le_of_le_one_left (norm_nonneg a) ContinuousLinearMap.norm_id_le)

private theorem hα₀ : (0 : ℝ≥0) < 2⁻¹ := by norm_num

private theorem hα₁ : (2⁻¹ : ℝ≥0) < 1 := by norm_num

variable (F) in
/-- The sources: `1/2`-Hölder functions supported in the unit disc. -/
private abbrev Source := supportedHolderSubmodule (Y := F) (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1)

variable [FiniteDimensional ℂ F]

variable (F) in
/-- The derivative of the Cauchy transform on the unit disc, as a bounded operator from sources
to `1/2`-Hölder fields of real-linear maps. -/
private def derivOp : Source F →L[ℝ] HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) (ℂ →L[ℝ] F) :=
  cauchyDerivativeCLM hα₀ hα₁ zero_le_one zero_le_one

/-- The centre of the unit disc. -/
private def centre : closedBall (0 : ℂ) 1 := ⟨0, mem_closedBall_self zero_le_one⟩

private theorem coe_centre : (centre : ℂ) = 0 := (rfl)

private theorem derivOp_apply (f : Source F) (z : closedBall (0 : ℂ) 1) :
    derivOp F f z = fderiv ℝ (cauchyTransform ⇑f.val) z := by
  rw [funext (cauchyTransform_apply _)]
  exact cauchyDerivativeCLM_apply hα₀ hα₁ zero_le_one zero_le_one f z

private theorem differentiableAt_cauchyTransform (f : Source F) (z : ℂ) :
    DifferentiableAt ℝ (cauchyTransform ⇑f.val) z :=
  (contDiff_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁ zero_le_one
      f.property).differentiable
    one_ne_zero z

private theorem fderiv_discMap (ξ : F) (f : Source F) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    fderiv ℝ (discMap ξ ⇑f.val) z =
      (ContinuousLinearMap.id ℝ ℂ).smulRight ξ + derivOp F f ⟨z, hz⟩ -
        (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1) := by
  rw [(hasFDerivAt_discMap ξ
      (differentiableAt_cauchyTransform f z)).fderiv,
    derivOp_apply, derivOp_apply, coe_centre]

private theorem differentiableAt_discMap (ξ : F) (f : Source F) (z : ℂ) :
    DifferentiableAt ℝ (discMap ξ ⇑f.val) z :=
  (hasFDerivAt_discMap ξ (differentiableAt_cauchyTransform f z)).differentiableAt

private theorem norm_derivOp_apply_le (f : Source F) (z : closedBall (0 : ℂ) 1) :
    ‖derivOp F f z‖ ≤ ‖derivOp F‖ * ‖f‖ :=
  ((derivOp F f).norm_apply_le _).trans ((derivOp F).le_opNorm f)

private theorem norm_derivOp_apply_one_le (f : Source F) (z : closedBall (0 : ℂ) 1) :
    ‖derivOp F f z 1‖ ≤ ‖derivOp F‖ * ‖f‖ :=
  ((derivOp F f z).le_opNorm 1).trans (by rw [norm_one, mul_one]; exact norm_derivOp_apply_le f z)

/-- On the unit disc the derivative of the disc is bounded by `‖ξ‖ + 2 ‖D‖ ‖f‖`. -/
private theorem norm_fderiv_discMap_le (ξ : F) (f : Source F) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖fderiv ℝ (discMap ξ ⇑f.val) z‖ ≤ ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ := by
  rw [fderiv_discMap ξ f hz]
  have h1 := norm_derivOp_apply_le f ⟨z, hz⟩
  have h2 := norm_derivOp_apply_one_le f centre
  calc _ ≤ ‖(ContinuousLinearMap.id ℝ ℂ).smulRight ξ‖ + ‖derivOp F f ⟨z, hz⟩‖ +
        ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by linarith [norm_id_smulRight_le ξ, norm_id_smulRight_le (derivOp F f centre 1)]

/-- On the unit disc the derivatives of the discs of two sources differ by at most
`2 ‖D‖ ‖f - g‖`. -/
private theorem norm_fderiv_discMap_sub_le (ξ : F) (f g : Source F) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖fderiv ℝ (discMap ξ ⇑f.val) z - fderiv ℝ (discMap ξ ⇑g.val) z‖ ≤
      2 * ‖derivOp F‖ * ‖f - g‖ := by
  rw [fderiv_discMap ξ f hz, fderiv_discMap ξ g hz]
  have h1 := norm_derivOp_apply_le (f - g) ⟨z, hz⟩
  have h2 := norm_derivOp_apply_one_le (f - g) centre
  have h3 : ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1) -
      (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F g centre 1)‖ ≤
        ‖derivOp F f centre 1 - derivOp F g centre 1‖ := by
    rw [← ContinuousLinearMap.coe_smulRightₗ (T := ℝ), ← map_sub]
    exact norm_id_smulRight_le _
  simp only [map_sub, HolderSpace.sub_apply, sub_apply] at h1 h2
  calc _ = ‖(derivOp F f ⟨z, hz⟩ - derivOp F g ⟨z, hz⟩) -
        ((ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1) -
          (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F g centre 1))‖ := by
        congr 1; abel
    _ ≤ _ := (norm_sub_le _ _).trans (by linarith)

/-- The disc is `(‖ξ‖ + 2 ‖D‖ ‖f‖)`-Lipschitz on the unit disc. -/
private theorem norm_discMap_sub_le (ξ : F) (f : Source F) {z w : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1) :
    ‖discMap ξ ⇑f.val z - discMap ξ ⇑f.val w‖ ≤ (‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖) * ‖z - w‖ :=
  (convex_closedBall 0 1).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ ↦ differentiableAt_discMap ξ f x)
    (fun _ hx ↦ norm_fderiv_discMap_le ξ f hx) hw hz

/-- On the unit disc the difference of the discs of two sources is `2 ‖D‖ ‖f - g‖`-Lipschitz. -/
private theorem norm_discMap_sub_discMap_sub_le (ξ : F) (f g : Source F) {z w : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1) :
    ‖(discMap ξ ⇑f.val z - discMap ξ ⇑g.val z) - (discMap ξ ⇑f.val w - discMap ξ ⇑g.val w)‖ ≤
      2 * ‖derivOp F‖ * ‖f - g‖ * ‖z - w‖ := by
  have hd : ∀ x ∈ closedBall (0 : ℂ) 1,
      DifferentiableAt ℝ (fun y ↦ discMap ξ ⇑f.val y - discMap ξ ⇑g.val y) x := fun x _ ↦
    (differentiableAt_discMap ξ f x).sub (differentiableAt_discMap ξ g x)
  refine (convex_closedBall 0 1).norm_image_sub_le_of_norm_fderiv_le hd (fun x hx ↦ ?_) hw hz
  rw [fderiv_fun_sub (differentiableAt_discMap ξ f x) (differentiableAt_discMap ξ g x)]
  exact norm_fderiv_discMap_sub_le ξ f g hx

/-! ### Estimates for the structure -/

section Structure

variable {J : F → F →L[ℝ] F} {η : ℝ}

omit [FiniteDimensional ℂ F] in
/-- A structure whose derivative is bounded by `η` on the ball of radius `4` is `η`-Lipschitz
there. -/
private theorem norm_sub_le_of_norm_fderiv_le
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) {x y : F}
    (hx : x ∈ closedBall (0 : F) 4) (hy : y ∈ closedBall (0 : F) 4) :
    ‖J x - J y‖ ≤ η * ‖x - y‖ :=
  (convex_closedBall 0 4).norm_image_sub_le_of_norm_fderiv_le hd h1 hy hx

end Structure

/-! ### The fixed-point map -/

/-- A pointwise bound `M` and a Lipschitz bound `L` on the unit disc give a `1/2`-Hölder bound
with constant `L + 2 M`. -/
private theorem holderWith_of_norm_le {E : Type*} [NormedAddCommGroup E]
    {φ : closedBall (0 : ℂ) 1 → E} {L M : ℝ} (hM : ∀ z, ‖φ z‖ ≤ M)
    (hL : ∀ z w, ‖φ z - φ w‖ ≤ L * ‖(z : ℂ) - w‖) :
    HolderWith (L.toNNReal + 2 * M.toNNReal) (2⁻¹ : ℝ≥0) φ := by
  have hLip : LipschitzWith L.toNNReal φ := LipschitzWith.of_dist_le_mul fun z w ↦ by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact (hL z w).trans (by gcongr; exact Real.le_coe_toNNReal L)
  exact holderOnWith_univ.mp (hLip.lipschitzOnWith.holderOnWith_of_norm_le
    (fun z _ ↦ (hM z).trans (Real.le_coe_toNNReal M)) hα₁.le)

/-- A `1/2`-Hölder field on the unit disc with pointwise bound `M` and Lipschitz bound `L` has
norm at most `3 M + L`. -/
private theorem norm_le_of_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) E) {L M : ℝ} (hL0 : 0 ≤ L)
    (hM0 : 0 ≤ M) (hM : ∀ z, ‖φ z‖ ≤ M) (hL : ∀ z w, ‖φ z - φ w‖ ≤ L * ‖(z : ℂ) - w‖) :
    ‖φ‖ ≤ 3 * M + L := by
  refine (HolderSpace.norm_le_of_norm_le_of_holderWith hM0 hM
    (holderWith_of_norm_le hM hL)).trans ?_
  push_cast [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ hM0]
  linarith

variable (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (K : F → F →L[ℝ] F) (ξ : F)

/-- The coefficient `z ↦ K(u(z))` along the disc `u` of a source, on the unit disc. -/
private def kFun (f : Source F) (z : closedBall (0 : ℂ) 1) : F →L[ℝ] F :=
  K (discMap ξ ⇑f.val z)

open Classical in
/-- The coefficient `kFun` as a `1/2`-Hölder field when it is one, and `0` otherwise. -/
private def kField (f : Source F) :
    HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) (F →L[ℝ] F) :=
  if h : ∃ p : ℝ≥0 × ℝ, HolderWith p.1 (2⁻¹ : ℝ≥0) (kFun K ξ f) ∧ ∀ z, ‖kFun K ξ f z‖ ≤ p.2 then
    HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup (kFun K ξ f)
        ((Classical.choose_spec h).1.continuous hα₀) _ (Classical.choose_spec h).2)
      (by
        rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact ⟨_, (Classical.choose_spec h).1⟩)
  else 0

omit [FiniteDimensional ℂ F] in
private theorem kField_apply {f : Source F} {C : ℝ≥0} {M : ℝ}
    (hH : HolderWith C (2⁻¹ : ℝ≥0) (kFun K ξ f)) (hM : ∀ z, ‖kFun K ξ f z‖ ≤ M)
    (z : closedBall (0 : ℂ) 1) : kField K ξ f z = kFun K ξ f z := by
  rw [kField, dite_eq_left_of_eq_true (eq_true ⟨(C, M), hH, hM⟩),
    HolderSpace.ofBoundedContinuousFunction_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

/-- The field `z ↦ ℓ(Du(z))` of the disc `u` of a source, on the unit disc. -/
private def wField (f : Source F) : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight ξ)) +
    HolderSpace.compLeftL ℓ (derivOp F f) -
    HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1)))

private theorem wField_apply (f : Source F) (z : closedBall (0 : ℂ) 1) :
    wField ℓ ξ f z = ℓ (fderiv ℝ (discMap ξ ⇑f.val) z) := by
  rw [fderiv_discMap ξ f z.property]
  simp [wField, HolderSpace.compLeftL_apply, HolderSpace.const_apply]

variable {ℓ} in
/-- The part `z ↦ ℓ(D(T f)(z)) - ℓ(∂ₛ(T f)(0))` of `ℓ(Du)` that depends on the source is bounded
by `2 ‖D‖ ‖f‖` when `‖ℓ‖ ≤ 1`. -/
private theorem norm_compLeftL_sub_const_le (hℓ : ‖ℓ‖ ≤ 1) (f : Source F) :
    ‖HolderSpace.compLeftL ℓ (derivOp F f) -
      HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1)))‖ ≤
        2 * ‖derivOp F‖ * ‖f‖ := by
  have h1 : ‖HolderSpace.compLeftL ℓ (derivOp F f)‖ ≤ ‖derivOp F‖ * ‖f‖ :=
    ((HolderSpace.compLeftL ℓ).le_opNorm _).trans <| by
      calc _ ≤ 1 * (‖derivOp F‖ * ‖f‖) :=
            mul_le_mul ((HolderSpace.norm_compLeftL_le ℓ).trans hℓ)
              ((derivOp F).le_opNorm f) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have h2 : ‖(HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight
      (derivOp F f centre 1))) : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F)‖ ≤
        ‖derivOp F‖ * ‖f‖ :=
    (HolderSpace.norm_const_le _).trans <| (ℓ.le_opNorm _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) hℓ).trans <|
        (norm_id_smulRight_le _).trans (norm_derivOp_apply_one_le f centre)
  exact (norm_sub_le _ _).trans (by linarith)

variable {ℓ} in
private theorem norm_wField_le (hℓ : ‖ℓ‖ ≤ 1) (f : Source F) :
    ‖wField ℓ ξ f‖ ≤ ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ := by
  have h1 : ‖(HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight ξ)) :
      HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F)‖ ≤ ‖ξ‖ :=
    (HolderSpace.norm_const_le _).trans <| (ℓ.le_opNorm _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) hℓ).trans (norm_id_smulRight_le ξ)
  rw [wField, add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add h1 (norm_compLeftL_sub_const_le hℓ f))

variable {ℓ} in
private theorem norm_wField_sub_le (hℓ : ‖ℓ‖ ≤ 1) (f g : Source F) :
    ‖wField ℓ ξ f - wField ℓ ξ g‖ ≤ 2 * ‖derivOp F‖ * ‖f - g‖ := by
  have heq : wField ℓ ξ f - wField ℓ ξ g =
      HolderSpace.compLeftL ℓ (derivOp F (f - g)) -
        HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight
          (derivOp F (f - g) centre 1))) :=
    HolderSpace.ext fun z ↦ by
      simp only [wField, map_sub, HolderSpace.sub_apply, HolderSpace.add_apply,
        HolderSpace.compLeftL_apply, HolderSpace.const_apply, sub_apply,
        ← ContinuousLinearMap.coe_smulRightₗ (T := ℝ)]
      abel
  rw [heq]
  exact norm_compLeftL_sub_const_le hℓ (f - g)

/-- The right side `z ↦ K(u(z)) ℓ(Du(z))` of the equation `\bar∂u = K(u) ℓ(Du)`. -/
private def gField (f : Source F) : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ (kField K ξ f) (wField ℓ ξ f)

variable (F) in
/-- The bilinear map `(v, t) ↦ t v`. -/
private def smulPair : F →L[ℝ] ℝ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

omit [FiniteDimensional ℂ F] in
private theorem norm_smulPair_le : ‖smulPair F‖ ≤ 1 := by
  rw [smulPair, ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

/-- The fixed-point map `f ↦ χ · K(u) ℓ(Du)` on sources, with the radial cutoff `χ`. -/
private def fixedPointMap (f : Source F) : Source F :=
  (smulPair F).compHolder₂ExtendByZero (cutoffHolder hα₁.le) (gField ℓ K ξ f)

private theorem fixedPointMap_apply (f : Source F) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (fixedPointMap ℓ K ξ f).val z = discCutoff z • gField ℓ K ξ f ⟨z, hz⟩ := by
  rw [fixedPointMap, ContinuousLinearMap.compHolder₂ExtendByZero_apply_of_mem _ _ _ hz,
    cutoffHolder_apply, smulPair, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]

omit [FiniteDimensional ℂ F] in
/-- Multiplication by the cutoff, as an operator from fields on the unit disc to sources, has norm
at most `‖χ‖`. -/
private theorem norm_cutoffMul_le :
    ‖(smulPair F).compHolder₂ExtendByZero (cutoffHolder (α := 2⁻¹) hα₁.le)‖ ≤
      ‖cutoffHolder (α := 2⁻¹) hα₁.le‖ :=
  (ContinuousLinearMap.norm_compHolder₂ExtendByZero_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_smulPair_le)

private theorem norm_fixedPointMap_sub_le (f g : Source F) :
    ‖fixedPointMap ℓ K ξ f - fixedPointMap ℓ K ξ g‖ ≤
      ‖cutoffHolder (α := 2⁻¹) hα₁.le‖ * ‖gField ℓ K ξ f - gField ℓ K ξ g‖ := by
  rw [fixedPointMap, fixedPointMap, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

private theorem norm_fixedPointMap_le (f : Source F) :
    ‖fixedPointMap ℓ K ξ f‖ ≤ ‖cutoffHolder (α := 2⁻¹) hα₁.le‖ * ‖gField ℓ K ξ f‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

/-! ### Estimates on the ball of small sources -/

section Estimates

variable {ℓ K ξ} {η : ℝ}

/-- A small source gives a disc of norm at most `2` on the unit disc. -/
private theorem norm_discMap_le (hξ : ‖ξ‖ ≤ 1) {f : Source F} (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : ‖discMap ξ ⇑f.val z‖ ≤ 2 := by
  have h := norm_discMap_sub_le ξ f hz centre.property
  rw [coe_centre, discMap_zero, sub_zero,
    sub_zero] at h
  rw [mem_closedBall, dist_zero_right] at hz
  exact h.trans (by nlinarith [norm_nonneg z])

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
private theorem mem_closedBall_four {x : F} (hx : ‖x‖ ≤ 2) : x ∈ closedBall (0 : F) 4 := by
  rw [mem_closedBall, dist_zero_right]
  linarith

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
private theorem add_mem_closedBall_four {x y : F} (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) :
    x + y ∈ closedBall (0 : F) 4 := by
  rw [mem_closedBall, dist_zero_right]
  linarith [norm_add_le x y]

omit [FiniteDimensional ℂ F] in
private theorem nonneg_of_norm_fderiv_le
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) : 0 ≤ η :=
  (norm_nonneg (fderiv ℝ K 0)).trans (h1 0 (mem_closedBall_self (by norm_num)))

/-- For a small source the coefficient `K(u)` is bounded by `2 η` and `2 η`-Lipschitz on the
unit disc. -/
private theorem kFun_bounds (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) :
    (∀ z, ‖kFun K ξ f z‖ ≤ 2 * η) ∧
      ∀ z w, ‖kFun K ξ f z - kFun K ξ f w‖ ≤ 2 * η * ‖(z : ℂ) - w‖ := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hu : ∀ z : closedBall (0 : ℂ) 1, discMap ξ ⇑f.val z ∈ closedBall (0 : F) 4 := fun z ↦
    mem_closedBall_four (norm_discMap_le hξ hf z.property)
  refine ⟨fun z ↦ ?_, fun z w ↦ ?_⟩
  · have h := norm_sub_le_of_norm_fderiv_le hd h1 (hu z) (mem_closedBall_self (by norm_num))
    rw [sub_zero, hK0, sub_zero] at h
    exact h.trans (by nlinarith [norm_discMap_le hξ hf z.property])
  · refine (norm_sub_le_of_norm_fderiv_le hd h1 (hu z) (hu w)).trans ?_
    have h := norm_discMap_sub_le ξ f z.property w.property
    have hL : ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ ≤ 2 := by linarith
    calc _ ≤ η * ((‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖) * ‖(z : ℂ) - w‖) := by gcongr
      _ ≤ η * (2 * ‖(z : ℂ) - w‖) := by gcongr
      _ = _ := by ring

private theorem kField_eq (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (z : closedBall (0 : ℂ) 1) :
    kField K ξ f z = kFun K ξ f z :=
  kField_apply K ξ (holderWith_of_norm_le (kFun_bounds hξ hK0 hd h1 hf).1
    (kFun_bounds hξ hK0 hd h1 hf).2) (kFun_bounds hξ hK0 hd h1 hf).1 z

private theorem norm_kField_le (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖kField K ξ f‖ ≤ 8 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  obtain ⟨hM, hL⟩ := kFun_bounds hξ hK0 hd h1 hf
  refine (norm_le_of_lipschitz _ (L := 2 * η) (M := 2 * η) (by positivity) (by positivity)
    (fun z ↦ ?_) (fun z w ↦ ?_)).trans (le_of_eq (by ring))
  · rw [kField_eq hξ hK0 hd h1 hf]; exact hM z
  · rw [kField_eq hξ hK0 hd h1 hf, kField_eq hξ hK0 hd h1 hf]; exact hL z w

/-- For two small sources the coefficients differ by at most `12 η ‖D‖ ‖f - g‖` in Hölder
norm. -/
private theorem norm_kField_sub_le (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ K x - fderiv ℝ K y‖ ≤ η * ‖x - y‖) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) :
    ‖kField K ξ f - kField K ξ g‖ ≤ 12 * η * ‖derivOp F‖ * ‖f - g‖ := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hDd : 2 * ‖derivOp F‖ * ‖f - g‖ ≤ 2 := by
    have := mul_le_mul_of_nonneg_left (norm_sub_le f g) (norm_nonneg (derivOp F))
    nlinarith
  -- The difference of the discs vanishes at the centre and is `2 ‖D‖ ‖f - g‖`-Lipschitz.
  have hdiff : ∀ z : closedBall (0 : ℂ) 1,
      ‖discMap ξ ⇑f.val z - discMap ξ ⇑g.val z‖ ≤ 2 * ‖derivOp F‖ * ‖f - g‖ := fun z ↦ by
    have h := norm_discMap_sub_discMap_sub_le ξ f g z.property centre.property
    rw [coe_centre, discMap_zero, discMap_zero,
      sub_zero, sub_zero, sub_zero] at h
    have hz := z.property
    rw [mem_closedBall, dist_zero_right] at hz
    exact h.trans (mul_le_of_le_one_right (by positivity) hz)
  have hval : ∀ z, (kField K ξ f - kField K ξ g) z =
      K (discMap ξ ⇑f.val z) - K (discMap ξ ⇑g.val z) := fun z ↦ by
    rw [HolderSpace.sub_apply, kField_eq hξ hK0 hd h1 hf, kField_eq hξ hK0 hd h1 hg, kFun, kFun]
  refine (norm_le_of_lipschitz _ (L := 6 * η * ‖derivOp F‖ * ‖f - g‖)
    (M := 2 * η * ‖derivOp F‖ * ‖f - g‖) (by positivity)
    (by positivity) (fun z ↦ ?_) (fun z w ↦ ?_)).trans (le_of_eq (by ring))
  · rw [hval]
    refine (norm_sub_le_of_norm_fderiv_le hd h1
      (mem_closedBall_four (norm_discMap_le hξ hf z.property))
      (mem_closedBall_four (norm_discMap_le hξ hg z.property))).trans ?_
    nlinarith [hdiff z]
  · rw [hval, hval]
    -- The second difference of `K` at `a = u_g`, `b = u_f - u_g`.
    have hgz := norm_discMap_le hξ hg z.property
    have hgw := norm_discMap_le hξ hg w.property
    have h := (convex_closedBall (0 : F) 4).norm_image_sub_sub_sub_le_of_norm_fderiv_le hd h1 h2
      (mem_closedBall_four hgz) (mem_closedBall_four hgw)
      (add_mem_closedBall_four hgz ((hdiff z).trans hDd))
      (add_mem_closedBall_four hgz ((hdiff w).trans hDd))
      (add_mem_closedBall_four hgw ((hdiff w).trans hDd))
    rw [add_sub_cancel, add_sub_cancel] at h
    refine h.trans ?_
    have hb := norm_discMap_sub_discMap_sub_le ξ f g z.property w.property
    have ha := norm_discMap_sub_le ξ g z.property w.property
    have hLg : ‖ξ‖ + 2 * ‖derivOp F‖ * ‖g‖ ≤ 2 := by linarith
    calc η * ‖_‖ + η * ‖_‖ * ‖_‖
        ≤ η * (2 * ‖derivOp F‖ * ‖f - g‖ * ‖(z : ℂ) - w‖) +
          η * (2 * ‖derivOp F‖ * ‖f - g‖) * ((‖ξ‖ + 2 * ‖derivOp F‖ * ‖g‖) * ‖(z : ℂ) - w‖) := by
          gcongr
          · exact hdiff w
      _ ≤ η * (2 * ‖derivOp F‖ * ‖f - g‖ * ‖(z : ℂ) - w‖) +
          η * (2 * ‖derivOp F‖ * ‖f - g‖) * (2 * ‖(z : ℂ) - w‖) := by
          gcongr
      _ = 6 * η * ‖derivOp F‖ * ‖f - g‖ * ‖(z : ℂ) - w‖ := by ring

private theorem norm_gField_le (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖gField ℓ K ξ f‖ ≤ 16 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hk := norm_kField_le hξ hK0 hd h1 hf
  have hw : ‖wField ℓ ξ f‖ ≤ 2 := (norm_wField_le ξ hℓ f).trans (by linarith)
  calc ‖gField ℓ K ξ f‖ ≤ ‖kField K ξ f‖ * ‖wField ℓ ξ f‖ :=
        ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _
    _ ≤ 8 * η * 2 := by gcongr
    _ = 16 * η := by ring

private theorem norm_gField_sub_le (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ K x - fderiv ℝ K y‖ ≤ η * ‖x - y‖) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) :
    ‖gField ℓ K ξ f - gField ℓ K ξ g‖ ≤ 40 * η * ‖derivOp F‖ * ‖f - g‖ := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  set C := (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂
    (X := closedBall (0 : ℂ) 1) (α := 2⁻¹) (F := F)
  have heq : gField ℓ K ξ f - gField ℓ K ξ g =
      C (kField K ξ f) (wField ℓ ξ f - wField ℓ ξ g) +
        C (kField K ξ f - kField K ξ g) (wField ℓ ξ g) := by
    rw [gField, gField, map_sub, map_sub, sub_apply]
    abel
  have hk := norm_kField_le hξ hK0 hd h1 hf
  have hkd := norm_kField_sub_le hξ hK0 hd h1 h2 hf hg
  have hwd := norm_wField_sub_le ξ hℓ f g
  have hw : ‖wField ℓ ξ g‖ ≤ 2 := (norm_wField_le ξ hℓ g).trans (by linarith)
  rw [heq]
  calc ‖_‖ ≤ ‖kField K ξ f‖ * ‖wField ℓ ξ f - wField ℓ ξ g‖ +
        ‖kField K ξ f - kField K ξ g‖ * ‖wField ℓ ξ g‖ :=
        (norm_add_le _ _).trans (add_le_add
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _)
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _))
    _ ≤ 8 * η * (2 * ‖derivOp F‖ * ‖f - g‖) +
        12 * η * ‖derivOp F‖ * ‖f - g‖ * 2 := by gcongr
    _ = 40 * η * ‖derivOp F‖ * ‖f - g‖ := by ring

end Estimates

/-! ### The contraction and its unique fixed point -/

variable (F) in
/-- The smallness of the coefficient under which the fixed-point map contracts. -/
private def smallness : ℝ :=
  (640 * (‖cutoffHolder (α := 2⁻¹) hα₁.le‖ + 1) * (‖derivOp F‖ + 1))⁻¹

variable (F) in
/-- The radius of the ball of sources on which the fixed-point map contracts. -/
private def radius : ℝ := (4 * (‖derivOp F‖ + 1))⁻¹

private theorem smallness_pos : 0 < smallness F := by
  unfold smallness
  positivity

private theorem radius_pos : 0 < radius F := by
  unfold radius
  positivity

variable (F) in
/-- A coefficient `K` vanishing at `0` whose derivative is bounded by `smallness F` and is
`smallness F`-Lipschitz on the ball of radius `4`. -/
private def SmallCoeff (K : F → F →L[ℝ] F) : Prop :=
  K 0 = 0 ∧ (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x) ∧
    (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ smallness F) ∧
    ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ K x - fderiv ℝ K y‖ ≤ smallness F * ‖x - y‖

private theorem small_of_mem_closedBall {f : Source F}
    (hf : f ∈ closedBall (0 : Source F) (radius F)) : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1 := by
  have hD : 0 ≤ ‖derivOp F‖ := (derivOp F).opNorm_nonneg
  rw [mem_closedBall, dist_zero_right] at hf
  calc 2 * ‖derivOp F‖ * ‖f‖ ≤ 2 * ‖derivOp F‖ * radius F := by gcongr
    _ ≤ 1 := by
      rw [show 2 * ‖derivOp F‖ * radius F = ‖derivOp F‖ / (2 * (‖derivOp F‖ + 1)) by
          rw [radius]; field_simp; ring,
        div_le_one (by positivity)]
      linarith

section Contraction

variable {ℓ K ξ}

/-- On the unit disc, the fixed-point map of a small source is `χ · K(u) ℓ(Du)`. -/
private theorem fixedPointMap_apply_of_small (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (fixedPointMap ℓ K ξ f).val z =
      discCutoff z • K (discMap ξ ⇑f.val z) (ℓ (fderiv ℝ (discMap ξ ⇑f.val) z)) := by
  rw [fixedPointMap_apply ℓ K ξ f hz, gField, ContinuousLinearMap.compHolder₂_apply,
    ContinuousLinearMap.id_apply, kField_eq hξ hK.1 hK.2.1 hK.2.2.1 hf, wField_apply, kFun]

/-- The fixed-point map sends the ball of radius `radius F` into itself, since
`‖χ‖ · 16 η ≤ radius F`. -/
private theorem mapsTo_fixedPointMap (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    MapsTo (fixedPointMap ℓ K ξ) (closedBall 0 (radius F)) (closedBall 0 (radius F)) := by
  obtain ⟨hK0, hd, h1, -⟩ := hK
  set X := ‖cutoffHolder (α := 2⁻¹) hα₁.le‖
  set D := ‖derivOp F‖
  have hX : 0 ≤ X := norm_nonneg _
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  intro f hf
  rw [mem_closedBall, dist_zero_right]
  calc ‖fixedPointMap ℓ K ξ f‖ ≤ X * ‖gField ℓ K ξ f‖ := norm_fixedPointMap_le ℓ K ξ f
    _ ≤ X * (16 * smallness F) := by
      gcongr; exact norm_gField_le hℓ hξ hK0 hd h1 (small_of_mem_closedBall hf)
    _ ≤ radius F := by
      rw [show X * (16 * smallness F) = X / (40 * (X + 1) * (D + 1)) by
          rw [smallness]; field_simp; ring,
        div_le_iff₀ (by positivity),
        show radius F * (40 * (X + 1) * (D + 1)) = 10 * (X + 1) by rw [radius]; field_simp; ring]
      linarith

/-- On the ball of radius `radius F` the fixed-point map is a contraction with constant `1 / 2`,
since `‖χ‖ · 40 η ‖D‖ ≤ 1 / 2`. -/
private theorem norm_fixedPointMap_sub_le_half (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1)
    (hK : SmallCoeff F K) {f g : Source F} (hf : f ∈ closedBall 0 (radius F))
    (hg : g ∈ closedBall 0 (radius F)) :
    ‖fixedPointMap ℓ K ξ f - fixedPointMap ℓ K ξ g‖ ≤ 2⁻¹ * ‖f - g‖ := by
  obtain ⟨hK0, hd, h1, h2⟩ := hK
  set X := ‖cutoffHolder (α := 2⁻¹) hα₁.le‖
  set D := ‖derivOp F‖
  have hX : 0 ≤ X := norm_nonneg _
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  calc ‖fixedPointMap ℓ K ξ f - fixedPointMap ℓ K ξ g‖
      ≤ X * ‖gField ℓ K ξ f - gField ℓ K ξ g‖ := norm_fixedPointMap_sub_le ℓ K ξ f g
    _ ≤ X * (40 * smallness F * D * ‖f - g‖) := by
      gcongr
      exact norm_gField_sub_le hℓ hξ hK0 hd h1 h2 (small_of_mem_closedBall hf)
        (small_of_mem_closedBall hg)
    _ ≤ 2⁻¹ * ‖f - g‖ := by
      rw [show X * (40 * smallness F * D * ‖f - g‖) =
        (X * D / (16 * (X + 1) * (D + 1))) * ‖f - g‖ by rw [smallness]; field_simp; ring]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hX hD]

/-- The fixed-point map has a fixed point in the ball of radius `radius F`. -/
private theorem exists_fixedPointMap_eq (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    ∃ f ∈ closedBall (0 : Source F) (radius F), fixedPointMap ℓ K ξ f = f := by
  have hmaps := mapsTo_fixedPointMap hℓ hξ hK
  have hcontr : ContractingWith 2⁻¹ (hmaps.restrict _ _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun f g ↦ ?_⟩
    rw [Subtype.dist_eq (hmaps.restrict _ _ _ f) (hmaps.restrict _ _ _ g), Subtype.dist_eq f g,
      MapsTo.val_restrict_apply, MapsTo.val_restrict_apply, dist_eq_norm, dist_eq_norm]
    exact (norm_fixedPointMap_sub_le_half hℓ hξ hK f.property g.property).trans_eq
      (by push_cast; rfl)
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨f, hf, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hcontr (mem_closedBall_self radius_pos.le) (edist_ne_top _ _)
  exact ⟨f, hf, hfix⟩

/-- **Uniqueness of the source.** The fixed-point map has at most one fixed point in the ball of
radius `radius F`. -/
private theorem eq_of_fixedPointMap_eq (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K)
    {f g : Source F} (hf : f ∈ closedBall 0 (radius F)) (hg : g ∈ closedBall 0 (radius F))
    (hff : fixedPointMap ℓ K ξ f = f) (hgg : fixedPointMap ℓ K ξ g = g) : f = g := by
  have h := norm_fixedPointMap_sub_le_half hℓ hξ hK hf hg
  rw [hff, hgg] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (f - g)]))

end Contraction

open Classical in
/-- The source of the disc: the fixed point of `fixedPointMap` in the ball of radius
`radius F`, unique when the coefficient is small, and `0` if there is none. -/
private def discSource : Source F :=
  if h : ∃ f ∈ closedBall (0 : Source F) (radius F), fixedPointMap ℓ K ξ f = f then h.choose
  else 0

section Source

variable {ℓ K ξ}

private theorem discSource_spec (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    discSource ℓ K ξ ∈ closedBall (0 : Source F) (radius F) ∧
      fixedPointMap ℓ K ξ (discSource ℓ K ξ) = discSource ℓ K ξ := by
  unfold discSource
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_fixedPointMap_eq hℓ hξ hK) h

private theorem discSource_eq (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K)
    {f : Source F} (hf : f ∈ closedBall 0 (radius F)) (hff : fixedPointMap ℓ K ξ f = f) :
    discSource ℓ K ξ = f :=
  eq_of_fixedPointMap_eq hℓ hξ hK (discSource_spec hℓ hξ hK).1 hf (discSource_spec hℓ hξ hK).2
    hff

/-- The disc of the fixed source: it is `C¹` on the disc of radius `2`, has centre `0`, first jet
`ξ` and values of norm at most `2` on the unit disc, and on the disc of radius `1/2` it solves
`\bar∂u = K(u) ℓ(Du)`, where `\bar∂u = \bar∂ (T f)` because the other terms of `u` are
holomorphic. -/
private theorem discSource_props (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    ContDiffOn ℝ 1 (discMap ξ ⇑(discSource ℓ K ξ).val) (ball 0 2) ∧
      discMap ξ ⇑(discSource ℓ K ξ).val 0 = 0 ∧
      fderiv ℝ (discMap ξ ⇑(discSource ℓ K ξ).val) 0 1 = ξ ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ‖discMap ξ ⇑(discSource ℓ K ξ).val z‖ ≤ 2) ∧
      ∀ z ∈ ball (0 : ℂ) 2⁻¹, conjWirtingerDeriv (cauchyTransform ⇑(discSource ℓ K ξ).val) z 1 =
        K (discMap ξ ⇑(discSource ℓ K ξ).val z)
          (ℓ (fderiv ℝ (discMap ξ ⇑(discSource ℓ K ξ).val) z)) := by
  obtain ⟨hmem, hfix⟩ := discSource_spec hℓ hξ hK
  set f := discSource ℓ K ξ
  have hf := small_of_mem_closedBall hmem
  have hTC := (contDiff_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁ zero_le_one
    f.property).contDiffOn (s := ball 0 2)
  refine ⟨?_, discMap_zero ξ _, ?_, fun z hz ↦ norm_discMap_le hξ hf hz, fun z hz ↦ ?_⟩
  · exact (((contDiffOn_id.smul contDiffOn_const).add hTC).sub contDiffOn_const).sub
      (contDiffOn_id.smul contDiffOn_const)
  · rw [← coe_centre, fderiv_discMap ξ f centre.property]
    simp
  · have hz1 : z ∈ closedBall (0 : ℂ) 1 := closedBall_subset_closedBall (by norm_num)
      (ball_subset_closedBall hz)
    have hzn : ‖z‖ ≤ 2⁻¹ := by
      rw [mem_ball, dist_zero_right] at hz
      exact hz.le
    -- At the fixed point, `\bar∂ T f = f = χ · K(u) ℓ(Du)`, and `χ(z) = 1`.
    rw [conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁ zero_le_one
        f.property]
    conv_lhs => rw [← hfix]
    rw [fixedPointMap_apply_of_small hξ hK hf hz1, discCutoff_eq_one hzn, one_smul]

/-- The fixed source vanishes at the centre, since `K(u(0)) = K(0) = 0`. -/
private theorem discSource_apply_zero (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    (discSource ℓ K ξ).val 0 = 0 := by
  obtain ⟨hmem, hfix⟩ := discSource_spec hℓ hξ hK
  rw [← hfix, fixedPointMap_apply_of_small hξ hK (small_of_mem_closedBall hmem)
    (mem_closedBall_self zero_le_one)]
  simp [discMap_zero, hK.1]

end Source

/-! ### Discs solving `∂ₛu + J(u) ∂ₜu = 0` -/

omit [FiniteDimensional ℂ F] in
/-- The operator `L ↦ -L(i) / 2`, minus half the derivative `∂ₜ`, has norm at most `1`. -/
private theorem norm_neg_half_smul_apply_I_le :
    ‖(-(2 : ℝ)⁻¹) • ContinuousLinearMap.apply ℝ F I‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    rw [smul_apply, ContinuousLinearMap.apply_apply, norm_smul, one_mul]
    have h := L.le_opNorm I
    rw [norm_I, mul_one] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans h

omit [FiniteDimensional ℂ F] in
/-- The equation at a point: if `\bar∂ T h(z) = -(J(u(z)) - J(0)) ∂ₜu(z) / 2` and `J(0) = i`,
then the disc `u` of the source `h` solves `∂ₛu + J(u) ∂ₜu = 0` at `z`. -/
private theorem fderiv_discMap_add_eq_zero (J : F → F →L[ℝ] F) {ξ : F} {h : ℂ → F} {z : ℂ}
    (hJ0 : ∀ v, J 0 v = I • v) (hT : DifferentiableAt ℝ (cauchyTransform h) z)
    (hbar : conjWirtingerDeriv (cauchyTransform h) z 1 =
      (-(2 : ℝ)⁻¹) • (J (discMap ξ h z) - J 0) (fderiv ℝ (discMap ξ h) z I)) :
    fderiv ℝ (discMap ξ h) z 1 + J (discMap ξ h z) (fderiv ℝ (discMap ξ h) z I) = 0 := by
  rw [conjWirtingerDeriv_apply, (hasFDerivAt_discMap ξ hT).fderiv] at hbar
  rw [(hasFDerivAt_discMap ξ hT).fderiv]
  set A := fderiv ℝ (cauchyTransform h) z
  set a := fderiv ℝ (cauchyTransform h) 0 1
  set K := J (discMap ξ h z)
  simp only [add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, smul_eq_mul, mul_one, hJ0] at hbar ⊢
  set w := I • ξ + A I - I • a
  -- Multiplying the equation for `\bar∂ T h(z)` by `-2` gives `K w - i w = -(A 1 + i A i)`,
  -- since `(-2) (-1/2) = 1` and `(-2) (1/2) = -1`.
  have hY : K w - I • w = -(A 1 + I • A I) :=
    calc K w - I • w = (-2 : ℂ) • ((-(2 : ℝ)⁻¹) • (K w - I • w)) := by
          rw [← Complex.coe_smul, smul_smul,
            show (-2 : ℂ) * ((-(2 : ℝ)⁻¹ : ℝ) : ℂ) = 1 by push_cast; norm_num, one_smul]
      _ = (-2 : ℂ) • ((2 : ℂ)⁻¹ • (A 1 + I • A I)) := by rw [hbar]
      _ = -(A 1 + I • A I) := by
          rw [smul_smul, show (-2 : ℂ) * 2⁻¹ = -1 by norm_num, neg_one_smul]
  have hII : ∀ v : F, I • I • v = -v := fun v ↦ by rw [smul_smul, I_mul_I, neg_one_smul]
  rw [show K w = -(A 1 + I • A I) + I • w by rw [← hY]; abel]
  simp only [w, smul_add, smul_sub, hII]
  abel

/-- **Discs solving `∂ₛu + J(u) ∂ₜu = 0` for a nearly constant structure.** There is `η > 0`,
depending only on `F`, with the following property. Let `J : F → (F →L[ℝ] F)` satisfy
`J(0) v = i v`, and on the closed ball of radius `4` let `J` be differentiable with `‖DJ‖ ≤ η` and
with `DJ` `η`-Lipschitz. Then for every `ξ` with `‖ξ‖ ≤ 1` there is a map `u : ℂ → F`, `C¹` on
the disc of radius `2`, with `u(0) = 0`, `∂ₛu(0) = ξ` and values of norm at most `2` on the unit
disc, which solves `∂ₛu + J(u) ∂ₜu = 0` on the disc of radius `1/2`. -/
theorem exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero :
    ∃ η > 0, ∀ (J : F → F →L[ℝ] F) (ξ : F), ‖ξ‖ ≤ 1 → (∀ v, J 0 v = I • v) →
      (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x) →
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) →
      (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ η * ‖x - y‖) →
      ∃ u : ℂ → F, ContDiffOn ℝ 1 u (ball 0 2) ∧ u 0 = 0 ∧ fderiv ℝ u 0 1 = ξ ∧
        (∀ z ∈ closedBall (0 : ℂ) 1, ‖u z‖ ≤ 2) ∧
        ∀ z ∈ ball (0 : ℂ) 2⁻¹, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0 := by
  refine ⟨smallness F, smallness_pos, fun J ξ hξ hJ0 hd h1 h2 ↦ ?_⟩
  -- The equation reads `\bar∂u = K(u) ℓ(Du)` with `K = J - J(0)` and `ℓ(L) = -L(i) / 2`.
  have hfd : ∀ x ∈ closedBall (0 : F) 4, fderiv ℝ (fun x ↦ J x - J 0) x = fderiv ℝ J x :=
    fun x _ ↦ fderiv_sub_const _
  have hK : SmallCoeff F fun x ↦ J x - J 0 :=
    ⟨sub_self _, fun x hx ↦ (hd x hx).sub_const _, fun x hx ↦ (hfd x hx).symm ▸ h1 x hx,
      fun x hx y hy ↦ (hfd x hx).symm ▸ (hfd y hy).symm ▸ h2 x hx y hy⟩
  obtain ⟨hC, h0, h1', hb, heq⟩ := discSource_props norm_neg_half_smul_apply_I_le hξ hK
  refine ⟨_, hC, h0, h1', hb, fun z hz ↦ fderiv_discMap_add_eq_zero J hJ0
    (differentiableAt_cauchyTransform _ z) ?_⟩
  rw [heq z hz, smul_apply, ContinuousLinearMap.apply_apply, map_smul]

/-! ### Discs solving the Beltrami equation `\bar∂u = Q(u) ∂u` -/

variable (F) in
/-- The Wirtinger derivative `∂ = (∂ₛ - i ∂ₜ) / 2` at `1`, as an operator on real-linear maps
`ℂ → F`. -/
private def wirtingerAtOne : (ℂ →L[ℝ] F) →L[ℝ] F :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.apply ℝ F (1 : ℂ) - I • ContinuousLinearMap.apply ℝ F I)

omit [FiniteDimensional ℂ F] in
private theorem wirtingerAtOne_apply (L : ℂ →L[ℝ] F) :
    wirtingerAtOne F L = L.complexLinearPart 1 := by
  simp [wirtingerAtOne]

omit [FiniteDimensional ℂ F] in
private theorem norm_wirtingerAtOne_le : ‖wirtingerAtOne F‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    rw [one_mul, wirtingerAtOne_apply, ContinuousLinearMap.complexLinearPart_apply, norm_smul,
      Real.norm_of_nonneg (by norm_num), smul_eq_mul, mul_one]
    have h := norm_sub_le (L 1) (I • L I)
    rw [norm_smul, norm_I, one_mul] at h
    have h1 := L.le_opNorm 1
    have hI := L.le_opNorm I
    rw [norm_one, mul_one] at h1
    rw [norm_I, mul_one] at hI
    linarith

/-- On the unit circle `|c| = 1`, rotate a source: `z ↦ c⁻¹ h(c z)`. -/
private def rotSource {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) : Source F :=
  ⟨HolderSpace.compLeftL (ContinuousLinearMap.lsmul ℝ ℂ c⁻¹)
      (HolderSpace.compLipschitzL (fun z : ℂ ↦ c * z)
        (LipschitzWith.of_dist_le_mul fun z w ↦ by
          rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hc, NNReal.coe_one])
        f.val),
    mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ by
      have hcz : c * z ∉ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, norm_mul, hc] using hz
      simp [HolderSpace.compLeftL_apply, mem_supportedHolderSubmodule_iff.mp f.property _ hcz]⟩

omit [FiniteDimensional ℂ F] in
private theorem rotSource_apply {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) (z : ℂ) :
    (rotSource hc f).val z = c⁻¹ • f.val (c * z) := by
  simp [rotSource, HolderSpace.compLeftL_apply]

omit [FiniteDimensional ℂ F] in
private theorem norm_rotSource_le {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) :
    ‖rotSource hc f‖ ≤ ‖f‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe f]
  refine ((HolderSpace.compLeftL _).le_opNorm _).trans ?_
  refine (mul_le_mul ((HolderSpace.norm_compLeftL_le _).trans
    (ContinuousLinearMap.opNorm_lsmul_apply_le _)) (HolderSpace.norm_compLipschitzL_apply_le _ _)
    (norm_nonneg _) (norm_nonneg _)).trans ?_
  rw [norm_inv, hc, inv_one, one_mul]

omit [FiniteDimensional ℂ F] in
private theorem cauchyTransform_rotSource {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) (w : ℂ) :
    cauchyTransform ⇑(rotSource hc f).val w = cauchyTransform ⇑f.val (c * w) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have h : (⇑(rotSource hc f).val : ℂ → F) = c⁻¹ • fun z ↦ f.val (c * z) :=
    funext fun z ↦ rotSource_apply hc f z
  rw [h, cauchyTransform_smul, Pi.smul_apply, cauchyTransform_comp_mul_left hc, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

/-- Rotating the source of a disc whose source vanishes at the centre rotates the disc:
`u_{c ξ}(w) = u_ξ(c w)` for the rotated source. -/
private theorem discMap_rotSource {c : ℂ} (hc : ‖c‖ = 1) (ξ : F) {f : Source F}
    (hf0 : f.val 0 = 0) (w : ℂ) :
    discMap (c • ξ) ⇑(rotSource hc f).val w = discMap ξ ⇑f.val (c * w) := by
  have hT : cauchyTransform ⇑(rotSource hc f).val = fun w ↦ cauchyTransform ⇑f.val (c * w) :=
    funext (cauchyTransform_rotSource hc f)
  -- `\bar∂ (T f)(0) = f(0) = 0`, so `D(T f)(0)` is complex linear.
  have hlin :
      fderiv ℝ (cauchyTransform ⇑f.val) 0 c = c • fderiv ℝ (cauchyTransform ⇑f.val) 0 1 := by
    have h := conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁
      zero_le_one f.property 0
    rw [hf0] at h
    rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
      fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
    simp only [h, smul_zero, add_zero, one_smul]
  have hd := fderiv_comp_smul_apply (𝕜 := ℝ) (cauchyTransform ⇑f.val) c 0 1
  simp only [smul_eq_mul] at hd
  rw [discMap, discMap, hT, hd]
  simp only [mul_zero, mul_one, hlin, smul_smul, mul_comm w c]

variable {Q : F → F →L[ℝ] F}

/-- **Rotation equivariance of the source.** For a conjugate-linear coefficient `Q`, rotating the
source of the disc with first jet `ξ` gives the source of the disc with first jet `c ξ`. -/
private theorem discSource_smul (hξ : ‖ξ‖ ≤ 1) (hQ : SmallCoeff F Q)
    (hQI : ∀ x ∈ closedBall (0 : F) 4, ∀ v, Q x (I • v) = -(I • Q x v)) {c : ℂ} (hc : ‖c‖ = 1) :
    discSource (wirtingerAtOne F) Q (c • ξ) = rotSource hc (discSource (wirtingerAtOne F) Q ξ) := by
  have hcξ : ‖c • ξ‖ ≤ 1 := by rwa [norm_smul, hc, one_mul]
  obtain ⟨hmem, hfix⟩ := discSource_spec norm_wirtingerAtOne_le hξ hQ
  set f := discSource (wirtingerAtOne F) Q ξ
  set g := rotSource hc f
  have hgmem : g ∈ closedBall (0 : Source F) (radius F) := by
    rw [mem_closedBall, dist_zero_right] at hmem ⊢
    exact (norm_rotSource_le hc f).trans hmem
  have hf := small_of_mem_closedBall hmem
  have hg := small_of_mem_closedBall hgmem
  have hrot : ∀ w, discMap (c • ξ) ⇑g.val w = discMap ξ ⇑f.val (c * w) :=
    discMap_rotSource hc ξ (discSource_apply_zero norm_wirtingerAtOne_le hξ hQ)
  refine discSource_eq norm_wirtingerAtOne_le hcξ hQ hgmem
    (Subtype.ext (HolderSpace.ext fun z ↦ ?_))
  by_cases hz : z ∈ closedBall (0 : ℂ) 1
  · have hcz : c * z ∈ closedBall (0 : ℂ) 1 := by
      simpa [mem_closedBall, norm_mul, hc] using hz
    rw [fixedPointMap_apply_of_small hcξ hQ hg hz, rotSource_apply, ← hfix,
      fixedPointMap_apply_of_small hξ hQ hf hcz]
    have hconj := (Q (discMap ξ (⇑f.val) (c * z)) : F →ₗ[ℝ] F).map_smul_eq_conj_smul_of_map_I_smul
      (hQI _ (mem_closedBall_four (norm_discMap_le hξ hf hcz)))
    simp only [ContinuousLinearMap.coe_coe] at hconj
    -- The rotated disc is the disc precomposed with `w ↦ c w`, so its `∂` is multiplied by `c`.
    rw [hrot, show discMap (c • ξ) ⇑g.val = fun w ↦ discMap ξ ⇑f.val (c * w) from funext hrot,
      wirtingerAtOne_apply, wirtingerAtOne_apply, ← wirtingerDeriv_eq_complexLinearPart,
      ← wirtingerDeriv_eq_complexLinearPart,
      wirtingerDeriv_comp_mul_left,
      ← discCutoff_mul_left hc z, hconj,
      ← Complex.inv_eq_conj hc, smul_comm]
  · rw [mem_supportedHolderSubmodule_iff.mp (fixedPointMap _ _ _ g).property z hz,
      mem_supportedHolderSubmodule_iff.mp g.property z hz]

/-- **Rotation-equivariant discs solving `\bar∂u = Q(u) ∂u` for a small coefficient.** There is
`η > 0`, depending only on `F`, with the following property. Let `Q : F → (F →L[ℝ] F)` vanish at
`0` and, on the closed ball of radius `4`, be differentiable with `‖DQ‖ ≤ η` and `η`-Lipschitz
derivative. Then there is a family of maps `u_ξ : ℂ → F`, for `‖ξ‖ ≤ 1`, each `C¹` on the disc of
radius `2` with `u_ξ(0) = 0`, `∂ₛu_ξ(0) = ξ` and values of norm at most `2` on the unit disc,
solving the Beltrami equation `\bar∂u_ξ = Q(u_ξ) ∂u_ξ` on the disc of radius `1/2`. If moreover
`Q` takes conjugate-linear values on that ball, `Q(x)(i v) = -i Q(x) v`, as the Beltrami
coefficient of a complex structure near `i` does, then the family is equivariant under rotations:
`u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`. -/
theorem exists_pos_forall_exists_conjWirtingerDeriv_eq_apply_wirtingerDeriv_and_apply_smul_eq :
    ∃ η > 0, ∀ Q : F → F →L[ℝ] F, Q 0 = 0 →
      (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ Q x) →
      (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ Q x‖ ≤ η) →
      (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
        ‖fderiv ℝ Q x - fderiv ℝ Q y‖ ≤ η * ‖x - y‖) →
      ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
        ContDiffOn ℝ 1 (u ξ) (ball 0 2) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        (∀ z ∈ closedBall (0 : ℂ) 1, ‖u ξ z‖ ≤ 2) ∧
        ∀ z ∈ ball (0 : ℂ) 2⁻¹,
          conjWirtingerDeriv (u ξ) z 1 = Q (u ξ z) (wirtingerDeriv (u ξ) z 1)) ∧
        ((∀ x ∈ closedBall (0 : F) 4, ∀ v, Q x (I • v) = -(I • Q x v)) →
          ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w)) := by
  refine ⟨smallness F, smallness_pos, fun Q hQ0 hd h1 h2 ↦ ?_⟩
  have hQ : SmallCoeff F Q := ⟨hQ0, hd, h1, h2⟩
  refine ⟨fun ξ ↦ discMap ξ ⇑(discSource (wirtingerAtOne F) Q ξ).val, fun ξ hξ ↦ ?_,
    fun hQI ξ hξ c hc w ↦ ?_⟩
  · obtain ⟨hC, h0, h1', hb, heq⟩ := discSource_props norm_wirtingerAtOne_le hξ hQ
    refine ⟨hC, h0, h1', hb, fun z hz ↦ ?_⟩
    beta_reduce
    rw [conjWirtingerDeriv_discMap ξ (differentiableAt_cauchyTransform _ z), heq z hz,
      wirtingerAtOne_apply, wirtingerDeriv_eq_complexLinearPart]
  · beta_reduce
    rw [discSource_smul ξ hξ hQ hQI hc]
    exact discMap_rotSource hc ξ (discSource_apply_zero norm_wirtingerAtOne_le hξ hQ) w

/-! ### Rescaling -/

omit [FiniteDimensional ℂ F] in
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

omit [FiniteDimensional ℂ F] in
/-- The derivative of the rescaled disc `z ↦ t v(z / κ)`. -/
private theorem fderiv_rescale_apply {v : ℂ → F} {z : ℂ} (t κ : ℝ)
    (hv : DifferentiableAt ℝ v (κ⁻¹ • z)) (w : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ t • v (κ⁻¹ • z)) z w = (t * κ⁻¹) • fderiv ℝ v (κ⁻¹ • z) w := by
  have h : HasFDerivAt (fun z : ℂ ↦ t • v (κ⁻¹ • z)) _ z :=
    (hv.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul κ⁻¹)).const_smul t
  rw [h.fderiv]
  simp [smul_smul]

omit [FiniteDimensional ℂ F] in
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



omit [FiniteDimensional ℂ F] in
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
theorem exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt {J : F → F →L[ℝ] F}
    (hJ : ContDiffAt ℝ 2 J 0) (hJ0 : ∀ v, J 0 v = I • v) (ξ : F) :
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

/-! ### Rotation-equivariant families of `J`-holomorphic discs -/

/-! #### The Beltrami coefficient of a structure near `i`

The Beltrami coefficient of a real endomorphism `A` of `F` is `-cayleyCoord i A`, minus its
Cayley coordinate (`TauCeti.cayleyCoord`) relative to the standard structure `i`, in the normed
ring `F →L[ℝ] F`, where it depends smoothly on `A`. For `A² = -1` it is `(A + i)⁻¹ (i - A)`
(`TauCeti.add_mul_cayleyCoord`) and conjugate linear (`TauCeti.cayleyCoord_mul_eq_neg_mul`). -/

omit [FiniteDimensional ℂ F] in
private theorem lsmul_I_mul_self :
    (ContinuousLinearMap.lsmul ℝ ℂ I : F →L[ℝ] F) * ContinuousLinearMap.lsmul ℝ ℂ I = -1 := by
  ext v
  simp [smul_smul]

omit [FiniteDimensional ℂ F] in
private theorem mul_self_eq_neg_one {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v) : A * A = -1 := by
  ext v
  simp [hAA]

omit [FiniteDimensional ℂ F] in
/-- `(A + i) Q v = (i - A) v` for the Beltrami coefficient `Q` of `A`, when `A² = -1` and `i + A`
is invertible. -/
private theorem add_apply_neg_cayleyCoord {A : F →L[ℝ] F} (hAA : ∀ v, A (A v) = -v)
    (hA : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + A)) (v : F) :
    A ((-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) v) +
        I • (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) v = I • v - A v := by
  have h := congrArg (fun T : F →L[ℝ] F ↦ T v) (add_mul_cayleyCoord
    ((mul_self_eq_neg_one hAA).trans lsmul_I_mul_self.symm) hA)
  simp only [add_mul, mul_apply_eq_comp, add_apply, sub_apply,
    ContinuousLinearMap.lsmul_apply] at h
  simp only [neg_apply, map_neg, smul_neg]
  rw [← neg_add, h, neg_sub]

omit [FiniteDimensional ℂ F] in
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

omit [FiniteDimensional ℂ F] in
/-- The Beltrami form of the Cauchy–Riemann equation for a real multiple `L = s M` of a map `M`
solving it. -/
private theorem apply_one_add_apply_apply_I_eq_zero_of_eq_smul {A : F →L[ℝ] F}
    (hAA : ∀ v, A (A v) = -v) (hA : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + A))
    {L M : ℂ →L[ℝ] F} {s : ℝ} (hLM : L = s • M)
    (hM : M.complexAntilinearPart 1 =
      (-cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A) (M.complexLinearPart 1)) :
    L 1 + A (L I) = 0 := by
  refine apply_one_add_apply_apply_I_eq_zero hAA hA ?_
  rw [hLM, ContinuousLinearMap.complexAntilinearPart_smul,
    ContinuousLinearMap.complexLinearPart_smul, smul_apply, smul_apply, hM, map_smul]

/-- For a structure `J` of class `C²` near `0` with `J(0) = i` and `J² = -1` near `0`, the Beltrami
coefficient `Q = -cayleyCoord i J` vanishes at `0`, and on a small ball it is differentiable with
Lipschitz derivative, `J² = -1` and `i + J` is invertible. -/
private theorem exists_neg_cayleyCoord_local {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0)
    (hJ0 : ∀ v, J 0 v = I • v) (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) :
    ∃ r > 0, ∃ K : ℝ≥0, -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J 0) = 0 ∧
      (∀ x ∈ closedBall (0 : F) r,
        DifferentiableAt ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) x) ∧
      (∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
        ‖fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) x -
          fderiv ℝ (fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)) y‖ ≤
            K * ‖x - y‖) ∧
      ∀ x ∈ closedBall (0 : F) r,
        (∀ v, J x (J x v) = -v) ∧ IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J x) := by
  have := FiniteDimensional.completeSpace ℂ F
  have hI0 : J 0 = ContinuousLinearMap.lsmul ℝ ℂ I := by
    ext v
    simp [hJ0]
  -- `Q` is `C²` near `0`, since `i + J(0) = 2 i` is invertible.
  have hU : IsUnit (ContinuousLinearMap.lsmul ℝ ℂ I + J 0) := by
    have h2 := (IsUnit.mk0 (2 : ℝ) two_ne_zero).map (algebraMap ℝ (F →L[ℝ] F))
    rw [map_ofNat] at h2
    rw [hI0, ← two_mul]
    exact isUnit_two_mul_of_mul_self_eq_neg_one h2 lsmul_I_mul_self
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

/-- **A rotation-equivariant family of `J`-holomorphic discs with prescribed first jets.** Let
`J : F → (F →L[ℝ] F)` be of class `C²` near `0`, with `J(0) v = i v` and `J(x)² = -1` near `0`, as
for an almost complex structure in coordinates centred at a point where it is standard. Then
there are `ε > 0` and maps `u_ξ : ℂ → F`, for `‖ξ‖ ≤ 1`, each `C¹` on the disc of radius `ε` with
`u_ξ(0) = 0` and `∂ₛu_ξ(0) = ξ`, solving `∂ₛu_ξ + J(u_ξ) ∂ₜu_ξ = 0` there, such that rotating the
first jet rotates the parameter: `u_{c ξ}(w) = u_ξ(c w)` for `|c| = 1`. So the discs through `0`
with first jets `ξ` and `c ξ` have the same image, parametrized differently by the rotation
`w ↦ c w`. -/
theorem exists_pos_exists_forall_fderiv_one_add_apply_fderiv_I_eq_zero_and_apply_smul_eq
    {J : F → F →L[ℝ] F} (hJ : ContDiffAt ℝ 2 J 0) (hJ0 : ∀ v, J 0 v = I • v)
    (hJJ : ∀ᶠ x in 𝓝 0, ∀ v, J x (J x v) = -v) :
    ∃ ε > 0, ∃ u : F → ℂ → F, (∀ ξ : F, ‖ξ‖ ≤ 1 →
      ContDiffOn ℝ 1 (u ξ) (ball 0 ε) ∧ u ξ 0 = 0 ∧ fderiv ℝ (u ξ) 0 1 = ξ ∧
        ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ (u ξ) z 1 + J (u ξ z) (fderiv ℝ (u ξ) z I) = 0) ∧
      ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u (c • ξ) w = u ξ (c * w) := by
  obtain ⟨η, hη, hdisc⟩ :=
    exists_pos_forall_exists_conjWirtingerDeriv_eq_apply_wirtingerDeriv_and_apply_smul_eq (F := F)
  obtain ⟨r, hr, K, hQ0, hd, hL, hrJ⟩ := exists_neg_cayleyCoord_local hJ hJ0 hJJ
  set Q : F → F →L[ℝ] F := fun x ↦ -cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) (J x)
  obtain ⟨t, ht, htr, hdt, hAt, hLt⟩ := exists_rescale hη hr hd hL
  have hmem : ∀ x : F, ‖x‖ ≤ 4 → t • x ∈ closedBall (0 : F) r := fun x hx ↦ by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
    nlinarith
  obtain ⟨v, hv, hveq⟩ := hdisc (fun x ↦ Q (t • x)) (by rw [smul_zero]; exact hQ0) hdt hAt hLt
  replace hveq := hveq fun x hx w ↦ by
    -- The Cayley coordinate of a square root of `-1` anticommutes with `i`.
    have h := congrArg (fun T : F →L[ℝ] F ↦ T w) (cayleyCoord_mul_eq_neg_mul lsmul_I_mul_self
      (mul_self_eq_neg_one (hrJ _ (hmem x (by simpa using hx))).1))
    simp only [mul_apply_eq_comp, neg_apply, ContinuousLinearMap.lsmul_apply] at h
    simp only [Q, neg_apply, h, smul_neg]
  have hμ : (0 : ℝ) < 2⁻¹ := by norm_num
  have hμξ : ∀ ξ : F, ‖ξ‖ ≤ 1 → ‖(2⁻¹ : ℝ) • ξ‖ ≤ 1 := fun ξ hξ ↦ by
    rw [norm_smul, Real.norm_of_nonneg hμ.le]
    linarith
  refine ⟨t * 2⁻¹ / 2, by positivity, fun ξ z ↦ t • v ((2⁻¹ : ℝ) • ξ) ((t * 2⁻¹)⁻¹ • z),
    fun ξ hξ ↦ ?_, fun ξ hξ c hc w ↦ ?_⟩
  · obtain ⟨hvC, hv0, hv1, hvb, hvbel⟩ := hv _ (hμξ ξ hξ)
    obtain ⟨huC, hu0, hu1, hu⟩ := rescale_props ht hμ hvC hv0 hv1
    refine ⟨huC, hu0, hu1, fun z hz ↦ ?_⟩
    obtain ⟨hz', hDu⟩ := hu z hz
    set y := (t * 2⁻¹)⁻¹ • z
    have hvy : ‖v ((2⁻¹ : ℝ) • ξ) y‖ ≤ 4 :=
      (hvb y (ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num)) hz')).trans
        (by norm_num)
    have hy' := hrJ _ (hmem _ hvy)
    -- The derivative of the rescaled disc is a real multiple of that of `v`.
    refine apply_one_add_apply_apply_I_eq_zero_of_eq_smul hy'.1 hy'.2
      (ContinuousLinearMap.ext hDu) ?_
    rw [← conjWirtingerDeriv_eq_complexAntilinearPart, ← wirtingerDeriv_eq_complexLinearPart]
    exact hvbel y hz'
  · simp only
    rw [smul_comm (2⁻¹ : ℝ) c ξ, hveq _ (hμξ ξ hξ) c hc, mul_smul_comm]

end TauCeti
