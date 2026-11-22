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
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Pompeiu.Holder.Operator
import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Analysis.Holder.Bilinear
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Pseudoholomorphic discs with a prescribed centre and first jet

Let `F` be a finite-dimensional complex normed space and `J : F → (F →L[ℝ] F)` a field of real
endomorphisms with `J(0) v = i v`, such as an almost complex structure written in coordinates
centred at a point where it is standard. This file solves the nonlinear Cauchy–Riemann equation

`∂ₛu + J(u) ∂ₜu = 0`

for maps `u` from a disc in `ℂ = {s + i t}` to `F`. The theorems are stated for this equation and
an arbitrary field `J`. When every `J(x)` is an almost complex structure, `J(x)² = -1`, a solution
is `J`-holomorphic for the standard structure of `ℂ` in the sense of `TauCeti.IsJHolomorphicAt`
(`TauCeti.isJHolomorphicAt_iff_fderiv_one_add_apply_fderiv_I_eq_zero`).
Through the centre `0` there is a solution in every complex direction: for every `ξ ∈ F` there is
a `C¹` solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`
(`TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`).

The proof is a contraction for the Cauchy transform `T h(w) = π⁻¹ ∫ (w - z)⁻¹ h(z) dz`
(`TauCeti.cauchyTransform`), which satisfies `\bar∂ T h = h`. Write `J(x) = i + K(x)` with
`K(0) = 0`. The equation becomes
`2 \bar∂u = -K(u) ∂ₜu`, and its solutions with the prescribed centre and first jet are sought as

`u(w) = w ξ + T h(w) - T h(0) - w · ∂ₛ(T h)(0)`,

whose centre and first jet do not depend on the source `h`, because the subtracted terms are
holomorphic. The source solves the fixed-point equation `h = χ · (-K(u) ∂ₜu / 2)` with the radial
cutoff `χ(z) = min 1 (max 0 (2 - 2|z|))`, equal to `1` on `|z| ≤ 1/2` and vanishing off the unit
disc. On the Banach space of `1/2`-Hölder sources supported in the unit disc the right side is a
contraction near `0` as soon as the first derivative of `K` and the Lipschitz constant of that
derivative are small on a fixed ball
(`TauCeti.exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero`): the Cauchy transform
gains a derivative in Hölder norm (`TauCeti.cauchyDerivativeCLM`), so `∂ₜu` is Hölder, and the
Lipschitz bounds on `K` and its derivative make `h ↦ K(u)` Lipschitz in the Hölder norm. On
`|w| < 1/2`, where `χ = 1`, the fixed point solves the equation. A `C²` structure has these
smallness properties after rescaling `x ↦ J(λ x)` with small `λ`, which gives the local theorem for
every `ξ`.

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
* `TauCeti.exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_contDiffAt`: for a structure of class
  `C²` near `0`, a solution near `0` with `u(0) = 0` and `∂ₛu(0) = ξ`, for every `ξ`.

## References

* A. Nijenhuis and W. B. Woolf, *Some integration problems in almost-complex and complex
  manifolds*, Ann. of Math. (2) 77 (1963), 424–489.
* J.-C. Sikorav, *Some properties of holomorphic curves in almost complex manifolds*, in
  *Holomorphic curves in symplectic geometry*, Progr. Math. 117, Birkhäuser, 1994, 165–189.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
-/

public section

noncomputable section

open Complex Metric Set Function
open scoped NNReal BoundedContinuousFunction

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
    have hsub : (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1) -
        (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F g centre 1) =
          (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1 - derivOp F g centre 1) := by
      ext v
      simp [smul_sub]
    rw [hsub]
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

variable (ξ : F) (J : F → F →L[ℝ] F)

/-- The coefficient `z ↦ J(u(z)) - J(0)` along the disc `u` of a source, on the unit disc. -/
private def kFun (f : Source F) (z : closedBall (0 : ℂ) 1) : F →L[ℝ] F :=
  J (discMap ξ ⇑f.val z) - J 0

open Classical in
/-- The coefficient `kFun` as a `1/2`-Hölder field when it is one, and `0` otherwise. -/
private def kField (f : Source F) :
    HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) (F →L[ℝ] F) :=
  if h : ∃ p : ℝ≥0 × ℝ, HolderWith p.1 (2⁻¹ : ℝ≥0) (kFun ξ J f) ∧ ∀ z, ‖kFun ξ J f z‖ ≤ p.2 then
    HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup (kFun ξ J f)
        ((Classical.choose_spec h).1.continuous hα₀) _ (Classical.choose_spec h).2)
      (by
        rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact ⟨_, (Classical.choose_spec h).1⟩)
  else 0

omit [FiniteDimensional ℂ F] in
private theorem kField_apply {f : Source F} {C : ℝ≥0} {M : ℝ}
    (hH : HolderWith C (2⁻¹ : ℝ≥0) (kFun ξ J f)) (hM : ∀ z, ‖kFun ξ J f z‖ ≤ M)
    (z : closedBall (0 : ℂ) 1) : kField ξ J f z = kFun ξ J f z := by
  rw [kField, dite_eq_left_of_eq_true (eq_true ⟨(C, M), hH, hM⟩),
    HolderSpace.ofBoundedContinuousFunction_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

/-- The field `z ↦ ∂ₜu(z)` of the disc `u` of a source, on the unit disc. -/
private def wField (f : Source F) : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  HolderSpace.const (I • ξ) +
    (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)).compHolder₂ (derivOp F f) (HolderSpace.const I) -
    HolderSpace.const (I • derivOp F f centre 1)

private theorem wField_apply (f : Source F) (z : closedBall (0 : ℂ) 1) :
    wField ξ f z = fderiv ℝ (discMap ξ ⇑f.val) z I := by
  rw [fderiv_discMap ξ f z.property]
  simp [wField, ContinuousLinearMap.compHolder₂_apply, HolderSpace.const_apply]

private theorem norm_const_I_le :
    ‖(HolderSpace.const I : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) ℂ)‖ ≤ 1 :=
  (HolderSpace.norm_const_le _).trans_eq norm_I

/-- The part `z ↦ D(T f)(z) i - i ∂ₛ(T f)(0)` of `∂ₜu` that depends on the source is bounded by
`2 ‖D‖ ‖f‖`. -/
private theorem norm_compHolder₂_sub_const_le (f : Source F) :
    ‖(ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)).compHolder₂ (derivOp F f) (HolderSpace.const I) -
      HolderSpace.const (I • derivOp F f centre 1)‖ ≤ 2 * ‖derivOp F‖ * ‖f‖ := by
  have h2 : ‖(ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)).compHolder₂ (derivOp F f)
      (HolderSpace.const I)‖ ≤ ‖derivOp F‖ * ‖f‖ :=
    (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _).trans <| by
      simpa using mul_le_mul ((derivOp F).le_opNorm f) norm_const_I_le (norm_nonneg _)
        (by positivity)
  have h3 : ‖(HolderSpace.const (I • derivOp F f centre 1) :
      HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F)‖ ≤ ‖derivOp F‖ * ‖f‖ :=
    (HolderSpace.norm_const_le _).trans (by
      rw [norm_smul, norm_I, one_mul]; exact norm_derivOp_apply_one_le f centre)
  exact (norm_sub_le _ _).trans (by linarith)

private theorem norm_wField_le (f : Source F) :
    ‖wField ξ f‖ ≤ ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ := by
  have h1 : ‖(HolderSpace.const (I • ξ) :
      HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F)‖ ≤ ‖ξ‖ :=
    (HolderSpace.norm_const_le _).trans_eq (by rw [norm_smul, norm_I, one_mul])
  rw [wField, add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add h1 (norm_compHolder₂_sub_const_le f))

private theorem norm_wField_sub_le (f g : Source F) :
    ‖wField ξ f - wField ξ g‖ ≤ 2 * ‖derivOp F‖ * ‖f - g‖ := by
  have heq : wField ξ f - wField ξ g =
      (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)).compHolder₂ (derivOp F (f - g))
        (HolderSpace.const I) - HolderSpace.const (I • derivOp F (f - g) centre 1) :=
    HolderSpace.ext fun z ↦ by
      simp only [wField, map_sub, HolderSpace.sub_apply, HolderSpace.add_apply,
        ContinuousLinearMap.compHolder₂_apply, HolderSpace.const_apply, sub_apply, smul_sub,
        ContinuousLinearMap.id_apply]
      abel
  rw [heq]
  exact norm_compHolder₂_sub_const_le (f - g)

/-- The right side `z ↦ -K(u(z)) ∂ₜu(z) / 2` of the equation `\bar∂u = -K(u) ∂ₜu / 2`, where
`K = J - J(0)`. -/
private def gField (f : Source F) : HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  (-(2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ (kField ξ J f) (wField ξ f)

variable (F) in
/-- The bilinear map `(v, t) ↦ t v`. -/
private def smulPair : F →L[ℝ] ℝ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

omit [FiniteDimensional ℂ F] in
private theorem norm_smulPair_le : ‖smulPair F‖ ≤ 1 := by
  rw [smulPair, ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

/-- The fixed-point map `f ↦ χ · (-K(u) ∂ₜu / 2)` on sources, with the radial cutoff `χ`. -/
private def fixedPointMap (f : Source F) : Source F :=
  (smulPair F).compHolder₂ExtendByZero (cutoffHolder hα₁.le) (gField ξ J f)

private theorem fixedPointMap_apply (f : Source F) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (fixedPointMap ξ J f).val z = discCutoff z • gField ξ J f ⟨z, hz⟩ := by
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
    ‖fixedPointMap ξ J f - fixedPointMap ξ J g‖ ≤
      ‖cutoffHolder (α := 2⁻¹) hα₁.le‖ * ‖gField ξ J f - gField ξ J g‖ := by
  rw [fixedPointMap, fixedPointMap, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

private theorem norm_fixedPointMap_le (f : Source F) :
    ‖fixedPointMap ξ J f‖ ≤ ‖cutoffHolder (α := 2⁻¹) hα₁.le‖ * ‖gField ξ J f‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

/-! ### Estimates on the ball of small sources -/

section Estimates

variable {ξ J} {η : ℝ}

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
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) : 0 ≤ η :=
  (norm_nonneg (fderiv ℝ J 0)).trans (h1 0 (mem_closedBall_self (by norm_num)))

/-- For a small source the coefficient `K(u)` is bounded by `2 η` and `2 η`-Lipschitz on the
unit disc. -/
private theorem kFun_bounds (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) :
    (∀ z, ‖kFun ξ J f z‖ ≤ 2 * η) ∧
      ∀ z w, ‖kFun ξ J f z - kFun ξ J f w‖ ≤ 2 * η * ‖(z : ℂ) - w‖ := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hu : ∀ z : closedBall (0 : ℂ) 1, discMap ξ ⇑f.val z ∈ closedBall (0 : F) 4 := fun z ↦
    mem_closedBall_four (norm_discMap_le hξ hf z.property)
  refine ⟨fun z ↦ ?_, fun z w ↦ ?_⟩
  · have h := norm_sub_le_of_norm_fderiv_le hd h1 (hu z) (mem_closedBall_self (by norm_num))
    rw [sub_zero] at h
    exact h.trans (by nlinarith [norm_discMap_le hξ hf z.property])
  · rw [kFun, kFun, sub_sub_sub_cancel_right]
    refine (norm_sub_le_of_norm_fderiv_le hd h1 (hu z) (hu w)).trans ?_
    have h := norm_discMap_sub_le ξ f z.property w.property
    have hL : ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ ≤ 2 := by linarith
    calc _ ≤ η * ((‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖) * ‖(z : ℂ) - w‖) := by gcongr
      _ ≤ η * (2 * ‖(z : ℂ) - w‖) := by gcongr
      _ = _ := by ring

private theorem kField_eq (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (z : closedBall (0 : ℂ) 1) :
    kField ξ J f z = kFun ξ J f z :=
  kField_apply ξ J (holderWith_of_norm_le (kFun_bounds hξ hd h1 hf).1
    (kFun_bounds hξ hd h1 hf).2) (kFun_bounds hξ hd h1 hf).1 z

private theorem norm_kField_le (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖kField ξ J f‖ ≤ 8 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  obtain ⟨hM, hL⟩ := kFun_bounds hξ hd h1 hf
  refine (norm_le_of_lipschitz _ (L := 2 * η) (M := 2 * η) (by positivity) (by positivity)
    (fun z ↦ ?_) (fun z w ↦ ?_)).trans (le_of_eq (by ring))
  · rw [kField_eq hξ hd h1 hf]; exact hM z
  · rw [kField_eq hξ hd h1 hf, kField_eq hξ hd h1 hf]; exact hL z w

/-- For two small sources the coefficients differ by at most `12 η ‖D‖ ‖f - g‖` in Hölder
norm. -/
private theorem norm_kField_sub_le (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ η * ‖x - y‖) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) :
    ‖kField ξ J f - kField ξ J g‖ ≤ 12 * η * ‖derivOp F‖ * ‖f - g‖ := by
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
  have hval : ∀ z, (kField ξ J f - kField ξ J g) z =
      J (discMap ξ ⇑f.val z) - J (discMap ξ ⇑g.val z) := fun z ↦ by
    rw [HolderSpace.sub_apply, kField_eq hξ hd h1 hf, kField_eq hξ hd h1 hg, kFun, kFun,
      sub_sub_sub_cancel_right]
  refine (norm_le_of_lipschitz _ (L := 6 * η * ‖derivOp F‖ * ‖f - g‖)
    (M := 2 * η * ‖derivOp F‖ * ‖f - g‖) (by positivity)
    (by positivity) (fun z ↦ ?_) (fun z w ↦ ?_)).trans (le_of_eq (by ring))
  · rw [hval]
    refine (norm_sub_le_of_norm_fderiv_le hd h1
      (mem_closedBall_four (norm_discMap_le hξ hf z.property))
      (mem_closedBall_four (norm_discMap_le hξ hg z.property))).trans ?_
    nlinarith [hdiff z]
  · rw [hval, hval]
    -- The second difference of `J` at `a = u_g`, `b = u_f - u_g`.
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

private theorem norm_gField_le (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖gField ξ J f‖ ≤ 8 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  rw [gField, norm_smul, norm_neg, norm_inv, Real.norm_two]
  have hk := norm_kField_le hξ hd h1 hf
  have hw : ‖wField ξ f‖ ≤ 2 := (norm_wField_le ξ f).trans (by linarith)
  calc 2⁻¹ * ‖_‖ ≤ 2⁻¹ * (‖kField ξ J f‖ * ‖wField ξ f‖) := by
        gcongr; exact ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _
    _ ≤ 2⁻¹ * (8 * η * 2) := by gcongr
    _ = 8 * η := by ring

private theorem norm_gField_sub_le (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ η * ‖x - y‖) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) :
    ‖gField ξ J f - gField ξ J g‖ ≤ 20 * η * ‖derivOp F‖ * ‖f - g‖ := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  set C := (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂
    (X := closedBall (0 : ℂ) 1) (α := 2⁻¹) (F := F)
  have heq : gField ξ J f - gField ξ J g = (-(2 : ℝ)⁻¹) •
      (C (kField ξ J f) (wField ξ f - wField ξ g) +
        C (kField ξ J f - kField ξ J g) (wField ξ g)) := by
    rw [gField, gField, ← smul_sub, map_sub, map_sub, sub_apply]
    congr 1
    abel
  have hk := norm_kField_le hξ hd h1 hf
  have hkd := norm_kField_sub_le hξ hd h1 h2 hf hg
  have hwd := norm_wField_sub_le ξ f g
  have hw : ‖wField ξ g‖ ≤ 2 := (norm_wField_le ξ g).trans (by linarith)
  rw [heq, norm_smul, norm_neg, norm_inv, Real.norm_two]
  calc 2⁻¹ * ‖_‖ ≤ 2⁻¹ * (‖kField ξ J f‖ * ‖wField ξ f - wField ξ g‖ +
        ‖kField ξ J f - kField ξ J g‖ * ‖wField ξ g‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _)
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _))
    _ ≤ 2⁻¹ * (8 * η * (2 * ‖derivOp F‖ * ‖f - g‖) +
        12 * η * ‖derivOp F‖ * ‖f - g‖ * 2) := by gcongr
    _ = 20 * η * ‖derivOp F‖ * ‖f - g‖ := by ring

end Estimates

/-! ### The fixed point and the disc -/

/-- A fixed point of `fixedPointMap` in the ball of small sources. -/
private theorem exists_fixedPointMap_eq (hξ : ‖ξ‖ ≤ 1)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ J x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ J x‖ ≤
      (320 * (‖cutoffHolder (α := 2⁻¹) hα₁.le‖ + 1) * (‖derivOp F‖ + 1))⁻¹)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤
        (320 * (‖cutoffHolder (α := 2⁻¹) hα₁.le‖ + 1) * (‖derivOp F‖ + 1))⁻¹ * ‖x - y‖) :
    ∃ f : Source F, 2 * ‖derivOp F‖ * ‖f‖ ≤ 1 ∧ fixedPointMap ξ J f = f := by
  set X := ‖cutoffHolder (α := 2⁻¹) hα₁.le‖
  set D := ‖derivOp F‖
  set η := (320 * (X + 1) * (D + 1))⁻¹ with hη
  set ρ := (4 * (D + 1))⁻¹ with hρdef
  have hX : 0 ≤ X := norm_nonneg _
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  have hρ : 0 ≤ ρ := by positivity
  have hsmall : ∀ f : Source F, f ∈ closedBall (0 : Source F) ρ → 2 * D * ‖f‖ ≤ 1 := by
    intro f hf
    rw [mem_closedBall, dist_zero_right] at hf
    calc 2 * D * ‖f‖ ≤ 2 * D * ρ := by gcongr
      _ ≤ 1 := by
        rw [show 2 * D * ρ = D / (2 * (D + 1)) by rw [hρdef]; field_simp; ring,
          div_le_one (by positivity)]
        linarith
  -- The map sends the ball of radius `ρ` into itself, since `‖χ‖ · 8 η ≤ ρ`.
  have hmaps : MapsTo (fixedPointMap ξ J) (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro f hf
    rw [mem_closedBall, dist_zero_right]
    calc ‖fixedPointMap ξ J f‖ ≤ X * ‖gField ξ J f‖ := norm_fixedPointMap_le ξ J f
      _ ≤ X * (8 * η) := by gcongr; exact norm_gField_le hξ hd h1 (hsmall f hf)
      _ ≤ ρ := by
        rw [show X * (8 * η) = X / (40 * (X + 1) * (D + 1)) by rw [hη]; field_simp; ring,
          div_le_iff₀ (by positivity),
          show ρ * (40 * (X + 1) * (D + 1)) = 10 * (X + 1) by rw [hρdef]; field_simp; ring]
        linarith
  -- On that ball it is a contraction with constant `1 / 2`, since `‖χ‖ · 20 η ‖D‖ ≤ 1 / 2`.
  have hcontr : ContractingWith 2⁻¹ (hmaps.restrict _ _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun f g ↦ ?_⟩
    rw [Subtype.dist_eq (hmaps.restrict _ _ _ f) (hmaps.restrict _ _ _ g), Subtype.dist_eq f g,
      MapsTo.val_restrict_apply, MapsTo.val_restrict_apply, dist_eq_norm, dist_eq_norm]
    calc ‖fixedPointMap ξ J f - fixedPointMap ξ J g‖
        ≤ X * ‖gField ξ J f - gField ξ J g‖ := norm_fixedPointMap_sub_le ξ J f g
      _ ≤ X * (20 * η * D * ‖(f : Source F) - g‖) := by
        gcongr; exact norm_gField_sub_le hξ hd h1 h2 (hsmall f f.property) (hsmall g g.property)
      _ ≤ (2⁻¹ : ℝ≥0) * ‖(f : Source F) - g‖ := by
        rw [show X * (20 * η * D * ‖(f : Source F) - g‖) =
          (X * D / (16 * (X + 1) * (D + 1))) * ‖(f : Source F) - g‖ by
            rw [hη]; field_simp; ring]
        gcongr
        rw [div_le_iff₀ (by positivity)]
        push_cast
        nlinarith [mul_nonneg hX hD]
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨f, hf, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hcontr (mem_closedBall_self hρ) (edist_ne_top _ _)
  exact ⟨f, hsmall f hf, hfix⟩

omit [FiniteDimensional ℂ F] in
/-- The equation at a point: if `\bar∂ T h(z) = -K(u(z)) ∂ₜu(z) / 2` with `K = J - J(0)` and
`J(0) = i`, then the disc `u` of the source `h` solves `∂ₛu + J(u) ∂ₜu = 0` at `z`. -/
private theorem fderiv_discMap_add_eq_zero {ξ : F} {h : ℂ → F} {z : ℂ}
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

/-! ### Solutions of the nonlinear Cauchy–Riemann equation -/

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
  refine ⟨(320 * (‖cutoffHolder (α := 2⁻¹) hα₁.le‖ + 1) * (‖derivOp F‖ + 1))⁻¹, by positivity,
    fun J ξ hξ hJ0 hd h1 h2 ↦ ?_⟩
  obtain ⟨f, hf, hfix⟩ := exists_fixedPointMap_eq ξ J hξ hd h1 h2
  have hTC := (contDiff_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁ zero_le_one
    f.property).contDiffOn (s := ball 0 2)
  refine ⟨discMap ξ ⇑f.val, ?_, discMap_zero ξ _, ?_, fun z hz ↦ norm_discMap_le hξ hf hz,
    fun z hz ↦ ?_⟩
  · exact (((contDiffOn_id.smul contDiffOn_const).add hTC).sub contDiffOn_const).sub
      (contDiffOn_id.smul contDiffOn_const)
  · rw [← coe_centre, fderiv_discMap ξ f centre.property]
    simp
  · have hz1 : z ∈ closedBall (0 : ℂ) 1 := closedBall_subset_closedBall (by norm_num)
      (ball_subset_closedBall hz)
    have hzn : ‖z‖ ≤ 2⁻¹ := by
      rw [mem_ball, dist_zero_right] at hz
      exact hz.le
    refine fderiv_discMap_add_eq_zero J hJ0 (differentiableAt_cauchyTransform f z) ?_
    -- At the fixed point, `\bar∂ T f = f = χ · (-K(u) ∂ₜu / 2)`, and `χ(z) = 1`.
    rw [conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule hα₀ hα₁ zero_le_one
        f.property]
    conv_lhs => rw [← hfix]
    rw [fixedPointMap_apply ξ J f hz1, discCutoff_eq_one hzn, one_smul,
      gField, HolderSpace.smul_apply, ContinuousLinearMap.compHolder₂_apply,
      ContinuousLinearMap.id_apply, kField_eq hξ hd h1 hf, wField_apply, kFun]

omit [FiniteDimensional ℂ F] in
/-- Rescaling the argument of a structure by `t` multiplies its derivative by `t` and the
Lipschitz constant of the derivative by `t²`: bounds `A` and `L` on the ball of radius `r ≥ 4 t`
give bounds `t A` and `t² L` for `x ↦ J (t x)` on the ball of radius `4`. -/
private theorem rescale_bounds {r A L t : ℝ} (ht : 0 < t) (htr : 4 * t ≤ r)
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
/-- A disc `v` for the rescaled structure `x ↦ J (t x)` with `∂ₛv(0) = μ ξ` gives the disc
`u(z) = t v(z / (t μ))` for `J` with `∂ₛu(0) = ξ`, on the disc of radius `t μ / 2`. -/
private theorem exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_rescale {ξ : F} {t μ : ℝ}
    (ht : 0 < t) (hμ : 0 < μ) {v : ℂ → F} (hvC : ContDiffOn ℝ 1 v (ball 0 2)) (hv0 : v 0 = 0)
    (hv1 : fderiv ℝ v 0 1 = μ • ξ)
    (hveq : ∀ z ∈ ball (0 : ℂ) 2⁻¹, fderiv ℝ v z 1 + J (t • v z) (fderiv ℝ v z I) = 0) :
    ∃ ε > 0, ∃ u : ℂ → F, ContDiffOn ℝ 1 u (ball 0 ε) ∧ u 0 = 0 ∧ fderiv ℝ u 0 1 = ξ ∧
      ∀ z ∈ ball (0 : ℂ) ε, fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z I) = 0 := by
  set κ := t * μ
  have hκ : 0 < κ := mul_pos ht hμ
  have hmaps : ∀ z ∈ ball (0 : ℂ) (κ / 2), κ⁻¹ • z ∈ ball (0 : ℂ) 2⁻¹ := fun z hz ↦ by
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hκ.le), inv_mul_lt_iff₀ hκ]
    linarith
  have hvd : ∀ z ∈ ball (0 : ℂ) (κ / 2), DifferentiableAt ℝ v (κ⁻¹ • z) := fun z hz ↦
    (hvC.contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by norm_num) (hmaps z hz)))).differentiableAt one_ne_zero
  refine ⟨κ / 2, by positivity, fun z ↦ t • v (κ⁻¹ • z), ?_, by simp [hv0], ?_, fun z hz ↦ ?_⟩
  · exact (hvC.comp (contDiffOn_id.const_smul κ⁻¹) fun z hz ↦
      ball_subset_ball (by norm_num) (hmaps z hz)).const_smul t
  · rw [fderiv_rescale_apply t κ (by simpa using hvd 0 (by simpa using hκ)), smul_zero, hv1,
      smul_smul, mul_right_comm, mul_inv_cancel₀ hκ.ne', one_smul]
  · rw [fderiv_rescale_apply t κ (hvd z hz), fderiv_rescale_apply t κ (hvd z hz), map_smul,
      ← smul_add, hveq _ (hmaps z hz), smul_zero]

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
  obtain ⟨K, t₀, ht₀, hK⟩ := (hJ.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrJ⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
    ((hJ.eventually (by simp)).and ht₀)
  have hd : ∀ x ∈ closedBall (0 : F) r, DifferentiableAt ℝ J x := fun x hx ↦
    (hrJ hx).1.differentiableAt (by norm_num)
  have hL : ∀ x ∈ closedBall (0 : F) r, ∀ y ∈ closedBall (0 : F) r,
      ‖fderiv ℝ J x - fderiv ℝ J y‖ ≤ K * ‖x - y‖ := fun x hx y hy ↦ by
    simpa [dist_eq_norm] using hK.dist_le_mul x (hrJ hx).2 y (hrJ hy).2
  have hA : ∀ x ∈ closedBall (0 : F) r, ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + K * r := fun x hx ↦ by
    have h := hL x hx 0 (mem_closedBall_self hr.le)
    rw [sub_zero] at h
    rw [mem_closedBall, dist_zero_right] at hx
    calc ‖fderiv ℝ J x‖ ≤ ‖fderiv ℝ J 0‖ + ‖fderiv ℝ J x - fderiv ℝ J 0‖ :=
          norm_le_insert' (fderiv ℝ J x) (fderiv ℝ J 0)
      _ ≤ _ := by gcongr; exact h.trans (by gcongr)
  -- Rescale `J` by `t ≤ min (r / 4) 1` small enough for the nearly constant case.
  set A := ‖fderiv ℝ J 0‖ + K * r
  have hA0 : 0 ≤ A := by positivity
  set t := min (min (r / 4) 1) (η / (A + K + 1))
  have ht : 0 < t := lt_min (lt_min (by positivity) one_pos) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have htη : t * A + t * K + t ≤ η := by
    have h : t * (A + K + 1) ≤ η := by
      rw [← le_div_iff₀ (by positivity)]
      exact min_le_right _ _
    linarith [mul_add t (A + K) 1, mul_add t A K]
  obtain ⟨hdt, hAt, hLt⟩ := rescale_bounds J ht (by
    have : t ≤ r / 4 := (min_le_left _ _).trans (min_le_left (r / 4) 1)
    linarith) hd hA hL
  have htK : 0 ≤ t * K := mul_nonneg ht.le K.coe_nonneg
  have hAη : t * A ≤ η := by linarith
  have hLη : t ^ 2 * K ≤ η := by
    have h := mul_le_mul_of_nonneg_right ht1 htK
    rw [one_mul, ← mul_assoc, ← pow_two] at h
    linarith [mul_nonneg ht.le hA0]
  set μ := (‖ξ‖ + 1)⁻¹
  have hμ : 0 < μ := by positivity
  obtain ⟨v, hvC, hv0, hv1, -, hveq⟩ := hdisc (fun x ↦ J (t • x)) (μ • ξ)
    (by
      rw [norm_smul, Real.norm_of_nonneg hμ.le, inv_mul_le_one₀ (by positivity)]
      linarith)
    (by simpa using hJ0) hdt
    (fun x hx ↦ (hAt x hx).trans hAη)
    (fun x hx y hy ↦ (hLt x hx y hy).trans (mul_le_mul_of_nonneg_right hLη (norm_nonneg _)))
  exact exists_fderiv_one_add_apply_fderiv_I_eq_zero_of_rescale J ht hμ hvC hv0 hv1 hveq

end TauCeti
