/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.Pompeiu.Holder.Operator
import TauCeti.Analysis.Complex.Pompeiu.Rotation
import TauCeti.Analysis.Holder.Bilinear
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Topology.MetricSpace.BallCutoff
import TauCeti.Topology.MetricSpace.Holder

/-!
# Pseudoholomorphic discs with a prescribed centre and first jet

Let `F` be a finite-dimensional complex normed space and `J : F → (F →L[ℝ] F)` a field of real
endomorphisms with `J(0) v = i v`, such as an almost complex structure written in coordinates
centred at a point where it is standard. This file solves the nonlinear Cauchy–Riemann equation

`∂ₛu + J(u) ∂ₜu = 0`

for maps `u` from a disc in `ℂ = {s + i t}` to `F`, with `u(0) = 0` and a prescribed first jet
`∂ₛu(0) = ξ`, when the derivative of `J` and its Lipschitz constant are small on a fixed ball of
`F`. Structures of class `C²` are reduced to this case by rescaling in
`TauCeti.Geometry.Symplectic.JHolomorphic.Disc.Rescaling`. When every `J(x)` is an almost complex
structure, `J(x)² = -1`, a solution is `J`-holomorphic for the standard structure of `ℂ` in the
sense of `TauCeti.IsJHolomorphicAt`
(`TauCeti.isJHolomorphicAt_iff_fderiv_one_add_apply_fderiv_I_eq_zero`).

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
  (`TauCeti.exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le`).
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

**Dependence on the coefficient and the first jet.** The source of the disc is the unique fixed
point of a contraction with constant `1/2`, so it depends Lipschitz continuously on the data of
the fixed-point map. If `Q - Q'` and `DQ - DQ'` are bounded by `ε` on the ball of radius `4`, the
right sides `Q(u) ∂u` and `Q'(u') ∂u'` of a common source with first jets `ξ` and `ξ'` differ by
`O(‖ξ - ξ'‖ + ε)` in Hölder norm, and the fixed points `h`, `h'` satisfy
`‖h - h'‖ ≤ ‖Φ h - Φ h'‖ + ‖Φ h' - Φ' h'‖ ≤ ‖h - h'‖ / 2 + O(‖ξ - ξ'‖ + ε)`. The Cauchy transform
gains a derivative, so on the unit disc the discs `u_{Q, ξ}` and `u_{Q', ξ'}` and their derivatives
differ by at most `C (‖ξ - ξ'‖ + ε)`, with `C` depending only on `F`. In the normal disc families
of the large-parameter analysis, `Q` is the Beltrami coefficient of the almost complex structure in
coordinates centred at a point of the curve and `ξ` a unit normal vector there, so this is the
estimate from which continuity of the family in the base point is to be derived, once it is
transferred through the rescaling.

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
* `TauCeti.exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le`:
  the same for the Beltrami equation `\bar∂u = Q(u) ∂u` when `Q(0) = 0` and `DQ` and its
  Lipschitz constant are small on the closed ball of radius `4`, for a family `u_{Q, ξ}` chosen
  uniformly in `Q`; if `Q` is also conjugate-linear on the closed ball of radius `2`, the family
  satisfies `u_{Q, c ξ}(w) = u_{Q, ξ}(c w)` for `|c| = 1`; for `Q = 0` the discs are the complex
  lines `w ↦ w ξ`; and on the unit disc `u_{Q, ξ}` and its derivative depend Lipschitz
  continuously on `ξ` and on `Q` in the `C¹` norm on the ball of radius `4`.

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

public noncomputable section

open Complex Metric Set Function
open scoped NNReal BoundedContinuousFunction Topology

namespace TauCeti

/-! ### The radial cutoff and Hölder helpers -/

section Cutoff

/-- The radial cutoff `z ↦ min 1 (max 0 (2 - 2 ‖z‖))`, the cutoff of the closed ball of radius
`1 / 2`. -/
private def discCutoff (z : ℂ) : ℝ :=
  ballCutoff 0 2⁻¹ z

private theorem discCutoff_eq_one {z : ℂ} (hz : ‖z‖ ≤ 2⁻¹) : discCutoff z = 1 :=
  ballCutoff_eq_one_of_mem_closedBall (by norm_num) (mem_closedBall_zero_iff.2 hz)

private theorem discCutoff_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : discCutoff z = 0 :=
  ballCutoff_eq_zero_of_two_mul_le_dist (by norm_num) (by norm_num [hz])

/-- The cutoff is invariant under rotations `z ↦ c z`, `|c| = 1`. -/
private theorem discCutoff_mul_left {c : ℂ} (hc : ‖c‖ = 1) (z : ℂ) :
    discCutoff (c * z) = discCutoff z := by
  simp [discCutoff, ballCutoff_apply, hc]

/-- The radial cutoff as a bounded continuous function. -/
private def cutoffBCF : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup discCutoff
    (lipschitzWith_ballCutoff 0 2⁻¹).continuous 1 (norm_ballCutoff_le 0 2⁻¹)

private theorem coe_cutoffBCF : ⇑cutoffBCF = discCutoff :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

/-- The radial cutoff as a `1/2`-Hölder function supported in the unit disc. -/
private def cutoffHolder : supportedHolderSubmodule (Y := ℝ) (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) :=
  ⟨HolderSpace.ofBoundedContinuousFunction cutoffBCF (by
      rw [coe_cutoffBCF]
      exact ⟨_, holderWith_ballCutoff 0 2⁻¹ two_inv_lt_one.le⟩),
    mem_supportedHolderSubmodule_iff.mpr fun z hz ↦ by
      simp only [mem_closedBall, dist_zero_right, not_le] at hz
      rw [HolderSpace.ofBoundedContinuousFunction_apply, coe_cutoffBCF]
      exact discCutoff_eq_zero hz.le⟩

private theorem cutoffHolder_apply (z : ℂ) :
    (cutoffHolder : HolderSpace (2⁻¹ : ℝ≥0) ℂ ℝ) z = discCutoff z := by
  rw [cutoffHolder, HolderSpace.ofBoundedContinuousFunction_apply, coe_cutoffBCF]

/-- The centre of the unit disc. -/
private def centre : closedBall (0 : ℂ) 1 := ⟨0, mem_closedBall_self zero_le_one⟩

private theorem coe_centre : (centre : ℂ) = 0 := rfl

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
    (fun z _ ↦ (hM z).trans (Real.le_coe_toNNReal M)) two_inv_lt_one.le)

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

private theorem mem_closedBall_four {E : Type*} [NormedAddCommGroup E] {x : E} (hx : ‖x‖ ≤ 2) :
    x ∈ closedBall (0 : E) 4 := by
  rw [mem_closedBall, dist_zero_right]
  linarith

private theorem add_mem_closedBall_four {E : Type*} [NormedAddCommGroup E] {x y : E}
    (hx : ‖x‖ ≤ 2) (hy : ‖y‖ ≤ 2) : x + y ∈ closedBall (0 : E) 4 := by
  rw [mem_closedBall, dist_zero_right]
  linarith [norm_add_le x y]

end Cutoff

/-! ### The normalized disc of a source -/

section DiscMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The disc `w ↦ w ξ + T h(w) - T h(0) - w ∂ₛ(T h)(0)` with source `h`. Its centre is `0`, and
the subtracted terms are holomorphic, so its conjugate Wirtinger derivative is that of `T h`. -/
private def discMap (ξ : F) (h : ℂ → F) (w : ℂ) : F :=
  w • ξ + cauchyTransform h w - cauchyTransform h 0 - w • fderiv ℝ (cauchyTransform h) 0 1

private theorem discMap_zero (ξ : F) (h : ℂ → F) : discMap ξ h 0 = 0 := by
  simp [discMap]

/-- Changing the first jet of the disc of a source from `ξ'` to `ξ` adds `w (ξ - ξ')`. -/
private theorem discMap_sub_discMap (ξ ξ' : F) (h : ℂ → F) (w : ℂ) :
    discMap ξ h w - discMap ξ' h w = w • (ξ - ξ') := by
  simp only [discMap, smul_sub]
  abel

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

variable (F) in
/-- The sources: `1/2`-Hölder functions supported in the unit disc. -/
private abbrev Source := supportedHolderSubmodule (Y := F) (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1)

/-- The coefficient `z ↦ K(u(z))` along the disc `u` of a source, on the unit disc. -/
private def kFun (K : F → F →L[ℝ] F) (ξ : F) (f : Source F) (z : closedBall (0 : ℂ) 1) :
    F →L[ℝ] F :=
  K (discMap ξ ⇑f.val z)

open Classical in
/-- The coefficient `kFun` as a `1/2`-Hölder field when it is one, and `0` otherwise. -/
private def kField (K : F → F →L[ℝ] F) (ξ : F) (f : Source F) :
    HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) (F →L[ℝ] F) :=
  if h : ∃ p : ℝ≥0 × ℝ, HolderWith p.1 (2⁻¹ : ℝ≥0) (kFun K ξ f) ∧ ∀ z, ‖kFun K ξ f z‖ ≤ p.2 then
    HolderSpace.ofBoundedContinuousFunction
      (BoundedContinuousFunction.ofNormedAddCommGroup (kFun K ξ f)
        ((Classical.choose_spec h).1.continuous (inv_pos.2 two_pos)) _ (Classical.choose_spec h).2)
      (by
        rw [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact ⟨_, (Classical.choose_spec h).1⟩)
  else 0

private theorem kField_apply {K : F → F →L[ℝ] F} {ξ : F} {f : Source F} {C : ℝ≥0} {M : ℝ}
    (hH : HolderWith C (2⁻¹ : ℝ≥0) (kFun K ξ f)) (hM : ∀ z, ‖kFun K ξ f z‖ ≤ M)
    (z : closedBall (0 : ℂ) 1) : kField K ξ f z = kFun K ξ f z := by
  rw [kField, dite_eq_left_of_eq_true (eq_true ⟨(C, M), hH, hM⟩),
    HolderSpace.ofBoundedContinuousFunction_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup]

variable (F) in
/-- The bilinear map `(v, t) ↦ t v`. -/
private def smulPair : F →L[ℝ] ℝ →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

private theorem norm_smulPair_le : ‖smulPair F‖ ≤ 1 := by
  rw [smulPair, ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

/-- Multiplication by the cutoff, as an operator from fields on the unit disc to sources, has norm
at most `‖χ‖`. -/
private theorem norm_cutoffMul_le :
    ‖(smulPair F).compHolder₂ExtendByZero cutoffHolder‖ ≤ ‖cutoffHolder‖ :=
  (ContinuousLinearMap.norm_compHolder₂ExtendByZero_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_smulPair_le)

private theorem nonneg_of_norm_fderiv_le {K : F → F →L[ℝ] F} {η : ℝ}
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) : 0 ≤ η :=
  (norm_nonneg (fderiv ℝ K 0)).trans (h1 0 (mem_closedBall_self (by norm_num)))

/-- A structure whose derivative is bounded by `η` on the ball of radius `4` is `η`-Lipschitz
there. -/
private theorem norm_sub_le_of_norm_fderiv_le {K : F → F →L[ℝ] F} {η : ℝ}
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {x y : F}
    (hx : x ∈ closedBall (0 : F) 4) (hy : y ∈ closedBall (0 : F) 4) :
    ‖K x - K y‖ ≤ η * ‖x - y‖ :=
  (convex_closedBall 0 4).norm_image_sub_le_of_norm_fderiv_le hd h1 hy hx

end DiscMap

/-! ### Derivative and Lipschitz bounds for the normalized disc -/

section DiscBounds

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

variable (F) in
/-- The derivative of the Cauchy transform on the unit disc, as a bounded operator from sources
to `1/2`-Hölder fields of real-linear maps. -/
private def derivOp : Source F →L[ℝ] HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) (ℂ →L[ℝ] F) :=
  cauchyDerivativeCLM (inv_pos.2 two_pos) two_inv_lt_one zero_le_one zero_le_one

private theorem derivOp_apply (f : Source F) (z : closedBall (0 : ℂ) 1) :
    derivOp F f z = fderiv ℝ (cauchyTransform ⇑f.val) z := by
  rw [funext (cauchyTransform_apply _)]
  exact cauchyDerivativeCLM_apply (inv_pos.2 two_pos) two_inv_lt_one zero_le_one zero_le_one f z

private theorem differentiableAt_cauchyTransform (f : Source F) (z : ℂ) :
    DifferentiableAt ℝ (cauchyTransform ⇑f.val) z :=
  (contDiff_cauchyTransform_of_mem_supportedHolderSubmodule (inv_pos.2 two_pos) two_inv_lt_one
      zero_le_one f.property).differentiable
    one_ne_zero z

private theorem fderiv_discMap (ξ : F) (f : Source F) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    fderiv ℝ (discMap ξ ⇑f.val) z =
      (ContinuousLinearMap.id ℝ ℂ).smulRight ξ + derivOp F f ⟨z, hz⟩ -
        (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1) := by
  rw [(hasFDerivAt_discMap ξ (differentiableAt_cauchyTransform f z)).fderiv,
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

private theorem norm_derivOp_sub_smulRight_le (f : Source F) (z : closedBall (0 : ℂ) 1) :
    ‖derivOp F f z - (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1)‖ ≤
      2 * ‖derivOp F‖ * ‖f‖ :=
  (norm_sub_le _ _).trans <| by
    linarith [norm_derivOp_apply_le f z, norm_id_smulRight_le (derivOp F f centre 1),
      norm_derivOp_apply_one_le f centre]

/-- On the unit disc the derivative of the disc is bounded by `‖ξ‖ + 2 ‖D‖ ‖f‖`. -/
private theorem norm_fderiv_discMap_le (ξ : F) (f : Source F) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖fderiv ℝ (discMap ξ ⇑f.val) z‖ ≤ ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ := by
  rw [fderiv_discMap ξ f hz, add_sub_assoc]
  exact (norm_add_le _ _).trans <| add_le_add (norm_id_smulRight_le ξ)
    (norm_derivOp_sub_smulRight_le f ⟨z, hz⟩)

/-- On the unit disc the derivatives of the discs of two sources differ by at most
`2 ‖D‖ ‖f - g‖`. -/
private theorem norm_fderiv_discMap_sub_le (ξ : F) (f g : Source F) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖fderiv ℝ (discMap ξ ⇑f.val) z - fderiv ℝ (discMap ξ ⇑g.val) z‖ ≤
      2 * ‖derivOp F‖ * ‖f - g‖ := by
  have heq : fderiv ℝ (discMap ξ ⇑f.val) z - fderiv ℝ (discMap ξ ⇑g.val) z =
      derivOp F (f - g) ⟨z, hz⟩ -
        (ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F (f - g) centre 1) := by
    rw [fderiv_discMap ξ f hz, fderiv_discMap ξ g hz]
    ext w
    simp only [map_sub, HolderSpace.sub_apply, add_apply, sub_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_sub]
    abel
  rw [heq]
  exact norm_derivOp_sub_smulRight_le (f - g) ⟨z, hz⟩

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

/-- On the unit disc the discs of two sources differ by at most `2 ‖D‖ ‖f - g‖`. -/
private theorem norm_discMap_sub_discMap_le (ξ : F) (f g : Source F) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖discMap ξ ⇑f.val z - discMap ξ ⇑g.val z‖ ≤ 2 * ‖derivOp F‖ * ‖f - g‖ := by
  have h := norm_discMap_sub_discMap_sub_le ξ f g hz centre.property
  rw [coe_centre, discMap_zero, discMap_zero, sub_zero, sub_zero, sub_zero] at h
  rw [mem_closedBall, dist_zero_right] at hz
  exact h.trans (mul_le_of_le_one_right (by positivity) hz)

/-- A small source gives a disc of norm at most `2` on the unit disc. -/
private theorem norm_discMap_le {ξ : F} (hξ : ‖ξ‖ ≤ 1) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖discMap ξ ⇑f.val z‖ ≤ 2 := by
  have h := norm_discMap_sub_le ξ f hz centre.property
  rw [coe_centre, discMap_zero, sub_zero, sub_zero] at h
  rw [mem_closedBall, dist_zero_right] at hz
  exact h.trans (by nlinarith [norm_nonneg z])

end DiscBounds

/-! ### The fixed-point map and estimates on the ball of small sources -/

section FixedPoint

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The field `z ↦ ℓ(Du(z))` of the disc `u` of a source, on the unit disc. -/
private def wField (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (ξ : F) (f : Source F) :
    HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight ξ)) +
    HolderSpace.compLeftL ℓ (derivOp F f) -
    HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight (derivOp F f centre 1)))

private theorem wField_apply (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (ξ : F) (f : Source F)
    (z : closedBall (0 : ℂ) 1) :
    wField ℓ ξ f z = ℓ (fderiv ℝ (discMap ξ ⇑f.val) z) := by
  rw [fderiv_discMap ξ f z.property]
  simp [wField, HolderSpace.compLeftL_apply, HolderSpace.const_apply]

/-- The part `z ↦ ℓ(D(T f)(z)) - ℓ(∂ₛ(T f)(0))` of `ℓ(Du)` that depends on the source is bounded
by `2 ‖D‖ ‖f‖` when `‖ℓ‖ ≤ 1`. -/
private theorem norm_compLeftL_sub_const_le {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} (hℓ : ‖ℓ‖ ≤ 1)
    (f : Source F) :
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

private theorem norm_wField_le {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {ξ : F} (hℓ : ‖ℓ‖ ≤ 1) (f : Source F) :
    ‖wField ℓ ξ f‖ ≤ ‖ξ‖ + 2 * ‖derivOp F‖ * ‖f‖ := by
  have h1 : ‖(HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight ξ)) :
      HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F)‖ ≤ ‖ξ‖ :=
    (HolderSpace.norm_const_le _).trans <| (ℓ.le_opNorm _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) hℓ).trans (norm_id_smulRight_le ξ)
  rw [wField, add_sub_assoc]
  exact (norm_add_le _ _).trans (add_le_add h1 (norm_compLeftL_sub_const_le hℓ f))

private theorem norm_wField_sub_le {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} (ξ : F) (hℓ : ‖ℓ‖ ≤ 1)
    (f g : Source F) :
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
private def gField (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (K : F → F →L[ℝ] F) (ξ : F) (f : Source F) :
    HolderSpace (2⁻¹ : ℝ≥0) (closedBall (0 : ℂ) 1) F :=
  (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂ (kField K ξ f) (wField ℓ ξ f)

/-- The fixed-point map `f ↦ χ · K(u) ℓ(Du)` on sources, with the radial cutoff `χ`. -/
private def fixedPointMap (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (K : F → F →L[ℝ] F) (ξ : F) (f : Source F) :
    Source F :=
  (smulPair F).compHolder₂ExtendByZero cutoffHolder (gField ℓ K ξ f)

private theorem fixedPointMap_apply {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K : F → F →L[ℝ] F} {ξ : F}
    (f : Source F) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (fixedPointMap ℓ K ξ f).val z = discCutoff z • gField ℓ K ξ f ⟨z, hz⟩ := by
  rw [fixedPointMap, ContinuousLinearMap.compHolder₂ExtendByZero_apply_of_mem _ _ _ hz,
    cutoffHolder_apply, smulPair, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply]

private theorem norm_fixedPointMap_sub_le {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K : F → F →L[ℝ] F} {ξ : F}
    (f g : Source F) :
    ‖fixedPointMap ℓ K ξ f - fixedPointMap ℓ K ξ g‖ ≤
      ‖cutoffHolder‖ * ‖gField ℓ K ξ f - gField ℓ K ξ g‖ := by
  rw [fixedPointMap, fixedPointMap, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

private theorem norm_fixedPointMap_le {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K : F → F →L[ℝ] F} {ξ : F}
    (f : Source F) :
    ‖fixedPointMap ℓ K ξ f‖ ≤ ‖cutoffHolder‖ * ‖gField ℓ K ξ f‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact norm_cutoffMul_le)

section Estimates

variable {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K : F → F →L[ℝ] F} {ξ : F} {η : ℝ}

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
    kField K ξ f z = kFun K ξ f z := by
  obtain ⟨hM, hL⟩ := kFun_bounds hξ hK0 hd h1 hf
  exact kField_apply (holderWith_of_norm_le hM hL) hM z

private theorem norm_kField_le (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖kField K ξ f‖ ≤ 8 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  obtain ⟨hM, hL⟩ := kFun_bounds hξ hK0 hd h1 hf
  have hval := kField_eq hξ hK0 hd h1 hf
  refine (norm_le_of_lipschitz _ (L := 2 * η) (M := 2 * η) (by positivity) (by positivity)
    (fun z ↦ by simpa [hval] using hM z)
    (fun z w ↦ by simpa [hval] using hL z w)).trans (le_of_eq (by ring))

/-- **Comparison of two coefficient fields.** Let `u = u_{ξ, f}` and `u' = u_{ξ', g}` be the discs
of two small sources, whose difference is bounded by `δ ≤ 2` and `δ`-Lipschitz on the unit disc,
and let `K'` be a second coefficient such that `K - K'` and its derivative are bounded by `ε` on
the ball of radius `4`. Then the fields `K(u)` and `K'(u')` differ by at most `6 η δ + 5 ε` in
Hölder norm. -/
private theorem norm_kField_sub_kField_le {K' : F → F →L[ℝ] F} {ξ' : F} {δ ε : ℝ}
    (hξ : ‖ξ‖ ≤ 1) (hξ' : ‖ξ'‖ ≤ 1) (hK0 : K 0 = 0) (hK0' : K' 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (hd' : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K' x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η)
    (h1' : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K' x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ K x - fderiv ℝ K y‖ ≤ η * ‖x - y‖)
    (hε0 : ∀ x ∈ closedBall (0 : F) 4, ‖K x - K' x‖ ≤ ε)
    (hε1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x - fderiv ℝ K' x‖ ≤ ε) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) (hδ2 : δ ≤ 2)
    (hdiff : ∀ z : closedBall (0 : ℂ) 1, ‖discMap ξ ⇑f.val z - discMap ξ' ⇑g.val z‖ ≤ δ)
    (hdiffL : ∀ z w : closedBall (0 : ℂ) 1,
      ‖(discMap ξ ⇑f.val z - discMap ξ' ⇑g.val z) - (discMap ξ ⇑f.val w - discMap ξ' ⇑g.val w)‖ ≤
        δ * ‖(z : ℂ) - w‖) :
    ‖kField K ξ f - kField K' ξ' g‖ ≤ 6 * η * δ + 5 * ε := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hdiff centre)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hε0 0 (mem_closedBall_self (by norm_num)))
  -- `K - K'` is `ε`-Lipschitz on the ball of radius `4`.
  have hE : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖(K x - K' x) - (K y - K' y)‖ ≤ ε * ‖x - y‖ := fun x hx y hy ↦
    norm_sub_le_of_norm_fderiv_le (K := fun x ↦ K x - K' x)
      (fun x hx ↦ (hd x hx).sub (hd' x hx))
      (fun x hx ↦ by rw [fderiv_fun_sub (hd x hx) (hd' x hx)]; exact hε1 x hx) hx hy
  have hval : ∀ z, (kField K ξ f - kField K' ξ' g) z =
      (K (discMap ξ ⇑f.val z) - K (discMap ξ' ⇑g.val z)) +
        (K (discMap ξ' ⇑g.val z) - K' (discMap ξ' ⇑g.val z)) := fun z ↦ by
    rw [HolderSpace.sub_apply, kField_eq hξ hK0 hd h1 hf, kField_eq hξ' hK0' hd' h1' hg, kFun,
      kFun, sub_add_sub_cancel]
  refine (norm_le_of_lipschitz _ (L := 3 * η * δ + 2 * ε) (M := η * δ + ε) (by positivity)
    (by positivity) (fun z ↦ ?_) (fun z w ↦ ?_)).trans (le_of_eq (by ring))
  · rw [hval]
    refine (norm_add_le _ _).trans (add_le_add ?_
      (hε0 _ (mem_closedBall_four (norm_discMap_le hξ' hg z.property))))
    refine (norm_sub_le_of_norm_fderiv_le hd h1
      (mem_closedBall_four (norm_discMap_le hξ hf z.property))
      (mem_closedBall_four (norm_discMap_le hξ' hg z.property))).trans ?_
    exact mul_le_mul_of_nonneg_left (hdiff z) hη
  · rw [hval, hval, add_sub_add_comm]
    have hgz := norm_discMap_le hξ' hg z.property
    have hgw := norm_discMap_le hξ' hg w.property
    have ha := norm_discMap_sub_le ξ' g z.property w.property
    have hLg : ‖ξ'‖ + 2 * ‖derivOp F‖ * ‖g‖ ≤ 2 := by linarith
    refine (norm_add_le _ _).trans ((add_le_add ?_ ?_).trans (le_of_eq (add_mul _ _ _).symm))
    · -- The second difference of `K` at `a = u'`, `b = u - u'`.
      have h := (convex_closedBall (0 : F) 4).norm_image_sub_sub_sub_le_of_norm_fderiv_le hd h1 h2
        (mem_closedBall_four hgz) (mem_closedBall_four hgw)
        (add_mem_closedBall_four hgz ((hdiff z).trans hδ2))
        (add_mem_closedBall_four hgz ((hdiff w).trans hδ2))
        (add_mem_closedBall_four hgw ((hdiff w).trans hδ2))
      rw [add_sub_cancel, add_sub_cancel] at h
      refine h.trans ?_
      calc η * ‖_‖ + η * ‖_‖ * ‖_‖
          ≤ η * (δ * ‖(z : ℂ) - w‖) +
            η * δ * ((‖ξ'‖ + 2 * ‖derivOp F‖ * ‖g‖) * ‖(z : ℂ) - w‖) := by
            gcongr
            · exact hdiffL z w
            · exact hdiff w
        _ ≤ η * (δ * ‖(z : ℂ) - w‖) + η * δ * (2 * ‖(z : ℂ) - w‖) := by gcongr
        _ = 3 * η * δ * ‖(z : ℂ) - w‖ := by ring
    · refine (hE _ (mem_closedBall_four hgz) _ (mem_closedBall_four hgw)).trans ?_
      calc ε * ‖_‖ ≤ ε * ((‖ξ'‖ + 2 * ‖derivOp F‖ * ‖g‖) * ‖(z : ℂ) - w‖) := by gcongr
        _ ≤ ε * (2 * ‖(z : ℂ) - w‖) := by gcongr
        _ = 2 * ε * ‖(z : ℂ) - w‖ := by ring

/-- For two small sources the coefficients differ by at most `12 η ‖D‖ ‖f - g‖` in Hölder
norm. -/
private theorem norm_kField_sub_le (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η)
    (h2 : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
      ‖fderiv ℝ K x - fderiv ℝ K y‖ ≤ η * ‖x - y‖) {f g : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) (hg : 2 * ‖derivOp F‖ * ‖g‖ ≤ 1) :
    ‖kField K ξ f - kField K ξ g‖ ≤ 12 * η * ‖derivOp F‖ * ‖f - g‖ := by
  have hDd : 2 * ‖derivOp F‖ * ‖f - g‖ ≤ 2 := by
    have := mul_le_mul_of_nonneg_left (norm_sub_le f g) (norm_nonneg (derivOp F))
    nlinarith
  have hε : ∀ x ∈ closedBall (0 : F) 4, ‖K x - K x‖ ≤ 0 := fun x _ ↦ by
    rw [sub_self, norm_zero]
  have hε' : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x - fderiv ℝ K x‖ ≤ 0 := fun x _ ↦ by
    rw [sub_self]
    exact (norm_zero (E := F →L[ℝ] F →L[ℝ] F)).le
  refine (norm_kField_sub_kField_le hξ hξ hK0 hK0 hd hd h1 h1 h2 hε hε' hf hg hDd
    (fun z ↦ norm_discMap_sub_discMap_le ξ f g z.property)
    (fun z w ↦ norm_discMap_sub_discMap_sub_le ξ f g z.property w.property)).trans
    (le_of_eq (by ring))

private theorem norm_gField_le (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK0 : K 0 = 0)
    (hd : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x)
    (h1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ η) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) : ‖gField ℓ K ξ f‖ ≤ 16 * η := by
  have hη : 0 ≤ η := nonneg_of_norm_fderiv_le h1
  have hk := norm_kField_le hξ hK0 hd h1 hf
  have hw : ‖wField ℓ ξ f‖ ≤ 2 := (norm_wField_le hℓ f).trans (by linarith)
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
  have hw : ‖wField ℓ ξ g‖ ≤ 2 := (norm_wField_le hℓ g).trans (by linarith)
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

end FixedPoint

/-! ### The contraction and its unique fixed point -/

section Contraction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

variable (F) in
/-- The smallness of the coefficient under which the fixed-point map contracts. -/
private def smallness : ℝ :=
  (640 * (‖cutoffHolder‖ + 1) * (‖derivOp F‖ + 1))⁻¹

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
private structure SmallCoeff (K : F → F →L[ℝ] F) : Prop where
  map_zero : K 0 = 0
  differentiableAt : ∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ K x
  norm_fderiv_le : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x‖ ≤ smallness F
  lipschitz_fderiv : ∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
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

variable {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K : F → F →L[ℝ] F} {ξ : F}

/-- On the unit disc, the fixed-point map of a small source is `χ · K(u) ℓ(Du)`. -/
private theorem fixedPointMap_apply_of_small (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (fixedPointMap ℓ K ξ f).val z =
      discCutoff z • K (discMap ξ ⇑f.val z) (ℓ (fderiv ℝ (discMap ξ ⇑f.val) z)) := by
  rw [fixedPointMap_apply f hz, gField, ContinuousLinearMap.compHolder₂_apply,
    ContinuousLinearMap.id_apply,
    kField_eq hξ hK.map_zero hK.differentiableAt hK.norm_fderiv_le hf, wField_apply, kFun]

/-- The fixed-point map sends the ball of radius `radius F` into itself, since
`‖χ‖ · 16 η ≤ radius F`. -/
private theorem mapsTo_fixedPointMap (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    MapsTo (fixedPointMap ℓ K ξ) (closedBall 0 (radius F)) (closedBall 0 (radius F)) := by
  set X := ‖cutoffHolder‖
  set D := ‖derivOp F‖
  have hX : 0 ≤ X := norm_nonneg _
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  intro f hf
  rw [mem_closedBall, dist_zero_right]
  calc ‖fixedPointMap ℓ K ξ f‖ ≤ X * ‖gField ℓ K ξ f‖ := norm_fixedPointMap_le f
    _ ≤ X * (16 * smallness F) := by
      gcongr
      exact norm_gField_le hℓ hξ hK.map_zero hK.differentiableAt hK.norm_fderiv_le
        (small_of_mem_closedBall hf)
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
  set X := ‖cutoffHolder‖
  set D := ‖derivOp F‖
  have hX : 0 ≤ X := norm_nonneg _
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  calc ‖fixedPointMap ℓ K ξ f - fixedPointMap ℓ K ξ g‖
      ≤ X * ‖gField ℓ K ξ f - gField ℓ K ξ g‖ := norm_fixedPointMap_sub_le f g
    _ ≤ X * (40 * smallness F * D * ‖f - g‖) := by
      gcongr
      exact norm_gField_sub_le hℓ hξ hK.map_zero hK.differentiableAt hK.norm_fderiv_le
        hK.lipschitz_fderiv (small_of_mem_closedBall hf) (small_of_mem_closedBall hg)
    _ ≤ 2⁻¹ * ‖f - g‖ := by
      rw [show X * (40 * smallness F * D * ‖f - g‖) =
        (X * D / (16 * (X + 1) * (D + 1))) * ‖f - g‖ by rw [smallness]; field_simp; ring]
      gcongr
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hX hD]

/-- The fixed-point map, restricted to the ball of radius `radius F`, is a contraction with
constant `1 / 2`. -/
private theorem contractingWith_restrict_fixedPointMap (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1)
    (hK : SmallCoeff F K) :
    ContractingWith 2⁻¹ ((mapsTo_fixedPointMap hℓ hξ hK).restrict _ _ _) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun f g ↦ ?_⟩
  rw [Subtype.dist_eq (MapsTo.restrict _ _ _ _ f) (MapsTo.restrict _ _ _ _ g), Subtype.dist_eq f g,
    MapsTo.val_restrict_apply, MapsTo.val_restrict_apply, dist_eq_norm, dist_eq_norm]
  simpa using norm_fixedPointMap_sub_le_half hℓ hξ hK f.property g.property

/-- The fixed-point map has a fixed point in the ball of radius `radius F`. -/
private theorem exists_fixedPointMap_eq (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    ∃ f ∈ closedBall (0 : Source F) (radius F), fixedPointMap ℓ K ξ f = f := by
  have := FiniteDimensional.completeSpace ℂ F
  obtain ⟨f, hf, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    (mapsTo_fixedPointMap hℓ hξ hK) (contractingWith_restrict_fixedPointMap hℓ hξ hK)
    (mem_closedBall_self radius_pos.le) (edist_ne_top _ _)
  exact ⟨f, hf, hfix⟩

/-- **Uniqueness of the source.** The fixed-point map has at most one fixed point in the ball of
radius `radius F`. -/
private theorem eq_of_fixedPointMap_eq (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K)
    {f g : Source F} (hf : f ∈ closedBall 0 (radius F)) (hg : g ∈ closedBall 0 (radius F))
    (hff : fixedPointMap ℓ K ξ f = f) (hgg : fixedPointMap ℓ K ξ g = g) : f = g := by
  have h := norm_fixedPointMap_sub_le_half hℓ hξ hK hf hg
  rw [hff, hgg] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (f - g)]))

open Classical in
/-- The source of the disc: the fixed point of `fixedPointMap` in the ball of radius
`radius F`, unique when the coefficient is small, and `0` if there is none. -/
private def discSource (ℓ : (ℂ →L[ℝ] F) →L[ℝ] F) (K : F → F →L[ℝ] F) (ξ : F) : Source F :=
  if h : ∃ f ∈ closedBall (0 : Source F) (radius F), fixedPointMap ℓ K ξ f = f then h.choose
  else 0

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
  have hTC := (contDiff_cauchyTransform_of_mem_supportedHolderSubmodule (inv_pos.2 two_pos)
    two_inv_lt_one zero_le_one f.property).contDiffOn (s := ball 0 2)
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
    rw [conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule (inv_pos.2 two_pos)
        two_inv_lt_one zero_le_one f.property]
    conv_lhs => rw [← hfix]
    rw [fixedPointMap_apply_of_small hξ hK hf hz1, discCutoff_eq_one hzn, one_smul]

/-- The fixed source vanishes at the centre, since `K(u(0)) = K(0) = 0`. -/
private theorem discSource_apply_zero (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hK : SmallCoeff F K) :
    (discSource ℓ K ξ).val 0 = 0 := by
  obtain ⟨hmem, hfix⟩ := discSource_spec hℓ hξ hK
  rw [← hfix, fixedPointMap_apply_of_small hξ hK (small_of_mem_closedBall hmem)
    (mem_closedBall_self zero_le_one)]
  simp [discMap_zero, hK.map_zero]

/-- For the zero coefficient the fixed source is `0`, so the disc is the complex line
`w ↦ w ξ`. -/
private theorem discMap_discSource_zero (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (w : ℂ) :
    discMap ξ ⇑(discSource ℓ (0 : F → F →L[ℝ] F) ξ).val w = w • ξ := by
  have hs := (smallness_pos (F := F)).le
  have hK : SmallCoeff F (0 : F → F →L[ℝ] F) :=
    ⟨rfl, fun _ _ ↦ differentiableAt_const _,
      fun _ _ ↦ by simpa [ContinuousLinearMap.opNorm_zero] using hs,
      fun _ _ _ _ ↦ by simpa [ContinuousLinearMap.opNorm_zero] using mul_nonneg hs (norm_nonneg _)⟩
  have h0 : discSource ℓ (0 : F → F →L[ℝ] F) ξ = 0 := by
    refine discSource_eq hℓ hξ hK (mem_closedBall_self radius_pos.le)
      (Subtype.ext (HolderSpace.ext fun z ↦ ?_))
    by_cases hz : z ∈ closedBall (0 : ℂ) 1
    · rw [fixedPointMap_apply_of_small hξ hK (by simp) hz]
      simp
    · rw [mem_supportedHolderSubmodule_iff.mp (fixedPointMap _ _ _ _).property z hz]
      simp
  have hc : ⇑(discSource ℓ (0 : F → F →L[ℝ] F) ξ).val = (0 : ℂ → F) :=
    funext fun z ↦ by simp [h0]
  simp [hc, discMap, cauchyTransform_zero]

end Contraction

/-! ### Dependence on the first jet and the coefficient -/

section Dependence

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {ℓ : (ℂ →L[ℝ] F) →L[ℝ] F} {K K' : F → F →L[ℝ] F} {ξ ξ' : F} {ε : ℝ}

/-- Changing the first jet adds the constant `ℓ(w ↦ w (ξ - ξ'))` to the field `ℓ(Du)`. -/
private theorem norm_wField_sub_wField_le (hℓ : ‖ℓ‖ ≤ 1) (ξ ξ' : F) (f : Source F) :
    ‖wField ℓ ξ f - wField ℓ ξ' f‖ ≤ ‖ξ - ξ'‖ := by
  have heq : wField ℓ ξ f - wField ℓ ξ' f =
      HolderSpace.const (ℓ ((ContinuousLinearMap.id ℝ ℂ).smulRight (ξ - ξ'))) :=
    HolderSpace.ext fun z ↦ by
      simp only [wField, map_sub, HolderSpace.sub_apply, HolderSpace.add_apply,
        HolderSpace.compLeftL_apply, HolderSpace.const_apply,
        ← ContinuousLinearMap.coe_smulRightₗ (T := ℝ)]
      abel
  rw [heq]
  exact (HolderSpace.norm_const_le _).trans <| (ℓ.le_opNorm _).trans <|
    (mul_le_of_le_one_left (norm_nonneg _) hℓ).trans (norm_id_smulRight_le _)

/-- At a common small source, the right sides `K(u) ℓ(Du)` for two small coefficients `K`, `K'` and
two first jets `ξ`, `ξ'` differ by at most `20 η ‖ξ - ξ'‖ + 10 ε` in Hölder norm, where `K - K'`
and its derivative are bounded by `ε` on the ball of radius `4`. -/
private theorem norm_gField_sub_gField_le (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) (hξ' : ‖ξ'‖ ≤ 1)
    (hK : SmallCoeff F K) (hK' : SmallCoeff F K')
    (hε0 : ∀ x ∈ closedBall (0 : F) 4, ‖K x - K' x‖ ≤ ε)
    (hε1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x - fderiv ℝ K' x‖ ≤ ε) {f : Source F}
    (hf : 2 * ‖derivOp F‖ * ‖f‖ ≤ 1) :
    ‖gField ℓ K ξ f - gField ℓ K' ξ' f‖ ≤ 20 * smallness F * ‖ξ - ξ'‖ + 10 * ε := by
  set C := (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).compHolder₂
    (X := closedBall (0 : ℂ) 1) (α := 2⁻¹) (F := F)
  have heq : gField ℓ K ξ f - gField ℓ K' ξ' f =
      C (kField K ξ f) (wField ℓ ξ f - wField ℓ ξ' f) +
        C (kField K ξ f - kField K' ξ' f) (wField ℓ ξ' f) := by
    rw [gField, gField, map_sub, map_sub, sub_apply]
    abel
  have hξξ : ‖ξ - ξ'‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hk := norm_kField_le hξ hK.map_zero hK.differentiableAt hK.norm_fderiv_le hf
  -- The two discs differ by `z (ξ - ξ')`.
  have hkd := norm_kField_sub_kField_le hξ hξ' hK.map_zero hK'.map_zero hK.differentiableAt
    hK'.differentiableAt hK.norm_fderiv_le hK'.norm_fderiv_le hK.lipschitz_fderiv hε0 hε1 hf hf
    hξξ (fun z ↦ by
      rw [discMap_sub_discMap, norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) (mem_closedBall_zero_iff.1 z.property))
    (fun z w ↦ by
      rw [discMap_sub_discMap, discMap_sub_discMap, ← sub_smul, norm_smul]
      exact (mul_comm _ _).le)
  have hwd := norm_wField_sub_wField_le hℓ ξ ξ' f
  have hw : ‖wField ℓ ξ' f‖ ≤ 2 := (norm_wField_le hℓ f).trans (by linarith)
  rw [heq]
  calc ‖_‖ ≤ ‖kField K ξ f‖ * ‖wField ℓ ξ f - wField ℓ ξ' f‖ +
        ‖kField K ξ f - kField K' ξ' f‖ * ‖wField ℓ ξ' f‖ :=
        (norm_add_le _ _).trans (add_le_add
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _)
          (ContinuousLinearMap.norm_id_compHolder₂_apply_le _ _))
    _ ≤ 8 * smallness F * ‖ξ - ξ'‖ + (6 * smallness F * ‖ξ - ξ'‖ + 5 * ε) * 2 :=
        add_le_add (mul_le_mul hk hwd (norm_nonneg _) (by linarith [norm_nonneg (kField K ξ f)]))
          (mul_le_mul hkd hw (norm_nonneg _) ((norm_nonneg _).trans hkd))
    _ = 20 * smallness F * ‖ξ - ξ'‖ + 10 * ε := by ring

/-- **Lipschitz dependence of the source.** The sources of the discs for two small coefficients
`K`, `K'` and two first jets `ξ`, `ξ'` differ by at most `2 ‖χ‖ (20 η ‖ξ - ξ'‖ + 10 ε)`, where
`K - K'` and its derivative are bounded by `ε` on the ball of radius `4`. The fixed-point map `Φ` of
`(K, ξ)` contracts with constant `1/2`, so the fixed point `h'` of the fixed-point map `Φ'` of
`(K', ξ')` lies within `2 ‖h' - Φ h'‖ = 2 ‖Φ' h' - Φ h'‖` of the fixed point of `Φ`. -/
private theorem norm_discSource_sub_discSource_le (hℓ : ‖ℓ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1)
    (hξ' : ‖ξ'‖ ≤ 1) (hK : SmallCoeff F K) (hK' : SmallCoeff F K')
    (hε0 : ∀ x ∈ closedBall (0 : F) 4, ‖K x - K' x‖ ≤ ε)
    (hε1 : ∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ K x - fderiv ℝ K' x‖ ≤ ε) :
    ‖discSource ℓ K ξ - discSource ℓ K' ξ'‖ ≤
      2 * ‖cutoffHolder‖ * (20 * smallness F * ‖ξ - ξ'‖ + 10 * ε) := by
  obtain ⟨hmem, hfix⟩ := discSource_spec hℓ hξ hK
  obtain ⟨hmem', hfix'⟩ := discSource_spec hℓ hξ' hK'
  set f := discSource ℓ K ξ
  set g := discSource ℓ K' ξ'
  have h := (contractingWith_restrict_fixedPointMap hℓ hξ hK).dist_le_of_fixedPoint ⟨g, hmem'⟩
    (y := ⟨f, hmem⟩) (Subtype.ext hfix)
  have e1 : dist (⟨g, hmem'⟩ : closedBall (0 : Source F) (radius F)) ⟨f, hmem⟩ = ‖f - g‖ := by
    rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
  have e2 : dist (⟨g, hmem'⟩ : closedBall (0 : Source F) (radius F))
      ((mapsTo_fixedPointMap hℓ hξ hK).restrict _ _ _ ⟨g, hmem'⟩) =
        ‖fixedPointMap ℓ K' ξ' g - fixedPointMap ℓ K ξ g‖ := by
    rw [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    exact congrArg (‖· - fixedPointMap ℓ K ξ g‖) hfix'.symm
  have hK2 : (1 : ℝ) - ((2⁻¹ : ℝ≥0) : ℝ) = 2⁻¹ := by norm_num
  rw [e1, e2, hK2, div_inv_eq_mul] at h
  have h2 : ‖fixedPointMap ℓ K' ξ' g - fixedPointMap ℓ K ξ g‖ ≤
      ‖cutoffHolder‖ * (20 * smallness F * ‖ξ - ξ'‖ + 10 * ε) := by
    rw [norm_sub_rev, fixedPointMap, fixedPointMap, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul norm_cutoffMul_le
      (norm_gField_sub_gField_le hℓ hξ hξ' hK hK' hε0 hε1 (small_of_mem_closedBall hmem'))
      (norm_nonneg _) (norm_nonneg _))
  linarith

/-- On the unit disc, the discs `u = u_{ξ, f}` and `u' = u_{ξ', g}` of two sources, and their
derivatives, differ by at most `‖ξ - ξ'‖ + 2 ‖D‖ ‖f - g‖`. -/
private theorem norm_discMap_sub_discMap_le_and_norm_fderiv_sub_le (ξ ξ' : F) (f g : Source F)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖discMap ξ ⇑f.val z - discMap ξ' ⇑g.val z‖ ≤ ‖ξ - ξ'‖ + 2 * ‖derivOp F‖ * ‖f - g‖ ∧
      ‖fderiv ℝ (discMap ξ ⇑f.val) z - fderiv ℝ (discMap ξ' ⇑g.val) z‖ ≤
        ‖ξ - ξ'‖ + 2 * ‖derivOp F‖ * ‖f - g‖ := by
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.1 hz
  have hD : fderiv ℝ (discMap ξ ⇑g.val) z - fderiv ℝ (discMap ξ' ⇑g.val) z =
      (ContinuousLinearMap.id ℝ ℂ).smulRight (ξ - ξ') := by
    rw [fderiv_discMap ξ g hz, fderiv_discMap ξ' g hz]
    ext w
    simp only [sub_apply, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, smul_sub]
    abel
  constructor
  · rw [← sub_add_sub_cancel _ (discMap ξ ⇑g.val z), discMap_sub_discMap, add_comm]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_discMap_sub_discMap_le ξ f g hz))
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz1
  · rw [← sub_add_sub_cancel _ (fderiv ℝ (discMap ξ ⇑g.val) z), hD, add_comm]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_id_smulRight_le _) (norm_fderiv_discMap_sub_le ξ f g hz))

end Dependence

/-! ### Discs solving `∂ₛu + J(u) ∂ₜu = 0` -/

section AlmostComplexDisc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The operator `L ↦ -L(i) / 2`, minus half the derivative `∂ₜ`, has norm at most `1`. -/
private theorem norm_neg_half_smul_apply_I_le :
    ‖(-(2 : ℝ)⁻¹) • ContinuousLinearMap.apply ℝ F I‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ by
    rw [smul_apply, ContinuousLinearMap.apply_apply, norm_smul, one_mul]
    have h := L.le_opNorm I
    rw [norm_I, mul_one] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans h

/-- If `\bar∂u(z) = -(A(∂ₜu(z)) - i ∂ₜu(z)) / 2`, then `∂ₛu(z) + A(∂ₜu(z)) = 0`. -/
private theorem fderiv_one_add_apply_fderiv_I_eq_zero_of_conjWirtingerDeriv_eq
    {u : ℂ → F} {A : F → F} {z : ℂ}
    (hbar : conjWirtingerDeriv u z 1 = (-(2 : ℝ)⁻¹) • (A (fderiv ℝ u z I) - I • fderiv ℝ u z I)) :
    fderiv ℝ u z 1 + A (fderiv ℝ u z I) = 0 := by
  have h := fderiv_apply_one_add_I_smul_fderiv_apply_I u z
  rw [hbar, ← Complex.coe_smul, smul_smul] at h
  norm_num at h
  linear_combination (norm := module) h

/-- **Discs solving `∂ₛu + J(u) ∂ₜu = 0` for a nearly constant structure.** There is `η > 0`,
depending only on `F`, with the following property. Let `J : F → (F →L[ℝ] F)` satisfy
`J(0) v = i v`, and on the closed ball of radius `4` let `J` be differentiable with `‖DJ‖ ≤ η` and
with `DJ` `η`-Lipschitz. Then for every `ξ` with `‖ξ‖ ≤ 1` there is a map `u : ℂ → F`, `C¹` on
the disc of radius `2`, with `u(0) = 0`, `∂ₛu(0) = ξ` and values of norm at most `2` on the unit
disc, which solves `∂ₛu + J(u) ∂ₜu = 0` on the disc of radius `1/2`. -/
theorem exists_pos_forall_exists_fderiv_one_add_apply_fderiv_I_eq_zero [FiniteDimensional ℂ F] :
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
  refine ⟨_, hC, h0, h1', hb, fun z hz ↦
    fderiv_one_add_apply_fderiv_I_eq_zero_of_conjWirtingerDeriv_eq ?_⟩
  rw [conjWirtingerDeriv_discMap ξ (differentiableAt_cauchyTransform _ z), heq z hz,
    smul_apply, ContinuousLinearMap.apply_apply, map_smul, sub_apply, hJ0]

end AlmostComplexDisc

/-! ### Discs solving the Beltrami equation `\bar∂u = Q(u) ∂u` -/

section BeltramiDisc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- The Wirtinger derivative `∂ = (∂ₛ - i ∂ₜ) / 2` at `1`, as an operator on real-linear maps
`ℂ → F`. -/
private def wirtingerAtOne : (ℂ →L[ℝ] F) →L[ℝ] F :=
  (2⁻¹ : ℝ) • (ContinuousLinearMap.apply ℝ F (1 : ℂ) - I • ContinuousLinearMap.apply ℝ F I)

private theorem wirtingerAtOne_apply (L : ℂ →L[ℝ] F) :
    wirtingerAtOne F L = L.complexLinearPart 1 := by
  simp [wirtingerAtOne]

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

private theorem rotSource_apply {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) (z : ℂ) :
    (rotSource hc f).val z = c⁻¹ • f.val (c * z) := by
  simp [rotSource, HolderSpace.compLeftL_apply]

private theorem norm_rotSource_le {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) :
    ‖rotSource hc f‖ ≤ ‖f‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe f]
  refine ((HolderSpace.compLeftL _).le_opNorm _).trans ?_
  refine (mul_le_mul ((HolderSpace.norm_compLeftL_le _).trans
    (ContinuousLinearMap.opNorm_lsmul_apply_le _)) (HolderSpace.norm_compLipschitzL_apply_le _ _)
    (norm_nonneg _) (norm_nonneg _)).trans ?_
  rw [norm_inv, hc, inv_one, one_mul]

private theorem cauchyTransform_rotSource {c : ℂ} (hc : ‖c‖ = 1) (f : Source F) (w : ℂ) :
    cauchyTransform ⇑(rotSource hc f).val w = cauchyTransform ⇑f.val (c * w) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have h : (⇑(rotSource hc f).val : ℂ → F) = c⁻¹ • fun z ↦ f.val (c * z) :=
    funext fun z ↦ rotSource_apply hc f z
  rw [h, cauchyTransform_smul, Pi.smul_apply, cauchyTransform_comp_mul_left hc, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

section FiniteDim

variable [FiniteDimensional ℂ F]

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
    have h := conjWirtingerDeriv_cauchyTransform_of_mem_supportedHolderSubmodule (inv_pos.2 two_pos)
      two_inv_lt_one zero_le_one f.property 0
    rw [hf0] at h
    rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv,
      fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv]
    simp only [h, smul_zero, add_zero, one_smul]
  have hd := fderiv_comp_smul_apply (𝕜 := ℝ) (cauchyTransform ⇑f.val) c 0 1
  simp only [smul_eq_mul] at hd
  rw [discMap, discMap, hT, hd]
  simp only [mul_zero, mul_one, hlin, smul_smul, mul_comm w c]

/-- **Rotation equivariance of the source.** For a conjugate-linear coefficient `Q`, rotating the
source of the disc with first jet `ξ` gives the source of the disc with first jet `c ξ`. -/
private theorem discSource_smul {Q : F → F →L[ℝ] F} {ξ : F} (hξ : ‖ξ‖ ≤ 1) (hQ : SmallCoeff F Q)
    (hQI : ∀ x ∈ closedBall (0 : F) 2, ∀ v, Q x (I • v) = -(I • Q x v)) {c : ℂ} (hc : ‖c‖ = 1) :
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
      (hQI _ (mem_closedBall_zero_iff.mpr (norm_discMap_le hξ hf hcz)))
    simp only [ContinuousLinearMap.coe_coe] at hconj
    -- The rotated disc is the disc precomposed with `w ↦ c w`, so its `∂` is multiplied by `c`.
    rw [hrot, show discMap (c • ξ) ⇑g.val = fun w ↦ discMap ξ ⇑f.val (c * w) from funext hrot,
      wirtingerAtOne_apply, wirtingerAtOne_apply, ← wirtingerDeriv_eq_complexLinearPart,
      ← wirtingerDeriv_eq_complexLinearPart, wirtingerDeriv_comp_mul_left,
      ← discCutoff_mul_left hc z, hconj, ← Complex.inv_eq_conj hc, smul_comm]
  · rw [mem_supportedHolderSubmodule_iff.mp (fixedPointMap _ _ _ g).property z hz,
      mem_supportedHolderSubmodule_iff.mp g.property z hz]

/-- **Rotation-equivariant discs solving `\bar∂u = Q(u) ∂u`, depending Lipschitz continuously on
the coefficient and the first jet.** There are `η > 0` and `C ≥ 0`, depending only on `F`, and
maps `u_{Q, ξ} : ℂ → F` with the following properties, for all `Q : F → (F →L[ℝ] F)` vanishing at
`0` which, on the closed ball of radius `4`, are differentiable with `‖DQ‖ ≤ η` and `η`-Lipschitz
derivative, and all `ξ` with `‖ξ‖ ≤ 1`.

* Each `u_{Q, ξ}` is `C¹` on the disc of radius `2` with `u_{Q, ξ}(0) = 0`, `∂ₛu_{Q, ξ}(0) = ξ` and
  values of norm at most `2` on the unit disc, and solves the Beltrami equation
  `\bar∂u = Q(u) ∂u` on the disc of radius `1/2`.
* If `Q` takes conjugate-linear values on the closed ball of radius `2`, `Q(x)(i v) = -i Q(x) v`,
  as the Beltrami coefficient of a complex structure near `i` does, then the family is equivariant
  under rotations: `u_{Q, c ξ}(w) = u_{Q, ξ}(c w)` for `|c| = 1`.
* For the zero coefficient the discs are the complex lines `u_{0, ξ}(w) = w ξ`.
* For a second such coefficient `Q'`, if `Q - Q'` and `DQ - DQ'` are bounded by `ε` on the closed
  ball of radius `4`, then on the unit disc the discs `u_{Q, ξ}` and `u_{Q', ξ'}` and their
  derivatives differ by at most `C (‖ξ - ξ'‖ + ε)`. With `Q' = 0` this says that the disc of a
  coefficient bounded by `ε` is within `C ε` of the complex line `w ↦ w ξ` in the `C¹` norm. -/
theorem exists_pos_exists_conjWirtingerDeriv_eq_and_apply_smul_eq_and_norm_sub_le :
    ∃ η > 0, ∃ C ≥ 0, ∃ u : (F → F →L[ℝ] F) → F → ℂ → F,
      (∀ Q : F → F →L[ℝ] F, Q 0 = 0 →
        (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ Q x) →
        (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ Q x‖ ≤ η) →
        (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ Q x - fderiv ℝ Q y‖ ≤ η * ‖x - y‖) →
        (∀ ξ : F, ‖ξ‖ ≤ 1 →
          ContDiffOn ℝ 1 (u Q ξ) (ball 0 2) ∧ u Q ξ 0 = 0 ∧ fderiv ℝ (u Q ξ) 0 1 = ξ ∧
          (∀ z ∈ closedBall (0 : ℂ) 1, ‖u Q ξ z‖ ≤ 2) ∧
          ∀ z ∈ ball (0 : ℂ) 2⁻¹,
            conjWirtingerDeriv (u Q ξ) z 1 = Q (u Q ξ z) (wirtingerDeriv (u Q ξ) z 1)) ∧
          ((∀ x ∈ closedBall (0 : F) 2, ∀ v, Q x (I • v) = -(I • Q x v)) →
            ∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ c : ℂ, ‖c‖ = 1 → ∀ w, u Q (c • ξ) w = u Q ξ (c * w))) ∧
      (∀ ξ : F, ‖ξ‖ ≤ 1 → ∀ w, u 0 ξ w = w • ξ) ∧
      ∀ Q Q' : F → F →L[ℝ] F, Q 0 = 0 → Q' 0 = 0 →
        (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ Q x) →
        (∀ x ∈ closedBall (0 : F) 4, DifferentiableAt ℝ Q' x) →
        (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ Q x‖ ≤ η) →
        (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ Q' x‖ ≤ η) →
        (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ Q x - fderiv ℝ Q y‖ ≤ η * ‖x - y‖) →
        (∀ x ∈ closedBall (0 : F) 4, ∀ y ∈ closedBall (0 : F) 4,
          ‖fderiv ℝ Q' x - fderiv ℝ Q' y‖ ≤ η * ‖x - y‖) →
        ∀ (ξ ξ' : F) (ε : ℝ), ‖ξ‖ ≤ 1 → ‖ξ'‖ ≤ 1 →
          (∀ x ∈ closedBall (0 : F) 4, ‖Q x - Q' x‖ ≤ ε) →
          (∀ x ∈ closedBall (0 : F) 4, ‖fderiv ℝ Q x - fderiv ℝ Q' x‖ ≤ ε) →
          ∀ z ∈ closedBall (0 : ℂ) 1, ‖u Q ξ z - u Q' ξ' z‖ ≤ C * (‖ξ - ξ'‖ + ε) ∧
            ‖fderiv ℝ (u Q ξ) z - fderiv ℝ (u Q' ξ') z‖ ≤ C * (‖ξ - ξ'‖ + ε) := by
  set D := ‖derivOp F‖
  set X := ‖cutoffHolder‖
  have hD : 0 ≤ D := (derivOp F).opNorm_nonneg
  have hX : 0 ≤ X := norm_nonneg _
  have hη := (smallness_pos (F := F)).le
  refine ⟨smallness F, smallness_pos, 1 + 40 * D * X * (2 * smallness F + 1), by positivity,
    fun Q ξ ↦ discMap ξ ⇑(discSource (wirtingerAtOne F) Q ξ).val, fun Q hQ0 hd h1 h2 ↦ ?_,
    fun ξ hξ w ↦ discMap_discSource_zero norm_wirtingerAtOne_le hξ w,
    fun Q Q' hQ0 hQ0' hd hd' h1 h1' h2 h2' ξ ξ' ε hξ hξ' hε0 hε1 z hz ↦ ?_⟩
  · have hQ : SmallCoeff F Q := ⟨hQ0, hd, h1, h2⟩
    refine ⟨fun ξ hξ ↦ ?_, fun hQI ξ hξ c hc w ↦ ?_⟩
    · obtain ⟨hC, h0, h1', hb, heq⟩ := discSource_props norm_wirtingerAtOne_le hξ hQ
      refine ⟨hC, h0, h1', hb, fun z hz ↦ ?_⟩
      rw [conjWirtingerDeriv_discMap ξ (differentiableAt_cauchyTransform _ z), heq z hz,
        wirtingerAtOne_apply, wirtingerDeriv_eq_complexLinearPart]
    · dsimp only
      rw [discSource_smul hξ hQ hQI hc]
      exact discMap_rotSource hc ξ (discSource_apply_zero norm_wirtingerAtOne_le hξ hQ) w
  · have hQ : SmallCoeff F Q := ⟨hQ0, hd, h1, h2⟩
    have hQ' : SmallCoeff F Q' := ⟨hQ0', hd', h1', h2'⟩
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hε0 0 (mem_closedBall_self (by norm_num)))
    have hs := norm_discSource_sub_discSource_le norm_wirtingerAtOne_le hξ hξ' hQ hQ' hε0 hε1
    obtain ⟨hv, hdv⟩ := norm_discMap_sub_discMap_le_and_norm_fderiv_sub_le ξ ξ'
      (discSource (wirtingerAtOne F) Q ξ) (discSource (wirtingerAtOne F) Q' ξ') hz
    -- `‖ξ - ξ'‖ + 2 D ‖h - h'‖ ≤ ‖ξ - ξ'‖ + 4 D X (20 η ‖ξ - ξ'‖ + 10 ε) ≤ C (‖ξ - ξ'‖ + ε)`.
    have hb : ‖ξ - ξ'‖ + 2 * D * ‖discSource (wirtingerAtOne F) Q ξ -
        discSource (wirtingerAtOne F) Q' ξ'‖ ≤
          (1 + 40 * D * X * (2 * smallness F + 1)) * (‖ξ - ξ'‖ + ε) := by
      have hDX : 0 ≤ D * X := mul_nonneg hD hX
      have hs' := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * D)
      nlinarith [norm_nonneg (ξ - ξ'), mul_nonneg hDX hε, mul_nonneg hDX (norm_nonneg (ξ - ξ')),
        mul_nonneg (mul_nonneg hDX hη) hε]
    exact ⟨hv.trans hb, hdv.trans hb⟩

end FiniteDim

end BeltramiDisc

end TauCeti
