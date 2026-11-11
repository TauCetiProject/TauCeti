/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Derivatives of maps built from a continuous bilinear map

The quadratic map `z ↦ B z z` attached to a continuous bilinear map `B : E →L[𝕜] E →L[𝕜] F` is
smooth, with derivative at `y` the polarization `B.flip y + B y` of `B` evaluated at `y`; since
that derivative is linear in `y`, the second derivative is the constant continuous linear map
`B.flip + B`. This is the derivative computation behind the local model of a nondegenerate
critical point, but it depends on nothing beyond the bilinear chain rule
`ContinuousLinearMap.hasStrictFDerivAt_of_bilinear` and the smoothness of bounded bilinear maps.

The same chain rule differentiates the pairing `y ↦ B (u y) (∂_w u y)` of a `C²` map `u` with one
of its directional derivatives, the one-form `x ↦ B x` pulled back along `u` and evaluated in the
direction `w`; its derivative involves the second derivative of `u`.

## Main results

* `ContinuousLinearMap.contDiff_apply_self`: `z ↦ B z z` is `C^n` for every `n`, and its
  corollary `ContinuousLinearMap.differentiable_apply_self`.
* `ContinuousLinearMap.hasStrictFDerivAt_apply_self`: `z ↦ B z z` is strictly
  differentiable at `y`, with derivative the polarization of `B` evaluated at `y`.
* `ContinuousLinearMap.hasFDerivAt_apply_self`, and its `fderiv` form
  `ContinuousLinearMap.fderiv_apply_self`.
* `ContinuousLinearMap.fderiv_fderiv_apply_self`: the second derivative of `z ↦ B z z` is
  the constant `B.flip + B`.
* `ContinuousLinearMap.hasFDerivAt_bilinear_fderiv_apply`: the derivative of
  `y ↦ B (u y) (∂_w u y)` at a point where `u` is `C²`.
* `ContinuousLinearMap.contDiffAt_bilinear_fderiv_apply`: `y ↦ B (u y) (∂_w u y)` is `C^n` at a
  point where `u` is `C^(n+1)`.
* `ContinuousLinearMap.contDiff_precomp_comp`: the pullback `(v, w) ↦ B (L v) (L w)` of a
  continuous bilinear map `B` along a continuous linear map `L` depends smoothly on `(B, L)`.
* `ContDiffOn.clm_bilinearComp`: the pullback `B x (L₁ x ·) (L₂ x ·)` of a smooth family of
  bilinear maps along smooth families of linear maps is smooth.
* `ContinuousLinearMap.iteratedFDeriv_pullbackBilinL_comp`: the iterated derivatives of a family
  of bilinear maps, read along `u` and pulled back along `u`, are those of the family, taken in
  the directions of the images under `u` and pulled back along `u`.
* `ContinuousLinearMap.apply_self_fderiv_eq_of_eventuallyEq`: a local map fixing zero and
  preserving quadratic functions has a derivative preserving those quadratic functions.
* `ContinuousAt.hasFDerivAt_clm_apply_zero`: evaluating a family `A q` of continuous linear maps,
  continuous at `p`, on a vector `x` is differentiable at `(0, p)`, with no differentiability in
  `q`. For instance, the tube `(u, t) ↦ γ t + A t u` around a curve `γ`, built from a merely
  continuous frame `A t` of normal vectors, is differentiable along the curve.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}


/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is `C^n` for every `n`. -/
theorem _root_.ContinuousLinearMap.contDiff_apply_self (B : E →L[𝕜] E →L[𝕜] F) : ContDiff 𝕜 n
    (fun z ↦ B z z) :=
  B.isBoundedBilinearMap.contDiff.comp₂ contDiff_id contDiff_id

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable. -/
theorem _root_.ContinuousLinearMap.differentiable_apply_self (B : E →L[𝕜] E →L[𝕜] F) :
    Differentiable 𝕜 (fun z ↦ B z z) :=
  (ContinuousLinearMap.contDiff_apply_self (n := 1) B).differentiable one_ne_zero

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is strictly differentiable at
`y`, with derivative the polarization of `B` evaluated at `y`. -/
theorem _root_.ContinuousLinearMap.hasStrictFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasStrictFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have h : HasStrictFDerivAt (fun z ↦ B z z)
      (B.precompR E y (ContinuousLinearMap.id 𝕜 E) +
        B.precompL E (ContinuousLinearMap.id 𝕜 E) y) y :=
    B.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id y) (hasStrictFDerivAt_id y)
  convert h using 1
  ext v
  simp [add_comm]

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable at `y`, with
derivative the polarization of `B` evaluated at `y`. -/
theorem _root_.ContinuousLinearMap.hasFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y :=
  (ContinuousLinearMap.hasStrictFDerivAt_apply_self B y).hasFDerivAt

/-- At `y`, the differential of `z ↦ B z z` is `B.flip y + B y`. -/
@[simp]
theorem _root_.ContinuousLinearMap.fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fun z ↦ B z z) y = B.flip y + B y :=
  (ContinuousLinearMap.hasFDerivAt_apply_self B y).fderiv

/-- The second derivative of `z ↦ B z z` is the constant `B.flip + B`. -/
@[simp]
theorem _root_.ContinuousLinearMap.fderiv_fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fderiv 𝕜 fun z ↦ B z z) y = B.flip + B := by
  have hEq : (fderiv 𝕜 fun z ↦ B z z) = fun z ↦ (B.flip + B) z := by
    funext z
    rw [ContinuousLinearMap.fderiv_apply_self, add_apply]
  rw [hEq]
  exact (B.flip + B).fderiv

/-- The derivative of `y ↦ B (u y) (∂_w u y)` in the direction `v`, at a point where `u` is `C²`,
is `B (u) (∂_v ∂_w u) + B (∂_v u) (∂_w u)`. -/
theorem _root_.ContinuousLinearMap.hasFDerivAt_bilinear_fderiv_apply (B : F →L[𝕜] F →L[𝕜] G)
    {u : E → F} {z : E} (hu : ContDiffAt 𝕜 2 u z) (w : E) :
    HasFDerivAt (fun y ↦ B (u y) (fderiv 𝕜 u y w))
      (B.precompR E (u z) ((fderiv 𝕜 (fderiv 𝕜 u) z).flip w) +
        B.precompL E (fderiv 𝕜 u z) (fderiv 𝕜 u z w)) z :=
  B.hasFDerivAt_of_bilinear (hu.differentiableAt (by norm_num)).hasFDerivAt
    (hu.hasFDerivAt_fderiv_apply le_rfl w)

/-- If `u` is `C^(n+1)` at `z`, then `y ↦ B (u y) (∂_w u y)` is `C^n` at `z`. -/
theorem _root_.ContinuousLinearMap.contDiffAt_bilinear_fderiv_apply (B : F →L[𝕜] F →L[𝕜] G)
    {u : E → F} {z : E} (hu : ContDiffAt 𝕜 (n + 1) u z) (w : E) :
    ContDiffAt 𝕜 n (fun y ↦ B (u y) (fderiv 𝕜 u y w)) z :=
  (B.contDiff.contDiffAt.comp z (hu.of_le le_self_add)).clm_apply
    ((hu.fderiv_right le_rfl).clm_apply contDiffAt_const)

/-- The pullback `(v, w) ↦ B (L v) (L w)` of a continuous bilinear map `B` along a continuous linear
map `L` is `C^n` as a function of the pair `(B, L)`. -/
theorem _root_.ContinuousLinearMap.contDiff_precomp_comp :
    ContDiff 𝕜 n fun p : (F →L[𝕜] F →L[𝕜] G) × (E →L[𝕜] F) ↦
      (ContinuousLinearMap.precomp G p.2).comp (p.1.comp p.2) := by
  have h : (fun p : (F →L[𝕜] F →L[𝕜] G) × (E →L[𝕜] F) ↦
      (ContinuousLinearMap.precomp G p.2).comp (p.1.comp p.2)) = fun p ↦
      ((ContinuousLinearMap.compL 𝕜 E F G).flip p.2).comp (p.1.comp p.2) := by
    ext p v w
    rfl
  rw [h]
  exact ((ContinuousLinearMap.compL 𝕜 E F G).flip.contDiff.comp contDiff_snd).clm_comp
    (contDiff_fst.clm_comp contDiff_snd)

/-- The pullback `(v, w) ↦ B x (L₁ x v) (L₂ x w)` of a `C^n` family of continuous bilinear maps
along two `C^n` families of continuous linear maps is `C^n`. -/
theorem _root_.ContDiffOn.clm_bilinearComp {P E₁ E₂ F₁ F₂ : Type*} [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂]
    [NormedSpace 𝕜 E₂] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂]
    [NormedSpace 𝕜 F₂] {s : Set P} {B : P → F₁ →L[𝕜] F₂ →L[𝕜] G} {L₁ : P → E₁ →L[𝕜] F₁}
    {L₂ : P → E₂ →L[𝕜] F₂} (hB : ContDiffOn 𝕜 n B s) (hL₁ : ContDiffOn 𝕜 n L₁ s)
    (hL₂ : ContDiffOn 𝕜 n L₂ s) :
    ContDiffOn 𝕜 n (fun x ↦ (B x).bilinearComp (L₁ x) (L₂ x)) s := by
  refine (((ContinuousLinearMap.compL 𝕜 E₂ F₂ G).flip.contDiff.comp_contDiffOn hL₂).clm_comp
    (hB.clm_comp hL₁)).congr fun x _ ↦ ?_
  -- Both sides pull `B x` back along `L₁ x` in the first slot and `L₂ x` in the second.
  ext u v
  rfl

noncomputable section PullbackBilin

-- Cache the canonical operator-space instances: searching for the structure on nested operator
-- spaces otherwise fails.
private local instance : NormedAddCommGroup (E →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace 𝕜 (E →L[𝕜] G) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (F →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace 𝕜 (F →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

/-- The iterated derivatives of a family `B` of bilinear maps, read along a continuous linear map
`u` and pulled back along `u`, are those of `B` at the image point, taken in the directions of the
images under `u` and pulled back along `u`. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_pullbackBilinL_comp
    {B : F → F →L[𝕜] F →L[𝕜] G} {U : Set F} (hU : IsOpen U) (hB : ContDiffOn 𝕜 n B U)
    (u : E →L[𝕜] F) {z : E} (hz : u z ∈ U) {m : ℕ} (hm : m ≤ n) :
    iteratedFDeriv 𝕜 m (ContinuousLinearMap.pullbackBilinL u ∘ (B ∘ u)) z =
      (ContinuousLinearMap.pullbackBilinL u).compContinuousMultilinearMap
        ((iteratedFDeriv 𝕜 m B (u z)).compContinuousLinearMap fun _ ↦ u) := by
  have hU' : IsOpen (u ⁻¹' U) := hU.preimage u.continuous
  have hBu : ContDiffAt 𝕜 n (B ∘ u) z :=
    (hB.contDiffAt (hU.mem_nhds hz)).comp z u.contDiff.contDiffAt
  rw [(ContinuousLinearMap.pullbackBilinL u).iteratedFDeriv_comp_left hBu hm,
    ← iteratedFDerivWithin_of_isOpen m hU' hz, ← iteratedFDerivWithin_of_isOpen m hU hz,
    u.iteratedFDerivWithin_comp_right hB hU.uniqueDiffOn hU'.uniqueDiffOn hz hm]

end PullbackBilin

/-- If a family `A` of continuous linear maps is continuous at `p`, then `(x, q) ↦ A q x` is
differentiable at `(0, p)`, with derivative `(x, q) ↦ A p x`. No differentiability in `q` is
needed. -/
theorem _root_.ContinuousAt.hasFDerivAt_clm_apply_zero {P : Type*} [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] {A : P → E →L[𝕜] F} {p : P} (hA : ContinuousAt A p) :
    HasFDerivAt (fun q : E × P ↦ A q.2 q.1) ((A p).comp (ContinuousLinearMap.fst 𝕜 E P))
      (0, p) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrem : (fun h : E × P ↦ A ((0, p) + h).2 ((0, p) + h).1 - A (0, p).2 (0, p).1 -
      (A p).comp (ContinuousLinearMap.fst 𝕜 E P) h) = fun h ↦ (A (p + h.2) - A p) h.1 := by
    ext h
    simp
  have htend : Filter.Tendsto (fun h : E × P ↦ ‖A (p + h.2) - A p‖) (nhds 0) (nhds 0) := by
    have : Filter.Tendsto (fun h : E × P ↦ A (p + h.2)) (nhds 0) (nhds (A p)) := by
      refine hA.tendsto.comp ?_
      simpa using (tendsto_const_nhds (x := p)).add
        ((continuous_snd (X := E) (Y := P)).tendsto (0 : E × P))
    simpa using (this.sub_const (A p)).norm
  rw [hrem]
  refine Asymptotics.IsBigO.trans_isLittleO
    (g := fun h : E × P ↦ ‖A (p + h.2) - A p‖ * ‖h‖) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h ↦ ?_)
    rw [one_mul, Real.norm_of_nonneg (by positivity)]
    exact ((A (p + h.2) - A p).le_opNorm h.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le h) (norm_nonneg _))
  · have h := ((Asymptotics.isLittleO_one_iff ℝ).2 htend).mul_isBigO
      (Asymptotics.isBigO_refl (fun h : E × P ↦ ‖h‖) (nhds 0))
    simp only [one_mul] at h
    exact h.trans_isBigO (Asymptotics.isBigO_norm_left.2 (Asymptotics.isBigO_refl _ _))

end TauCeti

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative at the origin of a local map preserving quadratic functions also preserves
those quadratic functions. Only differentiability at the origin is required; the bilinear forms
need not be symmetric or nondegenerate. -/
theorem apply_self_fderiv_eq_of_eventuallyEq (B : F →L[ℝ] F →L[ℝ] ℝ)
    (C : E →L[ℝ] E →L[ℝ] ℝ) {φ : E → F} (hφ : DifferentiableAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (h : (fun y ↦ B (φ y) (φ y)) =ᶠ[nhds 0] (fun y ↦ C y y)) (v : E) :
    B (fderiv ℝ φ 0 v) (fderiv ℝ φ 0 v) = C v v := by
  -- Rescale along the ray through v; quadratic homogeneity removes the scale.
  have hlim := hφ.hasFDerivAt.lim_real v
  simp only [zero_add, hφ0, sub_zero] at hlim
  have hquad := (B.continuous₂.tendsto _).comp (hlim.prodMk_nhds hlim)
  have hnear : Filter.Tendsto (fun t : ℝ ↦ t⁻¹ • v) Filter.atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const v
  have heq : (fun t : ℝ ↦ B (t • φ (t⁻¹ • v)) (t • φ (t⁻¹ • v)))
      =ᶠ[Filter.atTop] (fun _ ↦ C v v) := by
    filter_upwards [hnear.eventually h, Filter.eventually_ne_atTop 0] with t ht ht0
    simp only [map_smul, smul_apply, smul_smul]
    rw [ht]
    simp [mul_assoc, ht0]
  exact tendsto_nhds_unique hquad (tendsto_const_nhds.congr' heq.symm)

end ContinuousLinearMap

end
