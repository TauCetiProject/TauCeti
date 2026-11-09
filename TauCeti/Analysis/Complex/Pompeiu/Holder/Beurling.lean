/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Higher
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
import TauCeti.Analysis.Complex.Wirtinger.Holder
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# The Beurling operator on `C^{k,α}` data

The Beurling operator is `B = ∂ T`, the Wirtinger derivative `∂ = (∂_s - i ∂_t) / 2` of the
normalized Cauchy transform `T f w = π⁻¹ ∫ (w - z)⁻¹ • f z`. For every `k : ℕ` and `0 < α < 1`
it maps `C^{k,α}` data supported in a fixed disc `closedBall c r` boundedly to `C^{k,α}` functions
on each output disc `closedBall c R`.

The operator is the Wirtinger component of `TauCeti.cauchyTransformCkCLM`: the derivative of
order `i` of `B f` is the derivative of order `i + 1` of `T f`, curried on the right and followed
by the fixed real-linear map `φ ↦ (φ 1 - i φ i) / 2` of norm at most one. So the operator norm of
the Beurling operator is at most that of the Cauchy transform on the same discs.

## Main results

* `TauCeti.beurlingCkCLM`: the Beurling operator as a bounded real-linear operator from `C^{k,α}`
  data supported in `closedBall c r` to the derivative fields of `B f` of orders through `k` on
  `closedBall c R` with the supremum norm, together with the `α`-Hölder field of order `k`.
* `TauCeti.beurlingCkCLM_apply_fst`, `TauCeti.beurlingCkCLM_apply_snd`,
  `TauCeti.beurlingCkCLM_apply_fst_zero`: its components are the iterated derivatives of the
  actual function `w ↦ ∂ (T f) w 1`.
* `TauCeti.norm_beurlingCkCLM_apply_le`: `‖B f‖ ≤ ‖T f‖` in these norms, so its operator norm
  is at most that of `TauCeti.cauchyTransformCkCLM`.
* `TauCeti.continuous_beurlingCkCLM_comp`: continuity in parameters for families of data with
  common support.
* `TauCeti.beurlingCkCLM_apply_fst_zero_ae_eq_beurlingLp`: for smooth data the value field agrees
  almost everywhere on the output disc with the Beurling operator on `Lᵖ(ℂ)`, `1 < p < ∞`.
* `TauCeti.holderOnWith_wirtingerDeriv_cauchyTransform_norm_rpow_mul`: the cone-point check, in
  derivative form: for the source `‖z‖ ^ α χ(z)` the function `B f` is `α`-Hölder on every
  closed disc about `0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 4.4.
-/

public noncomputable section

open Complex Metric MeasureTheory Set
open scoped NNReal ENNReal ContDiff BoundedContinuousFunction

namespace TauCeti

section Postcomposition

variable {α : ℝ≥0} {X Y Y' : Type*} [MetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Y'] [NormedSpace ℝ Y']

omit [NormedSpace ℝ Y'] in
/-- Postcomposition with a `K`-Lipschitz map multiplies the Hölder constant by `K`. -/
private theorem holderWith_postcomp {g : Y → Y'} {K : ℝ≥0} (hg : LipschitzWith K g)
    (h : HolderSpace α X Y) :
    HolderWith (K * nnHolderNorm α (h : X → Y)) α (fun x ↦ g (h x)) := by
  have hc := (holderWith_one.2 hg).comp h.holderWith
  rw [NNReal.coe_one, NNReal.rpow_one, one_mul] at hc
  exact hc

/-- Postcomposition of bounded Hölder functions with a continuous linear map. -/
private def holderPostcomp (g : Y →L[ℝ] Y') (h : HolderSpace α X Y) : HolderSpace α X Y' :=
  HolderSpace.ofBoundedContinuousFunction
    (g.compLeftContinuousBounded X h.toBoundedContinuousFunction) (by
      have e : ⇑(g.compLeftContinuousBounded X h.toBoundedContinuousFunction) =
          fun x ↦ g (h x) := funext fun x ↦ by
        rw [ContinuousLinearMap.compLeftContinuousBounded_apply,
          HolderSpace.toBoundedContinuousFunction_apply]
      rw [e]
      exact (holderWith_postcomp g.lipschitzWith h).memHolder)

private theorem holderPostcomp_apply (g : Y →L[ℝ] Y') (h : HolderSpace α X Y) (x : X) :
    holderPostcomp g h x = g (h x) := by
  rw [holderPostcomp, HolderSpace.ofBoundedContinuousFunction_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    HolderSpace.toBoundedContinuousFunction_apply]

/-- If `‖g y‖ ≤ K ‖y‖` for all `y`, postcomposition with `g` multiplies the Hölder-space norm by
at most `K`. -/
private theorem norm_holderPostcomp_le (g : Y →L[ℝ] Y') {K : ℝ≥0} (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖)
    (h : HolderSpace α X Y) : ‖holderPostcomp g h‖ ≤ K * ‖h‖ := by
  have hL : LipschitzWith K g := by
    simpa only [Real.toNNReal_coe] using AddMonoidHomClass.lipschitz_of_bound g (K : ℝ) hg
  have hH : HolderWith (K * nnHolderNorm α (h : X → Y)) α (holderPostcomp g h) := by
    have e : ⇑(holderPostcomp g h) = fun x ↦ g (h x) :=
      funext fun x ↦ holderPostcomp_apply g h x
    rw [e]
    exact holderWith_postcomp hL h
  refine (HolderSpace.norm_le_of_norm_le_of_holderWith
    (M := K * ‖h.toBoundedContinuousFunction‖) (by positivity) (fun x ↦ ?_) hH).trans ?_
  · rw [holderPostcomp_apply, ← HolderSpace.toBoundedContinuousFunction_apply]
    exact (hg _).trans (mul_le_mul_of_nonneg_left
      (h.toBoundedContinuousFunction.norm_coe_le_norm x) K.coe_nonneg)
  · rw [HolderSpace.norm_def h, mul_add, HolderSpace.coe_toBoundedContinuousFunction]
    push_cast
    exact le_rfl

/-- Postcomposition of bounded Hölder functions with a continuous linear map `g`, as a
continuous linear map. -/
private def holderPostcompL (g : Y →L[ℝ] Y') : HolderSpace α X Y →L[ℝ] HolderSpace α X Y' :=
  LinearMap.mkContinuous
    { toFun := holderPostcomp g
      map_add' h₁ h₂ := HolderSpace.ext fun x ↦ by
        simp only [holderPostcomp_apply, HolderSpace.add_apply, map_add]
      map_smul' a h := HolderSpace.ext fun x ↦ by
        simp only [holderPostcomp_apply, HolderSpace.smul_apply, map_smul, RingHom.id_apply] }
    ‖g‖ fun h ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact norm_holderPostcomp_le g (K := ‖g‖₊) g.le_opNorm h

private theorem holderPostcompL_apply (g : Y →L[ℝ] Y') (h : HolderSpace α X Y) :
    holderPostcompL g h = holderPostcomp g h :=
  (rfl)

end Postcomposition

section Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] {k : ℕ} {α : ℝ≥0} {c : ℂ} {r R : ℝ}

/-- The complex-linear part of a real-linear map `φ : ℂ → F`, evaluated at `1`:
`φ ↦ (φ 1 - i φ i) / 2`. Applied to `D g x` it gives `∂ g x 1`. -/
private def wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun φ := (2 : ℂ)⁻¹ • (φ 1 - I • φ (I • 1))
      map_add' φ ψ := by
        simp only [FunLike.coe_add, Pi.add_apply, smul_add, smul_sub]
        abel
      map_smul' a φ := by
        simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
        rw [smul_comm I a, ← smul_sub]
        exact smul_comm _ _ _ }
    1 fun φ ↦ by
      have h1 : ‖-(I • φ (I • 1))‖ ≤ ‖φ‖ := by
        rw [norm_neg, norm_smul, norm_I, one_mul]
        have h := φ.le_opNorm (I • (1 : ℂ))
        rwa [norm_smul, norm_I, norm_one, mul_one, mul_one] at h
      have h2 : ‖φ 1‖ ≤ ‖φ‖ := by simpa using φ.le_opNorm 1
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul, sub_eq_add_neg]
      exact norm_two_inv_smul_add_le h2 h1

private theorem wirtingerOne_apply (φ : ℂ →L[ℝ] F) :
    wirtingerOne φ = (2 : ℂ)⁻¹ • (φ 1 - I • φ (I • 1)) :=
  (rfl)

private theorem norm_wirtingerOne_le : ‖(wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The derivative of order `i` of `∂ g (·) 1` in terms of the derivative of order `i + 1` of
`g`: curry on the right, then apply `wirtingerOne`. -/
private def beurlingFieldMap (i : ℕ) : (ℂ [×i + 1]→L[ℝ] F) →L[ℝ] (ℂ [×i]→L[ℝ] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ ℂ) (ℂ →L[ℝ] F) F
      wirtingerOne).comp
    (continuousMultilinearCurryRightEquiv' ℝ i ℂ F).toContinuousLinearEquiv.toContinuousLinearMap

private theorem beurlingFieldMap_apply (i : ℕ) (Φ : ℂ [×i + 1]→L[ℝ] F) :
    beurlingFieldMap i Φ =
      wirtingerOne.compContinuousMultilinearMap (continuousMultilinearCurryRightEquiv' ℝ i ℂ F Φ) :=
  (rfl)

private theorem norm_beurlingFieldMap_apply_le (i : ℕ) (Φ : ℂ [×i + 1]→L[ℝ] F) :
    ‖beurlingFieldMap i Φ‖ ≤ ‖Φ‖ := by
  have h := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F) (continuousMultilinearCurryRightEquiv' ℝ i ℂ F Φ)
  rw [LinearIsometryEquiv.norm_map] at h
  rw [beurlingFieldMap_apply]
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) norm_wirtingerOne_le)

/-- The function `w ↦ ∂ g w 1` is `wirtingerOne` applied to the real derivative of `g`. -/
private theorem wirtingerDeriv_one_eq_comp (g : ℂ → F) :
    (fun w ↦ wirtingerDeriv g w 1) = (wirtingerOne : (ℂ →L[ℝ] F) →L[ℝ] F) ∘ fderiv ℝ g := by
  -- The real action is uniquely determined by the compatible complex action.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  exact funext fun w ↦ by rw [Function.comp_apply, wirtingerOne_apply, wirtingerDeriv_apply]

/-- **The iterated derivatives of `∂ g (·) 1`.** For `g` of class `C^{i+1}`, the derivative of
order `i` of `w ↦ ∂ g w 1` is the image of the derivative of order `i + 1` of `g` under the fixed
map `beurlingFieldMap i`. -/
private theorem iteratedFDeriv_wirtingerDeriv_one {g : ℂ → F} {i : ℕ}
    (hg : ContDiff ℝ (i + 1 : ℕ) g) (x : ℂ) :
    iteratedFDeriv ℝ i (fun w ↦ wirtingerDeriv g w 1) x =
      beurlingFieldMap i (iteratedFDeriv ℝ (i + 1) g x) := by
  have hD : ContDiff ℝ i (fderiv ℝ g) := hg.fderiv_right (by push_cast; exact le_rfl)
  rw [wirtingerDeriv_one_eq_comp, wirtingerOne.iteratedFDeriv_comp_left hD.contDiffAt le_rfl,
    iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, beurlingFieldMap_apply,
    LinearIsometryEquiv.apply_symm_apply]

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
private theorem hasCompactSupport_source
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    HasCompactSupport (f : CkHolderSpace k α ℂ F) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r)
    (support_subset_of_mem_supportedCkHolderSubmodule f.property)

/-- The Beurling transform `B f = ∂ (T f)` of compactly supported `C^{k,α}` data is globally
`C^k`, for `0 < α < 1`. -/
theorem _root_.HasCompactSupport.contDiff_wirtingerDeriv_cauchyTransform_of_holderWith
    [FiniteDimensional ℂ F] {f : ℂ → F} (hc : HasCompactSupport f) (hα : 0 < α) (hα1 : α < 1)
    {H : ℝ≥0} (hf : ContDiff ℝ k f) (hH : HolderWith H α (iteratedFDeriv ℝ k f)) :
    ContDiff ℝ k (fun w ↦ wirtingerDeriv (cauchyTransform f) w 1) := by
  have hT := hc.contDiff_cauchyTransform_of_holderWith_iteratedFDeriv hα hα1 hf hH
  rw [wirtingerDeriv_one_eq_comp]
  exact wirtingerOne.contDiff.comp (hT.fderiv_right (by push_cast; exact le_rfl))

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`, as in
`TauCeti.cauchyTransformCkCLM`. It is local, and no public statement mentions it. -/
private local instance instNormedAddCommGroupBoundedContinuousFunction {X : Type*}
    [TopologicalSpace X] (n : ℕ) : NormedAddCommGroup (X →ᵇ (ℂ [×n]→L[ℝ] F)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`. It is local
for the same reason. -/
private local instance instNormedSpaceBoundedContinuousFunction {X : Type*} [TopologicalSpace X]
    (n : ℕ) : NormedSpace ℝ (X →ᵇ (ℂ [×n]→L[ℝ] F)) :=
  inferInstance

variable (k α c R) in
/-- The fixed map taking the Cauchy fields of orders through `k + 1` and the Hölder field of
order `k + 1` on `closedBall c R` to the Beurling fields of orders through `k` and the Hölder
field of order `k`. -/
private def beurlingPost :
    (((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
        HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) →L[ℝ]
      (((i : Fin (k + 1)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
        HolderSpace α (closedBall c R) (ℂ [×k]→L[ℝ] F)) :=
  (ContinuousLinearMap.pi fun i : Fin (k + 1) ↦
      ((beurlingFieldMap (F := F) i).compLeftContinuousBounded (closedBall c R)).comp
        ((ContinuousLinearMap.proj (R := ℝ)
            (φ := fun j : Fin (k + 2) ↦ closedBall c R →ᵇ (ℂ [×j]→L[ℝ] F))
            (⟨i + 1, by omega⟩ : Fin (k + 2))).comp
          (ContinuousLinearMap.fst ℝ _ _))).prod
    ((holderPostcompL (beurlingFieldMap k)).comp (ContinuousLinearMap.snd ℝ _ _))

private theorem beurlingPost_apply_fst
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) (i : Fin (k + 1)) (x : closedBall c R) :
    (beurlingPost k α c R u).1 i x = beurlingFieldMap i (u.1 ⟨i + 1, by omega⟩ x) :=
  (rfl)

private theorem beurlingPost_apply_snd
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) (x : closedBall c R) :
    (beurlingPost k α c R u).2 x = beurlingFieldMap k (u.2 x) :=
  holderPostcomp_apply _ _ x

private theorem norm_beurlingPost_apply_le
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) :
    ‖beurlingPost k α c R u‖ ≤ ‖u‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le_max ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [beurlingPost_apply_fst]
    exact (norm_beurlingFieldMap_apply_le _ _).trans
      (((u.1 ⟨i + 1, by omega⟩).norm_coe_le_norm x).trans (norm_le_pi_norm u.1 _))
  · have h := norm_holderPostcomp_le (beurlingFieldMap (F := F) k) (K := 1)
      (fun y ↦ by simpa only [NNReal.coe_one, one_mul] using norm_beurlingFieldMap_apply_le k y)
      u.2
    rw [NNReal.coe_one, one_mul] at h
    exact h

variable [FiniteDimensional ℂ F]

/-- **The Beurling operator as a bounded operator `C^{k,α}(D_r) → C^{k,α}(D_R)`.** For
`0 < α < 1`, it sends `C^{k,α}` data `f` supported in `closedBall c r` to the derivative fields
`x ↦ D^i (B f) x` of orders `i ≤ k` on `closedBall c R`, each with the supremum norm, together
with the `α`-Hölder field `D^k (B f)` on `closedBall c R`, where `B f = ∂ (T f)` is the Wirtinger
derivative of the Cauchy transform. It is the Wirtinger component of
`TauCeti.cauchyTransformCkCLM`, real linear and bounded, with operator norm at most that of the
Cauchy transform (`TauCeti.norm_beurlingCkCLM_apply_le`). -/
def beurlingCkCLM (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R) :
    supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r) →L[ℝ]
      ((i : Fin (k + 1)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
        HolderSpace α (closedBall c R) (ℂ [×k]→L[ℝ] F) :=
  (beurlingPost k α c R).comp (cauchyTransformCkCLM k hα hα1 hr hR)

/-- The derivative-field component of `TauCeti.beurlingCkCLM` is the iterated derivative of the
actual Beurling transform `w ↦ ∂ (T f) w 1`. -/
@[simp]
theorem beurlingCkCLM_apply_fst (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (i : Fin (k + 1)) (x : closedBall c R) :
    (beurlingCkCLM k hα hα1 hr hR f).1 i x =
      iteratedFDeriv ℝ i
        (fun w ↦ wirtingerDeriv (cauchyTransform (f : CkHolderSpace k α ℂ F)) w 1) x := by
  have hT := (hasCompactSupport_source f).contDiff_cauchyTransform_of_holderWith_iteratedFDeriv
    hα hα1 (f : CkHolderSpace k α ℂ F).contDiff
    (f : CkHolderSpace k α ℂ F).memHolder_iteratedFDeriv.holderWith
  have hi : (i : ℕ) + 1 ≤ k + 1 := by omega
  rw [iteratedFDeriv_wirtingerDeriv_one (hT.of_le (by exact_mod_cast hi)), beurlingCkCLM,
    ContinuousLinearMap.comp_apply, beurlingPost_apply_fst]
  exact congrArg (beurlingFieldMap i)
    (cauchyTransformCkCLM_apply_fst k hα hα1 hr hR f ⟨i + 1, by omega⟩ x)

/-- The Hölder component of `TauCeti.beurlingCkCLM` is the derivative of order `k` of the actual
Beurling transform `w ↦ ∂ (T f) w 1`. -/
@[simp]
theorem beurlingCkCLM_apply_snd (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (x : closedBall c R) :
    (beurlingCkCLM k hα hα1 hr hR f).2 x =
      iteratedFDeriv ℝ k
        (fun w ↦ wirtingerDeriv (cauchyTransform (f : CkHolderSpace k α ℂ F)) w 1) x := by
  have hT := (hasCompactSupport_source f).contDiff_cauchyTransform_of_holderWith_iteratedFDeriv
    hα hα1 (f : CkHolderSpace k α ℂ F).contDiff
    (f : CkHolderSpace k α ℂ F).memHolder_iteratedFDeriv.holderWith
  rw [iteratedFDeriv_wirtingerDeriv_one hT, beurlingCkCLM, ContinuousLinearMap.comp_apply,
    beurlingPost_apply_snd]
  exact congrArg (beurlingFieldMap k) (cauchyTransformCkCLM_apply_snd k hα hα1 hr hR f x)

/-- The value field of `TauCeti.beurlingCkCLM` is the Beurling transform `∂ (T f) x 1`. -/
theorem beurlingCkCLM_apply_fst_zero (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r))
    (x : closedBall c R) (m : Fin 0 → ℂ) :
    (beurlingCkCLM k hα hα1 hr hR f).1 0 x m =
      wirtingerDeriv (cauchyTransform (f : CkHolderSpace k α ℂ F)) x 1 := by
  rw [beurlingCkCLM_apply_fst]
  exact iteratedFDeriv_zero_apply m

/-- The norm of the Beurling transform `TauCeti.beurlingCkCLM` of `f` is at most that of the
Cauchy transform `TauCeti.cauchyTransformCkCLM` of `f` on the same discs; so the operator norm
of the Beurling operator is at most that of the Cauchy transform. -/
theorem norm_beurlingCkCLM_apply_le (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)) :
    ‖beurlingCkCLM k hα hα1 hr hR f‖ ≤ ‖cauchyTransformCkCLM k hα hα1 hr hR f‖ :=
  norm_beurlingPost_apply_le _

/-- **Continuity in parameters.** A continuous family of `C^{k,α}` data with common support in
`closedBall c r` has a continuous family of Beurling transforms in `C^{k,α}(closedBall c R)`. -/
theorem continuous_beurlingCkCLM_comp {P : Type*} [TopologicalSpace P] (k : ℕ) (hα : 0 < α)
    (hα1 : α < 1) (hr : 0 ≤ r) (hR : 0 ≤ R)
    {f : P → supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c r)}
    (hf : Continuous f) :
    Continuous fun t ↦ beurlingCkCLM k hα hα1 hr hR (f t) :=
  (beurlingCkCLM k hα hα1 hr hR).continuous.comp hf

end Operator

section Lp

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G] [FiniteDimensional ℂ G] [CompleteSpace G] {k : ℕ} {α : ℝ≥0} {c : ℂ}
  {r R : ℝ}

/-- **Agreement with the `Lᵖ` Beurling operator.** For smooth data in the supported `C^{k,α}`
space and `1 < p < ∞`, the value field of `TauCeti.beurlingCkCLM` agrees almost everywhere on
the output disc with the Beurling operator on `Lᵖ(ℂ)` applied to the data. -/
theorem beurlingCkCLM_apply_fst_zero_ae_eq_beurlingLp (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (hR : 0 ≤ R) (f : supportedCkHolderSubmodule (E := ℂ) (F := G) k α (closedBall c r))
    (hf : ContDiff ℝ ∞ (f : CkHolderSpace k α ℂ G)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (hfp : MemLp (f : CkHolderSpace k α ℂ G) p volume) :
    ∀ᵐ x ∂volume, ∀ hx : x ∈ closedBall c R,
      (beurlingCkCLM k hα hα1 hr hR f).1 0 ⟨x, hx⟩ (0 : Fin 0 → ℂ) =
        beurlingLp p hp hp_top (hfp.toLp _) x := by
  -- The real action is uniquely determined by the compatible complex action.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := G)
  have hc := hasCompactSupport_source f
  have h := hc.wirtingerDeriv_cauchyTransform_ae_eq_beurlingLp hf hp hp_top
  have hL : (hf.continuous.memLp_of_hasCompactSupport (p := p) (μ := volume) hc).toLp _ =
      hfp.toLp _ := rfl
  rw [hL] at h
  filter_upwards [h] with x hx hxR
  rw [beurlingCkCLM_apply_fst_zero]
  exact hx

end Lp

section ConePoint

/-- **The cone-point check for the Beurling operator.** For `0 < α < 1` and a compactly supported
`C¹` cutoff `χ`, the Beurling transform `∂ (T f) (·) 1` of the source `f z = ‖z‖ ^ α χ(z)` is
`α`-Hölder on every closed disc about `0`. -/
theorem holderOnWith_wirtingerDeriv_cauchyTransform_norm_rpow_mul {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fun w ↦ wirtingerDeriv (cauchyTransform fun z : ℂ ↦ ((‖z‖ ^ (α : ℝ) * χ z : ℝ) : ℂ)) w 1)
      (closedBall 0 R) := by
  obtain ⟨-, C, hC⟩ := contDiffOn_holderOnWith_fderiv_cauchyTransform_norm_rpow_mul hα hα1 hχ hc hR
  exact ⟨C * ‖(1 : ℂ)‖₊, hC.wirtingerDeriv_apply 1⟩

end ConePoint

end TauCeti
