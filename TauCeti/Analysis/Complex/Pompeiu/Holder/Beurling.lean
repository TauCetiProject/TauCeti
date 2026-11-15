/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Higher
public import TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy
public import TauCeti.Analysis.Complex.Wirtinger.IteratedFDeriv
import TauCeti.Analysis.Complex.Wirtinger.Holder

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

section Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] {k : ℕ} {α : ℝ≥0} {c : ℂ} {r R : ℝ}

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
      ((wirtingerOneCurryRight (F := F) i).compLeftContinuousBounded (closedBall c R)).comp
        ((ContinuousLinearMap.proj (R := ℝ)
            (φ := fun j : Fin (k + 2) ↦ closedBall c R →ᵇ (ℂ [×j]→L[ℝ] F))
            (⟨i + 1, by omega⟩ : Fin (k + 2))).comp
          (ContinuousLinearMap.fst ℝ _ _))).prod
    ((HolderSpace.compLeftL (wirtingerOneCurryRight k)).comp (ContinuousLinearMap.snd ℝ _ _))

private theorem beurlingPost_apply_fst
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) (i : Fin (k + 1)) (x : closedBall c R) :
    (beurlingPost k α c R u).1 i x = wirtingerOneCurryRight i (u.1 ⟨i + 1, by omega⟩ x) :=
  (rfl)

private theorem beurlingPost_apply_snd
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) (x : closedBall c R) :
    (beurlingPost k α c R u).2 x = wirtingerOneCurryRight k (u.2 x) :=
  HolderSpace.compLeftL_apply _ _ x

private theorem norm_beurlingPost_apply_le
    (u : ((i : Fin (k + 2)) → closedBall c R →ᵇ (ℂ [×i]→L[ℝ] F)) ×
      HolderSpace α (closedBall c R) (ℂ [×k + 1]→L[ℝ] F)) :
    ‖beurlingPost k α c R u‖ ≤ ‖u‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le_max ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x ↦ ?_
    rw [beurlingPost_apply_fst]
    exact (norm_wirtingerOneCurryRight_apply_le _ _).trans
      (((u.1 ⟨i + 1, by omega⟩).norm_coe_le_norm x).trans (norm_le_pi_norm u.1 _))
  · have hg : ‖wirtingerOneCurryRight (F := F) k‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
        simpa only [one_mul] using norm_wirtingerOneCurryRight_apply_le k y
    exact ((HolderSpace.compLeftL (α := α) (X := closedBall c R)
      (wirtingerOneCurryRight k)).le_of_opNorm_le
      ((HolderSpace.norm_compLeftL_le _).trans hg) u.2).trans_eq (one_mul _)

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
  exact congrArg (wirtingerOneCurryRight i)
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
  exact congrArg (wirtingerOneCurryRight k) (cauchyTransformCkCLM_apply_snd k hα hα1 hr hR f x)

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
