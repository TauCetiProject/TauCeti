/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Continuous
public import TauCeti.Analysis.Sobolev.Trace.Kernel
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Sobolev.Wkp.Translation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Vanishing on part of the boundary of a half-space, by the trace

Let `H = TauCeti.normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, with
boundary hyperplane `{a} × E`, and let `T : W^{1,p}(H) → Lᵖ(E)` be its trace
`TauCeti.W1p.halfSpaceTrace`, `1 ≤ p < ∞`. For a set `Γ`, the space `W^{1,p}_Γ(H)`
(`TauCeti.w1pVanishingOnSubmodule`) is the closure of the restrictions to `H` of test functions on
the whole space supported away from `closure Γ`. This file identifies it by the trace when `Γ` is a
half-hyperplane of the boundary,

`Γ = {x | x.fst = a ∧ ℓ x.snd < c}` for a nonzero `ℓ : E →L[ℝ] ℝ`:

`u ∈ W^{1,p}_Γ(H) ↔ T u = 0` almost everywhere on `{y | ℓ y < c}`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero`).

This is the flat model of the characterization of `W^{1,p}_Γ(Ω)` by the trace on a Lipschitz
domain `Ω` with a Lipschitz boundary part `Γ`. After a partition of unity, a boundary chart is
flattened by a shear onto a half-space, and the relative boundary of `Γ` by a second shear of the
base onto the hyperplane `{ℓ = c}`. When `Γ` is instead the whole boundary hyperplane,
`W^{1,p}_Γ(H) = W^{1,p}_0(H)` (`TauCeti.w1pVanishingOnSubmodule_frontier`) is the kernel of the
trace (`TauCeti.W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero`).

## The argument

Every `u ∈ W^{1,p}_Γ(H)` has trace zero on `{y | (a, y) ∈ Γ}`, for any `Γ`: the generators are
continuous up to the boundary and vanish on `closure Γ`, and the trace is continuous
(`TauCeti.W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`).

Conversely, let `T u = 0` on `{ℓ < c}` and let `w` be a whole-space extension of `u`. Pick `v`
with `ℓ v = 1`. For `τ > 0` the translate `w_τ = w (· - (0, τ v))` has trace zero on the larger
set `{ℓ < c + τ}` (`TauCeti.W1p.hyperplaneTrace_translate_ae`). Split `w_τ` with a smooth cutoff
`ψ` of `ℓ x.snd`, equal to `0` for `ℓ x.snd ≤ c + τ / 3` and to `1` for `ℓ x.snd ≥ c + 2τ / 3`.

* The part `ψ w_τ` is cut off away from `closure Γ ⊆ {ℓ x.snd ≤ c}`, so its restriction to `H` lies
  in `W^{1,p}_Γ(H)` (`TauCeti.W1p.restrictL_contDiffSMul_mem_w1pVanishingOnSubmodule`).
* The part `(1 - ψ) w_τ` has trace `(1 - ψ) T w_τ = 0`, since `1 - ψ` vanishes where `T w_τ` need
  not, so it lies in `W^{1,p}_0(H) ⊆ W^{1,p}_Γ(H)` by the kernel theorem.

As `τ → 0` the translates converge to `w` in `W^{1,p}`, and `W^{1,p}_Γ(H)` is closed.

## Main declarations

* `TauCeti.W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`: functions vanishing on
  `Γ` have zero trace on `Γ`.
* `TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero`: on a half-hyperplane
  of the boundary, vanishing is exactly zero trace.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), Lemma 3.1 and
  Appendix A (the trace characterization of `H¹_Γ` in dimension three).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2 (functions of zero
  trace, by translation and cutoff).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal Gradient ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### A cutoff in a tangential direction -/

/-- The smooth cutoff `x ↦ σ(k (ℓ x.snd - c) - 1)` in the direction of `ℓ`, where `σ` is
`Real.smoothTransition`: for `k > 0` it vanishes where `ℓ x.snd ≤ c + 1 / k` and is one where
`ℓ x.snd ≥ c + 2 / k`. -/
private def tangentialCutoff (ℓ : E →L[ℝ] ℝ) (c k : ℝ) (x : WithLp 2 (ℝ × E)) : ℝ :=
  Real.smoothTransition (k * (ℓ x.snd - c) - 1)

private theorem contDiff_tangentialCutoff (ℓ : E →L[ℝ] ℝ) (c k : ℝ) :
    ContDiff ℝ ∞ (tangentialCutoff ℓ c k) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul
    ((ℓ.comp (WithLp.sndL 2 ℝ ℝ E)).contDiff.sub contDiff_const)).sub contDiff_const)

variable [CompleteSpace E] in
/-- The tangential cutoff and its gradient are bounded by a common constant. -/
private theorem exists_tangentialCutoff_bound (ℓ : E →L[ℝ] ℝ) (c : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∃ M, 0 ≤ M ∧ (∀ x, |tangentialCutoff ℓ c k x| ≤ M) ∧
      ∀ x, ‖∇ (tangentialCutoff ℓ c k) x‖ ≤ M := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  -- The inner map `x ↦ k (ℓ x.snd - c) - 1` is affine with linear part `k • ℓ ∘ snd`.
  let D : WithLp 2 (ℝ × E) →L[ℝ] ℝ := k • ℓ.comp (WithLp.sndL 2 ℝ ℝ E)
  have hD : ‖D‖ ≤ k * ‖ℓ‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le k _).trans ?_
    rw [Real.norm_of_nonneg hk]
    gcongr
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [one_mul]
      exact WithLp.norm_snd_le ℝ y
  refine ⟨max 1 (L * (k * ‖ℓ‖)), zero_le_one.trans (le_max_left _ _), fun x => ?_, fun x => ?_⟩
  · exact (Real.smoothTransition.abs_le_one _).trans (le_max_left _ _)
  · have hf : HasFDerivAt (fun y : WithLp 2 (ℝ × E) => k * (ℓ y.snd - c) - 1) D x := by
      have h := ((((ℓ.comp (WithLp.sndL 2 ℝ ℝ E)).hasFDerivAt (x := x)).sub_const c).const_mul
        k).sub_const 1
      simpa only [D, smul_smul, ContinuousLinearMap.comp_apply, WithLp.sndL_apply] using h
    have hψ : HasFDerivAt (tangentialCutoff ℓ c k)
        (deriv Real.smoothTransition (k * (ℓ x.snd - c) - 1) • D) x :=
      hf.smoothTransition
    rw [norm_gradient_eq_norm_fderiv, hψ.fderiv, norm_smul]
    exact (mul_le_mul (hL _) hD (norm_nonneg D) hL0).trans (le_max_right _ _)

/-- For `k > 0` the tangential cutoff is supported in `{x | 1 ≤ k (ℓ x.snd - c)}`. -/
private theorem tsupport_tangentialCutoff_subset (ℓ : E →L[ℝ] ℝ) (c k : ℝ) :
    tsupport (tangentialCutoff ℓ c k) ⊆ {x | 1 ≤ k * (ℓ x.snd - c)} :=
  closure_minimal (fun x hx => by
      by_contra h
      exact hx (Real.smoothTransition.zero_of_nonpos (by simp only [mem_ofPred_eq] at h; linarith)))
    (isClosed_le continuous_const (by fun_prop))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Zero trace on `Γ` -/

/-- **Functions vanishing on `Γ` have zero trace on `Γ`.** For `p < ∞` and any set `Γ`, the
half-space trace of every `u ∈ W^{1,p}_Γ(H)` vanishes almost everywhere on the set of `y` with
`(a, y) ∈ Γ`. -/
theorem W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (a : ℝ) {Γ : Set (WithLp 2 (ℝ × E))}
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ) :
    W1p.halfSpaceTrace hp a u =ᵐ[volume.restrict {y | WithLp.toLp 2 (a, y) ∈ Γ}] 0 := by
  set S := {y : E | WithLp.toLp 2 (a, y) ∈ Γ}
  -- Vanishing on `S` is the kernel of a continuous linear map, hence a closed condition.
  let R := (LpToLpRestrictCLM E ℝ ℝ volume p S).comp (W1p.halfSpaceTrace hp a)
  have hclosed : IsClosed {v | R v = 0} := isClosed_eq R.continuous continuous_const
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · exact (LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ) S _).1 h
  -- The trace of a generator is its restriction, which vanishes where `(a, y) ∈ closure Γ`.
  have hS : IsClosed {y : E | WithLp.toLp 2 (a, y) ∈ closure Γ} :=
    isClosed_closure.preimage (by fun_prop)
  rw [mem_ofPred, ContinuousLinearMap.comp_apply, LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ),
    W1p.halfSpaceTrace_restrictL]
  have hSS : S ⊆ {y : E | WithLp.toLp 2 (a, y) ∈ closure Γ} := fun _ hy => subset_closure hy
  filter_upwards [ae_restrict_of_ae (W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ),
    ae_restrict_of_ae_restrict_of_subset hSS (ae_restrict_mem hS.measurableSet)] with y hy hyΓ
  rw [hy, Pi.zero_apply]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right hyΓ)

/-! ### Translates of a function with zero trace on a half-hyperplane -/

/-- The translate `x ↦ w (x + (0, h))` of a whole-space Sobolev function in a direction parallel to
the boundary hyperplane. -/
private def tangentialTranslate (h : E) (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
  W1p.translate (V := ⊤) (h := WithLp.toLp 2 ((0 : ℝ), h)) (fun _ _ => by simp) w

/-- A whole-space function whose trace vanishes on `{ℓ < c + τ}` for some `τ > 0` restricts to an
element of `W^{1,p}_Γ(H)` for `Γ = {x | x.fst = a ∧ ℓ x.snd < c}`: split it by a cutoff in the
direction of `ℓ` into a part supported away from `closure Γ` and a part of zero trace. -/
private theorem restrictL_mem_w1pVanishingOnSubmodule_of_hyperplaneTrace
    (hp : p ≠ (∞ : ℝ≥0∞)) (a c : ℝ) (ℓ : E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0 < τ)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ y ∂(volume : Measure E), ℓ y < c + τ → W1p.hyperplaneTrace hp a w y = 0) :
    W1p.restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤) w ∈
      w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ ℓ x.snd < c} := by
  set Γ : Set (WithLp 2 (ℝ × E)) := {x | x.fst = a ∧ ℓ x.snd < c}
  have hk : 0 < 3 / τ := by positivity
  obtain ⟨M, hM, hψM, hgradM⟩ := exists_tangentialCutoff_bound ℓ c hk.le
  set ψ := tangentialCutoff ℓ c (3 / τ)
  have hψ := contDiff_tangentialCutoff ℓ c (3 / τ)
  set v := W1p.contDiffSMul ψ hψ hM (fun x _ => hψM x) (fun x _ => hgradM x) w
  -- `ψ w` is cut off away from `closure Γ ⊆ {ℓ x.snd ≤ c}`.
  have hΓ : closure Γ ⊆ {x | ℓ x.snd ≤ c} :=
    closure_minimal (fun x hx => hx.2.le) (isClosed_le (by fun_prop) continuous_const)
  have hv : W1p.restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤) v ∈
      w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ := by
    refine W1p.restrictL_contDiffSMul_mem_w1pVanishingOnSubmodule hp hψ hM _ _ ?_ w
    refine Set.disjoint_left.2 fun x hx hxΓ => ?_
    have h1 := tsupport_tangentialCutoff_subset ℓ c (3 / τ) hx
    have h2 : ℓ x.snd ≤ c := hΓ hxΓ
    simp only [mem_ofPred_eq] at h1
    nlinarith
  -- `(1 - ψ) w` has zero trace, so it lies in `W^{1,p}_0(H) ⊆ W^{1,p}_Γ(H)`.
  have hrest : W1p.restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤) w -
      W1p.restrictL le_top v ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ := by
    refine w1p0Submodule_le_w1pVanishingOnSubmodule (Set.disjoint_left.2 fun x hx hxH => ?_) ?_
    · rw [SetLike.mem_coe, mem_normalHalfSpace, hx.1] at hxH
      exact lt_irrefl a hxH
    rw [W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero hp, map_sub,
      W1p.halfSpaceTrace_restrictL, W1p.halfSpaceTrace_restrictL]
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [Lp.coeFn_sub (W1p.hyperplaneTrace hp a w) (W1p.hyperplaneTrace hp a v),
      W1p.hyperplaneTrace_contDiffSMul_ae hp a hψ hψM hgradM w, hw] with y hsub hψy hwy
    rw [hsub, Pi.sub_apply, hψy, Pi.zero_apply]
    by_cases hy : ℓ y < c + τ
    · rw [hwy hy, mul_zero, sub_zero]
    · have h1 : tangentialCutoff ℓ c (3 / τ) (WithLp.toLp 2 (a, y)) = 1 := by
        refine Real.smoothTransition.one_of_one_le ?_
        rw [WithLp.toLp_snd, div_mul_eq_mul_div, le_sub_iff_add_le, le_div_iff₀ hτ]
        linarith [not_lt.1 hy]
      rw [h1, one_mul, sub_self]
  simpa using add_mem hrest hv

/-- For `τ > 0`, the translate by `-τ v`, with `ℓ v = 1`, of a whole-space function whose trace
vanishes on `{ℓ < c}` has trace vanishing on `{ℓ < c + τ}`, so its restriction lies in
`W^{1,p}_Γ(H)` for `Γ = {x | x.fst = a ∧ ℓ x.snd < c}`. -/
private theorem restrictL_tangentialTranslate_mem_w1pVanishingOnSubmodule
    (hp : p ≠ (∞ : ℝ≥0∞)) (a c : ℝ) (ℓ : E →L[ℝ] ℝ) {v : E} (hv : ℓ v = 1) {τ : ℝ}
    (hτ : 0 < τ) (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.hyperplaneTrace hp a w y = 0) :
    W1p.restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤) (tangentialTranslate (-(τ • v)) w) ∈
      w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ ℓ x.snd < c} := by
  refine restrictL_mem_w1pVanishingOnSubmodule_of_hyperplaneTrace hp a c ℓ hτ
    (tangentialTranslate (-(τ • v)) w) ?_
  filter_upwards [W1p.hyperplaneTrace_translate_ae hp a (-(τ • v)) w,
    (measurePreserving_add_right (volume : Measure E) (-(τ • v))).quasiMeasurePreserving.ae hw]
    with y h1 h2 hy
  rw [tangentialTranslate, h1]
  refine h2 ?_
  rw [map_add, map_neg, map_smul, hv, smul_eq_mul, mul_one]
  linarith

/-! ### The trace characterization on a half-hyperplane -/

/-- **On a half-hyperplane of the boundary, vanishing is zero trace.** Let `ℓ : E →L[ℝ] ℝ` be
nonzero, `c : ℝ` and `1 ≤ p < ∞`, and let `Γ = {x | x.fst = a ∧ ℓ x.snd < c}` be a half of the
boundary hyperplane `{a} × E` of the half-space `H = {x | a < x.fst}`. Then `u ∈ W^{1,p}(H)` lies in
`W^{1,p}_Γ(H)` if and only if its trace vanishes almost everywhere on `{y | ℓ y < c}`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (a c : ℝ) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ ℓ x.snd < c} ↔
      W1p.halfSpaceTrace hp a u =ᵐ[volume.restrict {y | ℓ y < c}] 0 := by
  have hS : {y : E | WithLp.toLp 2 (a, y) ∈ {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd < c}} =
      {y | ℓ y < c} := by
    ext y
    simp
  constructor
  · intro hu
    have h := W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp a hu
    rwa [hS] at h
  intro hu
  -- A direction `v` transversal to the hyperplanes `{ℓ = const}`.
  obtain ⟨v, hv⟩ : ∃ v, ℓ v = 1 := by
    obtain ⟨v₀, hv₀⟩ := DFunLike.ne_iff.1 hℓ
    rw [zero_apply] at hv₀
    exact ⟨(ℓ v₀)⁻¹ • v₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀]⟩
  -- The reflection extension `w` of `u`, whose trace vanishes on `{ℓ < c}`.
  let w := W1p.extendByReflectionL a u
  have hw : ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.hyperplaneTrace hp a w y = 0 := by
    rw [W1p.halfSpaceTrace_apply] at hu
    filter_upwards [(ae_restrict_iff' (isOpen_lt ℓ.continuous continuous_const).measurableSet).1
      hu] with y hy hyc
    exact hy hyc
  -- The translates of `w` by `-τ v` depend continuously on `τ`.
  have hg : Continuous fun τ : ℝ => WithLp.toLp 2 ((0 : ℝ), -(τ • v)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.continuous.comp
      (continuous_const.prodMk (continuous_id.smul continuous_const).neg)
  have hcont : Continuous fun τ : ℝ => tangentialTranslate (-(τ • v)) w :=
    ((Wkp.continuous_translate hp 1 w).comp hg).congr fun τ =>
      Wkp.translate_one_eq_W1p_translate _ w
  have h0 : tangentialTranslate (-((0 : ℝ) • v)) w = w := by
    rw [zero_smul, neg_zero]
    refine (Wkp.translate_one_eq_W1p_translate (WithLp.toLp 2 ((0 : ℝ), (0 : E))) w).symm.trans ?_
    rw [Prod.mk_zero_zero, WithLp.toLp_zero]
    exact Wkp.translate_zero 1 w
  have htend := ((W1p.restrictL (U := normalHalfSpace a) le_top).continuous.comp hcont).tendsto 0
    |>.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [Function.comp_apply, h0, W1p.restrictL_extendByReflectionL] at htend
  -- For `τ > 0` the translates lie in `W^{1,p}_Γ(H)`, which is closed.
  have hclosed := (w1pVanishingOnSubmodule volume (normalHalfSpace a) p
    {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd < c}).isClosed
  exact SetLike.mem_coe.1 (hclosed.mem_of_tendsto htend
    (eventually_nhdsWithin_of_forall fun τ hτ => SetLike.mem_coe.2
      (restrictL_tangentialTranslate_mem_w1pVanishingOnSubmodule hp a c ℓ hv (mem_Ioi.1 hτ) w
        hw)))

end TauCeti
