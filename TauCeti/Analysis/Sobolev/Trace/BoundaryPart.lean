/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Kernel
public import TauCeti.Analysis.Sobolev.Trace.Multiplication
public import TauCeti.Analysis.Sobolev.Trace.Translation
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.SpecialFunctions.LinearCutoff
import TauCeti.Analysis.Sobolev.Wkp.Translation
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Functions whose half-space trace vanishes on a half-hyperplane

Let `H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`, with boundary
hyperplane `{a} × E`, and let `ℓ : E →L[ℝ] ℝ` be nonzero. The half-hyperplane
`Γ = {a} × {y | ℓ y < c}` is the flat model of a boundary part: near a point of its relative
boundary `{a} × {ℓ = c}`, a boundary portion of a Lipschitz domain of the admissible kind becomes
`Γ` after flattening the boundary and the interface by two shears. Its closure is
`K = {x | x.fst = a ∧ ℓ x.snd ≤ c}`.

This file proves the trace characterization of the functions vanishing on `Γ` in this model. For
`1 ≤ p < ∞` and `u ∈ W^{1,p}(H)`, the trace of `u` vanishes almost everywhere on `{ℓ < c}` if and
only if `u` is the `W^{1,p}(H)`-limit of restrictions to `H` of test functions on `ℝ × E` whose
supports are disjoint from `K`
(`TauCeti.W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero`). For
`ℓ = 0` the statement fails: with `c = 0` the trace condition is empty while `K` is the whole
boundary hyperplane.

In terms of the space `W^{1,p}_Γ(H)` of functions vanishing on `Γ`
(`TauCeti.w1pVanishingOnSubmodule`), whose generators are the restricted test functions with
support disjoint from `closure Γ ⊆ K`, the characterization reads
`u ∈ W^{1,p}_Γ(H) ↔ T u = 0` almost everywhere on `{ℓ < c}`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero`). Unlike the sequence form,
this holds also for `ℓ = 0`, since `closure Γ` is then empty or the whole boundary hyperplane. The
direction "`u` lies in `W^{1,p}_Γ(H)` implies zero trace on `Γ`" holds for every set `Γ`
(`TauCeti.W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule`).

## The argument

One direction holds because the trace of a restricted test function is its boundary value, which
vanishes on `K`, and the trace is continuous. For the other, let `w` be the reflection extension
of `u` and fix `e` with `ℓ e = 1`. For `τ > 0` the tangential translate
`w_τ = w (· - (0, τ e))` restricts to a function `v_τ` on `H` whose trace vanishes on the larger
region `{ℓ < c + τ}` (`TauCeti.W1p.hyperplaneTrace_translate`), and `v_τ → u` as `τ → 0`. A smooth
cutoff `χ` of the coordinate `ℓ x.snd` (`TauCeti.linearCutoff`), vanishing on `{ℓ ≤ c + τ / 3}`
and equal to one on `{ℓ ≥ c + 2τ / 3}`, splits `v_τ = (v_τ - χ v_τ) + χ v_τ`.

* The trace of `v_τ - χ v_τ` is `(1 - χ) Tr v_τ`, which vanishes everywhere, so this part lies in
  `W^{1,p}_0(H)` by the kernel theorem `TauCeti.W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero`;
  test functions on `H` have support disjoint from the boundary hyperplane.
* The part `χ v_τ` is the restriction of `χ w_τ`, and `χ ψ_k → χ w_τ` for test functions
  `ψ_k → w_τ`; each `χ ψ_k` is supported in `{ℓ ≥ c + τ / 3}`, disjoint from `K`.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. **48** (2016), 2912–2943, Lemma 3.1
  and Appendix A (the trace characterization for `p = 2` in dimension three).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 2 (functions of zero
  trace).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ENNReal Gradient Distributions ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Restricted test functions supported away from `closure Γ` -/

/-- A whole-space Sobolev function multiplied by a smooth cutoff whose support is disjoint from
`closure Γ` restricts to an element of `W^{1,p}_Γ(H)`. -/
private theorem restrictL_contDiffSMul_mem_w1pVanishingOnSubmodule (hp : p ≠ (∞ : ℝ≥0∞)) {a : ℝ}
    {Γ : Set (WithLp 2 (ℝ × E))} {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ ∞ χ) {M : ℝ}
    (hM : 0 ≤ M) (hχM : ∀ x, |χ x| ≤ M) (hgradM : ∀ x, ‖∇ χ x‖ ≤ M)
    (hχΓ : Disjoint (tsupport χ) (closure Γ))
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p.restrictL le_top (W1p.contDiffSMul χ hχ hM (fun x _ => hχM x) (fun x _ => hgradM x) w) ∈
      w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ := by
  let F := (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top).comp
    (W1p.contDiffSMulL χ hχ hM (fun x _ => hχM x) (fun x _ => hgradM x) :
      W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ] _)
  suffices key : F w ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ by
    simpa only [F, ContinuousLinearMap.coe_comp, Function.comp_apply,
      W1p.contDiffSMulL_apply] using key
  refine (W1p.denseRange_ofTestFunctionₗ_top hp).induction_on (p := fun w => F w ∈ _) w
    ((w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ).isClosed.preimage F.continuous)
    fun ψ => ?_
  have heq : W1p.restrictL le_top
      (W1p.ofTestFunctionₗ volume ⊤ p (TestFunction.smulLeftCLM hχ ψ)) =
        F (W1p.ofTestFunctionₗ volume ⊤ p ψ) :=
    congrArg _ (W1p.ext_value (Lp.ext ?_))
  · rw [← heq]
    exact W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
      (hχΓ.mono_left ((TestFunction.tsupport_smulLeftCLM_subset hχ ψ).trans inter_subset_left))
  filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p)
      (TestFunction.smulLeftCLM hχ ψ),
    W1p.value_contDiffSMul_ae (mu := volume) (Omega := ⊤) hχ hM (fun x _ => hχM x)
      (fun x _ => hgradM x) (W1p.ofTestFunctionₗ volume ⊤ p ψ),
    W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p) ψ] with x h₁ h₂ h₃
  rw [h₁, ContinuousLinearMap.coe_coe, W1p.contDiffSMulL_apply, h₂, h₃,
    TestFunction.smulLeftCLM_apply]

/-! ### Tangential translation -/

/-- The tangential translate `x ↦ w (x - (0, τ e))` of a whole-space Sobolev function. -/
private def tangentialTranslate (e : E) (τ : ℝ)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
  W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (0, -(τ • e))) (fun _ _ => by simp) w

/-- The tangential translates of a fixed function depend continuously on `τ` and start at it. -/
private theorem tendsto_restrictL_tangentialTranslate (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ) (e : E)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    Tendsto (fun τ => W1p.restrictL (U := normalHalfSpace (E := E) a) le_top
      (tangentialTranslate e τ w)) (𝓝 0) (𝓝 (W1p.restrictL le_top w)) := by
  have hg : Tendsto (fun τ : ℝ => WithLp.toLp 2 ((0 : ℝ), -(τ • e))) (𝓝 0) (𝓝 0) := by
    refine Continuous.tendsto' ?_ 0 0 (by simp)
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.continuous.comp
      (continuous_const.prodMk (continuous_id.smul continuous_const).neg)
  exact ((W1p.restrictL le_top).continuous.tendsto w).comp (W1p.tendsto_translate hp hg w)

/-- After the tangential translation by `τ e` with `ℓ e = 1`, the trace vanishes on the larger
region `{ℓ < c + τ}`. -/
private theorem halfSpaceTrace_restrictL_tangentialTranslate_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    {a c : ℝ}
    {ℓ : E →L[ℝ] ℝ} {e : E} (he : ℓ e = 1) (τ : ℝ)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0) :
    ∀ᵐ y ∂(volume : Measure E), ℓ y < c + τ →
      W1p.halfSpaceTrace hp a (W1p.restrictL le_top
        (tangentialTranslate e τ (W1p.extendByReflectionL a u))) y = 0 := by
  rw [W1p.halfSpaceTrace_restrictL, tangentialTranslate, W1p.hyperplaneTrace_translate]
  filter_upwards [Measure.coeFn_translateLp (mu := (volume : Measure E)) (p := p) (-(τ • e))
      (W1p.hyperplaneTrace hp a (W1p.extendByReflectionL a u)),
    (measurePreserving_add_right (volume : Measure E) (-(τ • e))).quasiMeasurePreserving.ae hu]
    with y h₁ h₂ hy
  rw [h₁, Function.comp_apply, ← W1p.halfSpaceTrace_apply]
  refine h₂ ?_
  rw [map_add, map_neg, map_smul, he, smul_eq_mul, mul_one]
  linarith

/-! ### The trace characterization -/

/-- **Functions vanishing on `Γ` have zero trace on `Γ`.** For `p < ∞` and any set `Γ`, the
half-space trace of every `u ∈ W^{1,p}_Γ(H)` vanishes almost everywhere on the set of `y` with
`(a, y) ∈ Γ`: the generators are continuous up to the boundary and vanish on `closure Γ`, and the
trace is continuous. The argument adapts the proof of
`TauCeti.W1p.frontierTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule` for bounded Lipschitz
domains. -/
theorem W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule (hp : p ≠ (∞ : ℝ≥0∞))
    (a : ℝ) {Γ : Set (WithLp 2 (ℝ × E))}
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p Γ) :
    W1p.halfSpaceTrace hp a u =ᵐ[volume.restrict {y | WithLp.toLp 2 (a, y) ∈ Γ}] 0 := by
  set S := {y : E | WithLp.toLp 2 (a, y) ∈ Γ}
  -- Vanishing on `S` is the kernel of a continuous linear map, hence a closed condition.
  let R := (LpToLpRestrictCLM E ℝ ℝ (volume : Measure E) p S).comp (W1p.halfSpaceTrace hp a)
  have hclosed : IsClosed {v | R v = 0} := isClosed_eq R.continuous continuous_const
  have h := w1pVanishingOnSubmodule_subset_of_isClosed hclosed (fun φ hφ => ?_) hu
  · exact (LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ) S _).1 h
  -- The trace of a generator is its restriction, which vanishes where `(a, y) ∈ closure Γ`.
  have hC : IsClosed {y : E | WithLp.toLp 2 (a, y) ∈ closure Γ} :=
    isClosed_closure.preimage (by fun_prop)
  rw [mem_ofPred, ContinuousLinearMap.comp_apply, LpToLpRestrictCLM_eq_zero_iff (𝕜 := ℝ),
    W1p.halfSpaceTrace_restrictL]
  filter_upwards [ae_restrict_of_ae (W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ),
    ae_restrict_of_ae_restrict_of_subset (t := {y : E | WithLp.toLp 2 (a, y) ∈ closure Γ})
      (fun _ hy => subset_closure hy) (ae_restrict_mem hC.measurableSet)] with y hy hyC
  rw [hy, Pi.zero_apply]
  exact image_eq_zero_of_notMem_tsupport (hφ.notMem_of_mem_right hyC)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The set `K = {x | x.fst = a ∧ ℓ x.snd ≤ c}`, which contains the half-hyperplane, is closed. -/
private theorem isClosed_setOf_fst_eq_and_le (a c : ℝ) (ℓ : E →L[ℝ] ℝ) :
    IsClosed {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd ≤ c} :=
  (isClosed_eq (WithLp.fstL 2 ℝ ℝ E).continuous continuous_const).inter
    (isClosed_le (ℓ.comp (WithLp.sndL 2 ℝ ℝ E)).continuous continuous_const)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A subset of the boundary hyperplane `{a} × E` misses `H = {x | a < x.fst}`. -/
private theorem disjoint_setOf_fst_eq_and_normalHalfSpace (a : ℝ) (P : WithLp 2 (ℝ × E) → Prop) :
    Disjoint {x : WithLp 2 (ℝ × E) | x.fst = a ∧ P x}
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
  Set.disjoint_left.2 fun x (hx : x.fst = a ∧ _) hxH => ((mem_normalHalfSpace a x).1 hxH).ne' hx.1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The half-hyperplane `{x | x.fst = a ∧ ℓ x.snd < c}` lies in `K`. -/
private theorem setOf_fst_eq_and_lt_subset (a c : ℝ) (ℓ : E →L[ℝ] ℝ) :
    {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd < c} ⊆ {x | x.fst = a ∧ ℓ x.snd ≤ c} :=
  fun _ hx => ⟨hx.1, hx.2.le⟩

/-- A function whose trace vanishes on `{ℓ < c + τ}`, `τ > 0`, lies in `W^{1,p}_K(H)`. -/
private theorem restrictL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    {a c τ : ℝ} (hτ : 0 < τ)
    (ℓ : E →L[ℝ] ℝ) (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ y ∂(volume : Measure E), ℓ y < c + τ →
      W1p.halfSpaceTrace hp a (W1p.restrictL le_top w) y = 0) :
    W1p.restrictL le_top w ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p
      {x | x.fst = a ∧ ℓ x.snd ≤ c} := by
  set L := ℓ.comp (WithLp.sndL 2 ℝ ℝ E)
  set χ := linearCutoff L (3 / τ) (c + τ / 3)
  have hχ := contDiff_linearCutoff L (3 / τ) (c + τ / 3)
  obtain ⟨M, hM, hχM, hderivM⟩ := exists_linearCutoff_bound L (3 / τ) (c + τ / 3)
  have hgradM : ∀ x, ‖∇ χ x‖ ≤ M := fun x =>
    (norm_gradient_eq_norm_fderiv χ x).trans_le (hderivM x)
  set v := W1p.restrictL (U := normalHalfSpace (E := E) a) le_top w
  set χv := W1p.contDiffSMul χ hχ hM (fun x _ => hχM x) (fun x _ => hgradM x) v
  -- The rest has zero trace, since `1 - χ` vanishes where the trace of `v` may not.
  have hrest : v - χv ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p := by
    rw [W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero hp, map_sub]
    refine Lp.ext ?_
    filter_upwards [hw, W1p.halfSpaceTrace_contDiffSMul_ae hp a hχ hχM hgradM v,
      Lp.coeFn_sub (W1p.halfSpaceTrace hp a v) (W1p.halfSpaceTrace hp a χv),
      Lp.coeFn_zero ℝ p (volume : Measure E)] with y h₁ h₂ h₃ h₄
    rw [h₃, h₄, Pi.sub_apply, h₂, Pi.zero_apply]
    by_cases hy : ℓ y < c + τ
    · rw [h₁ hy, mul_zero, sub_zero]
    · rw [linearCutoff_eq_one (by
          rw [div_mul_eq_mul_div, le_div_iff₀ hτ]
          simp only [L, ContinuousLinearMap.coe_comp, Function.comp_apply, WithLp.sndL_apply,
            WithLp.toLp_snd]
          linarith), one_mul, sub_self]
  have hχK : Disjoint (tsupport χ) (closure {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd ≤ c}) := by
    rw [(isClosed_setOf_fst_eq_and_le a c ℓ).closure_eq]
    refine Set.disjoint_left.2 fun x hx hxK => ?_
    have h : c + τ / 3 ≤ ℓ x.snd :=
      tsupport_linearCutoff_subset L (by positivity : (0 : ℝ) ≤ 3 / τ) (c + τ / 3) hx
    linarith [hxK.2]
  -- The cutoff part is the restriction of `χ w`.
  have hχv := restrictL_contDiffSMul_mem_w1pVanishingOnSubmodule (a := a) hp hχ hM hχM hgradM hχK w
  rw [W1p.restrictL_contDiffSMul] at hχv
  have hsub : v = (v - χv) + χv := (sub_add_cancel v χv).symm
  rw [hsub]
  -- `K` lies in the boundary hyperplane, so it misses `H`.
  exact add_mem (w1p0Submodule_le_w1pVanishingOnSubmodule
    (disjoint_setOf_fst_eq_and_normalHalfSpace a _) hrest) hχv

/-- A function whose trace vanishes on `{ℓ < c}`, for `ℓ ≠ 0`, lies in `W^{1,p}_K(H)`: it is the
limit of its tangential translates, which lie there. -/
private theorem mem_w1pVanishingOnSubmodule_of_halfSpaceTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    {a c : ℝ} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ ℓ x.snd ≤ c} := by
  obtain ⟨e', he'⟩ : ∃ e', ℓ e' ≠ 0 := by simpa using DFunLike.ne_iff.1 hℓ
  have he : ℓ ((ℓ e')⁻¹ • e') = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ he']
  have hlim := tendsto_restrictL_tangentialTranslate hp a ((ℓ e')⁻¹ • e')
    (W1p.extendByReflectionL a u) |>.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [W1p.restrictL_extendByReflectionL] at hlim
  exact (w1pVanishingOnSubmodule _ _ _ _).isClosed.mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun τ hτ =>
      restrictL_mem_w1pVanishingOnSubmodule_of_ae_eq_zero hp hτ ℓ _
        (halfSpaceTrace_restrictL_tangentialTranslate_ae_eq_zero hp he τ hu))

/-- **The trace characterization of `W^{1,p}_Γ(H)` on a half-hyperplane.** Let `1 ≤ p < ∞`, let
`H = {x | a < x.fst}` in `ℝ × E`, let `ℓ : E →L[ℝ] ℝ`, and let `Γ = {x | x.fst = a ∧ ℓ x.snd < c}`
be a half of the boundary hyperplane `{a} × E`. Then `u ∈ W^{1,p}(H)` lies in `W^{1,p}_Γ(H)` if
and only if its trace vanishes almost everywhere on `{y | ℓ y < c}`. For `ℓ = 0`, `Γ` is either
empty, when every `u` qualifies by density of test functions, or the whole boundary hyperplane,
when this is the kernel theorem `TauCeti.W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero`. -/
theorem W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    (a c : ℝ) (ℓ : E →L[ℝ] ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace a) p {x | x.fst = a ∧ ℓ x.snd < c} ↔
      ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0 := by
  have hmeas : MeasurableSet {y : E | ℓ y < c} :=
    (isOpen_lt ℓ.continuous continuous_const).measurableSet
  constructor
  · intro hu
    have h := W1p.halfSpaceTrace_ae_eq_zero_of_mem_w1pVanishingOnSubmodule hp a hu
    have hS : {y : E | WithLp.toLp 2 (a, y) ∈ {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd < c}} =
        {y | ℓ y < c} := by
      ext y
      simp
    rw [hS] at h
    exact (ae_restrict_iff' hmeas).1 h
  intro hu
  obtain rfl | hℓ := eq_or_ne ℓ 0
  · by_cases hc : 0 < c
    · -- `Γ` is the boundary hyperplane, disjoint from `H`, and the trace of `u` vanishes.
      exact w1p0Submodule_le_w1pVanishingOnSubmodule
        (disjoint_setOf_fst_eq_and_normalHalfSpace a _)
        ((W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero hp a u).2
          (Lp.eq_zero_iff_ae_eq_zero.2 (hu.mono fun y hy => hy (by simpa using hc))))
    · -- `Γ` is empty, and restrictions of test functions are dense.
      have hΓ : {x : WithLp 2 (ℝ × E) | x.fst = a ∧ (0 : E →L[ℝ] ℝ) x.snd < c} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => hc (by simpa using hx.2)
      rw [hΓ, w1pVanishingOnSubmodule_empty_eq_top_iff.2
        (W1p.denseRange_restrictL_ofTestFunctionₗ_normalHalfSpace hp a)]
      exact ClosedSubmodule.mem_top
  -- `u` lies in `W^{1,p}_K(H)` for `K ⊇ Γ`.
  exact w1pVanishingOnSubmodule_antitone (setOf_fst_eq_and_lt_subset a c ℓ)
    (mem_w1pVanishingOnSubmodule_of_halfSpaceTrace_ae_eq_zero hp hℓ hu)

/-- **The trace characterization on a half-space, for a half-hyperplane.** Let `1 ≤ p < ∞`, let
`H = {x | a < x.fst}` in `ℝ × E`, and let `ℓ : E →L[ℝ] ℝ` be nonzero. A function `u ∈ W^{1,p}(H)`
is the limit in `W^{1,p}(H)` of restrictions to `H` of test functions on `ℝ × E` whose supports are
disjoint from `{x | x.fst = a ∧ ℓ x.snd ≤ c}` if and only if its trace on `{a} × E` vanishes almost
everywhere on `{y | ℓ y < c}`. -/
theorem W1p.exists_seq_tendsto_restrictL_ofTestFunctionₗ_iff_halfSpaceTrace_ae_eq_zero
    (hp : p ≠ (∞ : ℝ≥0∞)) (a c : ℝ) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    (∃ φ : ℕ → 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
        (∀ k, Disjoint (tsupport (φ k)) {x | x.fst = a ∧ ℓ x.snd ≤ c}) ∧
          Tendsto (fun k => W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ p (φ k))) atTop
            (𝓝 u)) ↔
      ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0 := by
  rw [← (isClosed_setOf_fst_eq_and_le a c ℓ).closure_eq,
    ← mem_w1pVanishingOnSubmodule_iff_exists_seq_tendsto]
  -- The forward direction passes through `Γ = {ℓ < c} ⊆ K`.
  exact ⟨fun hu => (W1p.mem_w1pVanishingOnSubmodule_iff_halfSpaceTrace_ae_eq_zero hp a c ℓ u).1
      (w1pVanishingOnSubmodule_antitone (setOf_fst_eq_and_lt_subset a c ℓ) hu),
    mem_w1pVanishingOnSubmodule_of_halfSpaceTrace_ae_eq_zero hp hℓ⟩

end TauCeti
