/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Kernel
public import TauCeti.Analysis.Sobolev.Trace.Multiplication
public import TauCeti.Analysis.Sobolev.Trace.Translation
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

/-! ### The restricted test functions vanishing near `K` -/

/-- The restrictions to `H = {a < x.fst}` of the test functions on `ℝ × E` whose support is
disjoint from `{x | x.fst = a ∧ ℓ x.snd ≤ c}`, a subspace of `W^{1,p}(H)`. -/
private def vanishingNear (p : ℝ≥0∞) [Fact (1 ≤ p)] (a c : ℝ) (ℓ : E →L[ℝ] ℝ) :
    Submodule ℝ (W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) where
  carrier := {u | ∃ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
    Disjoint (tsupport φ) {x | x.fst = a ∧ ℓ x.snd ≤ c} ∧
      W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ p φ) = u}
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    refine ⟨φ + ψ, ?_, by simp only [map_add]⟩
    rw [FunLike.coe_add]
    exact (hφ.union_left hψ).mono_left (tsupport_add _ _)
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro r _ ⟨φ, hφ, rfl⟩
    refine ⟨r • φ, hφ.mono_left ?_, by simp only [map_smul]⟩
    rw [FunLike.coe_smul]
    exact tsupport_smul_subset_right (fun _ => r) φ

/-- `W^{1,p}_0(H)` lies in the closure: a test function on `H` extends to one on `ℝ × E` supported
in `H`, away from the boundary hyperplane. -/
private theorem w1p0Submodule_subset_closure_vanishingNear (a c : ℝ) (ℓ : E →L[ℝ] ℝ) :
    (w1p0Submodule volume (normalHalfSpace (E := E) a) p : Set _) ⊆
      closure (SetLike.coe (vanishingNear p a c ℓ)) := by
  refine w1p0Submodule_subset_of_isClosed isClosed_closure fun φ => subset_closure ?_
  have hcoe : ((TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
      WithLp 2 (ℝ × E) → ℝ) = φ := by
    simp [TestFunction.monoCLM_apply]
  refine ⟨TestFunction.monoCLM ℝ φ, ?_, W1p.restrictL_eq_of_value_ae_eq le_top ?_⟩
  · refine Set.disjoint_left.2 fun x hx hxK => ?_
    rw [hcoe] at hx
    exact (mem_normalHalfSpace a x).1 (φ.tsupport_subset hx) |>.ne hxK.1.symm
  · filter_upwards [ae_restrict_of_ae (W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := p)
      (TestFunction.monoCLM ℝ φ)), W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := p) φ]
      with x h₁ h₂
    rw [h₁, h₂, hcoe]

/-- A whole-space Sobolev function multiplied by a smooth cutoff whose support is disjoint from
`K` restricts to an element of the closure. -/
private theorem restrictL_contDiffSMul_mem_closure_vanishingNear (hp : p ≠ (∞ : ℝ≥0∞)) {a c : ℝ}
    {ℓ : E →L[ℝ] ℝ} {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ ∞ χ) {M : ℝ} (hM : 0 ≤ M)
    (hχM : ∀ x, |χ x| ≤ M) (hgradM : ∀ x, ‖∇ χ x‖ ≤ M)
    (hχK : Disjoint (tsupport χ) {x | x.fst = a ∧ ℓ x.snd ≤ c})
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p.restrictL le_top (W1p.contDiffSMul χ hχ hM (fun x _ => hχM x) (fun x _ => hgradM x) w) ∈
      closure (SetLike.coe (vanishingNear p a c ℓ)) := by
  let F := (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top).comp
    (W1p.contDiffSMulL χ hχ hM (fun x _ => hχM x) (fun x _ => hgradM x) :
      W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ] _)
  suffices key : F w ∈ closure (SetLike.coe (vanishingNear p a c ℓ)) by
    simpa only [F, ContinuousLinearMap.coe_comp, Function.comp_apply,
      W1p.contDiffSMulL_apply] using key
  refine (W1p.denseRange_ofTestFunctionₗ_top hp).induction_on (p := fun w => F w ∈ closure _) w
    (isClosed_closure.preimage F.continuous) fun ψ => subset_closure ?_
  refine ⟨TestFunction.smulLeftCLM hχ ψ, hχK.mono_left ((TestFunction.tsupport_smulLeftCLM_subset
    hχ ψ).trans inter_subset_left), congrArg _ (W1p.ext_value (Lp.ext ?_))⟩
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

/-- A function whose trace vanishes on `{ℓ < c + τ}`, `τ > 0`, lies in the closure. -/
private theorem mem_closure_vanishingNear_of_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞)) {a c τ : ℝ}
    (hτ : 0 < τ)
    (ℓ : E →L[ℝ] ℝ) (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ y ∂(volume : Measure E), ℓ y < c + τ →
      W1p.halfSpaceTrace hp a (W1p.restrictL le_top w) y = 0) :
    W1p.restrictL le_top w ∈ closure (SetLike.coe (vanishingNear p a c ℓ)) := by
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
  have hχK : Disjoint (tsupport χ) {x : WithLp 2 (ℝ × E) | x.fst = a ∧ ℓ x.snd ≤ c} :=
    Set.disjoint_left.2 fun x hx hxK => by
      have h : c + τ / 3 ≤ ℓ x.snd :=
        tsupport_linearCutoff_subset L (by positivity : (0 : ℝ) ≤ 3 / τ) (c + τ / 3) hx
      linarith [hxK.2]
  -- The cutoff part is the restriction of `χ w`.
  have hχv := restrictL_contDiffSMul_mem_closure_vanishingNear hp hχ hM hχM hgradM hχK w
  rw [W1p.restrictL_contDiffSMul] at hχv
  have hsub : v = (v - χv) + χv := (sub_add_cancel v χv).symm
  rw [hsub]
  exact (vanishingNear p a c ℓ).topologicalClosure.add_mem
    (w1p0Submodule_subset_closure_vanishingNear a c ℓ hrest) hχv

/-- Membership in the closure, as a limit of a sequence of generators. -/
private theorem mem_closure_vanishingNear_iff {a c : ℝ} {ℓ : E →L[ℝ] ℝ}
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p} :
    u ∈ closure (SetLike.coe (vanishingNear p a c ℓ)) ↔
      ∃ φ : ℕ → 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
        (∀ k, Disjoint (tsupport (φ k)) {x | x.fst = a ∧ ℓ x.snd ≤ c}) ∧
          Tendsto (fun k => W1p.restrictL le_top (W1p.ofTestFunctionₗ volume ⊤ p (φ k))) atTop
            (𝓝 u) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨v, hv, hlim⟩
    choose φ hφ hφv using hv
    exact ⟨φ, hφ, by simpa only [hφv] using hlim⟩
  · rintro ⟨φ, hφ, hlim⟩
    exact ⟨_, fun k => ⟨φ k, hφ k, rfl⟩, hlim⟩

/-- Every element of the closure has trace zero on `{ℓ < c}`: the functions with this property
form a closed set containing the generators, whose traces are their boundary values. -/
private theorem halfSpaceTrace_ae_eq_zero_of_mem_closure_vanishingNear (hp : p ≠ (∞ : ℝ≥0∞))
    {a c : ℝ} {ℓ : E →L[ℝ] ℝ}
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : u ∈ closure (SetLike.coe (vanishingNear p a c ℓ))) :
    ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0 := by
  have hclosed := (Lp.isClosed_setOf_ae_notMem_imp_eq_zero (μ := (volume : Measure E)) (F := ℝ)
    (p := p) {y | c ≤ ℓ y}).preimage (W1p.halfSpaceTrace hp a).continuous
  have h := closure_minimal (s := SetLike.coe (vanishingNear p a c ℓ)) ?_ hclosed hu
  · simpa only [mem_preimage, mem_ofPred_eq, not_le] using h
  rintro _ ⟨φ, hφ, rfl⟩
  simp only [mem_preimage, mem_ofPred_eq, not_le]
  rw [W1p.halfSpaceTrace_restrictL]
  filter_upwards [W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ] with y hy hyc
  rw [hy]
  exact image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hφ ⟨rfl, hyc.le⟩)

/-- A function whose trace vanishes on `{ℓ < c}`, for `ℓ ≠ 0`, lies in the closure: it is the
limit of its tangential translates, which lie in the closure. -/
private theorem mem_closure_vanishingNear_of_halfSpaceTrace_ae_eq_zero (hp : p ≠ (∞ : ℝ≥0∞))
    {a c : ℝ} {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0)
    {u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p}
    (hu : ∀ᵐ y ∂(volume : Measure E), ℓ y < c → W1p.halfSpaceTrace hp a u y = 0) :
    u ∈ closure (SetLike.coe (vanishingNear p a c ℓ)) := by
  obtain ⟨e', he'⟩ : ∃ e', ℓ e' ≠ 0 := by simpa using DFunLike.ne_iff.1 hℓ
  have he : ℓ ((ℓ e')⁻¹ • e') = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ he']
  have hlim := tendsto_restrictL_tangentialTranslate hp a ((ℓ e')⁻¹ • e')
    (W1p.extendByReflectionL a u) |>.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  rw [W1p.restrictL_extendByReflectionL] at hlim
  exact isClosed_closure.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun τ hτ =>
    mem_closure_vanishingNear_of_ae_eq_zero hp hτ ℓ _
      (halfSpaceTrace_restrictL_tangentialTranslate_ae_eq_zero hp he τ hu))

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
  rw [← mem_closure_vanishingNear_iff]
  exact ⟨halfSpaceTrace_ae_eq_zero_of_mem_closure_vanishingNear hp,
    mem_closure_vanishingNear_of_halfSpaceTrace_ae_eq_zero hp hℓ⟩

end TauCeti
