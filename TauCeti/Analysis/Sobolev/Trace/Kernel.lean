/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.IntegrationByParts
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.Wkp.Translation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The kernel of the half-space trace

Let `H = TauCeti.normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`. This file
identifies the functions of zero trace on `H` with the closure of the test functions:

`ker (Tr : H¹(H) → L²(E)) = H¹₀(H)`.

The inclusion `H¹₀(H) ⊆ ker Tr` is `TauCeti.W1p.halfSpaceTrace_eq_zero_of_w1p0`, and
`TauCeti.W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero` says that `Tr u = 0`
exactly when the extension of `u` by zero is a Sobolev function on `ℝ × E`. The remaining step,
proved here for every `1 ≤ p < ∞`, is that a function on `H` whose extension by zero lies in
`W^{1,p}(ℝ × E)` belongs to `W^{1,p}_0(H)`.

## The argument

Let `w ∈ W^{1,p}(ℝ × E)` vanish off `H`. For `s > 0`, translating `w` by `s` in the normal
direction gives a function vanishing on the layer `{x.fst < a + s}`. There it is unchanged by a
smooth cutoff of the normal coordinate that vanishes for `x.fst ≤ a + s / 2`, so it is a
whole-space Sobolev function times a bounded cutoff supported in `H`, and such functions lie in
`W^{1,p}_0(H)` (`TauCeti.W1p.restrictL_contDiffSMul_mem_w1p0Submodule`). As `s → 0` the translates
converge to `w` in `W^{1,p}(ℝ × E)` (`TauCeti.Wkp.continuous_translate`), so the restriction of
`w` to `H` lies in the closed subspace `W^{1,p}_0(H)`.

## Main declarations

* `TauCeti.W1p.restrictL_mem_w1p0Submodule_normalHalfSpace`: a function in `W^{1,p}(ℝ × E)`
  vanishing off `H` restricts to a function in `W^{1,p}_0(H)`.
* `TauCeti.W1p.mem_w1p0Submodule_normalHalfSpace_iff`: `u ∈ W^{1,p}_0(H)` if and only if its
  extension by zero lies in `W^{1,p}(ℝ × E)`.
* `TauCeti.W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero` and
  `TauCeti.W1p.ker_halfSpaceTrace`: the kernel of the half-space trace is `H¹₀(H)`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.5, Theorem 2 (functions of zero trace).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.18 and its proof.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ContDiff ENNReal Gradient

namespace TauCeti

/-! ### A cutoff of the boundary layer -/

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cutoff `x ↦ σ((2 / s) (x.fst - a) - 1)` of the normal coordinate, where `σ` is
`Real.smoothTransition`: zero for `x.fst ≤ a + s / 2` and one for `x.fst ≥ a + s`. -/
private def layerCutoff (a s : ℝ) (x : WithLp 2 (ℝ × E)) : ℝ :=
  Real.smoothTransition (2 / s * (x.fst - a) - 1)

private theorem contDiff_layerCutoff (a s : ℝ) : ContDiff ℝ ∞ (layerCutoff (E := E) a s) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul ((WithLp.fstL 2 ℝ ℝ E).contDiff.sub contDiff_const)).sub contDiff_const)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem layerCutoff_eq_one {a s : ℝ} (hs : 0 < s) {x : WithLp 2 (ℝ × E)}
    (hx : a + s ≤ x.fst) : layerCutoff a s x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_sub_iff_add_le, div_mul_eq_mul_div, le_div_iff₀ hs]
  linarith

/-- The cutoff is supported a positive distance inside the half-space. -/
private theorem tsupport_layerCutoff_subset {a s : ℝ} (hs : 0 < s) :
    tsupport (layerCutoff (E := E) a s) ⊆ normalHalfSpace (E := E) a := by
  have hclosed : IsClosed {x : WithLp 2 (ℝ × E) | a + s / 2 ≤ x.fst} :=
    isClosed_le continuous_const (WithLp.fstL 2 ℝ ℝ E).continuous
  refine (closure_minimal (fun x hx => ?_) hclosed).trans fun x hx => ?_
  · have h0 : 0 < 2 / s * (x.fst - a) - 1 := by
      by_contra h
      exact hx (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
    rw [sub_pos, div_mul_eq_mul_div, one_lt_div hs] at h0
    rw [mem_ofPred_eq]
    linarith
  · rw [SetLike.mem_coe, mem_normalHalfSpace]
    rw [mem_ofPred_eq] at hx
    exact lt_of_lt_of_le (by linarith) hx

private theorem hasFDerivAt_layerCutoff (a s : ℝ) (x : WithLp 2 (ℝ × E)) :
    HasFDerivAt (layerCutoff a s)
      (deriv Real.smoothTransition (2 / s * (x.fst - a) - 1) •
        (2 / s) • WithLp.fstL 2 ℝ ℝ E) x := by
  have hℓ : HasFDerivAt (fun y : WithLp 2 (ℝ × E) => 2 / s * (y.fst - a) - 1)
      ((2 / s) • WithLp.fstL 2 ℝ ℝ E) x :=
    (((WithLp.fstL 2 ℝ ℝ E).hasFDerivAt.sub_const a).const_mul (2 / s)).sub_const 1
  have hst : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (2 / s * (x.fst - a) - 1)) (2 / s * (x.fst - a) - 1) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact hst.comp_hasFDerivAt x hℓ

/-- The cutoff and its gradient are bounded by a common constant. -/
private theorem exists_layerCutoff_bound [CompleteSpace E] {a s : ℝ} (hs : 0 < s) :
    ∃ M, 0 ≤ M ∧ (∀ x, |layerCutoff (E := E) a s x| ≤ M) ∧
      ∀ x, ‖∇ (layerCutoff (E := E) a s) x‖ ≤ M := by
  obtain ⟨B, hB⟩ := (Real.smoothTransition.contDiff.continuous_deriv le_rfl).norm
    |>.bddAbove_range_of_hasCompactSupport Real.smoothTransition.hasCompactSupport_deriv.norm
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ⟨0, rfl⟩)
  refine ⟨max 1 (B * (2 / s)), zero_le_one.trans (le_max_left _ _), fun x => ?_, fun x => ?_⟩
  · rw [layerCutoff, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans (le_max_left _ _)
  · have hfst : ‖WithLp.fstL 2 ℝ ℝ E‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
        rw [one_mul]
        exact WithLp.norm_fst_le ℝ y
    rw [_root_.gradient, LinearIsometryEquiv.norm_map, (hasFDerivAt_layerCutoff a s x).fderiv,
      norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / s)]
    calc ‖deriv Real.smoothTransition (2 / s * (x.fst - a) - 1)‖ *
          (2 / s * ‖WithLp.fstL 2 ℝ ℝ E‖) ≤ B * (2 / s * 1) := by
          gcongr
          exact hB ⟨_, rfl⟩
      _ ≤ max 1 (B * (2 / s)) := by
          rw [mul_one]
          exact le_max_right _ _

end Cutoff

/-! ### Functions vanishing off the half-space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ENNReal} [Fact (1 ≤ p)]

private theorem ae_restrict_top_eq :
    ae ((volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))) = ae volume := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- Translating a function that vanishes off the half-space by `s > 0` into it makes it vanish on
the layer `{x.fst < a + s}`, where the boundary-layer cutoff is one. -/
private theorem contDiffSMul_layerCutoff_translate {a s : ℝ} (hs : 0 < s) {M : ℝ} (hM : 0 ≤ M)
    (hθM : ∀ x ∈ (⊤ : Opens (WithLp 2 (ℝ × E))), |layerCutoff a s x| ≤ M)
    (hθgradM : ∀ x ∈ (⊤ : Opens (WithLp 2 (ℝ × E))), ‖∇ (layerCutoff a s) x‖ ≤ M)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ x ∂volume, x ∉ normalHalfSpace (E := E) a → W1p.value w x = 0) :
    W1p.contDiffSMul (layerCutoff a s) (contDiff_layerCutoff a s) hM hθM hθgradM
        (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
          (fun _ _ => by simp) w) =
      W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
        (fun _ _ => by simp) w := by
  refine W1p.ext_value (Lp.ext ?_)
  have h1 := W1p.value_contDiffSMul_ae (contDiff_layerCutoff a s) hM hθM hθgradM
    (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
      (fun _ _ => by simp) w)
  have h2 := W1p.value_translate_ae (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
    (fun _ _ => by simp) w
  rw [ae_restrict_top_eq] at h1 h2 ⊢
  have h3 := (measurePreserving_add_right (volume : Measure (WithLp 2 (ℝ × E)))
    (WithLp.toLp 2 (-s, (0 : E)))).quasiMeasurePreserving.ae hw
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, smul_eq_mul]
  by_cases hx : a + s ≤ x.fst
  · rw [layerCutoff_eq_one hs hx, one_mul]
  · have hnot : x + WithLp.toLp 2 (-s, (0 : E)) ∉ normalHalfSpace (E := E) a := by
      rw [mem_normalHalfSpace]
      simp only [WithLp.ofLp_add, Prod.fst_add, WithLp.ofLp_fst, lt_add_neg_iff_add_lt, not_lt]
      linarith
    rw [hx3 hnot, mul_zero]

/-- The translate by `s > 0` into the half-space of a function vanishing off it has zero boundary
values: it is its own product with the boundary-layer cutoff, which is supported in `H`. -/
private theorem restrictL_translate_mem_w1p0Submodule (hp : p ≠ (∞ : ℝ≥0∞)) {a s : ℝ}
    (hs : 0 < s) (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ x ∂volume, x ∉ normalHalfSpace (E := E) a → W1p.value w x = 0) :
    W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
      (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
        (fun _ _ => by simp) w) ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p := by
  obtain ⟨M, hM, hθM, hθgradM⟩ := exists_layerCutoff_bound (E := E) (a := a) hs
  have h := W1p.restrictL_contDiffSMul_mem_w1p0Submodule hp (contDiff_layerCutoff a s) hM
    (fun x _ => hθM x) (fun x _ => hθgradM x) (tsupport_layerCutoff_subset hs)
    (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
      (fun _ _ => by simp) w)
  rwa [contDiffSMul_layerCutoff_translate hs hM _ _ w hw] at h

/-- **A whole-space Sobolev function vanishing off a half-space has zero boundary values there.**
If `w ∈ W^{1,p}(ℝ × E)`, `1 ≤ p < ∞`, vanishes almost everywhere outside `H = {x | a < x.fst}`,
then its restriction to `H` lies in `W^{1,p}_0(H)`. -/
theorem W1p.restrictL_mem_w1p0Submodule_normalHalfSpace (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ)
    (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p)
    (hw : ∀ᵐ x ∂volume, x ∉ normalHalfSpace (E := E) a → W1p.value w x = 0) :
    W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) w ∈
      w1p0Submodule volume (normalHalfSpace (E := E) a) p := by
  -- The translates of `w` by `s` in the normal direction depend continuously on `s`.
  have hcont : Continuous fun s : ℝ => W1p.restrictL
      (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
      (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
        (fun _ _ => by simp) w) := by
    have hg : Continuous fun s : ℝ => WithLp.toLp 2 (-s, (0 : E)) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.continuous.comp
        (continuous_neg.prodMk continuous_const)
    have h : Continuous fun s : ℝ => Wkp.translate (WithLp.toLp 2 (-s, (0 : E))) 1 w :=
      (Wkp.continuous_translate hp 1 w).comp hg
    exact (W1p.restrictL _).continuous.comp
      (h.congr fun s => Wkp.translate_one_eq_W1p_translate _ w)
  have h0 : W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-(0 : ℝ), (0 : E)))
      (fun _ _ => by simp) w = w := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_translate_ae (Omega := ⊤) (V := ⊤)
      (h := WithLp.toLp 2 (-(0 : ℝ), (0 : E))) (fun _ _ => by simp) w] with x hx
    rw [hx, neg_zero, Prod.mk_zero_zero, WithLp.toLp_zero, add_zero]
  have htend := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [h0] at htend
  -- For `s > 0` the translates lie in the closed subspace `W^{1,p}_0(H)`, hence so does the limit.
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), W1p.restrictL
      (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
      (W1p.translate (Omega := ⊤) (V := ⊤) (h := WithLp.toLp 2 (-s, (0 : E)))
        (fun _ _ => by simp) w) ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p :=
    eventually_nhdsWithin_of_forall fun s hs => restrictL_translate_mem_w1p0Submodule hp hs w hw
  exact (w1p0Submodule volume (normalHalfSpace (E := E) a) p).isClosed.mem_of_tendsto htend hev

/-- **`W^{1,p}_0` of a half-space consists of the functions that extend by zero.** For
`1 ≤ p < ∞`, a function `u ∈ W^{1,p}(H)` on `H = {x | a < x.fst}` lies in `W^{1,p}_0(H)` if and only
if its extension by zero, in value and weak gradient, is a Sobolev function on `ℝ × E`. -/
theorem W1p.mem_w1p0Submodule_normalHalfSpace_iff (hp : p ≠ (∞ : ℝ≥0∞)) (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    u ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p ↔
      Sobolev1JetLp.extendByZeroₗᵢ (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) ∈
          w1pSubmodule volume ⊤ p := by
  refine ⟨fun hu => Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule le_top hu, fun hJ => ?_⟩
  have hH : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  -- The extension `w` of `u` by zero, a whole-space Sobolev function vanishing off `H`.
  let w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p := ⟨_, hJ⟩
  have hw : ∀ᵐ x ∂volume, W1p.value w x =
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator (W1p.value u) x := by
    have h := coeFn_extendByZeroLpₗᵢ ℝ hH (SetLike.coe_subset_coe.mpr le_top) (W1p.value u)
    rw [ae_restrict_top_eq] at h
    filter_upwards [h] with x hx
    rw [W1p.value_coe, Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe, hx]
  have hwu : W1p.restrictL (show normalHalfSpace (E := E) a ≤ ⊤ from le_top) w = u := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_restrictL_ae le_top w, ae_restrict_of_ae hw, ae_restrict_mem hH]
      with x h1 h2 hx
    rw [h1, h2, indicator_of_mem hx]
  rw [← hwu]
  exact W1p.restrictL_mem_w1p0Submodule_normalHalfSpace hp a w
    (hw.mono fun x hx hxH => by rw [hx, indicator_of_notMem hxH])

/-- **The functions of zero trace on a half-space are those of `H¹₀`.** A function
`u ∈ H¹(H)` on `H = {x | a < x.fst}` lies in `H¹₀(H)` if and only if its trace on the boundary
hyperplane `{a} × E` vanishes. -/
theorem W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) 2) :
    u ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) 2 ↔ W1p.halfSpaceTrace a u = 0 := by
  rw [W1p.mem_w1p0Submodule_normalHalfSpace_iff ENNReal.ofNat_ne_top a u,
    W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTrace_eq_zero]

/-- **The kernel of the half-space trace is `H¹₀`.** On `H = {x | a < x.fst}`, the trace
`H¹(H) → L²(E)` on the boundary hyperplane `{a} × E` has kernel exactly `H¹₀(H)`, the closure of
the test functions on `H`. -/
theorem W1p.ker_halfSpaceTrace (a : ℝ) :
    LinearMap.ker (W1p.halfSpaceTrace (E := E) a).toLinearMap =
      (w1p0Submodule volume (normalHalfSpace (E := E) a) 2).toSubmodule := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ClosedSubmodule.mem_toSubmodule_iff,
    W1p.mem_w1p0Submodule_iff_halfSpaceTrace_eq_zero]

end TauCeti
