/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.SpecialFunctions.SmoothAbs
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.MeasureTheory.Integral.ContinuousMap
import TauCeti.Topology.Algebra.Module.WeakSpace.Basic

/-!
# Absolute values in the Sobolev space `H¹`

Let `M` be a compact manifold with a continuous Riemannian metric and Sobolev space `H¹(M)`
(`TauCeti.Manifold.SobolevH1`). This file shows that `H¹(M)` is closed under taking absolute
values, without increasing the Dirichlet energy: for every `w ∈ H¹(M)` there is `w' ∈ H¹(M)`
whose value in `L²(M)` is `|w|` and with

`D(w', w') ≤ D(w, w)`

(`TauCeti.Manifold.SobolevH1.exists_toLp_eq_abs_and_dirichletForm_le`), where `D` is the Dirichlet
form `TauCeti.Manifold.SobolevH1.dirichletForm`. When the value map `toLp` is injective
(`TauCeti.Manifold.SobolevH1.toLp_injective`, for a closed manifold with a `C¹` metric), the element
`w'` is unique.

This is the truncation that turns a minimizing sequence of a variational problem on `H¹(M)` whose
energy only depends on `|w|` outside the Dirichlet term, such as the Yamabe quotient, into a
minimizing sequence of nonnegative functions.

## The argument

Approximate `w` by smooth functions `uₖ` in `H¹(M)` and regularize them to the smooth functions
`vₖ = TauCeti.smoothAbs ηₖ ∘ uₖ = √(uₖ² + ηₖ²) - ηₖ` with `ηₖ → 0`. The derivative of
`TauCeti.smoothAbs ηₖ` has absolute value at most `1`, so by the chain rule the gradient of `vₖ`
is no longer than that of `uₖ` and `D(vₖ, vₖ) ≤ D(uₖ, uₖ)`. Moreover `|vₖ - |uₖ|| ≤ ηₖ`
pointwise, so `vₖ → |w|` in `L²(M)`.

The passage to the limit is a general closedness property of the Dirichlet energy
(`TauCeti.Manifold.SobolevH1.exists_toLp_eq_and_dirichletForm_le_of_tendsto`): if the values of
`vₖ ∈ H¹(M)` converge to `f` in `L²(M)` and `D(vₖ, vₖ) ≤ cₖ → c`, then `f` is the value of some
`x ∈ H¹(M)` with `D(x, x) ≤ c`. Indeed `vₖ` is then bounded in the Hilbert space `H¹(M)`, so a
subsequence converges weakly to some `x`. The value map is continuous and linear, so the value of
`x` is the strong limit `f` of the values, and the Dirichlet energy, a nonnegative continuous
quadratic form, is weakly lower semicontinuous.

The finer statement `|∇|w|| = |∇w|` almost everywhere, which gives `D(w', w') = D(w, w)`, needs
the pointwise weak gradient of an element of `H¹(M)` and is not proved here.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_toLp_eq_and_dirichletForm_le_of_tendsto`: an `L²` limit of
  elements of `H¹(M)` with convergent bounds on their Dirichlet energies lies in `H¹(M)`, with
  energy at most the limit bound.
* `TauCeti.Manifold.SobolevH1.exists_toLp_eq_abs_and_dirichletForm_le`: absolute values in
  `H¹(M)` do not increase the Dirichlet energy.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Lemma 7.6.
-/

public section

open Bornology Bundle Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The smooth function `TauCeti.smoothAbs η ∘ u`, a regularization of `|u|` for `η ≠ 0`. -/
private def smoothAbsComp (u : C^∞⟮I, M; ℝ⟯) {η : ℝ} (hη : η ≠ 0) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x ↦ TauCeti.smoothAbs η (u x), (TauCeti.contDiff_smoothAbs hη).comp_contMDiff u.contMDiff⟩

omit [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold I 1 M] [MeasurableSpace M]
  [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem coe_smoothAbsComp (u : C^∞⟮I, M; ℝ⟯) {η : ℝ} (hη : η ≠ 0) :
    ⇑(smoothAbsComp u hη) = fun x ↦ TauCeti.smoothAbs η (u x) :=
  (rfl)

/-- The regularization `TauCeti.smoothAbs η ∘ u` does not increase the Dirichlet energy. -/
private theorem dirichletForm_ofSmooth_smoothAbsComp_le (u : C^∞⟮I, M; ℝ⟯) {η : ℝ} (hη : η ≠ 0) :
    dirichletForm (ofSmooth (smoothAbsComp u hη)) (ofSmooth (smoothAbsComp u hη)) ≤
      dirichletForm (ofSmooth u) (ofSmooth u) := by
  have hu := u.contMDiff.of_le (n := ∞) (m := 1) (by simp)
  have hv := (smoothAbsComp u hη).contMDiff.of_le (n := ∞) (m := 1) (by simp)
  simp only [dirichletForm_ofSmooth, real_inner_self_eq_norm_sq]
  refine integral_mono (continuous_norm_sq_mgradient hv).integrable_of_compactSpace
    (continuous_norm_sq_mgradient hu).integrable_of_compactSpace fun x ↦ ?_
  have hg := mgradient_comp_hasDerivAt (TauCeti.hasDerivAt_smoothAbs hη (u x))
    (hu.mdifferentiableAt one_ne_zero)
  simp only [Function.comp_def] at hg
  rw [coe_smoothAbsComp, hg, norm_smul, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _)
    (Real.abs_div_sqrt_sq_add_le_one (sq_nonneg η) (u x))) 2

/-- For `η > 0`, the value of `TauCeti.smoothAbs η ∘ u` is within `C η` of `|u|` in `L²(M)`, where
`C` depends only on the volume of `M`. -/
private theorem norm_toLp_smoothAbsComp_sub_abs_le (u : C^∞⟮I, M; ℝ⟯) {η : ℝ} (hη : 0 < η) :
    ‖toLp (ofSmooth (smoothAbsComp u hη.ne')) - |toLp (ofSmooth u)|‖ ≤
      measureUnivNNReal (riemannianVolume I M) ^ (2 : ℝ≥0∞).toReal⁻¹ * η := by
  refine Lp.norm_le_of_ae_bound hη.le ?_
  filter_upwards [Lp.coeFn_sub (toLp (ofSmooth (smoothAbsComp u hη.ne'))) |toLp (ofSmooth u)|,
    Lp.coeFn_abs (toLp (ofSmooth u)), toLp_ofSmooth_ae_eq (smoothAbsComp u hη.ne'),
    toLp_ofSmooth_ae_eq u] with x hsub habs hv hu
  rw [hsub, Pi.sub_apply, habs, hv, hu, coe_smoothAbsComp, Real.norm_eq_abs]
  exact TauCeti.abs_smoothAbs_sub_abs_le hη.le (u x)

/-- **Closedness of the Dirichlet energy under `L²` convergence.** If the values of `vₙ ∈ H¹(M)`
converge to `f` in `L²(M)` while `D(vₙ, vₙ) ≤ cₙ` with `cₙ → c`, then `f` is the value of some
`x ∈ H¹(M)` with `D(x, x) ≤ c`. -/
theorem exists_toLp_eq_and_dirichletForm_le_of_tendsto {v : ℕ → SobolevH1 I M}
    {f : Lp ℝ 2 (riemannianVolume I M)} {c : ℕ → ℝ} {c₀ : ℝ}
    (hv : Tendsto (fun n ↦ toLp (v n)) atTop (𝓝 f)) (hc : Tendsto c atTop (𝓝 c₀))
    (hvc : ∀ n, dirichletForm (v n) (v n) ≤ c n) :
    ∃ x : SobolevH1 I M, toLp x = f ∧ dirichletForm x x ≤ c₀ := by
  -- Since `‖v n‖² = D(v n, v n) + ‖toLp (v n)‖²`, the sequence `v` is bounded in `H¹(M)`.
  have hb : IsBounded (range v) := by
    obtain ⟨R₁, hR₁⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hv)
    obtain ⟨R₂, hR₂⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hc)
    refine isBounded_iff_forall_norm_le.2 ⟨R₂ + R₁ ^ 2 + 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 := hR₁ _ (mem_range_self n)
    have h2 := (le_abs_self (c n)).trans (hR₂ _ (mem_range_self n))
    nlinarith [norm_sq_eq_dirichletForm_add (v n), hvc n, norm_nonneg (toLp (v n)),
      sq_nonneg (‖v n‖ - 1)]
  -- A subsequence converges weakly in the Hilbert space `H¹(M)`.
  obtain ⟨x, φ, hφ, hx⟩ := TauCeti.tendsto_subseq_toWeakSpace_of_isBounded (𝕜 := ℝ)
    TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace hb
  have hweak (ℓ : StrongDual ℝ (SobolevH1 I M)) :
      Tendsto (fun n ↦ ℓ (v (φ n))) atTop (𝓝 (ℓ x)) :=
    TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hx ℓ
  refine ⟨x, ?_, ?_⟩
  · -- The weak limit of the values is their strong limit `f`.
    set g := toLp x - f
    have h1 : Tendsto (fun n ↦ ⟪g, toLp (v (φ n))⟫_ℝ) atTop (𝓝 ⟪g, toLp x⟫_ℝ) :=
      hweak ((innerSL ℝ g).comp toLp)
    have h2 : Tendsto (fun n ↦ ⟪g, toLp (v (φ n))⟫_ℝ) atTop (𝓝 ⟪g, f⟫_ℝ) :=
      ((innerSL ℝ g).continuous.tendsto _).comp (hv.comp hφ.tendsto_atTop)
    have hg : ⟪g, g⟫_ℝ = 0 := by
      rw [inner_sub_right, tendsto_nhds_unique h1 h2, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 hg)
  · -- Weak lower semicontinuity: `0 ≤ D(v - x, v - x)` gives `2 D(x, v) - D(x, x) ≤ D(v, v)`.
    have h1 : Tendsto (fun n ↦ 2 * dirichletForm x (v (φ n)) - dirichletForm x x) atTop
        (𝓝 (dirichletForm x x)) := by
      convert ((hweak (dirichletForm x)).const_mul 2).sub_const (dirichletForm x x) using 2
      ring
    refine le_of_tendsto_of_tendsto' h1 (hc.comp hφ.tendsto_atTop) fun n ↦ ?_
    have h0 := dirichletForm_self_nonneg (v (φ n) - x)
    simp only [map_sub, sub_apply] at h0
    rw [dirichletForm_comm (v (φ n)) x] at h0
    rw [Function.comp_apply]
    linarith [hvc (φ n)]

/-- **Absolute values in `H¹(M)`.** For every `w ∈ H¹(M)` there is `w' ∈ H¹(M)` whose value in
`L²(M)` is `|w|` and whose Dirichlet energy is at most that of `w`. -/
theorem exists_toLp_eq_abs_and_dirichletForm_le (w : SobolevH1 I M) :
    ∃ w' : SobolevH1 I M, toLp w' = |toLp w| ∧ dirichletForm w' w' ≤ dirichletForm w w := by
  -- Smooth approximations `u n → w`, regularized to `v n = smoothAbs (1 / (n + 1)) ∘ u n`.
  obtain ⟨y, hy, hyw⟩ := mem_closure_iff_seq_limit.1 (denseRange_ofSmooth w)
  choose u hu using hy
  have hlim : Tendsto (fun n ↦ ofSmooth (u n)) atTop (𝓝 w) := by simpa only [hu] using hyw
  have hη (n : ℕ) : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
  refine exists_toLp_eq_and_dirichletForm_le_of_tendsto
    (v := fun n ↦ ofSmooth (smoothAbsComp (u n) (hη n).ne')) ?_
    (((dirichletForm.continuous.clm_apply continuous_id).tendsto w).comp hlim)
    fun n ↦ dirichletForm_ofSmooth_smoothAbsComp_le (u n) (hη n).ne'
  -- The values of `v n` are within `C / (n + 1)` of `|u n|`, which converge to `|w|` in `L²(M)`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C : ℝ := measureUnivNNReal (riemannianVolume I M) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hT : Tendsto (fun n ↦ ‖toLp (ofSmooth (u n)) - toLp w‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((toLp.continuous.tendsto w).comp hlim)
  have hη0 : Tendsto (fun n : ℕ ↦ C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  have h0 : Tendsto (fun n : ℕ ↦ C * (1 / ((n : ℝ) + 1)) +
      ‖toLp (ofSmooth (u n)) - toLp w‖) atTop (𝓝 0) := by
    simpa only [add_zero] using hη0.add hT
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) h0
  calc _ = ‖(toLp (ofSmooth (smoothAbsComp (u n) (hη n).ne')) - |toLp (ofSmooth (u n))|) +
          (|toLp (ofSmooth (u n))| - |toLp w|)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans
        (add_le_add (norm_toLp_smoothAbsComp_sub_abs_le (u n) (hη n)) (norm_abs_sub_abs _ _))

end TauCeti.Manifold.SobolevH1
