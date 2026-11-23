/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Sobolev.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Lp
public import TauCeti.Analysis.Complex.Pompeiu.Holder.Beurling
public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport

/-!
# Comparison of the finite-target Cauchy and Beurling operators

For every order `k ≥ 0`, `0 < α < 1`, and finite-dimensional complex normed target,
the supported Hölder and Sobolev operators have the same Cauchy value and Beurling field.
The order-zero case requires only the supported Hölder datum. On finite-dimensional
Hilbert targets, the Beurling operators agree on every `Lᵖ` input.
-/

public noncomputable section

open MeasureTheory Complex ComplexConjugate Metric Set TopologicalSpace Function
open scoped ENNReal NNReal SchwartzMap

namespace TauCeti.CauchyTransform

section Holder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The graph and all-order Hölder operator have exactly the same value field. -/
theorem graphL_holder_value {k : ℕ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c (r : ℝ))) :
    let hf := (f : CkHolderSpace k α ℂ F).contDiff.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (r : ℝ))
        (support_subset_of_mem_supportedCkHolderSubmodule f.property)) (p := p)
    ∀ᵐ w ∂volume.restrict (disc c R : Set ℂ), ∀ hw : w ∈ closedBall c (R : ℝ),
      WeakDerivStep.prev _ (graphL hp hp_top c r R
        ((hf.restrict (closedBall c (r : ℝ))).toLp (f : CkHolderSpace k α ℂ F))) w =
      (cauchyTransformCkCLM k hα hα1 r.coe_nonneg R.coe_nonneg f).1 0 ⟨w, hw⟩
        (fun _ ↦ 0) := by
  dsimp only
  have hf : MemLp (f : CkHolderSpace k α ℂ F) p (volume : Measure ℂ) :=
    (f : CkHolderSpace k α ℂ F).contDiff.continuous.memLp_of_hasCompactSupport
      (.of_support_subset_isCompact (isCompact_closedBall c (r : ℝ))
        (support_subset_of_mem_supportedCkHolderSubmodule f.property))
  filter_upwards [graphL_toLp_prev_ae hp hp_top hf
    (support_subset_of_mem_supportedCkHolderSubmodule f.property) R] with w hw
  intro hx
  rw [cauchyTransformCkCLM_apply_fst]
  exact hw.trans (iteratedFDeriv_zero_apply (𝕜 := ℝ)
    (f := cauchyTransform (f : CkHolderSpace k α ℂ F)) (x := w) (fun _ ↦ 0)).symm

/-- The original-norm `Lp` and Hölder Beurling operators agree, including rough k=0 data. -/
theorem beurling_holder_value {k : ℕ} {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (f : supportedCkHolderSubmodule (E := ℂ) (F := F) k α (closedBall c (r : ℝ))) :
    let hf := (f : CkHolderSpace k α ℂ F).contDiff.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c (r : ℝ))
        (support_subset_of_mem_supportedCkHolderSubmodule f.property)) (p := p)
    ∀ᵐ w ∂volume, ∀ hw : w ∈ closedBall c (R : ℝ),
      (beurlingCkCLM k hα hα1 r.coe_nonneg R.coe_nonneg f).1 0 ⟨w, hw⟩ (0 : Fin 0 → ℂ) =
        beurlingL hp hp_top (hf.toLp (f : CkHolderSpace k α ℂ F)) w := by
  dsimp only
  let u : CkHolderSpace k α ℂ F := f
  have hc : HasCompactSupport (u : ℂ → F) := .of_support_subset_isCompact
    (isCompact_closedBall c (r : ℝ)) (support_subset_of_mem_supportedCkHolderSubmodule f.property)
  have hf : MemLp (u : ℂ → F) p (volume : Measure ℂ) :=
    u.contDiff.continuous.memLp_of_hasCompactSupport hc
  have hT : ContDiff ℝ 1 (cauchyTransform u) :=
    (hc.contDiff_cauchyTransform_of_holderWith_iteratedFDeriv hα hα1
      u.contDiff u.memHolder_iteratedFDeriv.holderWith).of_le (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hD := (hasWeakFDerivOn_cauchy hp hp_top hf
    (support_subset_of_mem_supportedCkHolderSubmodule f.property) ⊤).ae_eq_fderiv
      ((hT.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      (fun x _ ↦ hT.differentiable one_ne_zero x)
  rw [Opens.coe_top, Measure.restrict_univ] at hD
  filter_upwards [hD, coe_global_jet hp hp_top hf] with w hD hj
  intro hw
  rw [beurlingCkCLM_apply_fst_zero]
  rw [hj, fderiv_eq_wirtingerPartsCLM] at hD
  exact (wirtingerPartsCLM_inj.mp hD).1.symm

end Holder

section Agreement

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On compactly supported inputs, the original-norm and Hilbert-target operators agree. -/
private theorem beurlingL_eq_beurlingLp_supported (hp : 1 < p) (hp_top : p ≠ ∞) {f : ℂ → F}
    (hf : MemLp f p (volume : Measure ℂ)) {c : ℂ} {r : ℝ≥0}
    (hs : support f ⊆ closedBall c (r : ℝ)) :
    beurlingL hp hp_top (hf.toLp f) = beurlingLp p hp hp_top (hf.toLp f) := by
  apply Lp.ext
  have hD := (hasWeakFDerivOn_cauchy hp hp_top hf hs ⊤).ae_eq
    (hasWeakFDerivOn_cauchyTransform_of_memLp hp hp_top hf hs ⊤)
  rw [Opens.coe_top, Measure.restrict_univ] at hD
  filter_upwards [hD, coe_global_jet hp hp_top hf] with w hD hj
  rw [hj] at hD
  exact (wirtingerPartsCLM_inj.mp hD).1

/-- On finite Hilbert targets the original-norm construction is exactly the Hilbert-target
operator. -/
theorem beurlingL_eq_beurlingLp (hp : 1 < p) (hp_top : p ≠ ∞) :
    beurlingL (F := F) hp hp_top = beurlingLp (F := F) p hp hp_top := by
  let S := {u : 𝓢(ℂ, F) // HasCompactSupport (u : ℂ → F)}
  have hd : DenseRange (fun u : S ↦ u.val.toLp p (volume : Measure ℂ)) :=
    (SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := F) (μ := volume) hp_top).comp
      SchwartzMap.dense_hasCompactSupport.denseRange_subtypeVal
      (SchwartzMap.toLpCLM ℂ F p (volume : Measure ℂ)).continuous
  apply DFunLike.coe_injective
  apply hd.equalizer (beurlingL hp hp_top).continuous (beurlingLp p hp hp_top).continuous
  funext u
  obtain ⟨r, hr⟩ := u.property.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hs : support (u.val : ℂ → F) ⊆ closedBall 0 (r.toNNReal : ℝ) :=
    (subset_tsupport _).trans (hr.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal r)))
  exact beurlingL_eq_beurlingLp_supported hp hp_top (u.val.memLp p volume) hs

end Agreement

end TauCeti.CauchyTransform
