/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integrability from polynomial bounds at infinity and at an endpoint

On a finite-dimensional real normed space of dimension `d`, a locally integrable function which is
`O((1 + ‖x‖) ^ (-r))` at infinity for some `r > d` is integrable, for every additive Haar measure.
This combines Mathlib's integrability of the Japanese bracket (`integrable_one_add_norm`) with its
criterion `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`.

On the half-line `(0, ∞)`, a function `q` with `q(t) = O(t^{a-1})` as `t → 0+` for some `a > 0`
is integrable near `0`, so `t ↦ e^{-σt} q(t)` is integrable on `(0, ∞)` exactly when `q` is
locally integrable on `(0, ∞)` and `t ↦ e^{-σt} q(t)` is integrable on `(1, ∞)`
(`TauCeti.integrableOn_exp_neg_mul_smul_iff`). This is the second form of the integrability
hypothesis of Watson's lemma `Asymptotics.hasAsymptoticExpansion_laplace`.
-/

public section

namespace MeasureTheory

open Asymptotics Filter Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {f : E → F}

/-- A locally integrable function on a finite-dimensional real normed space which is
`O((1 + ‖x‖) ^ (-r))` at infinity, with `r` larger than the dimension, is integrable. -/
theorem LocallyIntegrable.integrable_of_isBigO_one_add_norm_rpow_neg
    (hf : LocallyIntegrable f μ) {r : ℝ} (hr : (finrank ℝ E : ℝ) < r)
    (ho : f =O[cocompact E] fun x ↦ (1 + ‖x‖) ^ (-r)) : Integrable f μ :=
  hf.integrable_of_isBigO_cocompact ho ((integrable_one_add_norm hr).integrableAtFilter _)

end MeasureTheory

namespace TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-- The two forms of the integrability hypothesis of Watson's lemma. If `q(t) = O(t^{a-1})` as
`t → 0+` with `a > 0`, then `t ↦ e^{-σt} q(t)` is integrable on `(0, ∞)` if and only if `q` is
locally integrable on `(0, ∞)` and `t ↦ e^{-σt} q(t)` is integrable on `(1, ∞)`. -/
theorem integrableOn_exp_neg_mul_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℝ → E} {a σ : ℝ} (ha : 0 < a) (hq : q =O[𝓝[>] 0] fun t => t ^ (a - 1)) :
    IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0) ↔
      LocallyIntegrableOn q (Ioi 0) ∧ IntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 1) := by
  refine ⟨fun h => ⟨?_, h.mono_set (Ioi_subset_Ioi zero_le_one)⟩, fun ⟨hloc, h1⟩ => ?_⟩
  · refine (h.locallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
      (g := fun t => Real.exp (σ * t)) (by fun_prop)).congr (Eventually.of_forall fun t => ?_)
    simp [smul_smul, ← Real.exp_add]
  have hloc' : LocallyIntegrableOn (fun t => Real.exp (-σ * t) • q t) (Ioi 0) :=
    hloc.continuousOn_smul isOpen_Ioi.isLocallyClosed (by fun_prop)
  refine integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.2
    ⟨⟨Ioi 1, Ioi_mem_atTop 1, h1⟩, ?_, hloc'⟩
  have hexp : (fun t : ℝ => Real.exp (-σ * t)) =O[𝓝[>] 0] fun _ => (1 : ℝ) :=
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-σ * t)).tendsto 0).isBigO_one ℝ
      |>.mono nhdsWithin_le_nhds
  refine ((hexp.smul hq).congr_right fun t => one_smul ℝ _).integrableAtFilter
    ⟨Ioi 0, self_mem_nhdsWithin, hloc'.aestronglyMeasurable⟩
    ⟨Ioc 0 1, Ioc_mem_nhdsGT one_pos,
      (intervalIntegral.intervalIntegrable_rpow' (r := a - 1) (by linarith)).1⟩

end TauCeti
