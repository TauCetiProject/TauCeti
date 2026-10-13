/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Translation continuity in `L¹`

Translating an integrable function by a convergent family of shifts gives convergence in the
integral of the norm of the difference. The measure can be any locally finite, inner regular,
translation-invariant Borel measure on a normed additive commutative group.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory

/-- Translation is continuous in the `L¹` distance from a fixed translate. -/
theorem Integrable.continuous_integral_norm_translate_sub
    {G E : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    {k : G → E} (hk : Integrable k μ) (b : G) :
    Continuous (fun c : G ↦ ∫ z : G, ‖k (z - c) - k (z - b)‖ ∂μ) := by
  let g : G → C(G, G) := fun c ↦ ⟨fun z ↦ z - c, continuous_id.sub continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry g (continuous_snd.sub continuous_fst)
  let f : G → Lp E 1 μ := fun c ↦
    Lp.compMeasurePreserving (g c) (measurePreserving_sub_right μ c) (hk.toL1 k)
  have hf : Continuous f :=
    continuous_const.compMeasurePreservingLp hg (fun c ↦ measurePreserving_sub_right μ c)
      (by simp)
  have hae (c : G) : f c =ᵐ[μ] fun z ↦ k (z - c) :=
    (Lp.coeFn_compMeasurePreserving (hk.toL1 k) (measurePreserving_sub_right μ c)).trans
      ((measurePreserving_sub_right μ c).quasiMeasurePreserving.ae_eq_comp hk.coeFn_toL1)
  have heq (c : G) : ‖f c - f b‖ = ∫ z : G, ‖k (z - c) - k (z - b)‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae
      (((Lp.coeFn_sub (f c) (f b)).trans ((hae c).sub (hae b))).fun_comp (fun x : E ↦ ‖x‖))
  exact ((hf.sub continuous_const).norm).congr heq

/-- Convergent shifts of an integrable function converge in `L¹`. -/
theorem Integrable.tendsto_integral_norm_translate_sub
    {G E α : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant]
    [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    {k : G → E} (hk : Integrable k μ) {c : α → G} {b : G} {l : Filter α}
    (hc : Tendsto c l (𝓝 b)) :
    Tendsto (fun a ↦ ∫ z : G, ‖k (z - c a) - k (z - b)‖ ∂μ) l (𝓝 0) := by
  simpa only [Function.comp_def, sub_self, norm_zero, integral_zero] using
    (hk.continuous_integral_norm_translate_sub b).continuousAt.tendsto.comp hc

end MeasureTheory
