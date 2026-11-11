/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Evaluation of Pontryagin characters

Evaluation at a fixed monoid element is continuous on the Pontryagin dual. Its complex-valued
form is integrable against every finite measure. These two lemmas supply the integrands for
Fourier–Stieltjes transforms, and apply to arbitrary monoids with a topology. On a weakly locally
compact monoid, characters in a compact set are also uniformly close at nearby points; this
estimate needs the weak local compactness and feeds the continuity of the transform.
-/

public section

open MeasureTheory
open scoped Topology

namespace TauCeti.PontryaginDual

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- Complex-valued evaluation of a Pontryagin character at a fixed monoid element is continuous. -/
@[fun_prop]
theorem continuous_coe_eval_const (g : G) :
    Continuous (fun χ : _root_.PontryaginDual G => (χ g : ℂ)) :=
  continuous_subtype_val.comp (continuous_eval_const (F := G →ₜ* Circle) g)

/-- Characters in a compact set `K` are uniformly close at `x` and at `g`, once `x` is near `g`:
for every `δ > 0`, eventually in `x` near `g`, `‖χ x - χ g‖ ≤ δ` for all `χ ∈ K`. This is joint
continuity of evaluation together with compactness of `K`. -/
theorem eventually_forall_norm_coe_eval_sub_le [WeaklyLocallyCompactSpace G] (g : G)
    {K : Set (_root_.PontryaginDual G)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x in 𝓝 g, ∀ χ ∈ K, ‖(χ x : ℂ) - (χ g : ℂ)‖ ≤ δ := by
  -- Joint evaluation and compactness give a common bound for all characters in K.
  have heval : Continuous (fun p : G × _root_.PontryaginDual G => (p.2 p.1 : ℂ)) :=
    continuous_subtype_val.comp
      ((continuous_eval (F := G →ₜ* Circle)).comp continuous_swap)
  apply hK.eventually_forall_of_forall_eventually
  intro χ _
  have hcont := (heval.sub
    ((continuous_coe_eval_const g).comp continuous_snd)).norm
  exact (hcont.continuousAt.eventually_lt continuousAt_const
    (by simpa using hδ)).mono fun _ h => h.le

variable [MeasurableSpace (_root_.PontryaginDual G)]
  [OpensMeasurableSpace (_root_.PontryaginDual G)]

/-- Complex-valued evaluation of a Pontryagin character is integrable against a finite measure. -/
theorem integrable_coe_eval
    {μ : Measure (_root_.PontryaginDual G)} [IsFiniteMeasure μ] (g : G) :
    Integrable (fun χ : _root_.PontryaginDual G => (χ g : ℂ)) μ :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_coe_eval_const g).aestronglyMeasurable
    (.of_forall fun χ => by simp)

end TauCeti.PontryaginDual
