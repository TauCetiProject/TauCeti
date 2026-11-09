/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic

/-!
# Changing the inputs and outputs of a realization map

Postcomposing the outputs of a model, or precomposing its inputs, sends its neuromanifold
onto the corresponding image of realized functions. An injective output map preserves and
reflects parameter equivalence, as does a surjective input map. In these cases the realization
fibres over corresponding functions are equal, without identifying or changing parameters.

These statements concern equality at every input. In particular, restriction to a set of
sampled inputs need not reflect parameter equivalence. No nonemptiness assumptions are needed
on the parameters, inputs, or outputs.

The realization-map and fibre conventions follow Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), Definition 3.1 and §4.3.
The transport laws are elementary consequences of these definitions.
-/

public section

namespace TauCeti.Neuromanifold

variable {W X X' Y Z : Type*}

/-- Postcomposition on outputs sends the neuromanifold onto the image of its realized
functions under postcomposition. -/
theorem realizedFunctions_postcomp (f : W → X → Y) (h : Y → Z) :
    realizedFunctions (fun w => h ∘ f w) = (fun g => h ∘ g) '' realizedFunctions f := by
  simpa only [realizedFunctions_def] using
    realizedFunctions_eq_image_range (E := fun g => h ∘ g) (c := f) fun _ => rfl

/-- Precomposition on inputs sends the neuromanifold onto the image of its realized
functions under precomposition. -/
theorem realizedFunctions_precomp (f : W → X → Y) (a : X' → X) :
    realizedFunctions (fun w => f w ∘ a) = (fun g => g ∘ a) '' realizedFunctions f := by
  simpa only [realizedFunctions_def] using
    realizedFunctions_eq_image_range (E := fun g => g ∘ a) (c := f) fun _ => rfl

/-- An injective change of outputs preserves and reflects parameter equivalence. -/
@[simp] theorem parameterSetoid_postcomp (f : W → X → Y) {h : Y → Z}
    (hh : Function.Injective h) :
    parameterSetoid (fun w => h ∘ f w) = parameterSetoid f := by
  simpa only [Setoid.ext_iff, Setoid.ker_def, parameterSetoid_iff] using
    parameterSetoid_eq_ker (E := fun g => h ∘ g) (c := f) hh.comp_left fun _ => rfl

/-- A surjective change of inputs preserves and reflects parameter equivalence. -/
@[simp] theorem parameterSetoid_precomp (f : W → X → Y) {a : X' → X}
    (ha : Function.Surjective a) :
    parameterSetoid (fun w => f w ∘ a) = parameterSetoid f := by
  simpa only [Setoid.ext_iff, Setoid.ker_def, parameterSetoid_iff] using
    parameterSetoid_eq_ker (E := fun g => g ∘ a) (c := f) ha.injective_comp_right fun _ => rfl

/-- An injective change of outputs does not change the fibre over the corresponding
postcomposed function. -/
@[simp] theorem fiber_postcomp (f : W → X → Y) {h : Y → Z}
    (hh : Function.Injective h) (g : X → Y) :
    fiber (fun w => h ∘ f w) (h ∘ g) = fiber f g := by
  simpa only [fiber_def] using
    fiber_apply_eq_preimage (E := fun g => h ∘ g) (c := f) hh.comp_left (fun _ => rfl) g

/-- A surjective change of inputs does not change the fibre over the corresponding
precomposed function. -/
@[simp] theorem fiber_precomp (f : W → X → Y) {a : X' → X}
    (ha : Function.Surjective a) (g : X → Y) :
    fiber (fun w => f w ∘ a) (g ∘ a) = fiber f g := by
  simpa only [fiber_def] using
    fiber_apply_eq_preimage (E := fun g => g ∘ a) (c := f) ha.injective_comp_right (fun _ => rfl) g

end TauCeti.Neuromanifold
