/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic

/-!
# Reparametrization and restriction of models

Changing parameters by `r : W' → W` replaces a realization map `f` by `f ∘ r`.
It can only remove realized functions, and removes none when `r` is surjective.
Its fibres are preimages under `r`. Restricting parameters to a set uses the subtype,
so its realized functions are exactly the image of that set, including when it is empty.
No regularity or injectivity of the parameter map is needed.

These formulas complement `parameterSetoid_comp_iff` and `fiberEquiv`, which describe
parameter equivalence and transport of fibres along an equivalence of parameter spaces.
For the exact image of an arbitrary reparametrization, the existing presentation formula
`realizedFunctions_eq_image_range (fun _ => rfl)` gives
`realizedFunctions (f ∘ r) = f '' Set.range r`.

The realization-map and fibre conventions follow Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), Definition 3.1 and §4.3.
The elementary reparametrization consequences here use Mathlib's range, restriction,
and preimage APIs; they are not additional results attributed to the paper.
-/

public section

namespace TauCeti.Neuromanifold

variable {W W' X Y : Type*}

/-- Changing parameters can only remove realized functions. -/
theorem realizedFunctions_comp_subset (f : W → X → Y) (r : W' → W) :
    realizedFunctions (f ∘ r) ⊆ realizedFunctions f := by
  rw [realizedFunctions_def, realizedFunctions_def]
  exact Set.range_comp_subset_range r f

/-- A surjective change of parameters does not change the realized functions.
In particular, this applies to any equivalence of parameter spaces. -/
theorem realizedFunctions_comp_of_surjective (f : W → X → Y) {r : W' → W}
    (hr : Function.Surjective r) : realizedFunctions (f ∘ r) = realizedFunctions f := by
  rw [realizedFunctions_def, realizedFunctions_def, hr.range_comp]

/-- The fibre of a reparametrized model is the preimage of the original fibre. -/
@[simp] theorem fiber_comp (f : W → X → Y) (r : W' → W) (g : X → Y) :
    fiber (f ∘ r) g = r ⁻¹' fiber f g := by
  rw [fiber_def, fiber_def, Set.preimage_comp]

/-- Restricting parameters to `S` realizes exactly the image of `S`, with no nonemptiness
assumption. The restricted parameter space is the subtype `S`. -/
theorem realizedFunctions_domRestrict (f : W → X → Y) (S : Set W) :
    realizedFunctions (S.domRestrict f) = f '' S := by
  rw [realizedFunctions_def, Set.range_domRestrict]

end TauCeti.Neuromanifold
