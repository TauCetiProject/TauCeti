/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic

/-!
# Reparametrization and restriction of models

Precomposing a realization map with a parameter map can only reduce its realized image.
It preserves the image precisely when the parameter map meets every realized fibre;
surjectivity of the parameter map is sufficient but not necessary. Restriction to a set of
parameters is the subtype instance of this construction, including the empty set.
`realizedFunctions_domRestrict` reduces empty and singleton restrictions to the ordinary
image simp lemmas, so no nonemptiness assumption or separate degenerate-case API is needed.

These laws let a model with a constrained parameter space use the same realized-function and
fibre API as the unrestricted model. Parameter equivalence and equivalences of fibres under
an equivalence of parameter spaces are already supplied by `parameterSetoid_comp_iff` and
`fiberEquiv`.

The realization-map and fibre conventions follow Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), Definition 3.1 and §4.3.
The reparametrization laws are elementary consequences, not additional results attributed
to that paper. They use Mathlib's range, image, preimage, and domain-restriction APIs.
-/

public section

namespace TauCeti.Neuromanifold

variable {W W' X Y : Type*}

/-- Reparametrization cannot introduce a new realized function. -/
theorem realizedFunctions_comp_subset (f : W → X → Y) (r : W' → W) :
    realizedFunctions (f ∘ r) ⊆ realizedFunctions f := by
  simpa only [realizedFunctions_def] using Set.range_comp_subset_range r f

/-- A surjective change of parameters preserves the realized functions. -/
theorem realizedFunctions_comp_of_surjective (f : W → X → Y) {r : W' → W}
    (hr : Function.Surjective r) :
    realizedFunctions (f ∘ r) = realizedFunctions f := by
  simpa only [realizedFunctions_def] using hr.range_comp f

/-- Equivalent parameter spaces give the same realized functions. -/
@[simp] theorem realizedFunctions_comp_equiv (f : W → X → Y) (e : W' ≃ W) :
    realizedFunctions (f ∘ e) = realizedFunctions f :=
  realizedFunctions_comp_of_surjective f e.surjective

/-- Reparametrized fibres are preimages of the original fibres. -/
@[simp] theorem fiber_comp (f : W → X → Y) (r : W' → W) (g : X → Y) :
    fiber (f ∘ r) g = r ⁻¹' fiber f g := by
  simp only [fiber_def, Set.preimage_comp]

/-- Reparametrization preserves the image exactly when it meets every realized fibre.
This does not require the parameter map itself to be surjective. -/
theorem realizedFunctions_comp_eq_iff (f : W → X → Y) (r : W' → W) :
    realizedFunctions (f ∘ r) = realizedFunctions f ↔
      ∀ w, (r ⁻¹' fiber f (f w)).Nonempty := by
  constructor
  · intro h w
    have hw : f w ∈ realizedFunctions (f ∘ r) := by
      rw [h]
      exact (mem_realizedFunctions f (f w)).mpr ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := (mem_realizedFunctions (f ∘ r) (f w)).mp hw
    exact ⟨v, (mem_fiber f (f w) (r v)).mpr hv⟩
  · intro h
    apply (realizedFunctions_comp_subset f r).antisymm
    intro g hg
    obtain ⟨w, rfl⟩ := (mem_realizedFunctions f g).mp hg
    obtain ⟨v, hv⟩ := h w
    exact (mem_realizedFunctions (f ∘ r) (f w)).mpr
      ⟨v, (mem_fiber f (f w) (r v)).mp hv⟩

/-- Restricting parameters to `s` realizes exactly the image of `s`. -/
@[simp] theorem realizedFunctions_domRestrict (f : W → X → Y) (s : Set W) :
    realizedFunctions (s.domRestrict f) = f '' s := by
  simpa only [realizedFunctions_def] using Set.range_domRestrict f s

end TauCeti.Neuromanifold
