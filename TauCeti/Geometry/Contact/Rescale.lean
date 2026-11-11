/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Jacobi
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Changes of contact form for Hamiltonian fields and Jacobi brackets

If `β = u α` for a nowhere-zero function `u`, a section of the contact line represented by
`f` in the trivialization `α` is represented by `u f` in the trivialization `β`. Its contact
Hamiltonian vector field is unchanged, and its Jacobi bracket transforms by the same multiplier:
`X_(u f)^(u α) = X_f^α` and `{u f, u g}_(u α) = u {f, g}_α`.

These identities allow the local Hamiltonian fields and brackets to agree on overlaps of contact
line trivializations, including coorientation-reversing overlaps. They use only first derivatives
of the multiplier and Hamiltonians. The forms themselves are smooth, as in the existing contact
form API.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians).
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1} {u f g : M → ℝ}
  {X : (x : M) → TangentSpace I x}

/-- Changing a contact form by `u` changes the Hamiltonian of a fixed contact vector field
by the same factor. No positivity of `u` is required. -/
theorem IsContactHamiltonianVectorField.of_eq_smul
    (hX : α.IsContactHamiltonianVectorField f X) (hα : α.IsContactForm)
    (hu : ContMDiff I 𝓘(ℝ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
    (hβ : ∀ x, β.1 x = u x • α.1 x) (hf : MDifferentiable I 𝓘(ℝ) f) :
    β.IsContactHamiltonianVectorField (u * f) X := by
  have hβc := (isContactForm_iff_of_eq_smul hu hu₀ hβ).2 hα
  apply hβc.isContactHamiltonianVectorField_iff_kerDistribution.2
  intro x
  refine ⟨by simp [hβ, hX.apply_eq], fun v hv ↦ ?_⟩
  rw [kerDistribution_of_eq_smul hu₀ hβ] at hv
  have hvα := mem_kerDistribution.1 hv
  have hβ' : β.1 = fun y ↦ u y • α.1 y := funext hβ
  rw [hβ', mextDeriv_fun_smul_apply ((hu x).mdifferentiableAt one_ne_zero)
    (α.mdifferentiableAt x), hvα, hX.apply_eq, hX.mextDeriv_apply_eq,
    hvα, mvfderiv_mul ((hu x).mdifferentiableAt one_ne_zero) (hf x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- The Hamiltonian field of a contact-line section is independent of its trivialization:
simultaneously multiplying the form and the Hamiltonian by `u` leaves the field unchanged. -/
theorem contactHamiltonianVectorField_of_eq_smul
    (hu : ContMDiff I 𝓘(ℝ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
    (hβ : ∀ x, β.1 x = u x • α.1 x) (hf : MDifferentiable I 𝓘(ℝ) f) :
    β.contactHamiltonianVectorField (u * f) = α.contactHamiltonianVectorField f := by
  have hβc := (isContactForm_iff_of_eq_smul hu hu₀ hβ).2 hα
  exact (hβc.isContactHamiltonianVectorField_iff_eq.1
    ((hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).of_eq_smul
      hα hu hu₀ hβ hf)).symm

/-- The Reeb derivative of the transformed Hamiltonian is the infinitesimal multiplier
of its contact field, corrected by the derivative of the change of form. -/
theorem mul_mvfderiv_reebVectorField_of_eq_smul
    (hu : ContMDiff I 𝓘(ℝ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
    (hβ : ∀ x, β.1 x = u x • α.1 x) (hf : MDifferentiable I 𝓘(ℝ) f) (x : M) :
    u x * mvfderiv I (u * f) x (β.reebVectorField x) =
      mvfderiv I u x (α.contactHamiltonianVectorField f x) +
        u x * mvfderiv I f x (α.reebVectorField x) := by
  have hX := (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).of_eq_smul
    hα hu hu₀ hβ hf
  -- Evaluate the transformed contraction equation on the original Reeb vector.
  have h := hX.mextDeriv_apply_eq x (α.reebVectorField x)
  have hβ' : β.1 = fun y ↦ u y • α.1 y := funext hβ
  rw [hβ', mextDeriv_fun_smul_apply ((hu x).mdifferentiableAt one_ne_zero)
    (α.mdifferentiableAt x), hα.apply_reebVectorField,
    hα.apply_contactHamiltonianVectorField, hα.mextDeriv_reebVectorField_right,
    mvfderiv_mul ((hu x).mdifferentiableAt one_ne_zero) (hf x)] at h
  simp only [ContinuousAlternatingMap.smul_apply, add_apply,
    smul_apply, smul_eq_mul, hα.apply_reebVectorField] at h
  rw [mvfderiv_mul ((hu x).mdifferentiableAt one_ne_zero) (hf x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  linarith

/-- **The contact Jacobi bracket respects changes of contact-line trivialization.** For
`β = u α`, the bracket of `u f` and `u g` is `u {f,g}_α`, also for negative multipliers. -/
theorem jacobiBracket_of_eq_smul
    (hu : ContMDiff I 𝓘(ℝ) 1 u) (hu₀ : ∀ x, u x ≠ 0)
    (hβ : ∀ x, β.1 x = u x • α.1 x)
    (hf : MDifferentiable I 𝓘(ℝ) f) (hg : MDifferentiable I 𝓘(ℝ) g) (x : M) :
    β.jacobiBracket (u * f) (u * g) x = u x * α.jacobiBracket f g x := by
  have hβc := (isContactForm_iff_of_eq_smul hu hu₀ hβ).2 hα
  rw [hβc.jacobiBracket_eq_mvfderiv,
    hα.contactHamiltonianVectorField_of_eq_smul hu hu₀ hβ hf,
    hα.jacobiBracket_eq_mvfderiv,
    mvfderiv_mul ((hu x).mdifferentiableAt one_ne_zero) (hg x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Pi.mul_apply]
  have h := hα.mul_mvfderiv_reebVectorField_of_eq_smul hu hu₀ hβ hf x
  linear_combination -g x * h

end IsContactForm

end TauCeti.SmoothForm
