/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Proportional

/-!
# Transition functions for contact forms

Two nowhere-zero smooth real one-forms define the same hyperplane field exactly when one is a
unique nowhere-zero smooth function times the other. Applied on an overlap of contact charts,
this gives the transition function between their defining forms, without a metric or a chosen
transverse field. In particular, contactness depends only on the hyperplane field, provided the
defining forms do not vanish. Multipliers of either sign are allowed: preservation of a chosen
coorientation would additionally require positivity.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1}

/-- Two nowhere-zero smooth one-forms define the same hyperplanes exactly when they differ
by a unique nowhere-zero smooth multiplier. This applies, in particular, to local defining
forms restricted to an overlap. -/
theorem kerDistribution_eq_iff_existsUnique_fun_smul
    (hα : ∀ x, α.1 x ≠ 0) (hβ : ∀ x, β.1 x ≠ 0) :
    β.kerDistribution = α.kerDistribution ↔
      ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, f x ≠ 0) ∧
        ∀ x, β.1 x = f x • α.1 x := by
  constructor
  · intro hker
    have hle (x : M) : RoughForm.ker α.1 x ≤ RoughForm.ker β.1 x := by
      intro v hv
      simpa only [RoughForm.mem_ker, ← mem_kerDistribution, hker] using hv
    obtain ⟨f, ⟨hf, hmul⟩, huniq⟩ := existsUnique_fun_smul_of_ker_le hα hle
    have hf₀ (x : M) : f x ≠ 0 := by
      intro hz
      exact hβ x (by rw [hmul, hz, zero_smul])
    exact ⟨f, ⟨hf, hf₀, hmul⟩, fun g hg ↦ huniq g ⟨hg.1, hg.2.2⟩⟩
  · rintro ⟨f, ⟨_, hf₀, hmul⟩, _⟩
    exact kerDistribution_of_eq_smul hf₀ hmul

/-- A nowhere-zero smooth defining form of the hyperplanes of a contact form is itself
contact. Equivalently, nonvanishing is the only extra condition on a smooth form with that
kernel. -/
theorem IsContactForm.isContactForm_iff_of_kerDistribution_eq (hα : α.IsContactForm)
    (hker : β.kerDistribution = α.kerDistribution) :
    β.IsContactForm ↔ ∀ x, β.1 x ≠ 0 := by
  have hα₀ (x : M) : α.1 x ≠ 0 :=
    (isContactForm_iff_forall_isContactFormAt.mp hα x).ne_zero
  constructor
  · intro hβ x
    exact (isContactForm_iff_forall_isContactFormAt.mp hβ x).ne_zero
  · intro hβ₀
    obtain ⟨f, ⟨hf, hf₀, hmul⟩, _⟩ :=
      (kerDistribution_eq_iff_existsUnique_fun_smul hα₀ hβ₀).mp hker
    exact (isContactForm_iff_of_eq_smul (hf.of_le (by simp)) hf₀ hmul).mpr hα

end TauCeti.SmoothForm
