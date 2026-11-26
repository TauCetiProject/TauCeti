/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Proportional
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Topology.LocallyConstant.Sign

/-!
# Transition functions for contact forms

Two nowhere-zero smooth real one-forms define the same hyperplane field exactly when one is a
unique nowhere-zero smooth function times the other. Applied on an overlap of contact charts,
this gives the transition function between their defining forms, without a metric or a chosen
transverse field. In particular, contactness depends only on the hyperplane field: a form with
the same hyperplanes as a contact form is contact. Multipliers of either sign are allowed:
preservation of a chosen coorientation would additionally require positivity.

On a compact manifold, multiplying a form `β` with the kernel of a nowhere-vanishing form `α` by a
suitable locally constant nowhere-vanishing function `c`, a nonzero constant of the sign of the
transition function on each of the sets where that sign is constant, turns it into `f α` with `f`
above any given bound (`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`). This is how
Barraud, Damian, Humilière and Oancea, in their proof of Corollary E, reduce the contact forms
defining the contact structure of the boundary of a Liouville domain to the forms `f α` with
`f > 1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Corollary E.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1}

/-- A smooth one-form has the same hyperplanes as a nowhere-zero smooth one-form exactly when it
is a unique nowhere-zero smooth multiple of it. This applies, in particular, to local defining
forms restricted to an overlap. -/
theorem kerDistribution_eq_iff_existsUnique_fun_smul (hα : ∀ x, α.val x ≠ 0) :
    β.kerDistribution = α.kerDistribution ↔
      ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, f x ≠ 0) ∧
        ∀ x, β.val x = f x • α.val x := by
  constructor
  · intro hker
    have hle (x : M) : RoughForm.ker α.val x ≤ RoughForm.ker β.val x := by
      intro v hv
      simpa only [RoughForm.mem_ker, ← mem_kerDistribution, hker] using hv
    obtain ⟨f, ⟨hf, hmul⟩, huniq⟩ := existsUnique_fun_smul_of_ker_le hα hle
    have hf₀ (x : M) : f x ≠ 0 := by
      intro hz
      exact hα x ((apply_eq_zero_iff_of_kerDistribution_eq hker x).mp
        (by rw [hmul, hz, zero_smul]))
    exact ⟨f, ⟨hf, hf₀, hmul⟩, fun g hg ↦ huniq g ⟨hg.1, hg.2.2⟩⟩
  · rintro ⟨f, ⟨_, hf₀, hmul⟩, _⟩
    exact kerDistribution_of_eq_smul hf₀ hmul

/-- A smooth form with the same hyperplanes as a contact form is itself contact. -/
theorem IsContactForm.isContactForm_of_kerDistribution_eq (hα : α.IsContactForm)
    (hker : β.kerDistribution = α.kerDistribution) : β.IsContactForm := by
  obtain ⟨f, ⟨hf, hf₀, hmul⟩, _⟩ :=
    (kerDistribution_eq_iff_existsUnique_fun_smul hα.apply_ne_zero).mp hker
  exact (isContactForm_iff_of_eq_smul (hf.of_le (by simp)) hf₀ hmul).mpr hα

/-- **Rescaling a form with the kernel of `α` above a bound.** Let `α` be a nowhere-vanishing
one-form on a compact manifold and `β` a smooth one-form with the same kernel, `ker β = ker α`, such
as another contact form defining the same contact structure. For every `a`, there is a locally
constant nowhere-vanishing function `c`, a nonzero constant on each connected component, such that
`c β = f α` for a smooth function `f > a`. -/
theorem exists_isLocallyConstant_smul_eq_smul [CompactSpace M] (hα : ∀ x, α.val x ≠ 0)
    (hβ : β.kerDistribution = α.kerDistribution) (a : ℝ) :
    ∃ c f : M → ℝ, IsLocallyConstant c ∧ (∀ x, c x ≠ 0) ∧ ContMDiff I 𝓘(ℝ) ∞ f ∧
      (∀ x, a < f x) ∧ ∀ x, c x • β.val x = f x • α.val x := by
  obtain ⟨g, ⟨hg, hg₀, hgβ⟩, -⟩ := (kerDistribution_eq_iff_existsUnique_fun_smul hα).1 hβ
  obtain ⟨c, hc, hc₀, hcg⟩ := hg.continuous.exists_isLocallyConstant_lt_mul hg₀ a
  exact ⟨c, c * g, hc, hc₀, hc.contMDiff.mul hg, hcg, fun x ↦ by
    rw [hgβ, smul_smul, Pi.mul_apply]⟩

end TauCeti.SmoothForm
