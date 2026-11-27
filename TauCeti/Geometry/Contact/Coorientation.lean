/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.Distribution.Coorientation

/-!
# Coorientable contact structures and global contact forms

A contact structure `ξ` (`TauCeti.IsContactDistribution`) is defined by its hyperplanes alone.
Locally it is the kernel of a contact form, and the local contact forms at a point are the nonzero
elements of the annihilator line `ξ⁰ ⊆ T*M` (`TauCeti.CotangentBundle.annihilatorSpace`). A global
contact form with kernel `ξ` is extra data: it exists exactly when `ξ` is *coorientable*, that is,
when the line `ξ⁰` admits a continuous section vanishing nowhere, and exactly when the smooth line
bundle `ξ⁰` is trivial. A continuous choice of nonzero covectors in `ξ⁰`, up to positive multiples,
is a coorientation (`TauCeti.IsCoorientation`), and every coorientation is the coorientation of a
contact form (`TauCeti.IsContactDistribution.exists_isContactForm_pos_smul`,
`TauCeti.IsContactDistribution.exists_isContactForm_coorientation_eq`). On a nonempty connected
manifold a coorientable contact structure has exactly two coorientations, those of `α` and `-α` for
any contact form `α` defining it (`TauCeti.IsCoorientation.ncard_setOf_isCoorientation`,
`TauCeti.SmoothForm.coorientation_neg`).

These statements specialize the results for smooth hyperplane fields in
`TauCeti.Geometry.Manifold.Distribution.Coorientation`: a one-form with kernel a contact structure
which vanishes nowhere is a contact form
(`TauCeti.IsContactDistribution.isContactForm_and_kerDistribution_eq_iff`).

## Main results

* `TauCeti.IsContactDistribution.exists_isContactForm_pos_smul`: every coorientation of a contact
  structure is induced by a global contact form.
* `TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_continuous`: a
  contact structure is the kernel of a global contact form exactly when it is coorientable.
* `TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_trivialization`:
  a contact structure is the kernel of a global contact form exactly when its annihilator line
  bundle is smoothly trivial.
* `TauCeti.IsContactDistribution.exists_isContactForm_coorientation_eq`: every coorientation of a
  contact structure is the coorientation of a contact form.
* `TauCeti.IsContactDistribution.exists_isContactForm_kerDistribution_eq_iff_exists_isCoorientation`
  states that a contact structure is the kernel of a global contact form exactly when it has a
  coorientation.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Lemma 1.1.1 (coorientable contact structures and global contact forms).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {σ : Π x : M, TangentSpace I x →L[ℝ] ℝ}

namespace IsContactDistribution

variable [T2Space M] [SigmaCompactSpace M]

/-- **Every coorientation of a contact structure comes from a contact form.** Let `σ` be a
continuous section of the annihilator line `D⁰` of a contact structure `D` on a Hausdorff
σ-compact manifold, vanishing nowhere. Then some contact form `α` with kernel `D` is, at every
point, a positive multiple of `σ`. -/
theorem exists_isContactForm_pos_smul (hD : IsContactDistribution I ∞ D)
    (hσ : Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (hσD : ∀ x, σ x ∈ CotangentBundle.annihilatorSpace I D x) :
    ∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = D ∧
      ∀ x, ∃ c : ℝ, 0 < c ∧ SmoothForm.degreeOneEquiv α x = c • σ x := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  rcases isEmpty_or_nonempty M with hM | hM
  · obtain ⟨hc, hk⟩ := hD.isContactForm_and_kerDistribution_eq_iff (α := 0).2 isEmptyElim
    exact ⟨0, hc, hk, isEmptyElim⟩
  have hk := hD.finrank_sub_one_add_one
  obtain ⟨α, hα⟩ :=
    hD.isContMDiffDistribution.exists_smoothForm_pos_smul hk hσ hσ₀ hσD
  obtain ⟨hαc, hαD⟩ := hD.isContactForm_and_kerDistribution_eq_iff.2 fun x ↦ (hα x).1
  exact ⟨α, hαc, hαD, fun x ↦ (hα x).2⟩

/-- **A contact structure is the kernel of a global contact form exactly when it is
coorientable.** On a Hausdorff σ-compact manifold, a contact structure `D` is the kernel of a
global contact form exactly when its annihilator line `D⁰` has a continuous section vanishing
nowhere. -/
theorem exists_isContactForm_kerDistribution_eq_iff_exists_continuous
    (hD : IsContactDistribution I ∞ D) :
    (∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = D) ↔
      ∃ σ : Π x : M, TangentSpace I x →L[ℝ] ℝ,
        (Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x)) ∧
        ∀ x, σ x ≠ 0 ∧ σ x ∈ CotangentBundle.annihilatorSpace I D x := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  simp only [hD.isContactForm_and_kerDistribution_eq_iff]
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨fun _ ↦ ⟨isEmptyElim, continuous_of_discreteTopology, isEmptyElim⟩,
      fun _ ↦ ⟨0, isEmptyElim⟩⟩
  exact hD.isContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous
    hD.finrank_sub_one_add_one

/-- **A contact structure is the kernel of a global contact form exactly when its annihilator line
is trivial.** On a nonempty Hausdorff σ-compact manifold, a contact structure `D` is the kernel of
a contact form exactly when its annihilator line bundle `D⁰`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`) has a smooth linear trivialization over
all of `M`. -/
theorem exists_isContactForm_kerDistribution_eq_iff_exists_trivialization [Nonempty M]
    (hD : IsContactDistribution I ∞ D) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.isContMDiffDistribution.annihilatorFiberBundle hD.finrank_sub_one_add_one
    letI := hD.isContMDiffDistribution.annihilatorVectorBundle hD.finrank_sub_one_add_one
    (∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = D) ↔
      ∃ (e : Trivialization (Fin 1 → ℝ)
          (π (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x)) (_ : e.IsLinear ℝ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear M (Fin 1 → ℝ) I ∞).maximalAtlas
          (TotalSpace (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x) ∧
        e.baseSet = univ := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  simp only [hD.isContactForm_and_kerDistribution_eq_iff]
  exact hD.isContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization
    hD.finrank_sub_one_add_one

/-- **Every coorientation of a contact structure is the coorientation of a contact form.** On a
Hausdorff σ-compact manifold, every coorientation `o` of a contact structure `D`
(`TauCeti.IsCoorientation`) is the coorientation of a contact form with kernel `D`: one positive
for `o` at every point. -/
theorem exists_isContactForm_coorientation_eq (hD : IsContactDistribution I ∞ D)
    {o : Π x : M, Orientation ℝ (CotangentBundle.annihilatorSpace I D x) (Fin 1)}
    (ho : IsCoorientation I D o) :
    ∃ (α : SmoothForm I M ℝ 1) (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x),
      α.IsContactForm ∧ α.coorientation hα = o := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  rcases isEmpty_or_nonempty M with hM | hM
  · obtain ⟨hc, -⟩ := hD.isContactForm_and_kerDistribution_eq_iff (α := 0).2 isEmptyElim
    exact ⟨0, isEmptyElim, hc, funext isEmptyElim⟩
  obtain ⟨α, hα, rfl⟩ :=
    ho.exists_coorientation_eq hD.isContMDiffDistribution hD.finrank_sub_one_add_one
  exact ⟨α, hα, (hD.isContactForm_and_kerDistribution_eq_iff.2 hα).1, rfl⟩

/-- **A contact structure is the kernel of a global contact form exactly when it has a
coorientation.** On a Hausdorff σ-compact manifold, a contact structure `D` is the kernel of a
contact form exactly when it has a coorientation (`TauCeti.IsCoorientation`). -/
theorem exists_isContactForm_kerDistribution_eq_iff_exists_isCoorientation
    (hD : IsContactDistribution I ∞ D) :
    (∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = D) ↔
      ∃ o, IsCoorientation I D o := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  simp only [hD.isContactForm_and_kerDistribution_eq_iff]
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨fun _ ↦ ⟨isEmptyElim, isCoorientation_iff.2 isEmptyElim⟩, fun _ ↦ ⟨0, isEmptyElim⟩⟩
  exact (hD.isContMDiffDistribution.exists_isCoorientation_iff hD.finrank_sub_one_add_one).symm

end IsContactDistribution

end TauCeti
