/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.Distribution.Coorientation
public import TauCeti.Topology.VectorBundle.Orientation.PositiveSection
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# Coorientable contact structures and global contact forms

A contact structure `ξ` (`TauCeti.IsContactDistribution`) is defined by its hyperplanes alone.
Locally it is the kernel of a contact form, and the local contact forms at a point are the nonzero
elements of the annihilator line `ξ⁰ ⊆ T*M` (`TauCeti.CotangentBundle.annihilatorSpace`). A global
contact form with kernel `ξ` is extra data: it exists exactly when `ξ` is *coorientable*, that is,
when the line `ξ⁰` admits a continuous section vanishing nowhere, and exactly when the smooth line
bundle `ξ⁰` is trivial. A continuous choice of nonzero covectors in `ξ⁰`, up to positive multiples,
is a coorientation, and every coorientation is the coorientation of a contact form
(`TauCeti.IsContactDistribution.exists_isContactForm_pos_smul`).

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
* `exists_isContactForm_kerDistribution_eq_iff_nonempty_vectorBundleOrientation`, in the namespace
  `TauCeti.IsContactDistribution`: a contact structure is the kernel of a global contact form
  exactly when its annihilator line bundle is orientable.

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

/-- If a contact structure `D` is the kernel of a contact form `α`, its annihilator line is
orientable: `x ↦ α_x` is a continuous section of `D⁰` vanishing nowhere. -/
theorem nonempty_vectorBundleOrientation_of_isContactForm [Nonempty M]
    (hD : IsContactDistribution I ∞ D) {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (hαD : α.kerDistribution = D) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.isContMDiffDistribution.annihilatorFiberBundle hD.finrank_sub_one_add_one
    haveI := hD.isContMDiffDistribution.annihilatorVectorBundle hD.finrank_sub_one_add_one
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ)
      (fun x ↦ CotangentBundle.annihilatorSpace I D x) (Fin 1)) :=
  haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  letI := hD.isContMDiffDistribution.annihilatorFiberBundle hD.finrank_sub_one_add_one
  haveI := hD.isContMDiffDistribution.annihilatorVectorBundle hD.finrank_sub_one_add_one
  by
  have hj := hD.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
    hD.finrank_sub_one_add_one
  -- The covector `α_x` vanishes on `ker α_x = D x`.
  have hmem (x : M) : SmoothForm.degreeOneEquiv α x ∈ CotangentBundle.annihilatorSpace I D x := by
    refine CotangentBundle.mem_annihilatorSpace_iff.2 fun v hv ↦ ?_
    rw [← hαD, SmoothForm.mem_kerDistribution] at hv
    rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hv]
  let s (x : M) : CotangentBundle.annihilatorSpace I D x := ⟨_, hmem x⟩
  -- Followed by the embedding `D⁰ → T*M`, the section `s` is the smooth section `x ↦ α_x`.
  have hs : Continuous fun x ↦ TotalSpace.mk' (Fin 1 → ℝ) x (s x) := by
    refine hj.isEmbedding.isInducing.continuous_iff.2 ?_
    have hcomp : CotangentBundle.annihilatorInclusion I D (Fin 1 → ℝ) ∘
        (fun x ↦ TotalSpace.mk' (Fin 1 → ℝ) x (s x)) =
          fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x) :=
      funext fun x ↦ by simp [s]
    rw [hcomp]
    exact (SmoothForm.degreeOneEquiv α).contMDiff.continuous
  -- A contact form vanishes nowhere.
  have hs₀ (x : M) : s x ≠ 0 := fun h ↦ by
    obtain ⟨v, hv⟩ := hα.exists_ne_zero x
    have h' := congrArg
      (fun p : CotangentBundle.annihilatorSpace I D x ↦ (p : TangentSpace I x →L[ℝ] ℝ) v) h
    simp only [s, ZeroMemClass.coe_zero, SmoothForm.degreeOneEquiv_apply_apply_vec] at h'
    exact hv h'
  exact ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
    (fun x ↦ (VectorBundle.finrank_eq ℝ (Fin 1 → ℝ)
      (fun x ↦ CotangentBundle.annihilatorSpace I D x) x).trans (Module.finrank_fin_fun ℝ)) hs hs₀⟩

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

/-- **Coorientability is orientability of the annihilator line.** On a Hausdorff σ-compact
manifold, a contact structure `D` is the kernel of a global contact form exactly when its
annihilator line `D⁰`, the dual of the contact line `TM ⧸ D`, is orientable. -/
theorem exists_isContactForm_kerDistribution_eq_iff_nonempty_vectorBundleOrientation [Nonempty M]
    (hD : IsContactDistribution I ∞ D) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.isContMDiffDistribution.annihilatorFiberBundle hD.finrank_sub_one_add_one
    haveI := hD.isContMDiffDistribution.annihilatorVectorBundle hD.finrank_sub_one_add_one
    (∃ α : SmoothForm I M ℝ 1, α.IsContactForm ∧ α.kerDistribution = D) ↔
      Nonempty (VectorBundleOrientation (Fin 1 → ℝ)
        (fun x ↦ CotangentBundle.annihilatorSpace I D x) (Fin 1)) :=
  haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  letI := hD.isContMDiffDistribution.annihilatorFiberBundle hD.finrank_sub_one_add_one
  haveI := hD.isContMDiffDistribution.annihilatorVectorBundle hD.finrank_sub_one_add_one
  by
  refine ⟨fun ⟨α, hα, hαD⟩ ↦ hD.nonempty_vectorBundleOrientation_of_isContactForm hα hαD,
    fun ⟨o⟩ ↦ ?_⟩
  -- An orientation of `D⁰` gives a continuous nowhere-vanishing section of `D⁰`, hence of `T*M`.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨s, hs, hs₀⟩ := o.exists_continuous_section_ne_zero (by simp)
  refine hD.exists_isContactForm_kerDistribution_eq_iff_exists_continuous.2
    ⟨fun x ↦ s x, ?_, fun x ↦ ⟨fun h ↦ hs₀ x (Subtype.ext h), (s x).property⟩⟩
  refine ((hD.isContMDiffDistribution.contMDiff_annihilatorInclusion
    hD.finrank_sub_one_add_one).continuous.comp hs).congr fun x ↦ ?_
  simp

end IsContactDistribution

end TauCeti
