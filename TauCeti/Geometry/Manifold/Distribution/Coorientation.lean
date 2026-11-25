/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.VectorBundle.Section.Nonvanishing
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.Topology.VectorBundle.Orientation.Cover
import TauCeti.Topology.VectorBundle.Orientation.PositiveSection

/-!
# Coorientations of hyperplane fields and global defining forms

Let `D` be a smooth hyperplane field on a manifold `M`: a smooth distribution of rank
`dim M - 1`. Near every point it is the kernel of a nowhere-zero smooth one-form
(`TauCeti.IsContMDiffDistribution.exists_roughForm_ker_eq`), but in general there is no such form on
all of `M`. The local defining forms at a point are the nonzero elements of the annihilator line
`D⁰_x ⊆ T*_x M` (`TauCeti.CotangentBundle.annihilatorSpace`), so a global defining form is a
nowhere-zero smooth section of the line bundle `D⁰`.

This file proves that already a *continuous* nowhere-zero section `σ` of `D⁰`, that is, a
continuous choice of a nonzero annihilating covector at every point, gives a global defining form:
on a Hausdorff σ-compact manifold there is a smooth one-form `α` with `α_x` a positive multiple of
`σ_x` at every point (`TauCeti.IsContMDiffDistribution.exists_smoothForm_pos_smul`). Since `D⁰`
is a smooth line bundle (`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle`), this
is the general fact that a continuous nowhere-zero section of a smooth line bundle is a positive
multiple of a smooth section
(`TauCeti.exists_contMDiffSection_forall_exists_pos_smul_of_continuous`), whose proof glues local
sections by a smooth partition of unity.

Consequently `D` is the kernel of a global nowhere-zero smooth one-form exactly when its annihilator
line has a continuous nowhere-zero section
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous`), and exactly when
the smooth line bundle `D⁰` is trivial: it has a smooth trivialization over all of `M`
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization`), and exactly
when the line bundle `D⁰` is orientable
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_nonempty_vectorBundleOrientation`).
The forward implication, that a global defining form orients `D⁰`, needs no hypothesis on `M`
(`TauCeti.IsContMDiffDistribution.nonempty_vectorBundleOrientation_of_smoothForm_ker_eq`).

A choice of a continuous nowhere-zero section of `D⁰` up to positive multiples is a coorientation
of `D`. For a contact structure this is the statement that a global contact form exists exactly
when the contact structure is coorientable; see `TauCeti.Geometry.Contact.Coorientation`.

## Main results

* `TauCeti.IsContMDiffDistribution.exists_smoothForm_pos_smul`: a continuous nowhere-zero section of
  the annihilator line is a positive multiple of a global smooth one-form, which therefore vanishes
  nowhere and has kernel `D`.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_continuous`: a hyperplane
  field is the kernel of a global nowhere-zero smooth one-form exactly when its annihilator line
  has a continuous nowhere-zero section.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization`: it is the
  kernel of a global nowhere-zero smooth one-form exactly when its annihilator line bundle is
  smoothly trivial.
* `TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_nonempty_vectorBundleOrientation`:
  it is the kernel of a global nowhere-zero smooth one-form exactly when its annihilator line
  bundle is orientable.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  and Lemma 1.1.1 (a hyperplane field is the kernel of a global one-form exactly when it is
  coorientable).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Theorem 2.25 and Chapter 19 (partitions of unity and local defining forms).
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {σ : Π x : M, TangentSpace I x →L[ℝ] ℝ}

namespace IsContMDiffDistribution

/-- **A one-form proportional to a nonzero annihilating covector defines the hyperplane.** If the
value at `x` of a smooth one-form `α` is a nonzero multiple of a nonzero covector `σ_x` annihilating
the hyperplane `D x`, then `α` does not vanish at `x` and its kernel there is `D x`. -/
private theorem ne_zero_and_ker_eq_of_degreeOneEquiv_eq_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) {α : SmoothForm I M ℝ 1} {x : M} {c : ℝ} (hc : c ≠ 0)
    (hσ₀ : σ x ≠ 0) (hσD : σ x ∈ CotangentBundle.annihilatorSpace I D x)
    (hαc : SmoothForm.degreeOneEquiv α x = c • σ x) :
    α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x := by
  have hne : RoughForm.eval α.val x ≠ 0 := by
    rw [SmoothForm.eval_val, hαc]
    exact ContinuousLinearMap.coe_injective.ne (smul_ne_zero hc hσ₀)
  refine ⟨fun h ↦ hne ?_, ?_⟩
  · rw [SmoothForm.eval_val, SmoothForm.degreeOneEquiv_coe_eq_zero_iff.2 h]
  rw [RoughForm.ker_eq_ker_eval]
  refine Module.Dual.ker_eq_of_le_of_finrank_add_one _ hne (fun v hv ↦ ?_)
    (by rw [hD.finrank_eq x]; exact hk)
  rw [LinearMap.mem_ker, SmoothForm.eval_val, hαc]
  simp [(CotangentBundle.mem_annihilatorSpace_iff.1 hσD) v hv]

/-- A smooth one-form `α` vanishing nowhere with kernel `D` gives the continuous nowhere-zero
section `x ↦ α_x` of the annihilator line `D⁰`. -/
private theorem exists_continuous_of_smoothForm_ker_eq {α : SmoothForm I M ℝ 1}
    (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) :
    ∃ σ : Π x : M, TangentSpace I x →L[ℝ] ℝ,
      (Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x)) ∧
      ∀ x, σ x ≠ 0 ∧ σ x ∈ CotangentBundle.annihilatorSpace I D x := by
  refine ⟨fun x ↦ SmoothForm.degreeOneEquiv α x,
    (SmoothForm.degreeOneEquiv α).contMDiff.continuous, fun x ↦ ⟨fun h ↦ (hα x).1 ?_, ?_⟩⟩
  · exact SmoothForm.degreeOneEquiv_coe_eq_zero_iff.1 (congrArg ContinuousLinearMap.toLinearMap h)
  · refine CotangentBundle.mem_annihilatorSpace_iff.2 fun v hv ↦ ?_
    simpa [← (hα x).2] using hv

/-- **A global defining form orients the annihilator line.** If a smooth hyperplane field `D` is
the kernel of a smooth one-form `α` vanishing nowhere, its annihilator line bundle `D⁰`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`) is orientable: `x ↦ α_x` is a
continuous section of `D⁰` vanishing nowhere. -/
theorem nonempty_vectorBundleOrientation_of_smoothForm_ker_eq [FiniteDimensional ℝ E]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) {α : SmoothForm I M ℝ 1}
    (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.annihilatorFiberBundle hk
    haveI := hD.annihilatorVectorBundle hk
    Nonempty (VectorBundleOrientation (Fin 1 → ℝ)
      (fun x ↦ CotangentBundle.annihilatorSpace I D x) (Fin 1)) :=
  haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  letI := hD.annihilatorFiberBundle hk
  haveI := hD.annihilatorVectorBundle hk
  by
  obtain ⟨σ, hσ, hσD⟩ := exists_continuous_of_smoothForm_ker_eq hα
  exact ⟨VectorBundleOrientation.ofContinuousNonvanishingSection
    (fun x ↦ (VectorBundle.finrank_eq ℝ (Fin 1 → ℝ)
      (fun x ↦ CotangentBundle.annihilatorSpace I D x) x).trans (finrank_fin_fun ℝ))
    ((CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff
      (σ := fun x ↦ ⟨σ x, (hσD x).2⟩)).2 hσ)
    fun x h ↦ (hσD x).1 (congrArg Subtype.val h)⟩

variable [T2Space M] [SigmaCompactSpace M]

/-- **A coorientation of a hyperplane field is induced by a global smooth one-form.** Let `σ` be a
continuous section of the annihilator line `D⁰` of a smooth hyperplane field `D` on a Hausdorff
σ-compact manifold, vanishing nowhere. Then some smooth one-form `α` is, at every point, a positive
multiple of `σ`; in particular `α` vanishes nowhere and has kernel `D`. -/
theorem exists_smoothForm_pos_smul (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E)
    (hσ : Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x))
    (hσ₀ : ∀ x, σ x ≠ 0) (hσD : ∀ x, σ x ∈ CotangentBundle.annihilatorSpace I D x) :
    ∃ α : SmoothForm I M ℝ 1, ∀ x, (α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ∧
      ∃ c : ℝ, 0 < c ∧ SmoothForm.degreeOneEquiv α x = c • σ x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  let := hD.annihilatorContMDiffVectorBundle hk
  -- `σ` is a continuous nowhere-zero section of the smooth line bundle `D⁰`.
  obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_exists_pos_smul_of_continuous (I := I) (n := ⊤)
    (Module.finrank_fin_fun ℝ)
    ((CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff
      (σ := fun x ↦ ⟨σ x, hσD x⟩)).2 hσ)
    fun x h ↦ hσ₀ x (congrArg Subtype.val h)
  let s : ContMDiffSection I (E →L[ℝ] ℝ) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) :=
    ⟨fun x ↦ (t x : TangentSpace I x →L[ℝ] ℝ), by
      simpa only [Function.comp_def, CotangentBundle.annihilatorInclusion_mk'] using
        (hD.contMDiff_annihilatorInclusion hk).comp t.contMDiff⟩
  refine ⟨SmoothForm.degreeOneEquiv.symm s, fun x ↦ ?_⟩
  obtain ⟨c, hc, htc⟩ := ht x
  have hαc : SmoothForm.degreeOneEquiv (SmoothForm.degreeOneEquiv.symm s) x = c • σ x := by
    rw [LinearEquiv.apply_symm_apply]; exact congrArg Subtype.val htc
  exact ⟨hD.ne_zero_and_ker_eq_of_degreeOneEquiv_eq_smul hk hc.ne' (hσ₀ x) (hσD x) hαc, c, hc, hαc⟩

/-- **A hyperplane field is the kernel of a global one-form exactly when it is coorientable.** A
smooth hyperplane field `D` on a Hausdorff σ-compact manifold is the kernel of a smooth one-form
vanishing nowhere exactly when its annihilator line `D⁰` has a continuous section vanishing
nowhere. -/
theorem exists_smoothForm_ker_eq_iff_exists_continuous (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) :
    (∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ↔
      ∃ σ : Π x : M, TangentSpace I x →L[ℝ] ℝ,
        (Continuous fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) x (σ x)) ∧
        ∀ x, σ x ≠ 0 ∧ σ x ∈ CotangentBundle.annihilatorSpace I D x := by
  refine ⟨fun ⟨α, hα⟩ ↦ exists_continuous_of_smoothForm_ker_eq hα, fun ⟨σ, hσ, hσD⟩ ↦ ?_⟩
  obtain ⟨α, hα⟩ := hD.exists_smoothForm_pos_smul hk hσ (fun x ↦ (hσD x).1) fun x ↦ (hσD x).2
  exact ⟨α, fun x ↦ (hα x).1⟩

/-- **A hyperplane field is the kernel of a global one-form exactly when its annihilator line is
trivial.** A smooth hyperplane field `D` on a Hausdorff σ-compact manifold is the kernel of a smooth
one-form vanishing nowhere exactly when its annihilator line bundle `D⁰`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`) has a smooth linear trivialization over
all of `M`. -/
theorem exists_smoothForm_ker_eq_iff_exists_trivialization [FiniteDimensional ℝ E]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.annihilatorFiberBundle hk
    letI := hD.annihilatorVectorBundle hk
    (∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ↔
      ∃ (e : Trivialization (Fin 1 → ℝ)
          (π (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x)) (_ : e.IsLinear ℝ),
        e.toOpenPartialHomeomorph ∈ (contMDiffFiberwiseLinear M (Fin 1 → ℝ) I ∞).maximalAtlas
          (TotalSpace (Fin 1 → ℝ) fun x ↦ CotangentBundle.annihilatorSpace I D x) ∧
        e.baseSet = univ := by
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  let := hD.annihilatorContMDiffVectorBundle hk
  rw [ContMDiffVectorBundle.exists_trivialization_baseSet_eq_univ_iff_exists_ne_zero
    (Module.finrank_fin_fun ℝ), hD.exists_smoothForm_ker_eq_iff_exists_continuous hk]
  constructor
  · rintro ⟨σ, hσ, hσD⟩
    -- A continuous nowhere-zero section of `D⁰` gives a smooth one.
    obtain ⟨t, ht⟩ := exists_contMDiffSection_forall_ne_zero_of_continuous (I := I) (n := ⊤)
      ((CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff (P := Fin 1 → ℝ)
        (σ := fun x ↦ ⟨σ x, (hσD x).2⟩)).2 hσ)
      fun x h ↦ (hσD x).1 (congrArg Subtype.val h)
    exact ⟨t, t.contMDiff, ht⟩
  · rintro ⟨σ, hσ, hσ₀⟩
    exact ⟨fun x ↦ (σ x : TangentSpace I x →L[ℝ] ℝ),
      (CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff (P := Fin 1 → ℝ)).1
        hσ.continuous,
      fun x ↦ ⟨fun h ↦ hσ₀ x (Subtype.ext h), (σ x).property⟩⟩

/-- **A hyperplane field is the kernel of a global one-form exactly when its annihilator line is
orientable.** A smooth hyperplane field `D` on a Hausdorff σ-compact manifold is the kernel of a
smooth one-form vanishing nowhere exactly when its annihilator line bundle `D⁰`
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`), the dual of the normal line
`TM ⧸ D`, is orientable. -/
theorem exists_smoothForm_ker_eq_iff_nonempty_vectorBundleOrientation [FiniteDimensional ℝ E]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
    letI := hD.annihilatorFiberBundle hk
    haveI := hD.annihilatorVectorBundle hk
    (∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) ↔
      Nonempty (VectorBundleOrientation (Fin 1 → ℝ)
        (fun x ↦ CotangentBundle.annihilatorSpace I D x) (Fin 1)) :=
  haveI : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  letI := hD.annihilatorFiberBundle hk
  haveI := hD.annihilatorVectorBundle hk
  by
  refine ⟨fun ⟨α, hα⟩ ↦ hD.nonempty_vectorBundleOrientation_of_smoothForm_ker_eq hk hα,
    fun ⟨o⟩ ↦ ?_⟩
  -- An orientation of `D⁰` gives a continuous nowhere-zero section of `D⁰`, hence of `T*M`.
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨s, hs, hs₀⟩ := o.exists_continuous_section_ne_zero (by simp)
  exact (hD.exists_smoothForm_ker_eq_iff_exists_continuous hk).2
    ⟨fun x ↦ s x, (CotangentBundle.continuous_totalSpaceMk_annihilatorSpace_iff
      (P := Fin 1 → ℝ)).1 hs, fun x ↦ ⟨fun h ↦ hs₀ x (Subtype.ext h), (s x).property⟩⟩

end IsContMDiffDistribution

end TauCeti
