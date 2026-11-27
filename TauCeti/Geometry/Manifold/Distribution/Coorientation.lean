/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Nonvanishing
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Orientation.Basis
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
(`TauCeti.IsContMDiffDistribution.exists_smoothForm_ker_eq_iff_exists_trivialization`).

A **coorientation** of `D` (`TauCeti.IsCoorientation`) is an orientation of every annihilator line
`D⁰_x` which near every point is the orientation in which some continuous local annihilating
covector field is positive. As `D⁰_x` is the dual of the line `T_x M ⧸ D x`, this is a continuous
choice of a positive side of the hyperplanes. A one-form `α` vanishing nowhere with kernel `D`
defines the coorientation `α.coorientation` in which `α` is positive
(`TauCeti.SmoothForm.isCoorientation_coorientation`). If `β = c α` at `x`, then `β` gives the same
coorientation at `x` exactly when `c > 0`, and the opposite one exactly when `c < 0`
(`TauCeti.SmoothForm.coorientation_eq_iff_pos`, `TauCeti.SmoothForm.coorientation_eq_neg_iff_neg`).
Coorientations are the orientations of the line bundle `D⁰`
(`TauCeti.IsCoorientation.iff_exists_vectorBundleOrientation`), so on a connected manifold two of
them are equal or opposite; a coorientable hyperplane field on a nonempty connected manifold
therefore has exactly two coorientations (`TauCeti.IsCoorientation.ncard_setOf_isCoorientation`).
On a Hausdorff σ-compact manifold every coorientation is that of a global defining form
(`TauCeti.IsCoorientation.exists_coorientation_eq`), so `D` is coorientable exactly when it is the
kernel of a global nowhere-zero one-form
(`TauCeti.IsContMDiffDistribution.exists_isCoorientation_iff`). For a contact structure this is
the statement that a global contact form exists exactly when the contact structure is
coorientable; see `TauCeti.Geometry.Contact.Coorientation`.

## Main definitions

* `TauCeti.IsCoorientation I D o`: the orientations `o x` of the annihilator lines form a
  coorientation of `D`.
* `TauCeti.SmoothForm.coorientation`: the coorientation of a nowhere-zero defining form.

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
* `TauCeti.SmoothForm.orientation_eq_coorientation_iff`,
  `TauCeti.SmoothForm.coorientation_eq_coorientation_iff`: a covector is positive for the
  coorientation of `α` exactly when it lies on the ray of `α`.
* `TauCeti.SmoothForm.coorientation_eq_iff_pos`, `TauCeti.SmoothForm.coorientation_eq_neg_iff_neg`,
  `TauCeti.SmoothForm.coorientation_neg`: rescaling a defining form by `c` keeps the coorientation
  where `c > 0` and reverses it where `c < 0`.
* `TauCeti.IsCoorientation.iff_exists_vectorBundleOrientation`: coorientations are the
  orientations of the annihilator line bundle.
* `TauCeti.IsCoorientation.eq_or_eq_neg`, `TauCeti.IsCoorientation.setOf_isCoorientation_eq`,
  `TauCeti.IsCoorientation.ncard_setOf_isCoorientation`: on a connected manifold a coorientable
  hyperplane field has exactly the two coorientations `o` and `-o`.
* `TauCeti.IsCoorientation.exists_coorientation_eq`,
  `TauCeti.IsContMDiffDistribution.exists_isCoorientation_iff`: every coorientation is that of a
  global defining form, and a hyperplane field is coorientable exactly when it has one.

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
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {σ : Π x : M, TangentSpace I x →L[ℝ] ℝ}

namespace SmoothForm

variable {α : SmoothForm I M ℝ 1} {x : M}

/-- The covector of a one-form at `x` annihilates its kernel there. -/
theorem degreeOneEquiv_mem_annihilatorSpace (h : RoughForm.ker α.val x = D x) :
    degreeOneEquiv α x ∈ CotangentBundle.annihilatorSpace I D x :=
  CotangentBundle.mem_annihilatorSpace_iff.2 fun v hv ↦ by
    rw [← h, RoughForm.ker_eq_ker_eval, SmoothForm.eval_val] at hv
    exact LinearMap.mem_ker.1 hv

/-- The annihilator of the kernel of a one-form not vanishing at `x` is a line. -/
theorem finrank_annihilatorSpace_eq_one (h : α.val x ≠ 0) (hker : RoughForm.ker α.val x = D x) :
    finrank ℝ (CotangentBundle.annihilatorSpace I D x) = 1 := by
  rw [CotangentBundle.annihilatorSpace_eq_span_singleton (α := degreeOneEquiv α x)
    (by rw [← hker, RoughForm.ker_eq_ker_eval, SmoothForm.eval_val])]
  exact finrank_span_singleton (degreeOneEquiv_ne_zero h)

end SmoothForm

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
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨fun x ↦ SmoothForm.degreeOneEquiv α x,
      (SmoothForm.degreeOneEquiv α).contMDiff.continuous,
      fun x ↦ ⟨SmoothForm.degreeOneEquiv_ne_zero (hα x).1,
        SmoothForm.degreeOneEquiv_mem_annihilatorSpace (hα x).2⟩⟩
  · rintro ⟨σ, hσ, hσD⟩
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

end IsContMDiffDistribution

/-! ### Coorientations -/

open CotangentBundle

variable (I D) in
/-- A **coorientation** of a hyperplane field `D`: an orientation `o x` of every annihilator line
`D⁰_x ⊆ T*_x M` which, near every point, is the orientation in which some covector field
annihilating `D` and continuous there is positive: at every point `y` of a neighbourhood, the
one-vector basis formed by its value at `y` has the orientation `o y`. Since `D⁰_x` is the dual of
the line `T_x M ⧸ D x`, a coorientation is a continuous choice of a positive side of the
hyperplanes `D x`. -/
def IsCoorientation (o : Π x : M, Orientation ℝ (annihilatorSpace I D x) (Fin 1)) : Prop :=
  ∀ x, ∃ U ∈ 𝓝 x, ∃ σ : Π y : M, annihilatorSpace I D y,
    ContinuousOn (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (σ y : TangentSpace I y →L[ℝ] ℝ)) U ∧
    ∀ y ∈ U, ∃ β : Basis (Fin 1) ℝ (annihilatorSpace I D y), β 0 = σ y ∧ β.orientation = o y

/-- Unfolding `TauCeti.IsCoorientation`. -/
theorem isCoorientation_iff {o : Π x : M, Orientation ℝ (annihilatorSpace I D x) (Fin 1)} :
    IsCoorientation I D o ↔ ∀ x, ∃ U ∈ 𝓝 x, ∃ σ : Π y : M, annihilatorSpace I D y,
      ContinuousOn (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (σ y : TangentSpace I y →L[ℝ] ℝ)) U ∧
      ∀ y ∈ U, ∃ β : Basis (Fin 1) ℝ (annihilatorSpace I D y), β 0 = σ y ∧ β.orientation = o y :=
  Iff.rfl

namespace SmoothForm

variable {α β : SmoothForm I M ℝ 1} {x : M}

/-- The one-vector basis `(α_x)` of the annihilator line `D⁰_x`, for a one-form `α` not vanishing
at `x` with kernel `D x`. -/
private def coorientationBasis (hα : α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) :
    Basis (Fin 1) ℝ (annihilatorSpace I D x) :=
  FiniteDimensional.basisSingleton (Fin 1) (finrank_annihilatorSpace_eq_one hα.1 hα.2)
    ⟨degreeOneEquiv α x, degreeOneEquiv_mem_annihilatorSpace hα.2⟩
    fun h ↦ degreeOneEquiv_ne_zero hα.1 (congrArg Subtype.val h)

@[simp]
private theorem coorientationBasis_apply (hα : α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x)
    (i : Fin 1) :
    coorientationBasis hα i = ⟨degreeOneEquiv α x, degreeOneEquiv_mem_annihilatorSpace hα.2⟩ :=
  FiniteDimensional.basisSingleton_apply ..

/-- The **coorientation of a defining form**. For a one-form `α` vanishing nowhere with kernel
`D`, the orientation at `x` of the annihilator line `D⁰_x` in which `α_x` is positive: that of the
one-vector basis `(α_x)`. -/
def coorientation (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) (x : M) :
    Orientation ℝ (annihilatorSpace I D x) (Fin 1) :=
  (coorientationBasis (hα x)).orientation

/-- A one-vector basis of the annihilator line has the coorientation of `α` exactly when its vector
lies on the ray of `α_x`. -/
theorem orientation_eq_coorientation_iff (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x)
    (b : Basis (Fin 1) ℝ (annihilatorSpace I D x)) :
    b.orientation = α.coorientation hα x ↔
      SameRay ℝ (b 0 : TangentSpace I x →L[ℝ] ℝ) (degreeOneEquiv α x) := by
  rw [coorientation, Basis.orientation_eq_iff_sameRay, coorientationBasis_apply,
    ← (annihilatorSpace I D x).injective_subtype.sameRay_map_iff]
  simp only [Submodule.subtype_apply, Fin.default_eq_zero]

/-- Two defining forms give the same coorientation at `x` exactly when their values at `x` lie on
the same ray. -/
theorem coorientation_eq_coorientation_iff (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x)
    (hβ : ∀ x, β.val x ≠ 0 ∧ RoughForm.ker β.val x = D x) :
    α.coorientation hα x = β.coorientation hβ x ↔
      SameRay ℝ (degreeOneEquiv α x) (degreeOneEquiv β x) := by
  rw [coorientation, orientation_eq_coorientation_iff]
  simp only [coorientationBasis_apply]

/-- **Rescaling by a positive function keeps the coorientation.** If `β = c α` at `x`, the two
defining forms give the same coorientation at `x` exactly when `c > 0`. -/
theorem coorientation_eq_iff_pos (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x)
    (hβ : ∀ x, β.val x ≠ 0 ∧ RoughForm.ker β.val x = D x) {c : ℝ} (h : β.val x = c • α.val x) :
    β.coorientation hβ x = α.coorientation hα x ↔ 0 < c := by
  have hc : c ≠ 0 := by rintro rfl; exact (hβ x).1 (by rw [h, zero_smul])
  rw [coorientation_eq_coorientation_iff, degreeOneEquiv_eq_smul h,
    sameRay_smul_left_iff_of_ne (degreeOneEquiv_ne_zero (hα x).1) hc]

/-- `-α` does not vanish at `x` and has kernel `D x` there exactly when `α` does. -/
theorem neg_val_ne_zero_and_ker_eq_iff :
    (-α).val x ≠ 0 ∧ RoughForm.ker (-α).val x = D x ↔
      α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x := by
  simp

/-- The coorientation of `-α` is opposite to that of `α`. -/
@[simp]
theorem coorientation_neg (hα : ∀ x, (-α).val x ≠ 0 ∧ RoughForm.ker (-α).val x = D x) :
    (-α).coorientation hα =
      -α.coorientation fun x ↦ neg_val_ne_zero_and_ker_eq_iff.1 (hα x) := by
  funext x
  -- Both sides are orientations of the one-vector bases `coorientationBasis`, which are by
  -- definition `basisSingleton` bases; unfolding them exposes the shape of the general lemma
  -- `orientation_basisSingleton_neg`. It remains to match the vector `(-α)_x` with `-α_x` and
  -- the corresponding nonvanishing proofs, which `convert` separates.
  rw [Pi.neg_apply, coorientation, coorientation, coorientationBasis, coorientationBasis]
  convert orientation_basisSingleton_neg _ _ using 3
  · exact Subtype.ext (by simp)
  · exact neg_ne_zero.2 fun h ↦ degreeOneEquiv_ne_zero
      (neg_val_ne_zero_and_ker_eq_iff.1 (hα x)).1 (congrArg Subtype.val h)

/-- **Rescaling by a negative function reverses the coorientation.** If `β = c α` at `x`, the
defining form `β` gives at `x` the coorientation opposite to that of `α` exactly when `c < 0`. -/
theorem coorientation_eq_neg_iff_neg (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x)
    (hβ : ∀ x, β.val x ≠ 0 ∧ RoughForm.ker β.val x = D x) {c : ℝ} (h : β.val x = c • α.val x) :
    β.coorientation hβ x = -α.coorientation hα x ↔ c < 0 := by
  have hα' (y : M) := neg_val_ne_zero_and_ker_eq_iff.2 (hα y)
  have hneg := congrFun (coorientation_neg hα') x
  rw [Pi.neg_apply] at hneg
  rw [← hneg, coorientation_eq_iff_pos hα' hβ (c := -c) (by simp [h]), Left.neg_pos_iff]

/-- The coorientation of a defining form is a coorientation. -/
theorem isCoorientation_coorientation (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x) :
    IsCoorientation I D (α.coorientation hα) := fun _ ↦
  ⟨univ, Filter.univ_mem,
    fun y ↦ ⟨degreeOneEquiv α y, degreeOneEquiv_mem_annihilatorSpace (hα y).2⟩,
    (degreeOneEquiv α).contMDiff.continuous.continuousOn, fun y _ ↦
      ⟨coorientationBasis (hα y), coorientationBasis_apply .., rfl⟩⟩

end SmoothForm

namespace IsCoorientation

variable {o o' : Π x : M, Orientation ℝ (annihilatorSpace I D x) (Fin 1)}

/-- The opposite of a coorientation is a coorientation. -/
theorem neg (ho : IsCoorientation I D o) : IsCoorientation I D (-o) := fun x ↦ by
  obtain ⟨U, hU, σ, hσ, hpos⟩ := ho x
  refine ⟨U, hU, -σ, (continuousOn_const.smul_section (f := fun _ ↦ (-1 : ℝ)) hσ).congr
    fun y _ ↦ by simp, fun y hy ↦ ?_⟩
  obtain ⟨b, hb, hbo⟩ := hpos y hy
  refine ⟨b.unitsSMul (Function.update 1 0 (-1)), ?_, ?_⟩
  · simp [Basis.unitsSMul_apply, hb]
  · rw [Basis.orientation_neg_single, hbo, Pi.neg_apply]

/-- **Coorientations are the orientations of the annihilator line bundle.** For any structure of a
real line bundle on the annihilators `D⁰` of `D` with the topology of a subspace of `T*M`, such as
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`, a family of fibre orientations is a
coorientation of `D` exactly when it is an orientation of that bundle. -/
theorem iff_exists_vectorBundleOrientation
    [FiberBundle (Fin 1 → ℝ) fun x ↦ annihilatorSpace I D x]
    [VectorBundle ℝ (Fin 1 → ℝ) fun x ↦ annihilatorSpace I D x] :
    IsCoorientation I D o ↔
      ∃ o' : VectorBundleOrientation (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I D x) (Fin 1),
        ⇑o' = o := by
  have hι : Fintype.card (Fin 1) = finrank ℝ (Fin 1 → ℝ) := by simp
  -- Continuity of sections of `D⁰` is continuity in `T*M`.
  have hcont {U : Set M} {σ : Π y : M, annihilatorSpace I D y} :
      ContinuousOn (fun y ↦ TotalSpace.mk' (Fin 1 → ℝ) (E := fun y ↦ annihilatorSpace I D y) y
        (σ y)) U ↔ ContinuousOn (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (σ y : TangentSpace I y →L[ℝ] ℝ)) U := by
    rw [(isEmbedding_annihilatorInclusion I D (Fin 1 → ℝ)).continuousOn_iff, Function.comp_def]
    simp only [annihilatorInclusion_mk']
  constructor
  · intro ho
    refine ⟨VectorBundleOrientation.ofExistsContinuousOnSection o fun x ↦ ?_,
      VectorBundleOrientation.coe_ofExistsContinuousOnSection ..⟩
    obtain ⟨U, hU, σ, hσ, hpos⟩ := ho x
    exact ⟨U, hU, σ, hcont.2 hσ, hpos⟩
  · rintro ⟨o', rfl⟩ x
    obtain ⟨U, hU, σ, hσ, hpos⟩ := o'.exists_continuousOn_section_basis_orientation_eq hι x
    exact ⟨U, hU, σ, hcont.1 hσ, hpos⟩

/-- **A smooth hyperplane field on a connected manifold has at most two coorientations.** On a
preconnected manifold, two coorientations of a smooth hyperplane field are equal or opposite. -/
theorem eq_or_eq_neg [PreconnectedSpace M] (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) (ho : IsCoorientation I D o) (ho' : IsCoorientation I D o') :
    o' = o ∨ o' = -o := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  obtain ⟨O, rfl⟩ := iff_exists_vectorBundleOrientation.1 ho
  obtain ⟨O', rfl⟩ := iff_exists_vectorBundleOrientation.1 ho'
  rcases O'.eq_or_eq_neg (by simp) O with h | h
  · exact .inl (congrArg DFunLike.coe h)
  · exact .inr (funext fun x ↦ by rw [h, VectorBundleOrientation.neg_apply, Pi.neg_apply])

/-- On a preconnected manifold, the coorientations of a smooth hyperplane field with a
coorientation `o` are exactly `o` and `-o`. -/
theorem setOf_isCoorientation_eq [PreconnectedSpace M] (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + 1 = finrank ℝ E) (ho : IsCoorientation I D o) :
    {o' | IsCoorientation I D o'} = {o, -o} := by
  ext o'
  refine ⟨fun ho' ↦ ho.eq_or_eq_neg hD hk ho', ?_⟩
  rintro (rfl | rfl)
  exacts [ho, ho.neg]

/-- **A coorientable hyperplane field on a connected manifold has exactly two coorientations.** -/
theorem ncard_setOf_isCoorientation [PreconnectedSpace M] [Nonempty M]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E)
    (ho : IsCoorientation I D o) : {o' | IsCoorientation I D o'}.ncard = 2 := by
  rw [ho.setOf_isCoorientation_eq hD hk]
  refine ncard_pair fun h ↦ ?_
  obtain ⟨x⟩ := ‹Nonempty M›
  exact Module.Ray.ne_neg_self (o x) (congrFun h x)

/-- **Every coorientation is the coorientation of a global defining form.** On a Hausdorff
σ-compact manifold, every coorientation of a smooth hyperplane field `D` is the coorientation of a
smooth one-form vanishing nowhere with kernel `D`. -/
theorem exists_coorientation_eq [T2Space M] [SigmaCompactSpace M]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E)
    (ho : IsCoorientation I D o) :
    ∃ (α : SmoothForm I M ℝ 1) (hα : ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x),
      α.coorientation hα = o := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : IsManifold I (∞ + 1) M := .of_le (n := ∞) (by simp)
  let := hD.annihilatorFiberBundle hk
  let := hD.annihilatorVectorBundle hk
  obtain ⟨O, rfl⟩ := iff_exists_vectorBundleOrientation.1 ho
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  -- A positive continuous section of `D⁰` is a positive multiple of a smooth defining form.
  obtain ⟨s, hs, hpos⟩ := O.exists_continuous_section_basis_orientation_eq (by simp)
  have hs₀ (x : M) : (s x : TangentSpace I x →L[ℝ] ℝ) ≠ 0 := by
    obtain ⟨b, hb, -⟩ := hpos x
    exact fun h ↦ b.ne_zero default (hb.trans (Subtype.ext h))
  obtain ⟨α, hα⟩ := hD.exists_smoothForm_pos_smul hk
    (continuous_totalSpaceMk_annihilatorSpace_iff.1 hs) hs₀ fun x ↦ (s x).property
  refine ⟨α, fun x ↦ (hα x).1, funext fun x ↦ ?_⟩
  obtain ⟨b, hb, hbo⟩ := hpos x
  obtain ⟨c, hc, hαc⟩ := (hα x).2
  rw [← hbo, eq_comm, SmoothForm.orientation_eq_coorientation_iff, hαc, ← hb]
  exact SameRay.sameRay_pos_smul_right _ hc

end IsCoorientation

/-- **A hyperplane field is coorientable exactly when it is the kernel of a global one-form.** On a
Hausdorff σ-compact manifold, a smooth hyperplane field `D` has a coorientation exactly when it is
the kernel of a smooth one-form vanishing nowhere. -/
theorem IsContMDiffDistribution.exists_isCoorientation_iff [T2Space M] [SigmaCompactSpace M]
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + 1 = finrank ℝ E) :
    (∃ o, IsCoorientation I D o) ↔
      ∃ α : SmoothForm I M ℝ 1, ∀ x, α.val x ≠ 0 ∧ RoughForm.ker α.val x = D x := by
  refine ⟨fun ⟨o, ho⟩ ↦ ?_, fun ⟨α, hα⟩ ↦ ⟨_, SmoothForm.isCoorientation_coorientation hα⟩⟩
  obtain ⟨α, hα, -⟩ := ho.exists_coorientation_eq hD hk
  exact ⟨α, hα⟩


end TauCeti
