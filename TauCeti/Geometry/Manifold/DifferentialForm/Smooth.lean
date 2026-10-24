/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

/-!
# Smooth bundle-valued differential forms

This file packages smooth sections of the bundle of alternating maps on tangent fibres.  The
underlying rough form remains an unbundled dependent function, while `IsSmoothBundleForm` records
that its graph is a smooth section of the alternating bundle.  The corresponding `Submodule`
provides the bundled carrier `SmoothBundleForm`; fixed coefficients are the `SmoothForm`
specialization.  These carriers are the input for smooth wedge products and pullbacks.

The degree-two adapters below evaluate smooth forms on ordered pairs and expose real-valued fibres
as alternating bilinear forms.

Smoothness is expressed through the total-space charts of the topological alternating bundle.  The
module operations use Mathlib's smooth-section API, so this carrier does not require a chosen
trivialization or a global smooth alternating-bundle instance.

The fixed-coefficient section and degree-two evaluation adapters generalize the corresponding
declarations in `TauCeti.Geometry.Manifold.TwoForm.Basic`.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {k : ℕ}

/-- A rough bundle-valued form has `C^n` regularity when its graph is a `C^n` section of the
alternating bundle with fibres `TangentSpace I x [⋀^Fin k]→L[ℝ] V x`; `n = ∞` gives smoothness. -/
def IsSmoothBundleForm (I : ModelWithCorners ℝ E H) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (V : M → Type*)
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [IsManifold I 1 M] (n : WithTop ℕ∞) (φ : RoughBundleForm I M V k) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
    (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x))

/-- The defining characterization of `IsSmoothBundleForm`. -/
theorem isSmoothBundleForm_def [IsManifold I 1 M] (n : WithTop ℕ∞)
    (φ : RoughBundleForm I M V k) :
    IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) n φ ↔
      ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x)) :=
  Iff.rfl

private lemma smoothSection_zero [IsManifold I 1 M] :
    IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞)
      (0 : RoughBundleForm I M V k) := by
  exact contMDiff_zeroSection ℝ (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)

private lemma smoothSection_add [IsManifold I 1 M]
    {φ ψ : RoughBundleForm I M V k}
    (hφ : IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) φ)
    (hψ : IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) ψ) :
    IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) (φ + ψ) := by
  let sφ : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x) :=
    ⟨φ, hφ⟩
  let sψ : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x) :=
    ⟨ψ, hψ⟩
  rw [isSmoothBundleForm_def]
  convert (sφ + sψ).contMDiff using 1

private lemma smoothSection_smul [IsManifold I 1 M] (c : ℝ)
    {φ : RoughBundleForm I M V k}
    (hφ : IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) φ) :
    IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) (c • φ) := by
  let sφ : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x) :=
    ⟨φ, hφ⟩
  rw [isSmoothBundleForm_def]
  convert (c • sφ).contMDiff using 1

/-- The submodule of smooth `V`-valued rough `k`-forms. -/
def smoothBundleForms (I : ModelWithCorners ℝ E H) [IsManifold I 1 M] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] (k : ℕ) :
    Submodule ℝ (RoughBundleForm I M V k) where
  carrier := {φ | IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) φ}
  zero_mem' := smoothSection_zero (I := I) (V := V) (k := k)
  add_mem' := fun hφ hψ ↦ smoothSection_add (I := I) (V := V) (k := k) hφ hψ
  smul_mem' := fun c _φ hφ ↦ smoothSection_smul (I := I) (V := V) (k := k) c hφ

/-- Membership in `smoothBundleForms` is exactly smoothness of the corresponding section. -/
@[simp] theorem mem_smoothBundleForms [IsManifold I 1 M] {φ : RoughBundleForm I M V k} :
    φ ∈ smoothBundleForms (I := I) F V k ↔
      IsSmoothBundleForm (I := I) (F := F) (V := V) (k := k) (n := ∞) φ :=
  Iff.rfl

/-- A smooth bundle-valued differential `k`-form. -/
abbrev SmoothBundleForm (I : ModelWithCorners ℝ E H) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (V : M → Type*)
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
    [IsManifold I 1 M] (k : ℕ) : Type _ :=
  ↥(smoothBundleForms (I := I) F V k)

namespace SmoothBundleForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- Two smooth bundle-valued forms are equal when they agree on every tangent tuple. -/
@[ext]
theorem ext {φ ψ : SmoothBundleForm I F V k}
    (h : ∀ x v, φ.1 x v = ψ.1 x v) : φ = ψ := by
  apply Subtype.ext
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  exact h x v

/-- The smooth section underlying a smooth bundle-valued differential form. -/
def toContMDiffSection (φ : SmoothBundleForm I F V k) :
    ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x) :=
  ⟨φ.1, φ.2⟩

/-- Reconstruct a smooth bundle-valued form from its smooth section. -/
def ofContMDiffSection
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    SmoothBundleForm I F V k :=
  ⟨s, s.contMDiff⟩

@[simp]
theorem toContMDiffSection_apply (φ : SmoothBundleForm I F V k) (x : M) :
    φ.toContMDiffSection x = φ.1 x :=
  by
    simp only [toContMDiffSection]
    rfl

/-- The section view and reconstruction are mutual inverses on forms. -/
@[simp]
theorem ofContMDiffSection_toContMDiffSection (φ : SmoothBundleForm I F V k) :
    ofContMDiffSection φ.toContMDiffSection = φ := by
  apply Subtype.ext
  rfl

/-- The section view and reconstruction are mutual inverses on sections. -/
@[simp]
theorem toContMDiffSection_ofContMDiffSection
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    (ofContMDiffSection s).toContMDiffSection = s := by
  apply ContMDiffSection.ext
  intro x
  rfl

/-- The section view determines a smooth bundle-valued form uniquely. -/
theorem toContMDiffSection_injective :
    Function.Injective
      (toContMDiffSection : SmoothBundleForm I F V k →
        ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
          (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) := by
  exact Function.LeftInverse.injective ofContMDiffSection_toContMDiffSection

@[simp]
theorem zero_toContMDiffSection :
    (0 : SmoothBundleForm I F V k).toContMDiffSection = 0 :=
  by
    apply ContMDiffSection.ext
    intro x
    rfl

@[simp]
theorem add_toContMDiffSection (φ ψ : SmoothBundleForm I F V k) :
    (φ + ψ).toContMDiffSection = φ.toContMDiffSection + ψ.toContMDiffSection :=
  by
    apply ContMDiffSection.ext
    intro x
    rfl

@[simp]
theorem smul_toContMDiffSection (c : ℝ) (φ : SmoothBundleForm I F V k) :
    (c • φ).toContMDiffSection = c • φ.toContMDiffSection :=
  by
    apply ContMDiffSection.ext
    intro x
    rfl

@[simp]
theorem neg_toContMDiffSection (φ : SmoothBundleForm I F V k) :
    (-φ).toContMDiffSection = -φ.toContMDiffSection := by
  apply ContMDiffSection.ext
  intro x
  rfl

@[simp]
theorem sub_toContMDiffSection (φ ψ : SmoothBundleForm I F V k) :
    (φ - ψ).toContMDiffSection = φ.toContMDiffSection - ψ.toContMDiffSection := by
  apply ContMDiffSection.ext
  intro x
  rfl

end SmoothBundleForm

section FixedCoefficients

/-- A fixed-coefficient rough form is `C^n` when it is a `C^n` section of the existing
alternating tangent bundle. Degree and coefficient space are inferred from the form. -/
def IsSmoothForm (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]
    (n : WithTop ℕ∞) (φ : RoughForm I M F k) : Prop :=
  IsSmoothBundleForm (I := I) (F := F) (V := Bundle.Trivial M F) (k := k) n φ

/-- The fixed-coefficient regularity predicate is the existing section regularity predicate. -/
theorem isSmoothForm_def [IsManifold I 1 M] (n : WithTop ℕ∞) (φ : RoughForm I M F k) :
    IsSmoothForm I n φ ↔
      ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
        (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x)) :=
  Iff.rfl

/-- A regular fixed-coefficient form is a regular section of the alternating bundle. -/
theorem IsSmoothForm.contMDiff [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x)) :=
  (isSmoothForm_def n φ).mp hφ

/-- Addition preserves regularity of the actual fixed-coefficient bundle sections. -/
theorem IsSmoothForm.add [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ ψ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) (hψ : IsSmoothForm I n ψ) :
    IsSmoothForm I n (φ + ψ) := by
  rw [isSmoothForm_def]
  exact hφ.contMDiff.add_section hψ.contMDiff

/-- The zero differential form has every section regularity. -/
theorem IsSmoothForm.zero [IsManifold I 1 M] (n : WithTop ℕ∞) :
    IsSmoothForm I n (0 : RoughForm I M F k) := by
  rw [isSmoothForm_def]
  exact contMDiff_zeroSection ℝ (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F)

/-- Finite sums preserve section regularity of differential forms. -/
theorem IsSmoothForm.sum [IsManifold I 1 M] {n : WithTop ℕ∞} {ι : Type*}
    (φ : ι → RoughForm I M F k) (s : Finset ι) (hφ : ∀ i ∈ s, IsSmoothForm I n (φ i)) :
    IsSmoothForm I n (∑ i ∈ s, φ i) := by
  rw [isSmoothForm_def]
  simpa only [Finset.sum_apply] using
    ContMDiff.sum_section (fun i hi ↦ (hφ i hi).contMDiff)

/-- Negation preserves regularity of the actual fixed-coefficient bundle section. -/
theorem IsSmoothForm.neg [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) : IsSmoothForm I n (-φ) := by
  rw [isSmoothForm_def]
  exact hφ.contMDiff.neg_section

/-- Constant scalar multiplication preserves regularity of the actual bundle section. -/
theorem IsSmoothForm.smul [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) (c : ℝ) :
    IsSmoothForm I n (c • φ) := by
  rw [isSmoothForm_def]
  exact hφ.contMDiff.const_smul_section

/-- Multiplication by a scalar `C^n` function preserves the regularity of a rough form. -/
theorem IsSmoothForm.fun_smul [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) n f) : IsSmoothForm I n (fun x ↦ f x • φ x) := by
  rw [isSmoothForm_def]
  exact hf.smul_section hφ.contMDiff

/-- A `C^n` form is `C^m` for every `m ≤ n`. -/
theorem IsSmoothForm.of_le [IsManifold I 1 M] {m n : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) (hmn : m ≤ n) : IsSmoothForm I m φ :=
  (isSmoothForm_def m φ).mpr (hφ.contMDiff.of_le hmn)

/-- The submodule of smooth fixed-coefficient `F`-valued rough forms. -/
def smoothForms (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :
    Submodule ℝ (RoughForm I M F k) :=
  smoothBundleForms (I := I) F (Bundle.Trivial M F) k

/-- Membership in `smoothForms` is smoothness of the fixed-coefficient form as a section. -/
@[simp] theorem mem_smoothForms {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {φ : RoughForm I M F k} :
    φ ∈ smoothForms I M F k ↔
      IsSmoothBundleForm (I := I) (F := F) (V := Bundle.Trivial M F) (k := k) (n := ∞) φ :=
  Iff.rfl

/-- A smooth fixed-coefficient rough form lies in `smoothForms`. -/
theorem IsSmoothForm.mem_smoothForms [IsManifold I 1 M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I ∞ φ) : φ ∈ smoothForms I M F k :=
  TauCeti.mem_smoothForms.mpr ((isSmoothBundleForm_def ∞ φ).mpr ((isSmoothForm_def ∞ φ).mp hφ))

/-- A smooth fixed-coefficient differential `k`-form. -/
abbrev SmoothForm (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) : Type _ :=
  ↥(smoothForms I M F k)

namespace SmoothForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The underlying rough form of a smooth form is a smooth bundle section. -/
theorem isSmoothBundleForm (φ : SmoothForm I M F k) :
    IsSmoothBundleForm (I := I) (F := F) (V := Bundle.Trivial M F) (n := ∞) φ.1 :=
  mem_smoothForms.mp φ.2

/-- The section underlying a smooth form is smooth. -/
theorem contMDiff (φ : SmoothForm I M F k) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.1 x)) :=
  (isSmoothBundleForm_def ∞ φ.1).mp φ.isSmoothBundleForm

/-- The underlying rough form of a smooth form is a smooth fixed-coefficient form. -/
theorem isSmoothForm (φ : SmoothForm I M F k) : IsSmoothForm I ∞ φ.1 :=
  (isSmoothForm_def ∞ φ.1).mpr φ.contMDiff

/-- The section underlying a smooth form is differentiable. -/
theorem mdifferentiable (φ : SmoothForm I M F k) :
    MDiff (fun x ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.1 x) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Bundle.Trivial M F x))) :=
  φ.contMDiff.mdifferentiable (by simp)

/-- The section underlying a smooth form is differentiable at every point. -/
theorem mdifferentiableAt (φ : SmoothForm I M F k) (x : M) :
    MDiffAt (fun x ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.1 x) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Bundle.Trivial M F x))) x :=
  φ.contMDiff.mdifferentiableAt (by simp)

/-- The smooth section underlying a fixed-coefficient smooth form. -/
def toContMDiffSection {k : ℕ} (φ : SmoothForm I M F k) :
    ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) :=
  SmoothBundleForm.toContMDiffSection φ

/-- Reconstruct a fixed-coefficient smooth form from its smooth section. -/
def ofContMDiffSection {k : ℕ}
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F)) :
    SmoothForm I M F k :=
  SmoothBundleForm.ofContMDiffSection s

@[simp]
theorem toContMDiffSection_apply {k : ℕ} (φ : SmoothForm I M F k) (x : M) :
    φ.toContMDiffSection x = φ.1 x :=
  by
    exact SmoothBundleForm.toContMDiffSection_apply φ x

/-- The section view and reconstruction are mutual inverses on forms. -/
@[simp]
theorem ofContMDiffSection_toContMDiffSection {k : ℕ} (φ : SmoothForm I M F k) :
    ofContMDiffSection φ.toContMDiffSection = φ :=
  SmoothBundleForm.ofContMDiffSection_toContMDiffSection φ

/-- The section view and reconstruction are mutual inverses on sections. -/
@[simp]
theorem toContMDiffSection_ofContMDiffSection {k : ℕ}
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F)) :
    (ofContMDiffSection s).toContMDiffSection = s :=
  SmoothBundleForm.toContMDiffSection_ofContMDiffSection s

/-- The section view determines a smooth fixed-coefficient form uniquely. -/
theorem toContMDiffSection_injective {k : ℕ} :
    Function.Injective
      (toContMDiffSection : SmoothForm I M F k →
        ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
          (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F)) :=
  SmoothBundleForm.toContMDiffSection_injective

@[simp]
theorem zero_toContMDiffSection {k : ℕ} :
    (0 : SmoothForm I M F k).toContMDiffSection = 0 :=
  SmoothBundleForm.zero_toContMDiffSection

@[simp]
theorem add_toContMDiffSection {k : ℕ} (φ ψ : SmoothForm I M F k) :
    (φ + ψ).toContMDiffSection = φ.toContMDiffSection + ψ.toContMDiffSection := by
  exact SmoothBundleForm.add_toContMDiffSection φ ψ

@[simp]
theorem smul_toContMDiffSection {k : ℕ} (c : ℝ) (φ : SmoothForm I M F k) :
    (c • φ).toContMDiffSection = c • φ.toContMDiffSection := by
  exact SmoothBundleForm.smul_toContMDiffSection c φ

@[simp]
theorem neg_toContMDiffSection {k : ℕ} (φ : SmoothForm I M F k) :
    (-φ).toContMDiffSection = -φ.toContMDiffSection :=
  SmoothBundleForm.neg_toContMDiffSection φ

@[simp]
theorem sub_toContMDiffSection {k : ℕ} (φ ψ : SmoothForm I M F k) :
    (φ - ψ).toContMDiffSection = φ.toContMDiffSection - ψ.toContMDiffSection :=
  SmoothBundleForm.sub_toContMDiffSection φ ψ

/-- The rough form underlying a sum of smooth forms is the sum of their rough forms. -/
theorem add_toRoughForm {k : ℕ} (φ ψ : SmoothForm I M F k) :
    (φ + ψ).1 = φ.1 + ψ.1 :=
  rfl

/-- The rough form underlying the negation of a smooth form is the negation of its rough form. -/
theorem neg_toRoughForm {k : ℕ} (φ : SmoothForm I M F k) :
    (-φ).1 = -φ.1 :=
  rfl

/-- The constant smooth form whose value is the alternating map `A` in model-space coordinates. -/
def const {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) :
    SmoothForm (modelWithCornersSelf ℝ V) V F k := by
  let A' : ∀ x : V, TangentSpace (modelWithCornersSelf ℝ V) x [⋀^Fin k]→L[ℝ] F :=
    fun x ↦ A.compContinuousLinearMap (NormedSpace.fromTangentSpace x).toContinuousLinearMap
  exact ⟨A', by
    apply (mem_smoothForms (I := modelWithCornersSelf ℝ V) (M := V)
      (F := F) (k := k) (φ := A')).2
    -- Membership in `smoothForms` is definitionally the smooth-section predicate.
    change IsSmoothBundleForm (I := modelWithCornersSelf ℝ V) (F := F)
      (V := Bundle.Trivial V F) ∞ A'
    rw [isSmoothBundleForm_def]
    intro x
    rw [contMDiffAt_continuousAlternatingMap_bundle]
    refine ⟨?_, ?_⟩
    · simpa only [Function.id_def] using (contMDiffAt_id : ContMDiffAt (modelWithCornersSelf ℝ V)
          (modelWithCornersSelf ℝ V) ∞ id x)
    · -- The alternating-bundle regularity criterion asks for the fibre coordinate map.
      change ContMDiffAt (modelWithCornersSelf ℝ V)
        (𝓘(ℝ, V [⋀^Fin k]→L[ℝ] F)) ∞
        (fun y => ContinuousAlternatingMap.inCoordinates V F
          (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
          (E₂ := Bundle.Trivial V F) x y x y (A' y)) x
      have hcoord : (fun y : V =>
          ContinuousAlternatingMap.inCoordinates V F
            (E₁ := TangentSpace (modelWithCornersSelf ℝ V))
            (E₂ := Bundle.Trivial V F) x y x y (A' y)) = fun _ => A := by
        funext y
        ext v
        simp only [A', ContinuousAlternatingMap.inCoordinates,
          Bundle.Trivial.eq_trivialization V F
            (trivializationAt F (Trivial V F) x),
          Bundle.Trivial.continuousLinearMapAt_trivialization,
          TangentBundle.symmL_model_space]
        rfl
      rw [hcoord]
      exact contMDiffAt_const⟩

/-- The underlying rough form of `const A` is `A` transported to each tangent fibre. -/
theorem const_toRoughForm {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) :
    (const A).1 = (fun y : V => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap) := by
  rfl

/-- Evaluating a constant smooth form transports its arguments back to the model space. -/
@[simp]
theorem const_apply {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) (x : V)
    (v : Fin k → TangentSpace (modelWithCornersSelf ℝ V) x) :
    (const A).1 x v = A (fun i ↦ NormedSpace.fromTangentSpace x (v i)) := by
  rw [const_toRoughForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

/-- Evaluate a degree-two smooth form on an ordered pair of tangent vectors.

This ordered-pair view supplies the arguments for the algebraic bilinear-form conversion and
the extensionality principle for degree-two forms. -/
def eval₂ (φ : SmoothForm I M F 2) (x : M) (v w : TangentSpace I x) : F :=
  φ.1 x ![v, w]

@[simp]
theorem eval₂_apply (φ : SmoothForm I M F 2) (x : M) (v w : TangentSpace I x) :
    φ.eval₂ x v w = φ.1 x ![v, w] := by
  simp [eval₂]


section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluation in tangent coordinates agrees with the alternating-bundle coordinate chart.

This is the chartwise transport used by `contMDiff_apply`: the target tangent vectors are first
sent through the tangent-bundle trivialization, and the form is then read in the corresponding
alternating-map coordinates. -/
private theorem eval₂_eq_inCoordinates
    (form : SmoothForm I M F 2) {x y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet)
    (v w : TangentSpace I y) :
    SmoothForm.eval₂ form y v w =
      ContinuousAlternatingMap.inCoordinates E F
        (B₁ := M) (B₂ := M) (E₁ := TangentSpace I) (E₂ := Bundle.Trivial M F)
        x y x y ((SmoothForm.toContMDiffSection form) y)
        ![(trivializationAt E (TangentSpace I) x ⟨y, v⟩).2,
          (trivializationAt E (TangentSpace I) x ⟨y, w⟩).2] := by
  let e := trivializationAt E (TangentSpace I) x
  rw [ContinuousAlternatingMap.inCoordinates_eq (F₁ := E) (F₂ := F)
    (B₁ := M) (B₂ := M) (E₁ := TangentSpace I) (E₂ := Bundle.Trivial M F)
    hy (by simp)]
  have hv : e.symm y (e ⟨y, v⟩).2 = v := by
    rw [← e.symmL_apply (R := ℝ) hy]
    simpa [e.coe_linearMapAt_of_mem (R := ℝ) hy] using
      (e.symmL_continuousLinearMapAt (R := ℝ) hy v)
  have hw : e.symm y (e ⟨y, w⟩).2 = w := by
    rw [← e.symmL_apply (R := ℝ) hy]
    simpa [e.coe_linearMapAt_of_mem (R := ℝ) hy] using
      (e.symmL_continuousLinearMapAt (R := ℝ) hy w)
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, SmoothForm.eval₂_apply]
  simp only [Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearEquivAt_trivialization, ContinuousLinearEquiv.coe_refl,
    SmoothForm.toContMDiffSection_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.continuousLinearEquivAt_symm_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, ContinuousLinearMap.coe_id',
    Function.comp_apply, id_eq]
  congr 1
  funext i
  fin_cases i
  · simpa [Function.comp_apply] using hv.symm
  · convert hw.symm using 1 <;> rfl

/-- Evaluating a smooth degree-two form on two smooth tangent fields along a smooth map is smooth.

This result holds for arbitrary normed coefficient spaces and the regularity required by the
smooth-form carrier. -/
lemma contMDiff_apply {n : ℕ∞ω} [IsManifold I (n + 1) M] [ENat.LEInfty n]
    (form : SmoothForm I M F 2)
    {b : N → M}
    {V W : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (V y)))
    (hW : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (W y))) :
    ContMDiff I' 𝓘(ℝ, F) n (fun y ↦ SmoothForm.eval₂ form (b y) (V y) (W y)) := by
  have hb : ContMDiff I' I n b := fun y ↦ by
    have hy := hV y
    rw [← contMDiffWithinAt_univ] at hy ⊢
    exact (contMDiffWithinAt_totalSpace.mp hy).1
  have hform := (form.toContMDiffSection.contMDiff.of_le ENat.LEInfty.out).comp hb
  have hform' : ContMDiff I' (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F)) n
      (fun y ↦ Bundle.TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] F) (b y)
        (form.toContMDiffSection (b y))) := by
    convert hform using 1
    funext y
    rfl
  intro y₀
  let e := trivializationAt E (TangentSpace I) (b y₀)
  have he : b y₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (b y₀)
  let _ : ContMDiffVectorBundle n E (TangentSpace I) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have hV' := (e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' E (b y) (V y))
    (FiberBundle.mem_trivializationAt_proj_source (x := ⟨b y₀, V y₀⟩))).mp (hV y₀)
  have hW' := (e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' E (b y) (W y))
    (FiberBundle.mem_trivializationAt_proj_source (x := ⟨b y₀, W y₀⟩))).mp (hW y₀)
  have hf := (contMDiffAt_continuousAlternatingMap_bundle (IM := I') (IB := I) (n := n)
    (f := fun y : N ↦
      (Bundle.TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] F) (b y)
        (form.toContMDiffSection (b y))))
    ).mp (hform' y₀)
  have happly := (hf.2.continuousAlternatingMap_apply
    (f := fun i : Fin 2 ↦ Fin.cases
      (fun y ↦ (e ⟨b y, V y⟩).2)
      (fun _ ↦ fun y ↦ (e ⟨b y, W y⟩).2) i)
    (fun i ↦ by
    fin_cases i
    · exact hV'.2
    · exact hW'.2))
  refine happly.congr_of_eventuallyEq ?_
  filter_upwards [(hb y₀).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)] with y hy
  rw [eval₂_eq_inCoordinates form hy (V y) (W y)]
  congr 1
  funext i
  fin_cases i <;> rfl

end Evaluation

/-- The algebraic bilinear form represented by the value of a real degree-two smooth form.

This generalizes `SmoothTwoForm.bilinFormAt` from
`TauCeti.Geometry.Manifold.TwoForm.Basic`.  The view interoperates with APIs phrased in terms of
`LinearMap.BilinForm`, including the symplectic constructions. -/
def bilinFormAt (φ : SmoothForm I M ℝ 2) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  MultilinearMap.toBilinForm (φ.1 x).toMultilinearMap

@[simp]
theorem bilinFormAt_apply (φ : SmoothForm I M ℝ 2) (x : M) (v w : TangentSpace I x) :
    φ.bilinFormAt x v w = φ.eval₂ x v w :=
  by simp [bilinFormAt]

/-- The bilinear form represented by a degree-two smooth form is alternating. -/
theorem isAlt_bilinFormAt (φ : SmoothForm I M ℝ 2) (x : M) :
    (φ.bilinFormAt x).IsAlt := by
  apply MultilinearMap.isAlt_toBilinForm
  intro v
  exact (φ.1 x).map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

/-- Evaluation on two equal tangent vectors vanishes by alternation. -/
theorem eval₂_self (φ : SmoothForm I M F 2) (x : M) (v : TangentSpace I x) :
    φ.eval₂ x v v = 0 := by
  simpa only [eval₂_apply] using (φ.1 x).map_eq_zero_of_eq ![v, v] (by simp) Fin.zero_ne_one

/-- Swapping the inputs of a degree-two smooth form negates its value. -/
theorem eval₂_swap (φ : SmoothForm I M F 2) (x : M)
    (v w : TangentSpace I x) :
  φ.eval₂ x v w = -φ.eval₂ x w v := by
  have h := (φ.1 x).map_swap ![v, w] (i := 0) (j := 1) Fin.zero_ne_one
  have htuple : ![v, w] ∘ Equiv.swap 0 1 = ![w, v] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple] at h
  have h' : φ.eval₂ x w v = -φ.eval₂ x v w := by
    simpa [eval₂] using h
  calc
    φ.eval₂ x v w = - -φ.eval₂ x v w := by simp
    _ = -φ.eval₂ x w v := by rw [h']

/-- A degree-two smooth form is determined by its values on ordered pairs. -/
@[ext]
theorem ext {φ ψ : SmoothForm I M F 2}
    (h : ∀ x v w, φ.eval₂ x v w = ψ.eval₂ x v w) :
    φ = ψ := by
  apply Subtype.ext
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv]
  simpa only [eval₂_apply] using h x (v 0) (v 1)

section SectionView

variable {k : ℕ}

/-- The value of a smooth form as a continuous alternating map on the model fibre. -/
def altAt (φ : SmoothForm I M F k) (x : M) : E [⋀^Fin k]→L[ℝ] F := φ.1 x

@[simp]
theorem altAt_apply (φ : SmoothForm I M F k) (x : M) (v : Fin k → E) :
    φ.altAt x v = φ.1 x v :=
  by
    simp only [altAt]
    rfl

/-- The degree-two alternating-map view evaluated on a tuple agrees with ordered-pair evaluation. -/
theorem altAt_apply_eval₂ (φ : SmoothForm I M F 2) (x : M) (v : Fin 2 → E) :
    φ.altAt x v = φ.eval₂ x (v 0) (v 1) := by
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv]
  simp only [altAt, eval₂]
  rfl

end SectionView

end SmoothForm

end FixedCoefficients

end TauCeti

end
