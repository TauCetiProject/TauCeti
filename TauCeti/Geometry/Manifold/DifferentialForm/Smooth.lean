/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

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

/-- A smooth fixed-coefficient differential `k`-form. -/
abbrev SmoothForm (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) : Type _ :=
  ↥(smoothForms I M F k)

namespace SmoothForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

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

/-- Evaluate a degree-two smooth form on an ordered pair of tangent vectors.

This ordered-pair view supplies the arguments for the algebraic bilinear-form conversion and
the extensionality principle for degree-two forms. -/
def eval₂ (φ : SmoothForm I M F 2) (x : M) (v w : TangentSpace I x) : F :=
  φ.1 x ![v, w]

@[simp]
theorem eval₂_apply (φ : SmoothForm I M F 2) (x : M) (v w : TangentSpace I x) :
    φ.eval₂ x v w = φ.1 x ![v, w] := by
  simp [eval₂]

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
