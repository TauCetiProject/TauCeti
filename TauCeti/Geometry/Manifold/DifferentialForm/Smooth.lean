/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Topology.Algebra.Module.Alternating.Basic
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
import TauCeti.Topology.FiberBundle.Separation

/-!
# Smooth bundle-valued differential forms

This file packages smooth sections of the bundle of alternating maps on tangent fibres.  The
underlying rough form remains an unbundled dependent function, while `IsSmoothBundleForm` records
that its graph is a smooth section of the alternating bundle.  The corresponding `Submodule`
provides the bundled carrier `SmoothBundleForm`; fixed coefficients are the `SmoothForm`
specialization.  These carriers are the input for smooth wedge products and pullbacks.

The degree-two evaluation API below evaluates forms on ordered pairs and exposes real-valued fibres
as alternating bilinear forms.

In the trivialization at any point, the fiber coordinate of a form at `y` is the form pulled back
along the inverse tangent trivialization at `y`
(`FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd`),
with no chart-domain hypothesis. Hence a form is `C^n` exactly when its values on the frames of
these trivializations are (`TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply`).

Smoothness is expressed through the total-space charts of the topological alternating bundle.  The
module operations use Mathlib's smooth-section API, so this carrier does not require a chosen
trivialization or a global smooth alternating-bundle instance.

The fixed-coefficient section and degree-two evaluation adapters generalize the corresponding
declarations in `TauCeti.Geometry.Manifold.TwoForm.Basic`.

For degree two, use the ordered-pair evaluation to obtain the value in the fibre over a point.
The accompanying API provides alternation, extensionality, and `C^n` smoothness after applying
the form to `C^n` tangent fields; the fixed-coefficient section exposes the same operations in a
trivial bundle. On a Hausdorff manifold, two smooth forms agreeing on a dense set are equal
(`TauCeti.SmoothBundleForm.eq_of_forall_mem_dense`).
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
-- The proof uses Mathlib's `ContinuousAlternatingMap.ext` for the underlying alternating maps.
@[ext]
theorem ext {φ ψ : SmoothBundleForm I F V k}
    (h : ∀ x v, φ.val x v = ψ.val x v) : φ = ψ := by
  apply Subtype.ext
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  exact h x v

/-- Two smooth bundle-valued forms on a Hausdorff manifold that agree on a dense set are equal:
their sections are continuous maps into the total space of the alternating bundle, which is
Hausdorff. -/
theorem eq_of_forall_mem_dense [T2Space M] {s : Set M} (hs : Dense s)
    {φ ψ : SmoothBundleForm I F V k} (h : ∀ x ∈ s, φ.val x = ψ.val x) : φ = ψ := by
  have hcont (φ : SmoothBundleForm I F V k) :
      Continuous fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.val x) :=
    ((isSmoothBundleForm_def ∞ φ.val).mp (mem_smoothBundleForms.mp φ.property)).continuous
  have heq := (hcont φ).ext_on hs (hcont ψ) fun x hx ↦ by simp only [h x hx]
  exact Subtype.ext (funext fun x ↦ by simpa using congrFun heq x)

/-- The smooth section underlying a smooth bundle-valued differential form. -/
def toContMDiffSection (φ : SmoothBundleForm I F V k) :
    ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x) :=
  ⟨φ.val, φ.property⟩

/-- Reconstruct a smooth bundle-valued form from its smooth section. -/
def ofContMDiffSection
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    SmoothBundleForm I F V k :=
  ⟨s, s.contMDiff⟩

/-- The rough form underlying the form of a smooth section is the section. -/
@[simp]
theorem coe_ofContMDiffSection
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    ((ofContMDiffSection s : SmoothBundleForm I F V k) : RoughBundleForm I M V k) = ⇑s :=
  (rfl)

/-- Reconstructing forms from smooth sections preserves addition. -/
@[simp]
theorem ofContMDiffSection_add
    (s t : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    ofContMDiffSection (s + t) = ofContMDiffSection s + ofContMDiffSection t :=
  Subtype.ext (by simp)

/-- Reconstructing forms from smooth sections preserves scalar multiplication. -/
@[simp]
theorem ofContMDiffSection_smul (c : ℝ)
    (s : ContMDiffSection I (E [⋀^Fin k]→L[ℝ] F) ∞
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] V x)) :
    ofContMDiffSection (c • s) = c • ofContMDiffSection s :=
  Subtype.ext (by simp)

@[simp]
theorem toContMDiffSection_apply (φ : SmoothBundleForm I F V k) (x : M) :
    φ.toContMDiffSection x = φ.val x :=
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

namespace SmoothBundleForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/- The generic evaluation API follows Mathlib's
`Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap` declarations
`ContinuousAlternatingMap.map_eq_zero_of_eq`, `ContinuousAlternatingMap.map_swap`,
`ContinuousAlternatingMap.ext`, and `ContMDiff.continuousAlternatingMap_bundle_apply`; its
algebraic laws use `Mathlib.LinearAlgebra.Alternating.Basic`. -/
/-- Evaluation of a smooth bundle-valued two-form on an ordered pair of tangent vectors returns
the value in the fibre over the base point. -/
def eval₂ (φ : SmoothBundleForm I F V 2) (x : M) (v w : TangentSpace I x) : V x :=
  φ.val x ![v, w]

/-- Evaluation on two equal tangent vectors vanishes by alternation. -/
@[simp]
theorem eval₂_self (φ : SmoothBundleForm I F V 2) (x : M) (v : TangentSpace I x) :
    φ.eval₂ x v v = 0 := by
  simpa [eval₂] using (φ.val x).map_eq_zero_of_eq ![v, v] (by simp) Fin.zero_ne_one

/-- Swapping the inputs of a bundle-valued two-form negates its value. -/
theorem eval₂_swap (φ : SmoothBundleForm I F V 2) (x : M)
    (v w : TangentSpace I x) :
    φ.eval₂ x v w = -φ.eval₂ x w v := by
  simpa [eval₂] using (φ.val x).apply_vecCons_swap w v

@[simp]
theorem eval₂_apply (φ : SmoothBundleForm I F V 2) (x : M)
    (v w : TangentSpace I x) :
    φ.eval₂ x v w = φ.val x ![v, w] :=
  by simp [eval₂]

/-- Evaluation of a sum of degree-two forms is the sum of the evaluations. -/
theorem eval₂_add (φ ψ : SmoothBundleForm I F V 2) (x : M)
    (v w : TangentSpace I x) :
    (φ + ψ).eval₂ x v w = φ.eval₂ x v w + ψ.eval₂ x v w :=
  (rfl)

/-- Evaluation of the negative of a degree-two form is the negative of the evaluation. -/
theorem eval₂_neg (φ : SmoothBundleForm I F V 2) (x : M) (v w : TangentSpace I x) :
    (-φ).eval₂ x v w = -φ.eval₂ x v w :=
  (rfl)

/-- Ordered-pair evaluation is additive in its first tangent argument. -/
theorem eval₂_add_left (φ : SmoothBundleForm I F V 2) (x : M)
    (v v' w : TangentSpace I x) :
    φ.eval₂ x (v + v') w = φ.eval₂ x v w + φ.eval₂ x v' w := by
  simpa only [eval₂, Matrix.vecCons, Fin.update_cons_zero] using
    (φ.val x).map_update_add ![v, w] 0 v v'

/-- Ordered-pair evaluation is additive in its second tangent argument. -/
theorem eval₂_add_right (φ : SmoothBundleForm I F V 2) (x : M)
    (v w w' : TangentSpace I x) :
    φ.eval₂ x v (w + w') = φ.eval₂ x v w + φ.eval₂ x v w' := by
  simpa only [eval₂, Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
    (φ.val x).map_update_add ![v, w] (0 : Fin 1).succ w w'

/-- Ordered-pair evaluation vanishes when its first tangent argument is zero. -/
theorem eval₂_zero_left (φ : SmoothBundleForm I F V 2) (x : M) (w : TangentSpace I x) :
    φ.eval₂ x 0 w = 0 := by
  simpa using eval₂_add_left φ x 0 0 w

/-- Ordered-pair evaluation vanishes when its second tangent argument is zero. -/
theorem eval₂_zero_right (φ : SmoothBundleForm I F V 2) (x : M) (v : TangentSpace I x) :
    φ.eval₂ x v 0 = 0 := by
  simpa using eval₂_add_right φ x v 0 0

/-- Real scalar multiplication in the first tangent argument scales the fibre value. -/
theorem eval₂_smul_left (φ : SmoothBundleForm I F V 2) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    φ.eval₂ x (c • v) w = c • φ.eval₂ x v w := by
  simpa only [eval₂, Matrix.vecCons, Fin.update_cons_zero] using
    (φ.val x).map_update_smul ![v, w] 0 c v

/-- Real scalar multiplication in the second tangent argument scales the fibre value. -/
theorem eval₂_smul_right (φ : SmoothBundleForm I F V 2) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    φ.eval₂ x v (c • w) = c • φ.eval₂ x v w := by
  simpa only [eval₂, Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero] using
    (φ.val x).map_update_smul ![v, w] (0 : Fin 1).succ c w

/-- Negating the first tangent vector negates the evaluation of a degree-two form. -/
theorem eval₂_neg_left (φ : SmoothBundleForm I F V 2) (x : M) (v w : TangentSpace I x) :
    φ.eval₂ x (-v) w = -φ.eval₂ x v w := by
  simpa only [eval₂, Matrix.vecCons, Fin.update_cons_zero,
    ContinuousAlternatingMap.coe_toAlternatingMap] using
    (φ.val x).toAlternatingMap.map_update_neg ![v, w] (0 : Fin 2) v

/-- Negating the second tangent vector negates the evaluation of a degree-two form. -/
theorem eval₂_neg_right (φ : SmoothBundleForm I F V 2) (x : M) (v w : TangentSpace I x) :
    φ.eval₂ x v (-w) = -φ.eval₂ x v w := by
  simpa only [eval₂, Matrix.vecCons, ← Fin.cons_update, Fin.update_cons_zero,
    ContinuousAlternatingMap.coe_toAlternatingMap] using
    (φ.val x).toAlternatingMap.map_update_neg ![v, w] (0 : Fin 1).succ w

/-- Ordered-pair evaluation is subtractive in its first tangent argument. -/
theorem eval₂_sub_left (φ : SmoothBundleForm I F V 2) (x : M) (v v' w : TangentSpace I x) :
    φ.eval₂ x (v - v') w = φ.eval₂ x v w - φ.eval₂ x v' w := by
  rw [sub_eq_add_neg, eval₂_add_left, eval₂_neg_left, ← sub_eq_add_neg]

/-- Ordered-pair evaluation is subtractive in its second tangent argument. -/
theorem eval₂_sub_right (φ : SmoothBundleForm I F V 2) (x : M) (v w w' : TangentSpace I x) :
    φ.eval₂ x v (w - w') = φ.eval₂ x v w - φ.eval₂ x v w' := by
  rw [sub_eq_add_neg, eval₂_add_right, eval₂_neg_right, ← sub_eq_add_neg]

/-- Two smooth bundle-valued two-forms have the same value at a point when their ordered-pair
evaluations there agree. -/
theorem apply_eq_of_eval₂_eq {φ ψ : SmoothBundleForm I F V 2} {x : M}
    (h : ∀ v w, φ.eval₂ x v w = ψ.eval₂ x v w) : φ.val x = ψ.val x := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv]
  simpa [eval₂] using h (v 0) (v 1)

/-- Two smooth bundle-valued two-forms are equal when their ordered-pair evaluations agree. -/
theorem ext_eval₂ {φ ψ : SmoothBundleForm I F V 2}
    (h : ∀ x v w, φ.eval₂ x v w = ψ.eval₂ x v w) : φ = ψ :=
  Subtype.ext (funext fun x ↦ apply_eq_of_eval₂_eq (h x))

/-- Two smooth bundle-valued two-forms are equal exactly when all ordered-pair evaluations agree. -/
theorem ext_eval₂_iff {φ ψ : SmoothBundleForm I F V 2} :
    φ = ψ ↔ ∀ x v w, φ.eval₂ x v w = ψ.eval₂ x v w :=
  ⟨fun h ↦ by subst h; intros; rfl, ext_eval₂⟩

section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth bundle-valued two-form on two tangent fields along a map, both `C^n` at
`y₀`, is `C^n` at `y₀`. -/
theorem contMDiffAt_eval₂ {n : WithTop ℕ∞} [ENat.LEInfty n]
    (φ : SmoothBundleForm I F V 2) {b : N → M}
    {U W : ∀ y : N, TangentSpace I (b y)} {y₀ : N}
    (hU : ContMDiffAt I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (U y)) y₀)
    (hW : ContMDiffAt I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (W y)) y₀) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (φ.eval₂ (b y) (U y) (W y))) y₀ := by
  have hb : ContMDiffAt I' I n b y₀ := (contMDiff_proj (TangentSpace I)).contMDiffAt.comp y₀ hU
  have hφ := ((φ.toContMDiffSection.contMDiff.of_le ENat.LEInfty.out) (b y₀)).comp y₀ hb
  have hφ' : ContMDiffAt I' (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F)
        (E := fun x ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] V x) (b y)
        (φ.toContMDiffSection (b y))) y₀ := by
    convert hφ using 1
    funext y
    rfl
  have happly := ContMDiffAt.continuousAlternatingMap_bundle_apply
    (b := b) (v := fun i ↦ ![U, W] i) hφ'
    (fun i ↦ by
      fin_cases i
      · exact hU
      · exact hW)
  convert happly using 1
  funext y
  congr 1
  simp only [eval₂, SmoothBundleForm.toContMDiffSection_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Evaluating a smooth bundle-valued two-form on two `C^n` tangent fields along a `C^n` map is
`C^n`. -/
theorem contMDiff_eval₂ {n : WithTop ℕ∞} [ENat.LEInfty n]
    (φ : SmoothBundleForm I F V 2) {b : N → M}
    {U W : ∀ y : N, TangentSpace I (b y)}
    (hU : ContMDiff I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (U y)))
    (hW : ContMDiff I' I.tangent n
      (fun y ↦ TotalSpace.mk' E (b y) (W y))) :
    ContMDiff I' (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (φ.eval₂ (b y) (U y) (W y))) :=
  fun y ↦ φ.contMDiffAt_eval₂ (hU y) (hW y)

end Evaluation

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

/-- Multiplying a `C^n` form by a continuous scalar function gives a continuous (`C^0`) form. -/
theorem IsSmoothForm.fun_smul_of_continuous [IsManifold I 1 M] {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) {f : M → ℝ} (hf : Continuous f) :
    IsSmoothForm I 0 (fun x ↦ f x • φ x) :=
  (hφ.of_le bot_le).fun_smul (contMDiff_zero_iff.2 hf)

/-- **Smoothness of a form read in tangent trivializations**: for a finite-dimensional model
space, a form is `C^n` exactly when, near each point `x`, its values on the frame
`e.symmL y ∘ v` of the tangent trivialization `e` at `x`, for each fixed tuple `v` of model
vectors, are `C^n` at `x`. -/
theorem isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply [IsManifold I 1 M]
    [FiniteDimensional ℝ E]
    {n : WithTop ℕ∞} {φ : RoughForm I M F k} :
    IsSmoothForm I n φ ↔ ∀ (x : M) (v : Fin k → E), ContMDiffAt I 𝓘(ℝ, F) n
      (fun y ↦ φ y ((trivializationAt E (TangentSpace I) x).symmL ℝ y ∘ v)) x := by
  rw [isSmoothForm_def]
  refine forall_congr' fun x ↦ ?_
  simp only [contMDiffAt_section_iff,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- A smooth fixed-coefficient rough form lies in the smooth bundle-form submodule. -/
theorem IsSmoothForm.mem_smoothBundleForms [IsManifold I 1 M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I ∞ φ) : φ ∈ smoothBundleForms I F (Bundle.Trivial M F) k :=
  TauCeti.mem_smoothBundleForms.mpr
    ((isSmoothBundleForm_def ∞ φ).mpr ((isSmoothForm_def ∞ φ).mp hφ))

/-- A smooth fixed-coefficient differential `k`-form. -/
abbrev SmoothForm (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) : Type _ :=
  SmoothBundleForm I F (Bundle.Trivial M F) k

namespace SmoothForm

variable {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The underlying rough form of a smooth form is a smooth bundle section. -/
theorem isSmoothBundleForm (φ : SmoothForm I M F k) :
    IsSmoothBundleForm (I := I) (F := F) (V := Bundle.Trivial M F) (n := ∞) φ.val :=
  mem_smoothBundleForms.mp φ.property

/-- The section underlying a smooth form is smooth. -/
theorem contMDiff (φ : SmoothForm I M F k) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.val x)) :=
  (isSmoothBundleForm_def ∞ φ.val).mp φ.isSmoothBundleForm

/-- The underlying rough form of a smooth form is a smooth fixed-coefficient form. -/
theorem isSmoothForm (φ : SmoothForm I M F k) : IsSmoothForm I ∞ φ.val :=
  (isSmoothForm_def ∞ φ.val).mpr φ.contMDiff

/-- Evaluating a smooth form after transporting its degree across an equality. -/
theorem cast_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n m : ℕ} (h : n = m) (α : SmoothForm I M F n) (x : M)
    (v : Fin m → TangentSpace I x) :
    (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h α :
      RoughForm I M F m) x v = α.val x (v ∘ Fin.cast h) := by
  cases h
  rfl

/-- Evaluating the underlying rough form of a degree transport evaluates transported vectors. -/
theorem coe_cast {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n m : ℕ} (h : n = m) (α : SmoothForm I M F n) (x : M) :
    (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h α : RoughForm I M F m) x =
      (fun v ↦ α.val x (v ∘ Fin.cast h)) := by
  funext v
  exact cast_apply h α x v

/-- Transporting a smooth form along a trivial degree equality leaves it unchanged. -/
theorem cast_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (h : n = n) (α : SmoothForm I M F n) :
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h α = α :=
  (rfl)

/-- Successive degree transports collapse to the transport along their composite equality. -/
theorem cast_cast {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n m o : ℕ} (h : n = m) (h' : m = o)
    (α : SmoothForm I M F n) :
    LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h'
        (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h α) =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) (h.trans h') α := by
  cases h
  cases h'
  rfl

/-- Inverting a degree transport gives the transport along the inverse equality. -/
@[simp]
theorem cast_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n m : ℕ} (h : n = m) :
    (LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h).symm =
      LinearEquiv.cast (R := ℝ) (M := fun q : ℕ ↦ SmoothForm I M F q) h.symm := by
  cases h
  rfl

/-- The section underlying a smooth form is differentiable. -/
theorem mdifferentiable (φ : SmoothForm I M F k) :
    MDiff (fun x ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.val x) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Bundle.Trivial M F x))) :=
  φ.contMDiff.mdifferentiable (by simp)

/-- The section underlying a smooth form is differentiable at every point. -/
theorem mdifferentiableAt (φ : SmoothForm I M F k) (x : M) :
    MDiffAt (fun x ↦
      (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ.val x) :
        TotalSpace (E [⋀^Fin k]→L[ℝ] F)
          (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] Bundle.Trivial M F x))) x :=
  φ.contMDiff.mdifferentiableAt (by simp)

/-- Evaluating a smooth form on vector fields differentiable at a point gives a function
differentiable at that point. -/
theorem mdifferentiableAt_apply_vectorField (φ : SmoothForm I M F k)
    {V : Fin k → (y : M) → TangentSpace I y} {x : M}
    (hV : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (V i y : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ φ.val y (V · y)) x := by
  have h := (φ.mdifferentiableAt x).continuousAlternatingMap_bundle_apply (b := id) hV
  simpa using ((mdifferentiableAt_totalSpace _ _).1 h).2

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
    φ.toContMDiffSection x = φ.val x :=
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
    (φ + ψ).val = φ.val + ψ.val :=
  rfl

/-- The rough form underlying the negation of a smooth form is the negation of its rough form. -/
theorem neg_toRoughForm {k : ℕ} (φ : SmoothForm I M F k) :
    (-φ).val = -φ.val :=
  rfl

/-- Multiplication of smooth forms by a smooth real function, as a real-linear map. -/
def funSMulₗ {k : ℕ} (g : C^∞⟮I, M; ℝ⟯) : SmoothForm I M F k →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨fun x ↦ g x • φ.val x, (φ.isSmoothForm.fun_smul g.contMDiff).mem_smoothBundleForms⟩
  map_add' φ ψ := Subtype.ext <| funext fun x ↦ smul_add (g x) (φ.val x) (ψ.val x)
  map_smul' c φ := Subtype.ext <| funext fun x ↦ smul_comm (g x) c (φ.val x)

/-- The rough form underlying the product of a smooth form with a smooth function is the
pointwise product. -/
@[simp]
theorem coe_funSMulₗ {k : ℕ} (g : C^∞⟮I, M; ℝ⟯) (φ : SmoothForm I M F k) :
    (funSMulₗ g φ : RoughForm I M F k) = fun x ↦ g x • φ.val x :=
  (rfl)

/-- A smooth form whose degree exceeds the dimension of the model space vanishes. -/
theorem eq_zero_of_finrank_lt [FiniteDimensional ℝ E] (h : Module.finrank ℝ E < k)
    (φ : SmoothForm I M F k) : φ = 0 :=
  Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.eq_zero_of_finrank_lt (φ.val x)
    (by rwa [Fintype.card_fin])

/-- The constant smooth form whose value is the alternating map `A` in model-space coordinates. -/
def const {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) :
    SmoothForm (modelWithCornersSelf ℝ V) V F k := by
  let A' : ∀ x : V, TangentSpace (modelWithCornersSelf ℝ V) x [⋀^Fin k]→L[ℝ] F :=
    fun x ↦ A.compContinuousLinearMap (NormedSpace.fromTangentSpace x).toContinuousLinearMap
  exact ⟨A', by
    apply (mem_smoothBundleForms (I := modelWithCornersSelf ℝ V) (M := V)
      (F := F) (k := k) (φ := A')).2
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
    (const A).val = (fun y : V => A.compContinuousLinearMap
      (NormedSpace.fromTangentSpace y).toContinuousLinearMap) := by
  rfl

/-- Evaluating a constant smooth form transports its arguments back to the model space. -/
@[simp]
theorem const_apply {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (A : V [⋀^Fin k]→L[ℝ] F) (x : V)
    (v : Fin k → TangentSpace (modelWithCornersSelf ℝ V) x) :
    (const A).val x v = A (fun i ↦ NormedSpace.fromTangentSpace x (v i)) := by
  rw [const_toRoughForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rfl

/-- The coordinate one-form `dz` of the real line. -/
def realLineCoordForm : SmoothForm 𝓘(ℝ) ℝ ℝ 1 :=
  const (ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ 0 (ContinuousLinearMap.id ℝ ℝ))

/-- The coordinate one-form `dz` of the real line sends a tangent vector to itself. -/
@[simp]
theorem realLineCoordForm_apply (z : ℝ) (v : Fin 1 → TangentSpace 𝓘(ℝ) z) :
    realLineCoordForm.val z v = v 0 := by
  rw [realLineCoordForm, const_apply]
  -- Tangent vectors of `ℝ` are real numbers, on which `NormedSpace.fromTangentSpace` is the
  -- identity.
  rfl

section Evaluation

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- Evaluating a smooth degree-two form on two `C^n` tangent fields along a `C^n` map is `C^n`.

This is the trivial-bundle specialization of `SmoothBundleForm.contMDiff_eval₂`. -/
lemma contMDiff_apply {n : WithTop ℕ∞} [ENat.LEInfty n]
    (form : SmoothForm I M F 2)
    {b : N → M}
    {V W : ∀ y : N, TangentSpace I (b y)}
    (hV : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (V y)))
    (hW : ContMDiff I' I.tangent n (fun y ↦ TotalSpace.mk' E (b y) (W y))) :
    ContMDiff I' 𝓘(ℝ, F) n (fun y ↦ form.eval₂ (b y) (V y) (W y)) := by
  have h := SmoothBundleForm.contMDiff_eval₂ form hV hW
  intro y₀
  have hy := h y₀
  have hy' := (Bundle.contMDiffAt_totalSpace_iff (IM := I') (IB := I) (n := n)).mp hy
  simpa [Bundle.Trivial.eq_trivialization, SmoothBundleForm.eval₂] using hy'.2

end Evaluation

/-- Evaluating a degree-two form at two equal points agrees after identifying their tangent spaces
by `tangentSpaceCast`. -/
theorem eval₂_tangentSpaceCast (φ : SmoothForm I M F 2) {x y : M} (h : x = y)
    (v w : TangentSpace I x) :
    φ.eval₂ y (tangentSpaceCast I x y v) (tangentSpaceCast I x y w) = φ.eval₂ x v w := by
  subst h
  -- `tangentSpaceCast I x x` is the identity of the model fibre.
  rfl

/-- The algebraic bilinear form represented by the value of a real degree-two smooth form.

This generalizes `SmoothTwoForm.bilinFormAt` from
`TauCeti.Geometry.Manifold.TwoForm.Basic`.  The view interoperates with APIs phrased in terms of
`LinearMap.BilinForm`, including the symplectic constructions. -/
def bilinFormAt (φ : SmoothForm I M ℝ 2) (x : M) :
    LinearMap.BilinForm ℝ (TangentSpace I x) :=
  MultilinearMap.toBilinMap (φ.val x).toMultilinearMap

@[simp]
theorem bilinFormAt_apply (φ : SmoothForm I M ℝ 2) (x : M) (v w : TangentSpace I x) :
    φ.bilinFormAt x v w = φ.eval₂ x v w :=
  by simp [bilinFormAt, SmoothBundleForm.eval₂]

/-- The bilinear form represented by a degree-two smooth form is alternating. -/
theorem isAlt_bilinFormAt (φ : SmoothForm I M ℝ 2) (x : M) :
    (φ.bilinFormAt x).IsAlt := by
  apply MultilinearMap.isAlt_toBilinMap
  intro v
  exact (φ.val x).map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

/-- The bilinear form represented by a degree-two smooth form at a point vanishes exactly when the
form vanishes there. -/
@[simp]
theorem bilinFormAt_eq_zero_iff (φ : SmoothForm I M ℝ 2) (x : M) :
    φ.bilinFormAt x = 0 ↔ φ.val x = 0 := by
  refine ⟨fun h => ContinuousAlternatingMap.ext fun v => ?_, fun h => ?_⟩
  · have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
    rw [hv]
    simpa using LinearMap.congr_fun₂ h (v 0) (v 1)
  · ext v w
    simp [h]

/-- A tangent vector lies in the kernel of the bilinear form of a degree-two smooth form exactly
when the form vanishes on every pair with that vector as its first argument. -/
theorem mem_ker_bilinFormAt_iff {φ : SmoothForm I M ℝ 2} {x : M} {v : TangentSpace I x} :
    v ∈ LinearMap.ker (φ.bilinFormAt x) ↔ ∀ w, φ.val x ![v, w] = 0 := by
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, bilinFormAt_apply,
    SmoothBundleForm.eval₂_apply, LinearMap.zero_apply]

section SectionView

variable {k : ℕ}

/-- The value of a smooth form as a continuous alternating map on the model fibre. -/
def altAt (φ : SmoothForm I M F k) (x : M) : E [⋀^Fin k]→L[ℝ] F := φ.val x

@[simp]
theorem altAt_apply (φ : SmoothForm I M F k) (x : M) (v : Fin k → E) :
    φ.altAt x v = φ.val x v :=
  by
    simp only [altAt]
    rfl

/-- The degree-two alternating-map view evaluated on a tuple agrees with ordered-pair evaluation. -/
theorem altAt_apply_eval₂ (φ : SmoothForm I M F 2) (x : M) (v : Fin 2 → E) :
    φ.altAt x v = φ.eval₂ x (v 0) (v 1) := by
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv]
  simp only [altAt, SmoothBundleForm.eval₂]
  rfl

/-- Every tangent space is the model space, so a degree-two form can be evaluated on the same pair
of vectors at two base points; the values agree when the base points are equal. -/
theorem eval₂_congr_basePoint (φ : SmoothForm I M F 2) {x y : M} (h : x = y) (v w : E) :
    φ.eval₂ x v w = φ.eval₂ y v w := by
  subst h
  rfl

end SectionView

end SmoothForm

end FixedCoefficients

end TauCeti

end
