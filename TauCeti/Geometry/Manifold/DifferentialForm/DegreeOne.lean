/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Degree-one forms as sections of the bundle of fibrewise linear maps

A degree-one form with values in a vector bundle `V` assigns to each point an alternating map of
one tangent vector. Mathlib's `ContinuousAlternatingMap.ofSubsingleton` identifies these with
continuous linear maps `TangentSpace I x →L[ℝ] V x`, which are the fibres of the smooth bundle of
fibrewise linear maps. This file shows that the identification preserves regularity, and packages
it as a linear equivalence between smooth `V`-valued one-forms and smooth sections of that bundle.

For the trivial bundle `V = Bundle.Trivial M ℝ` the bundle of fibrewise linear maps is the
cotangent bundle `TauCeti.CotangentBundle I M`, so smooth real one-forms are exactly smooth
sections of the cotangent bundle. This is the comparison used to treat a covector field, such as
the tautological one-form of a cotangent bundle, as a differential form to which the exterior
derivative applies.

## Main declarations

* `TauCeti.mdifferentiableAt_ofSubsingleton_iff`: a family of linear maps is differentiable
  at a point as a section of the linear-map bundle exactly when its degree-one form is.
* `TauCeti.contMDiffAt_ofSubsingleton_iff`, `TauCeti.isSmoothBundleForm_ofSubsingleton_iff`: a
  family of linear maps has `C^n` graph in the linear-map bundle, at a point or everywhere, exactly
  when the corresponding degree-one form does. More generally, a family of linear maps along a map
  `b : N → M` is `C^n` exactly when its family of degree-one forms is
  (`TauCeti.contMDiffAt_sectionAlong_ofSubsingleton_iff`).
* `TauCeti.SmoothBundleForm.degreeOneEquiv`: the linear equivalence between smooth degree-one
  forms and smooth sections of the bundle of fibrewise linear maps.
* `TauCeti.SmoothBundleForm.tangentIdentity`: the tangent-valued one-form sending a tangent
  vector to itself.
* `TauCeti.isSmoothForm_ofSubsingleton_iff`, `TauCeti.SmoothForm.degreeOneEquiv`: the same
  statements for fixed-coefficient forms. For `F = ℝ` the bundle of fibrewise linear maps is
  `TauCeti.CotangentBundle I M`, so these identify smooth real one-forms with smooth sections of
  the cotangent bundle.
* `TauCeti.SmoothForm.contMDiffAt_apply_vectorField`,
  `TauCeti.SmoothForm.contMDiff_apply_vectorField`: a smooth real one-form evaluated on a vector
  field that is `C^n` at a point (resp. everywhere) is `C^n` there.
* `TauCeti.SmoothForm.degreeOneEquiv_mpullback_apply`,
  `TauCeti.SmoothForm.degreeOneEquiv_mpullback`: the section of a pulled-back one-form evaluates a
  tangent vector through the differential of the map, so it is the original section composed with
  the differential.
* `TauCeti.isLocalFrameOn_degreeOneEquiv_iff`: real one-forms are a frame of the cotangent bundle
  on a set exactly when their values are a basis of every cotangent space over it.
* `TauCeti.SmoothForm.degreeOneEquiv_mextDerivₗ`: the section of the exterior derivative `df` of a
  smooth function is its manifold derivative.
* `ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv_uncurry`,
  `ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry`: the differentials of a family of functions
  which is jointly `C^(n+1)` at a point (resp. everywhere) are jointly `C^n` there.
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

section OnceDifferentiable

variable [IsManifold I 1 M]

/-- A bundle-valued one-form is differentiable exactly when the corresponding section
of the bundle of continuous linear maps is differentiable. -/
theorem mdifferentiableAt_ofSubsingleton_iff
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} {x₀ : M} :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) (fun x ↦
        TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) x
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1) (α x)))
        x₀ ↔
      MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] F))
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x)) x₀ := by
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (ι := Fin 1) 0).toContinuousLinearEquiv
  rw [mdifferentiableAt_totalSpace, mdifferentiableAt_hom_bundle]
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.inCoordinates_ofSubsingleton]
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun h ↦ L.mdifferentiableAt.comp x₀ h⟩
  exact (L.symm.mdifferentiableAt.comp x₀ h).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ by simp [L])

/-- A family of fibrewise linear maps along a map `b : N → M` is `C^n` at `m₀` as a section of the
bundle of linear maps `TangentSpace I x →L[ℝ] V x` along `b` exactly when the family of degree-one
forms it defines is `C^n` at `m₀` along `b`. -/
theorem contMDiffAt_sectionAlong_ofSubsingleton_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M}
    {α : (m : N) → TangentSpace I (b m) →L[ℝ] V (b m)} {m₀ : N} :
    ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) n (fun m ↦
        TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] V x) (b m)
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I (b m)) (V (b m)) (0 : Fin 1)
            (α m))) m₀ ↔
      ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun m ↦ TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] V x) (b m) (α m)) m₀ := by
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (ι := Fin 1) 0).toContinuousLinearEquiv
  rw [contMDiffAt_continuousAlternatingMap_bundle, contMDiffAt_hom_bundle]
  refine and_congr Iff.rfl ?_
  simp only [ContinuousAlternatingMap.inCoordinates_ofSubsingleton]
  refine ⟨fun h ↦ ?_, fun h ↦ L.contDiff.comp_contMDiffAt h⟩
  exact (L.symm.contDiff.comp_contMDiffAt h).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x ↦ by simp [L])

/-- A family of fibrewise linear maps is `C^n` at `x₀` as a section of the bundle of linear maps
`TangentSpace I x →L[ℝ] V x` exactly when the degree-one form it defines is `C^n` at `x₀`. -/
theorem contMDiffAt_ofSubsingleton_iff {n : WithTop ℕ∞}
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} {x₀ : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) n (fun x ↦
        TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) x
          (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1) (α x)))
        x₀ ↔
      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x))
        x₀ :=
  contMDiffAt_sectionAlong_ofSubsingleton_iff (b := id)

/-- A family of fibrewise linear maps is a `C^n` section of the bundle of linear maps
`TangentSpace I x →L[ℝ] V x` exactly when the degree-one form it defines is `C^n`. -/
theorem isSmoothBundleForm_ofSubsingleton_iff {n : WithTop ℕ∞}
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} :
    IsSmoothBundleForm I F V n (fun x ↦
        ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1) (α x)) ↔
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x)) := by
  rw [isSmoothBundleForm_def]
  exact forall_congr' fun _ ↦ contMDiffAt_ofSubsingleton_iff

namespace SmoothBundleForm

/-- Smooth `V`-valued degree-one forms are smooth sections of the bundle of fibrewise linear maps
`TangentSpace I x →L[ℝ] V x`, through `ContinuousAlternatingMap.ofSubsingleton` on each fibre. -/
def degreeOneEquiv :
    SmoothBundleForm I F V 1 ≃ₗ[ℝ]
      ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] V x) where
  toFun φ :=
    ⟨fun x ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) 0).symm (φ.val x),
      isSmoothBundleForm_ofSubsingleton_iff.mp (by simpa using mem_smoothBundleForms.mp φ.property)⟩
  invFun s :=
    ⟨fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) 0 (s x),
      mem_smoothBundleForms.mpr (isSmoothBundleForm_ofSubsingleton_iff.mpr s.contMDiff)⟩
  map_add' φ ψ := by
    ext x v
    simp
  map_smul' c φ := by
    ext x v
    simp
  left_inv φ := by
    apply Subtype.ext
    ext x v
    simp
  right_inv s := by
    ext x v
    simp

/-- The section of a smooth degree-one form evaluates a tangent vector as the form does. -/
@[simp]
theorem degreeOneEquiv_apply_apply (φ : SmoothBundleForm I F V 1) (x : M)
    (v : TangentSpace I x) :
    degreeOneEquiv φ x v = φ.val x (fun _ ↦ v) :=
  (rfl)

/-- The degree-one form of a smooth section evaluates a single tangent vector as the section
does. -/
@[simp]
theorem degreeOneEquiv_symm_apply_apply
    (s : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] V x)) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (degreeOneEquiv.symm s).val x v = s x (v 0) :=
  (rfl)

/-- The canonical tangent-valued one-form: the identity on every tangent fibre. -/
def tangentIdentity : SmoothBundleForm I E (TangentSpace I : M → Type _) 1 :=
  degreeOneEquiv.symm ⟨fun x ↦ ContinuousLinearMap.id ℝ (TangentSpace I x), by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)
      (n := ∞)).congr_of_eventuallyEq ?_⟩
    let e := FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x
    filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E
      (TangentSpace I : M → Type _) x)] with y hy
    ext v
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    exact e.continuousLinearMapAt_symmL hy v⟩

/-- The tangent identity one-form evaluates to its sole tangent-vector argument. -/
@[simp]
theorem tangentIdentity_apply (x : M) (v : Fin 1 → TangentSpace I x) :
    (tangentIdentity (I := I)).val x v = v 0 := by
  simp only [tangentIdentity, degreeOneEquiv_symm_apply_apply]
  rfl

end SmoothBundleForm

/-- A family of linear functionals `TangentSpace I x →L[ℝ] F` is a `C^n` section of the bundle of
linear maps exactly when the fixed-coefficient degree-one form it defines is `C^n`. For `F = ℝ`
the total space of this bundle is `TauCeti.CotangentBundle I M`. -/
theorem isSmoothForm_ofSubsingleton_iff {n : WithTop ℕ∞}
    {α : (x : M) → TangentSpace I x →L[ℝ] F} :
    IsSmoothForm I n (fun x ↦
        ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) F (0 : Fin 1) (α x)) ↔
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) x (α x)) := by
  rw [isSmoothForm_def, ← isSmoothBundleForm_def]
  exact isSmoothBundleForm_ofSubsingleton_iff

end OnceDifferentiable

section OnceDifferentiable

variable [IsManifold I 1 M]

/-- **The differential of a family which is jointly `C^(n+1)` at a point is jointly `C^n` there.**
For a family of functions `f : N → M → F` which is jointly `C^(n+1)` at `q ∈ N × M`, the
differentials `(p, x) ↦ d(f p)_x` form a map into the bundle of linear maps
`TangentSpace I x →L[ℝ] F`, lying over the projection `N × M → M`, which is `C^n` at `q`. -/
theorem _root_.ContMDiffAt.contMDiffAt_totalSpaceMk_mvfderiv_uncurry {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    {n : WithTop ℕ∞} {f : N → M → F} {q : N × M}
    (hf : ContMDiffAt (J.prod I) 𝓘(ℝ, F) (n + 1) (Function.uncurry f) q) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun q : N × M ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) q.2 (mvfderiv I (f q.1) q.2)) q := by
  have hf' : ContMDiffAt ((J.prod I).prod I) 𝓘(ℝ, F) (n + 1) (fun p : (N × M) × M ↦ f p.1.1 p.2)
      (q, q.2) :=
    hf.comp (q, q.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have hd := ContMDiffAt.mfderiv (fun p : N × M ↦ f p.1) Prod.snd hf' contMDiffAt_snd le_rfl
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)⟩
  -- In the trivial bundle and in the tangent bundle of the model space `F`, the coordinate
  -- changes are the identity, and `mvfderiv` is `mfderiv` read in `F`.
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    inTangentCoordinates, TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- **The differential of a jointly `C^(n+1)` family is jointly `C^n`.** For a family of functions
`f : N → M → F` which is jointly `C^(n+1)` on `N × M`, the differentials `(p, x) ↦ d(f p)_x` form a
`C^n` map into the bundle of linear maps `TangentSpace I x →L[ℝ] F`, lying over the projection
`N × M → M`. For `N = ℝ` this is the regularity in time and space of the differential of a
time-dependent function. -/
theorem _root_.ContMDiff.contMDiff_totalSpaceMk_mvfderiv_uncurry {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    {n : WithTop ℕ∞} {f : N → M → F}
    (hf : ContMDiff (J.prod I) 𝓘(ℝ, F) (n + 1) (Function.uncurry f)) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun q : N × M ↦ TotalSpace.mk' (E →L[ℝ] F)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) q.2 (mvfderiv I (f q.1) q.2)) :=
  fun q ↦ (hf q).contMDiffAt_totalSpaceMk_mvfderiv_uncurry

namespace SmoothForm

/-- Smooth `F`-valued one-forms are smooth sections of the bundle of linear maps
`TangentSpace I x →L[ℝ] F`, through `ContinuousAlternatingMap.ofSubsingleton` on each fibre. For
`F = ℝ` these are the smooth sections of `TauCeti.CotangentBundle I M`. This is
`SmoothBundleForm.degreeOneEquiv` for the trivial bundle `Bundle.Trivial M F`. -/
def degreeOneEquiv :
    SmoothForm I M F 1 ≃ₗ[ℝ]
      ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F) :=
  SmoothBundleForm.degreeOneEquiv (V := Bundle.Trivial M F)

/-- The section of a smooth one-form evaluates a tangent vector as the form does. -/
theorem degreeOneEquiv_apply_apply (φ : SmoothForm I M F 1) (x : M) (v : TangentSpace I x) :
    degreeOneEquiv φ x v = φ.val x (fun _ ↦ v) :=
  (rfl)

/-- The section of a smooth one-form evaluates a tangent vector `v` as the form evaluates the
one-element family `![v]`. -/
@[simp]
theorem degreeOneEquiv_apply_apply_vec (φ : SmoothForm I M F 1) (x : M) (v : TangentSpace I x) :
    degreeOneEquiv φ x v = φ.val x ![v] := by
  rw [degreeOneEquiv_apply_apply, Matrix.vec_single_eq_const]

/-- **A smooth real one-form evaluated on a vector field that is `C^n` at `x` is `C^n` at `x`**,
for `n ≤ ∞`. -/
theorem contMDiffAt_apply_vectorField {n : WithTop ℕ∞} [ENat.LEInfty n] (φ : SmoothForm I M ℝ 1)
    {V : Π x : M, TangentSpace I x} {x : M} (hV : ContMDiffAt I I.tangent n (T% V) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ φ.val y ![V y]) x := by
  have hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) y (degreeOneEquiv φ y)) x :=
    ((degreeOneEquiv φ).contMDiff x).of_le ENat.LEInfty.out
  simpa using hφ.clm_bundle_apply_scalar hV

/-- **A smooth real one-form evaluated on a `C^n` vector field is a `C^n` function**, for
`n ≤ ∞`. -/
theorem contMDiff_apply_vectorField {n : WithTop ℕ∞} [ENat.LEInfty n] (φ : SmoothForm I M ℝ 1)
    {V : Π x : M, TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V)) :
    ContMDiff I 𝓘(ℝ) n fun x ↦ φ.val x ![V x] := fun x ↦
  φ.contMDiffAt_apply_vectorField (hV x)

/-- A family of smooth one-forms `α m`, evaluated along a map `b : N → M`, is `C^n` at `m₀` as a
section of the bundle of linear maps exactly when it is `C^n` as a section of the bundle of
alternating maps. -/
theorem contMDiffAt_sectionAlong_degreeOneEquiv_iff {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] {n : WithTop ℕ∞} {b : N → M} {α : N → SmoothForm I M F 1} {m₀ : N} :
    ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] F)) n (fun m ↦ TotalSpace.mk' (E →L[ℝ] F)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] F) (b m) (degreeOneEquiv (α m) (b m))) m₀ ↔
      ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] F)) n (fun m ↦
        TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M F x) (b m)
          ((α m).val (b m))) m₀ := by
  rw [← contMDiffAt_sectionAlong_ofSubsingleton_iff (V := Trivial M F)]
  refine Iff.of_eq (congrArg (ContMDiffAt _ _ _ · m₀) (funext fun m ↦ ?_))
  refine congrArg (TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] F) (b m)) ?_
  ext u
  have hu : u = ![u 0] := by
    ext i
    fin_cases i
    rfl
  conv_rhs => rw [hu]
  simp

/-- A smooth one-form sends the one-element family `![-v]` to minus its value on `![v]`. -/
@[simp]
theorem apply_neg_vec (φ : SmoothForm I M F 1) (x : M) (v : TangentSpace I x) :
    φ.val x ![-v] = -φ.val x ![v] := by
  rw [← degreeOneEquiv_apply_apply_vec, map_neg, degreeOneEquiv_apply_apply_vec]

/-- The section of a smooth one-form, read as a linear map, evaluates a tangent vector `v` as the
form evaluates the one-element family `![v]`. -/
theorem degreeOneEquiv_coe_apply (φ : SmoothForm I M F 1) (x : M) (v : TangentSpace I x) :
    (degreeOneEquiv φ x : TangentSpace I x →ₗ[ℝ] F) v = φ.val x ![v] := by
  rw [ContinuousLinearMap.coe_coe, degreeOneEquiv_apply_apply_vec]

/-- The section of a smooth one-form, read as a linear map, vanishes at `x` exactly when the form
vanishes at `x`. -/
theorem degreeOneEquiv_coe_eq_zero_iff {φ : SmoothForm I M F 1} {x : M} :
    (degreeOneEquiv φ x : TangentSpace I x →ₗ[ℝ] F) = 0 ↔ φ.val x = 0 := by
  refine ⟨fun h ↦ ContinuousAlternatingMap.ext fun v ↦ ?_, fun h ↦ LinearMap.ext fun v ↦ ?_⟩
  · have hv : ![v 0] = v := by
      ext i
      fin_cases i
      rfl
    rw [← hv, ← degreeOneEquiv_coe_apply, h, LinearMap.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  · rw [degreeOneEquiv_coe_apply, h, LinearMap.zero_apply,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- The section of a smooth one-form is nonzero at `x` when the form does not vanish at `x`. -/
theorem degreeOneEquiv_ne_zero {φ : SmoothForm I M F 1} {x : M} (h : φ.val x ≠ 0) :
    degreeOneEquiv φ x ≠ 0 := fun h' ↦
  h (degreeOneEquiv_coe_eq_zero_iff.1 (congrArg ContinuousLinearMap.toLinearMap h'))

/-- If `ψ = c φ` at `x`, the sections of `ψ` and `φ` at `x` differ by the factor `c`. -/
theorem degreeOneEquiv_eq_smul {φ ψ : SmoothForm I M F 1} {x : M} {c : ℝ}
    (h : ψ.val x = c • φ.val x) : degreeOneEquiv ψ x = c • degreeOneEquiv φ x :=
  ContinuousLinearMap.ext fun v ↦ by simp [h]

/-- The sections of `ψ` and `φ` at `x` differ by the factor `c` exactly when `ψ = c φ` at `x`. -/
theorem degreeOneEquiv_eq_smul_iff {φ ψ : SmoothForm I M F 1} {x : M} {c : ℝ} :
    degreeOneEquiv ψ x = c • degreeOneEquiv φ x ↔ ψ.val x = c • φ.val x := by
  refine ⟨fun h ↦ ContinuousAlternatingMap.ext fun v ↦ ?_, degreeOneEquiv_eq_smul⟩
  have hv : v = fun _ ↦ v 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hv, ContinuousAlternatingMap.smul_apply, ← degreeOneEquiv_apply_apply,
    ← degreeOneEquiv_apply_apply, h, _root_.smul_apply]

/-- The linear functional `RoughForm.eval` of a smooth real one-form at `x` is its section, read as
a linear map. -/
theorem eval_val (φ : SmoothForm I M ℝ 1) (x : M) :
    RoughForm.eval φ.val x = (degreeOneEquiv φ x : TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.ext fun v ↦ by rw [RoughForm.eval_apply, degreeOneEquiv_coe_apply]

/-- The one-form of a smooth section evaluates a single tangent vector as the section does. -/
@[simp]
theorem degreeOneEquiv_symm_apply_apply
    (s : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (degreeOneEquiv.symm s).val x v = s x (v 0) :=
  (rfl)

/-- The section of the pullback of a smooth one-form `φ` along `f` evaluates a tangent vector `v`
at `x` as the section of `φ` evaluates `df_x v` at `f x`. -/
theorem degreeOneEquiv_mpullback_apply {E' H' M' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' 1 M'] {f : M → M'} (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' F 1) (x : M) (v : TangentSpace I x) :
    degreeOneEquiv (mpullback f hf φ) x v = degreeOneEquiv φ (f x) (mfderiv I I' f x v) :=
  mpullback_apply f hf φ x _

/-- The section of the pullback of a smooth one-form `φ` along `f` at `x` is the section of `φ` at
`f x` composed with the differential `df_x`. -/
theorem degreeOneEquiv_mpullback {E' H' M' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' 1 M'] {f : M → M'} (hf : ContMDiff I I' ∞ f)
    (φ : SmoothForm I' M' F 1) (x : M) :
    degreeOneEquiv (mpullback f hf φ) x = degreeOneEquiv φ (f x) ∘L mfderiv I I' f x :=
  ContinuousLinearMap.ext (degreeOneEquiv_mpullback_apply hf φ x)

end SmoothForm

end OnceDifferentiable

section Coframe

variable [IsManifold I 1 M] {ι : Type*}

/-- Real one-forms form a frame of the cotangent bundle on a set `U` exactly when their values form
a basis of every cotangent space over `U`: smoothness of the frame is automatic. -/
theorem isLocalFrameOn_degreeOneEquiv_iff {α : ι → SmoothForm I M ℝ 1} {U : Set M} :
    IsLocalFrameOn I (E →L[ℝ] ℝ) ∞ (fun i ↦ ⇑(SmoothForm.degreeOneEquiv (α i))) U ↔
      ∀ x ∈ U, LinearIndependent ℝ (fun i ↦ SmoothForm.degreeOneEquiv (α i) x) ∧
        ⊤ ≤ Submodule.span ℝ (Set.range fun i ↦ SmoothForm.degreeOneEquiv (α i) x) :=
  ⟨fun h _ hx ↦ ⟨h.linearIndependent hx, h.generating hx⟩, fun h ↦
    { linearIndependent := fun hx ↦ (h _ hx).1
      generating := fun hx ↦ (h _ hx).2
      contMDiffOn := fun i ↦ (SmoothForm.degreeOneEquiv (α i)).contMDiff.contMDiffOn }⟩

end Coframe

namespace SmoothForm

variable [IsManifold I 2 M]

/-- The section of the exterior derivative `df` of a smooth function is its differential: at each
point it is the manifold derivative of the function. -/
@[simp]
theorem degreeOneEquiv_mextDerivₗ (f : SmoothForm I M F 0) (x : M) :
    degreeOneEquiv (mextDerivₗ I 0 f) x = mvfderiv I (fun y ↦ f.val y 0) x := by
  ext v
  rw [degreeOneEquiv_apply_apply_vec, mextDerivₗ_zero_apply]

end SmoothForm

end TauCeti
