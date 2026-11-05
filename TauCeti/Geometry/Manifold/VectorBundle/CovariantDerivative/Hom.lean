/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The induced connection on a Hom bundle

Connections on `V` and `W` induce a connection on the native bundle `Hom(V, W)`.
Its evaluation rule is `((∇ A)(X)) s = ∇_X (A s) - A (∇_X s)`.
This rule uniquely determines the induced connection on differentiable sections,
and makes the identity endomorphism parallel. Iterating this construction supplies
the connections on covariant tensors needed to differentiate curvature.

The source bundle has finite rank; the target bundle need not. The construction
uses Mathlib's tensoriality criterion, rather than a choice of bundle frame.
At a point where `A` is not differentiable the operator is defined to be zero,
since the axioms of a native covariant derivative concern differentiable inputs.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*,
second edition, Chapter 4 (induced connections on tensor bundles).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)

private def homAux (A : Π x : M, V x →L[𝕜] W x) (s : Π x : M, V x) (x : M) :
    TangentSpace I x →L[𝕜] W x :=
  covW (fun y ↦ A y (s y)) x - (A x).comp (covV s x)

omit [CompleteSpace 𝕜] [IsManifold I 1 M] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle 1 F V I] in
private theorem tensorialAt_homAux {A : Π x : M, V x →L[𝕜] W x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x) :
    TensorialAt I F (fun s ↦ homAux covV covW A s x) x where
  add {s t} hs ht := by
    have hsum : (fun y ↦ A y ((s + t) y)) =
        (fun y ↦ A y (s y)) + fun y ↦ A y (t y) := by ext y; simp
    simp only [homAux, hsum, covW.isCovariantDerivativeOnUniv.add
      (hA.clm_bundle_apply hs) (hA.clm_bundle_apply ht),
      covV.isCovariantDerivativeOnUniv.add hs ht]
    ext v
    simp
    abel
  smul {f s} hf hs := by
    have hsmul : (fun y ↦ A y ((f • s) y)) = f • fun y ↦ A y (s y) := by
      ext y; simp
    simp only [homAux, hsmul, covW.isCovariantDerivativeOnUniv.leibniz
      (hA.clm_bundle_apply hs) hf, covV.isCovariantDerivativeOnUniv.leibniz hs hf]
    ext v
    simp
    module

open scoped Classical in
private def homValue (A : Π x : M, V x →L[𝕜] W x) (x : M) :
    TangentSpace I x →L[𝕜] V x →L[𝕜] W x :=
  letI := (VectorBundle.continuousLinearEquivAt 𝕜 F V x).isNormableSpace
  letI := (VectorBundle.continuousLinearEquivAt 𝕜 G W x).isNormableSpace
  letI := (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I) x).isNormableSpace
  if hA : MDiffAt
    (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x then
    (TensorialAt.mkHom (fun s ↦ homAux covV covW A s x) x
      (tensorialAt_homAux covV covW hA)).flip
  else 0

private theorem homValue_apply {A : Π x : M, V x →L[𝕜] W x} {s : Π x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (hs : MDiffAt (T% s) x) (v : TangentSpace I x) :
    homValue covV covW A x v (s x) =
      covW (fun y ↦ A y (s y)) x v - A x (covV s x v) := by
  simp only [homValue, dite_eq_left hA, ContinuousLinearMap.flip_apply,
    TensorialAt.mkHom_apply _ hs, homAux, sub_apply,
    ContinuousLinearMap.comp_apply]

/-- The connection on the native Hom bundle induced by connections on its source and target.
It is characterized on differentiable inputs by `CovariantDerivative.hom_apply`. -/
def hom : CovariantDerivative I (F →L[𝕜] G) (fun x ↦ V x →L[𝕜] W x) where
  toFun := homValue covV covW
  isCovariantDerivativeOnUniv := {
    add := by
      intro A B x hA hB _
      ext v u
      let s := extend F u
      have hs : MDiffAt (T% s) x := mdifferentiableAt_extend ..
      have hsum : (fun y ↦ (A + B) y (s y)) =
          (fun y ↦ A y (s y)) + fun y ↦ B y (s y) := by ext y; simp
      have heq : s x = u := extend_apply_self ..
      rw [← heq]
      simp only [add_apply, homValue_apply covV covW
        (mdifferentiableAt_add_section hA hB) hs, homValue_apply covV covW hA hs,
        homValue_apply covV covW hB hs, hsum,
        covW.isCovariantDerivativeOnUniv.add (hA.clm_bundle_apply hs) (hB.clm_bundle_apply hs)]
      simp
      abel
    leibniz := by
      intro A f x hA hf _
      ext v u
      let s := extend F u
      have hs : MDiffAt (T% s) x := mdifferentiableAt_extend ..
      have hsmul : (fun y ↦ (f • A) y (s y)) = f • fun y ↦ A y (s y) := by ext y; simp
      have heq : s x = u := extend_apply_self ..
      rw [← heq]
      simp only [homValue_apply covV covW (hf.smul_section hA) hs,
        add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, homValue_apply covV covW hA hs, hsmul,
        covW.isCovariantDerivativeOnUniv.leibniz (hA.clm_bundle_apply hs) hf]
      simp
      module }

/-- Evaluation of the induced Hom connection on a differentiable homomorphism and section. -/
theorem hom_apply {A : Π x : M, V x →L[𝕜] W x} {s : Π x : M, V x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (hs : MDiffAt (T% s) x) (v : TangentSpace I x) :
    covV.hom covW A x v (s x) =
      covW (fun y ↦ A y (s y)) x v - A x (covV s x v) :=
  homValue_apply covV covW hA hs v

/-- Evaluate the induced Hom connection on a fibre vector using its local extension. -/
theorem hom_apply_eq_extend {A : Π x : M, V x →L[𝕜] W x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (v : TangentSpace I x) (u : V x) :
    covV.hom covW A x v u =
      covW (fun y ↦ A y (extend F u y)) x v - A x (covV (extend F u) x v) := by
  simpa using hom_apply covV covW hA (mdifferentiableAt_extend I F u) v

/-- At a nondifferentiable Hom section the induced connection uses the zero extension. -/
@[simp] theorem hom_eq_zero_of_not_mdifferentiableAt {A : Π x : M, V x →L[𝕜] W x} {x : M}
    (hA : ¬ MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x) :
    covV.hom covW A x = 0 := by
  simp [hom, homValue, hA]

/-- The evaluation rule uniquely determines the covariant derivative of a differentiable
Hom section at a point. -/
theorem hom_eq_of_apply {A : Π x : M, V x →L[𝕜] W x} {x : M}
    (hA : MDiffAt
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] G) (E := fun z ↦ V z →L[𝕜] W z) y (A y)) x)
    (D : TangentSpace I x →L[𝕜] V x →L[𝕜] W x)
    (hD : ∀ s : Π x : M, V x, MDiffAt (T% s) x → ∀ v : TangentSpace I x,
      D v (s x) = covW (fun y ↦ A y (s y)) x v - A x (covV s x v)) :
    D = covV.hom covW A x := by
  ext v u
  simpa using (hD (extend F u) (mdifferentiableAt_extend ..) v).trans
    (hom_apply covV covW hA (mdifferentiableAt_extend I F u) v).symm

/-- The identity endomorphism is parallel for the induced endomorphism connection. -/
@[simp] theorem hom_id (x : M) :
    covV.hom covV (fun y ↦ ContinuousLinearMap.id 𝕜 (V y)) x = 0 := by
  ext v u
  by_cases hA : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[𝕜] F)
    (E := fun z ↦ V z →L[𝕜] V z) y (ContinuousLinearMap.id 𝕜 (V y))) x
  · simpa using hom_apply covV covV hA (mdifferentiableAt_extend I F u) v
  · simp [hom_eq_zero_of_not_mdifferentiableAt covV covV hA]

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W I]
  (covV : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
  [ContMDiffCovariantDerivative covV ∞] [ContMDiffCovariantDerivative covW ∞]

/-- The covariant derivative of a smooth homomorphism is a smooth section of
`Hom(TM, Hom(V, W))`. Smoothness of the original connections suffices. -/
theorem contMDiff_hom {A : Π x : M, V x →L[ℝ] W x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun y ↦ V y →L[ℝ] W y) x (A x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] G)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] W y) x
        (covV.hom covW A x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro s hs
  have hAs := hA.clm_bundle_apply hs
  have hWs := covW.contMDiff_apply hX (by simpa using hAs)
  have hVs := covV.contMDiff_apply hX (by simpa using hs)
  have hdiff := hWs.sub_section (hA.clm_bundle_apply hVs)
  apply hdiff.congr
  intro x
  exact congrArg (TotalSpace.mk' G x) (hom_apply covV covW
    (hA.mdifferentiableAt (by simp)) (hs.mdifferentiableAt (by simp)) (X x))

/-- Smooth connections induce a smooth connection on the native Hom bundle. -/
instance : ContMDiffCovariantDerivative (covV.hom covW) ∞ where
  contMDiff.contMDiff {A} hA := by
    rw [contMDiffOn_univ] at hA ⊢
    exact contMDiff_hom covV covW (by simpa using hA)

end Smooth

end CovariantDerivative
