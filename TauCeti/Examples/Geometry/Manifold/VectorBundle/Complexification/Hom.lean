/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Examples of complexification of native density-Hom bundles -/
public section
noncomputable section
open Bundle FiberBundle TauCeti Set
open scoped TensorProduct TauCeti.Complexification ContDiff Manifold Topology
namespace TauCeti.Examples.HomComplexification

/-- Literal nonzero imaginary scalar coefficient on an original native bundle fibre. -/
theorem imaginary_native_line (x : ℝ) :
    bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) x
      (Complex.I ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ)) (1 ⊗ₜ[ℝ] (1 : ℝ)) =
        Complex.I ⊗ₜ[ℝ] (1 : ℝ) := by simp

/-- The actual inverse recovers the imaginary coefficient, not its real restriction. -/
theorem imaginary_inverse (x : ℝ) :
    (bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) x).symm
      (Complex.I • (ContinuousLinearMap.id ℝ ℝ).baseChangeComplex) =
      Complex.I ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ) := by
  apply (bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ)
    x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext v
  apply complexification_ext <;> simp

/-- This test does not reduce to the zero map. -/
theorem imaginary_native_line_ne_zero (x : ℝ) :
    bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) x
      (Complex.I ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ)) (1 ⊗ₜ[ℝ] (1 : ℝ)) ≠ 0 := by
  rw [imaginary_native_line]
  intro h
  have := congrArg (imaginaryPart ℝ) h
  simp at this

/-- Literal real coefficient and value. -/
theorem real_native_line (x : ℝ) :
    bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) x
      (1 ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ)) (1 ⊗ₜ[ℝ] (1 : ℝ)) =
        1 ⊗ₜ[ℝ] (1 : ℝ) := by simp

/-- A nonconstant positive real frame on the same original real line. -/
def varyingFrame (t : ℝ) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (1 + t^2) (by positivity))

@[simp] theorem varyingFrame_apply (t v : ℝ) : varyingFrame t v = (1+t^2)*v := by
  simp [varyingFrame, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def]

/-- A genuinely nonconstant frame enters the entire commuting square, including the inverse
source frame in the induced Hom chart. -/
theorem varying_frame_square (t : ℝ) (u : ℂ ⊗[ℝ] (ℝ →L[ℝ] ℝ)) :
    ((varyingFrame t).baseChangeComplex.trans
      (tensorContinuousLinearEquivComplexification ℝ)).arrowCongr
      ((ContinuousLinearEquiv.refl ℝ ℝ).baseChangeComplex.trans
        (tensorContinuousLinearEquivComplexification ℝ))
      (bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) t u) =
    Complexification.continuousLinearMapEquiv ℝ ℝ
      ((((varyingFrame t).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).baseChangeComplex.trans
        (tensorContinuousLinearEquivComplexification (ℝ →L[ℝ] ℝ))) u) := by
  simpa only [bundleHomComplexificationEquiv_coe] using
    homComplexificationLinearEquiv_in_frames (varyingFrame t) (ContinuousLinearEquiv.refl ℝ ℝ) u

/-- The two displayed real frames differ concretely. -/
theorem varyingFrame_nonconstant : varyingFrame 0 1 ≠ varyingFrame 1 1 := by norm_num

/-- The actual inverse recovers a real coefficient as well. -/
theorem real_inverse (x : ℝ) :
    (bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ) x).symm
      (ContinuousLinearMap.id ℝ ℝ).baseChangeComplex =
      1 ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ) := by
  apply (bundleHomComplexificationEquiv (F := ℝ) (G := ℝ) (V := Trivial ℝ ℝ) (L := Trivial ℝ ℝ)
    x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext v
  apply complexification_ext <;> simp

/-- Native construction for arbitrary, possibly incomplete coefficient models. -/
theorem arbitrary_model_smooth (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ∞ω) :
    letI := VectorBundle.restrictScalars ℝ ℂ
      (Complexification F →L[ℂ] Complexification ℝ)
      (fun x : ℝ ↦ (ℂ ⊗[ℝ] Trivial ℝ F x) →L[ℂ] (ℂ ⊗[ℝ] Trivial ℝ ℝ x))
    ContMDiffVectorBundle n (Complexification F →L[ℂ] Complexification ℝ)
      (fun x : ℝ ↦ (ℂ ⊗[ℝ] Trivial ℝ F x) →L[ℂ] (ℂ ⊗[ℝ] Trivial ℝ ℝ x)) 𝓘(ℝ) := by
  exact instContMDiffVectorBundleComplexificationHom (G := ℝ) (V := Trivial ℝ F) (L := Trivial ℝ ℝ)

/-- Evaluation on an infinite-dimensional continuous-function model. -/
theorem infinite_model (x : ℝ) :
    bundleHomComplexificationEquiv (F := C(Icc (0 : ℝ) 1, ℝ)) (G := ℝ)
      (V := Trivial ℝ C(Icc (0 : ℝ) 1, ℝ)) (L := Trivial ℝ ℝ) x
      (Complex.I ⊗ₜ[ℝ]
        (ContinuousMap.evalCLM (R := ℝ) (M := ℝ) (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)))
      (1 ⊗ₜ[ℝ] (ContinuousMap.const (Icc (0 : ℝ) 1) (1 : ℝ))) =
      Complex.I ⊗ₜ[ℝ] (1 : ℝ) := by simp

/-- The nonzero infinite-dimensional evaluation client. -/
theorem infinite_model_ne_zero (x : ℝ) :
    bundleHomComplexificationEquiv (F := C(Icc (0 : ℝ) 1, ℝ)) (G := ℝ)
      (V := Trivial ℝ C(Icc (0 : ℝ) 1, ℝ)) (L := Trivial ℝ ℝ) x
      (Complex.I ⊗ₜ[ℝ]
        (ContinuousMap.evalCLM (R := ℝ) (M := ℝ) (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)))
      (1 ⊗ₜ[ℝ] (ContinuousMap.const (Icc (0 : ℝ) 1) (1 : ℝ))) ≠ 0 := by
  rw [infinite_model]
  intro h
  have := congrArg (imaginaryPart ℝ) h
  simp at this

section NativeDensity
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The density fibre has its native topological additive group. -/
local instance densityFiberAddGroup (x : M) : IsTopologicalAddGroup (DensityBundle I M x) :=
  VectorBundle.isTopologicalAddGroup ℝ ℝ (DensityBundle I M) x
/-- The density fibre has native continuous real scalar multiplication. -/
local instance densityFiberSMul (x : M) : ContinuousSMul ℝ (DensityBundle I M x) :=
  VectorBundle.continuousSMul ℝ ℝ (DensityBundle I M) x

/-- Actual tangent-to-density Hom, with the new smooth mixin on the native complex-Hom atlas. -/
theorem tangent_density_smooth :
    letI := VectorBundle.restrictScalars ℝ ℂ
      (Complexification E →L[ℂ] Complexification ℝ)
      (fun x : M ↦ (ℂ ⊗[ℝ] TangentSpace I x) →L[ℂ] (ℂ ⊗[ℝ] DensityBundle I M x))
    ContMDiffVectorBundle ∞ (Complexification E →L[ℂ] Complexification ℝ)
      (fun x : M ↦ (ℂ ⊗[ℝ] TangentSpace I x) →L[ℂ] (ℂ ⊗[ℝ] DensityBundle I M x)) I := by
  exact instContMDiffVectorBundleComplexificationHom (G := ℝ) (V := TangentSpace I) (L :=
    DensityBundle I M)

/-- The full original native tangent-density total-space diffeomorphism. -/
theorem tangent_density_diffeomorph : Nonempty
    (TotalSpace (Complexification (E →L[ℝ] ℝ))
      (fun x : M ↦ ℂ ⊗[ℝ] (TangentSpace I x →L[ℝ] DensityBundle I M x))
      ≃ₘ⟮I.prod 𝓘(ℝ, Complexification (E →L[ℝ] ℝ)),
        I.prod 𝓘(ℝ, Complexification E →L[ℂ] Complexification ℝ)⟯
      TotalSpace (Complexification E →L[ℂ] Complexification ℝ)
        (fun x : M ↦ (ℂ ⊗[ℝ] TangentSpace I x) →L[ℂ] (ℂ ⊗[ℝ] DensityBundle I M x))) :=
  ⟨bundleHomComplexificationDiffeomorph (G := ℝ)⟩

omit [FiniteDimensional ℝ E] in
/-- The arbitrary-target result includes actual tangent endomorphisms. -/
theorem tangent_endomorphism_smooth :
    letI := fun x ↦ VectorBundle.isTopologicalAddGroup ℝ E (TangentSpace I : M → Type _) x
    letI := fun x ↦ VectorBundle.continuousSMul ℝ E (TangentSpace I : M → Type _) x
    ContMDiffVectorBundle ∞ (Complexification E →L[ℂ] Complexification E)
      (fun x : M ↦ (ℂ ⊗[ℝ] TangentSpace I x) →L[ℂ] (ℂ ⊗[ℝ] TangentSpace I x)) I := by
  let : ∀ x, IsTopologicalAddGroup (TangentSpace I x) := fun x ↦
    VectorBundle.isTopologicalAddGroup ℝ E (TangentSpace I : M → Type _) x
  let : ∀ x, ContinuousSMul ℝ (TangentSpace I x) := fun x ↦
    VectorBundle.continuousSMul ℝ E (TangentSpace I : M → Type _) x
  infer_instance

end NativeDensity
/-- Zero coefficient rank, using the constructed original-fibre map. -/
theorem zero_rank_apply (x : ℝ) (u : ℂ ⊗[ℝ] ((Fin 0 → ℝ) →L[ℝ] ℝ))
    (v : ℂ ⊗[ℝ] (Fin 0 → ℝ)) :
    bundleHomComplexificationEquiv (F := Fin 0 → ℝ) (G := ℝ) (V := Trivial ℝ (Fin 0 → ℝ))
      (L := Trivial ℝ ℝ) x u v = 0 := by
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero]

/-- Empty coordinate index: the full native diffeomorphism is still constructed. -/
theorem empty_index_diffeomorph : Nonempty
    (TotalSpace (Complexification ((Empty → ℝ) →L[ℝ] ℝ))
      (fun _ : ℝ ↦ ℂ ⊗[ℝ] ((Empty → ℝ) →L[ℝ] ℝ))
      ≃ₘ⟮(𝓘(ℝ)).prod 𝓘(ℝ, Complexification ((Empty → ℝ) →L[ℝ] ℝ)),
        (𝓘(ℝ)).prod 𝓘(ℝ, Complexification (Empty → ℝ) →L[ℂ] Complexification ℝ)⟯
      TotalSpace (Complexification (Empty → ℝ) →L[ℂ] Complexification ℝ)
        (fun _ : ℝ ↦ (ℂ ⊗[ℝ] (Empty → ℝ)) →L[ℂ] (ℂ ⊗[ℝ] ℝ))) :=
  ⟨bundleHomComplexificationDiffeomorph (G := ℝ) (V := Trivial ℝ (Empty → ℝ)) (L := Trivial ℝ ℝ)⟩

/-- The native empty manifold charts, with no chosen base point. -/
local instance emptyBaseCharts : ChartedSpace ℝ Empty := ChartedSpace.empty ℝ Empty

/-- Empty base: the actual native total-space construction requires no chosen point. -/
theorem empty_base_diffeomorph : Nonempty
    (TotalSpace (Complexification (ℝ →L[ℝ] ℝ))
      (fun _ : Empty ↦ ℂ ⊗[ℝ] (ℝ →L[ℝ] ℝ))
      ≃ₘ⟮(𝓘(ℝ)).prod 𝓘(ℝ, Complexification (ℝ →L[ℝ] ℝ)),
        (𝓘(ℝ)).prod 𝓘(ℝ, Complexification ℝ →L[ℂ] Complexification ℝ)⟯
      TotalSpace (Complexification ℝ →L[ℂ] Complexification ℝ)
        (fun _ : Empty ↦ (ℂ ⊗[ℝ] ℝ) →L[ℂ] (ℂ ⊗[ℝ] ℝ))) :=
  ⟨bundleHomComplexificationDiffeomorph (G := ℝ) (V := Trivial Empty ℝ) (L := Trivial Empty ℝ)⟩

/-- Disconnected base: the original coefficient is recovered on each component. -/
theorem disconnected_roundtrip (x : ℝ ⊕ ℝ) (u : ℂ ⊗[ℝ] (ℝ →L[ℝ] ℝ)) :
    (bundleHomComplexificationDiffeomorph (F := ℝ) (G := ℝ) (IB := 𝓘(ℝ)) (n := ∞)
      (V := Trivial (ℝ ⊕ ℝ) ℝ) (L := Trivial (ℝ ⊕ ℝ) ℝ)).symm
      ((bundleHomComplexificationDiffeomorph (F := ℝ) (G := ℝ) (IB := 𝓘(ℝ)) (n := ∞)
        (V := Trivial (ℝ ⊕ ℝ) ℝ) (L := Trivial (ℝ ⊕ ℝ) ℝ)) ⟨x, u⟩) = ⟨x, u⟩ :=
  Diffeomorph.symm_apply_apply _ _

/-- Native topological addition on the actual zero-dimensional density fibre. -/
local instance zeroDimDensityFiberAddGroup (x : Fin 0 → ℝ) :
    IsTopologicalAddGroup (DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) x) :=
  VectorBundle.isTopologicalAddGroup ℝ ℝ
    (DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ)) x
/-- Native scalar continuity on the actual zero-dimensional density fibre. -/
local instance zeroDimDensityFiberSMul (x : Fin 0 → ℝ) :
    ContinuousSMul ℝ (DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) x) :=
  VectorBundle.continuousSMul ℝ ℝ
    (DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ)) x

/-- The density fibre is nonzero even when the base has dimension zero. -/
theorem zero_dim_density_nonzero (x : Fin 0 → ℝ) :
    ∃ d : DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) x, d ≠ 0 := by
  let L := DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ)
  let e := (trivializationAt ℝ L x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt ℝ L x)
  exact ⟨e.symm 1, by simp⟩

/-- Dimension-zero base with its actual tangent-density coefficient and native atlas. -/
theorem zero_dim_tangent_density_diffeomorph : Nonempty
    (TotalSpace (Complexification ((Fin 0 → ℝ) →L[ℝ] ℝ))
      (fun x : Fin 0 → ℝ ↦ ℂ ⊗[ℝ]
        (TangentSpace 𝓘(ℝ, Fin 0 → ℝ) x →L[ℝ]
          DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) x))
      ≃ₘ⟮(𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Complexification ((Fin 0 → ℝ) →L[ℝ] ℝ)),
        (𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Complexification (Fin 0 → ℝ) →L[ℂ] Complexification ℝ)⟯
      TotalSpace (Complexification (Fin 0 → ℝ) →L[ℂ] Complexification ℝ)
        (fun x : Fin 0 → ℝ ↦ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, Fin 0 → ℝ) x) →L[ℂ]
          (ℂ ⊗[ℝ] DensityBundle 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) x))) :=
  ⟨bundleHomComplexificationDiffeomorph (G := ℝ)⟩

section ArbitraryTarget
variable (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Arbitrary source and target models give the actual smooth native Hom atlas. -/
theorem arbitrary_target_smooth (n : ℕ∞ω) :
    ContMDiffVectorBundle n (Complexification F →L[ℂ] Complexification G)
      (fun x : ℝ ↦ (ℂ ⊗[ℝ] Trivial ℝ F x) →L[ℂ] (ℂ ⊗[ℝ] Trivial ℝ G x)) 𝓘(ℝ) :=
  inferInstance

/-- The real and imaginary coefficients of arbitrary target rank survive inverse recovery. -/
theorem arbitrary_target_inverse (x : ℝ) (T S : F →L[ℝ] G) :
    (bundleHomComplexificationEquiv (F := F) (G := G)
      (V := Trivial ℝ F) (L := Trivial ℝ G) x).symm
      (T.baseChangeComplex + Complex.I • S.baseChangeComplex) =
        1 ⊗ₜ[ℝ] T + Complex.I ⊗ₜ[ℝ] S := by
  apply (bundleHomComplexificationEquiv (F := F) (G := G)
    (V := Trivial ℝ F) (L := Trivial ℝ G) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext v
  apply complexification_ext <;> simp

/-- No norm or completeness on original fibres is required beyond the native bundle models. -/
theorem arbitrary_native_target
    {B EB HB : Type*} [TopologicalSpace B]
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    (I : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
    (V L : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
    [TopologicalSpace (TotalSpace G L)] [FiberBundle G L] [VectorBundle ℝ G L]
    (n : ℕ∞ω) :
    letI := fun x ↦ VectorBundle.isTopologicalAddGroup ℝ G L x
    letI := fun x ↦ VectorBundle.continuousSMul ℝ G L x
    Nonempty
      (TotalSpace (Complexification (F →L[ℝ] G))
        (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
        ≃ₘ^n⟮I.prod 𝓘(ℝ, Complexification (F →L[ℝ] G)),
          I.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G)⟯
        TotalSpace (Complexification F →L[ℂ] Complexification G)
          (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) := by
  let : ∀ x, IsTopologicalAddGroup (L x) := fun x ↦
    VectorBundle.isTopologicalAddGroup ℝ G L x
  let : ∀ x, ContinuousSMul ℝ (L x) := fun x ↦
    VectorBundle.continuousSMul ℝ G L x
  exact ⟨bundleHomComplexificationDiffeomorph (F := F) (G := G)⟩

end ArbitraryTarget

/-- A genuinely two-dimensional target coefficient. -/
theorem product_target_nonzero (x : ℝ) :
    bundleHomComplexificationEquiv (F := ℝ) (G := ℝ × ℝ)
      (V := Trivial ℝ ℝ) (L := Trivial ℝ (ℝ × ℝ)) x
      (Complex.I ⊗ₜ[ℝ] ContinuousLinearMap.inl ℝ ℝ ℝ) (1 ⊗ₜ[ℝ] (1 : ℝ)) ≠ 0 := by
  simp only [bundleHomComplexificationEquiv_coe, homComplexificationLinearEquiv_tmul_apply_tmul]
  intro h
  have := congrArg (fun u ↦ (imaginaryPart (ℝ × ℝ) u).1) h
  simp at this

/-- The full comparison also admits a zero-dimensional target model. -/
theorem zero_target_smooth :
    ContMDiffVectorBundle ∞ (Complexification ℝ →L[ℂ] Complexification (Fin 0 → ℝ))
      (fun x : ℝ ↦ (ℂ ⊗[ℝ] Trivial ℝ ℝ x) →L[ℂ]
        (ℂ ⊗[ℝ] Trivial ℝ (Fin 0 → ℝ) x)) 𝓘(ℝ) := inferInstance

/-- An actual nonzero infinite-dimensional target, with no finite-rank target hypothesis. -/
theorem infinite_target_nonzero (x : ℝ) :
    bundleHomComplexificationEquiv (F := ℝ) (G := C(Icc (0 : ℝ) 1, ℝ))
      (V := Trivial ℝ ℝ) (L := Trivial ℝ C(Icc (0 : ℝ) 1, ℝ)) x
      (Complex.I ⊗ₜ[ℝ] (ContinuousLinearMap.id ℝ ℝ).smulRight
        (ContinuousMap.const (Icc (0 : ℝ) 1) (1 : ℝ))) (1 ⊗ₜ[ℝ] (1 : ℝ)) ≠ 0 := by
  simp only [bundleHomComplexificationEquiv_coe, homComplexificationLinearEquiv_tmul_apply_tmul]
  intro h
  have := congrArg (fun u ↦ imaginaryPart C(Icc (0 : ℝ) 1, ℝ) u
    (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)) h
  simp at this

end TauCeti.Examples.HomComplexification
