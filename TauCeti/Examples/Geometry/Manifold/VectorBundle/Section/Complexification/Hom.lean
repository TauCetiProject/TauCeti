/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Complexification.Hom

/-!
# Native density-valued Hom test coefficients

These examples specialize the generic real continuous linear equivalence to the actual
`DensityBundle`. They include arbitrary normed source models, a constructed nonzero value,
a rank-zero source and a concrete empty base. No complex module structure is added to
`BundleTest` and no distribution-dual identification is asserted.
-/

public section

noncomputable section
open Bundle FiberBundle Set TauCeti ContMDiffSection
open scoped TensorProduct ContDiff Manifold Topology TauCeti.Complexification

namespace TauCeti.Examples.HomTestCoefficients

section Density
universe uE uH uM uF uV
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type uV} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

-- The source model may be incomplete and infinite dimensional. Finite dimensionality
-- here belongs only to the base of the actual density bundle.
example :
    BundleTest I (Complexification (F →L[ℝ] ℝ))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] DensityBundle I M x)) ≃L[ℝ]
    BundleTest I (Complexification F →L[ℂ] Complexification ℝ)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] DensityBundle I M x)) :=
  BundleTest.homComplexificationCLE (I := I) (F := F) (G := ℝ)
    (V := V) (L := DensityBundle I M)

example (s : BundleTest I (Complexification (F →L[ℝ] ℝ))
    (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] DensityBundle I M x))) :
    (BundleTest.homComplexificationCLE (I := I) (F := F) (G := ℝ)
      (V := V) (L := DensityBundle I M)).symm
      (BundleTest.homComplexificationCLE (I := I) (F := F) (G := ℝ)
        (V := V) (L := DensityBundle I M) s) = s :=
  ContinuousLinearEquiv.symm_apply_apply _ s

end Density

/-- An actual native test section has a nonzero density-valued coefficient. -/
theorem exists_nonzero_density_coefficient : ∃ s : BundleTest 𝓘(ℝ, ℝ) (Complexification (ℝ →L[ℝ] ℝ))
    (fun x : ℝ ↦ ℂ ⊗[ℝ] (Bundle.Trivial ℝ ℝ x →L[ℝ] DensityBundle 𝓘(ℝ, ℝ) ℝ x)),
    BundleTest.homComplexificationCLE (I := 𝓘(ℝ, ℝ))
      (F := ℝ) (G := ℝ) (V := Bundle.Trivial ℝ ℝ) (L := DensityBundle 𝓘(ℝ, ℝ) ℝ) s 0 (1 ⊗ₜ[ℝ] (1 :
        ℝ)) ≠ 0 := by
  let e : DensityBundle 𝓘(ℝ, ℝ) ℝ 0 ≃L[ℝ] ℝ :=
    (trivializationAt ℝ (DensityBundle 𝓘(ℝ, ℝ) ℝ) 0).continuousLinearEquivAt ℝ 0
      (mem_baseSet_trivializationAt ℝ (DensityBundle 𝓘(ℝ, ℝ) ℝ) 0)
  let ρ : DensityBundle 𝓘(ℝ, ℝ) ℝ 0 := e.symm 1
  have hρ : ρ ≠ 0 := by
    intro h
    have h' := congrArg e h
    simp only [ρ, ContinuousLinearEquiv.apply_symm_apply, map_zero, one_ne_zero] at h'
  let t : ℝ →L[ℝ] DensityBundle 𝓘(ℝ, ℝ) ℝ 0 := ContinuousLinearMap.toSpanSingleton ℝ ρ
  obtain ⟨s, hs⟩ := BundleTest.exists_apply_eq (I := 𝓘(ℝ, ℝ))
    (F := Complexification (ℝ →L[ℝ] ℝ))
    (V := fun x : ℝ ↦ ℂ ⊗[ℝ] (Bundle.Trivial ℝ ℝ x →L[ℝ] DensityBundle 𝓘(ℝ, ℝ) ℝ x))
    0 (1 ⊗ₜ[ℝ] t)
  refine ⟨s, ?_⟩
  rw [BundleTest.homComplexificationCLE_apply, hs]
  rw [bundleHomComplexificationEquiv_coe]
  change homComplexificationLinearEquiv (1 ⊗ₜ[ℝ] t) (1 ⊗ₜ[ℝ] (1 : ℝ)) ≠ 0
  rw [homComplexificationLinearEquiv_tmul_apply_tmul]
  simp only [one_mul, t, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change (1 : ℂ) ⊗ₜ[ℝ] ρ ≠ 0
  intro h
  apply hρ
  have h' := congrArg (realPart (DensityBundle 𝓘(ℝ, ℝ) ℝ 0)) h
  simpa only [realPart_tmul, Complex.one_re, one_smul, map_zero] using h'


-- Rank zero is an actual native source model, not an extra nonzero-rank hypothesis.
example :
    BundleTest 𝓘(ℝ, ℝ) (Complexification ((Fin 0 → ℝ) →L[ℝ] ℝ))
      (fun x : ℝ ↦ ℂ ⊗[ℝ] (Bundle.Trivial ℝ (Fin 0 → ℝ) x →L[ℝ] Bundle.Trivial ℝ ℝ x)) ≃L[ℝ]
    BundleTest 𝓘(ℝ, ℝ) (Complexification (Fin 0 → ℝ) →L[ℂ] Complexification ℝ)
      (fun x : ℝ ↦ (ℂ ⊗[ℝ] Bundle.Trivial ℝ (Fin 0 → ℝ) x) →L[ℂ]
        (ℂ ⊗[ℝ] Bundle.Trivial ℝ ℝ x)) :=
  BundleTest.homComplexificationCLE (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (F := Fin 0 → ℝ) (G := ℝ) (V := Bundle.Trivial ℝ (Fin 0 → ℝ))
    (L := Bundle.Trivial ℝ ℝ)

-- The default topology and the equivalence also elaborate on a concrete empty base.
example :
    let _ := ChartedSpace.empty ℝ Empty
    BundleTest 𝓘(ℝ, ℝ) (Complexification (ℝ →L[ℝ] ℝ))
      (fun x : Empty ↦ ℂ ⊗[ℝ] (Bundle.Trivial Empty ℝ x →L[ℝ] Bundle.Trivial Empty ℝ x)) ≃L[ℝ]
    BundleTest 𝓘(ℝ, ℝ) (Complexification ℝ →L[ℂ] Complexification ℝ)
      (fun x : Empty ↦ (ℂ ⊗[ℝ] Bundle.Trivial Empty ℝ x) →L[ℂ]
        (ℂ ⊗[ℝ] Bundle.Trivial Empty ℝ x)) := by
  let _ := ChartedSpace.empty ℝ Empty
  exact BundleTest.homComplexificationCLE (I := 𝓘(ℝ, ℝ)) (M := Empty)
    (F := ℝ) (G := ℝ) (V := Bundle.Trivial Empty ℝ) (L := Bundle.Trivial Empty ℝ)

end TauCeti.Examples.HomTestCoefficients
