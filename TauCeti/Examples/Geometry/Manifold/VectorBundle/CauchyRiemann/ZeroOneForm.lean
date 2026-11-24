/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.ZeroOneForm
import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic.Ring

/-!
# Examples: the native `(0,1)`-range bundle

The standard and negative almost complex structures distinguish the identity from conjugation.
The bundle clients retain zero coefficient rank, zero base dimension and an empty base. Smooth
clients install the infinity atlas once and use native monotonicity for finite regularity.
-/

open Bundle Module TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

public noncomputable section

-- Standard j: the identity in native tangent coordinates has zero (0,1)-part.
example (x : ℂ) : (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).zeroOnePart
    (V := Bundle.Trivial ℂ ℂ) (x := x)
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap = 0 := by
  ext v
  rw [SmoothAlmostComplexStructure.zeroOnePart_apply]
  simp only [ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply, zero_apply]
  obtain ⟨z, rfl⟩ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.surjective v
  simp [NormedSpace.fromTangentSpace_symm_apply, ← mul_assoc]

-- Standard j: conjugation in native tangent coordinates is fixed by the projection.
example (x : ℂ) : (SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).zeroOnePart
    (V := Bundle.Trivial ℂ ℂ) (x := x)
      (Complex.conjCLE.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap) =
      Complex.conjCLE.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := by
  ext v
  rw [SmoothAlmostComplexStructure.zeroOnePart_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply]
  obtain ⟨z, rfl⟩ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.surjective v
  simp [NormedSpace.fromTangentSpace_symm_apply, ← mul_assoc]
  ring

-- Negative j reverses the two roles: the identity is fixed.
example (x : ℂ) : (-SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).zeroOnePart
    (V := Bundle.Trivial ℂ ℂ) (x := x)
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap =
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap := by
  ext v
  rw [SmoothAlmostComplexStructure.zeroOnePart_apply, SmoothAlmostComplexStructure.neg_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_neg,
    NormedSpace.fromTangentSpace_apply]
  obtain ⟨z, rfl⟩ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.surjective v
  simp [NormedSpace.fromTangentSpace_symm_apply, ← mul_assoc]
  ring

-- Negative j: conjugation has zero (0,1)-part.
example (x : ℂ) : (-SmoothAlmostComplexStructure.ofComplexManifold ℂ ℂ).zeroOnePart
    (V := Bundle.Trivial ℂ ℂ) (x := x)
      (Complex.conjCLE.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap) = 0 := by
  ext v
  rw [SmoothAlmostComplexStructure.zeroOnePart_apply, SmoothAlmostComplexStructure.neg_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_neg,
    NormedSpace.fromTangentSpace_apply, zero_apply]
  obtain ⟨z, rfl⟩ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.surjective v
  simp [NormedSpace.fromTangentSpace_symm_apply, ← mul_assoc]

-- The public comparison computes on sums without exposing its defining body.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) (x : ℂ)
    (φ : ℂ ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)
    (hφ : ∀ z : ℂ, φ (Complex.I • z) = -(j x (φ z)))
    (η : j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ) x) (z w : ℂ) :
    j.zeroOneFormLinearEquiv x φ hφ η (z + w) = η.val (φ z) + η.val (φ w) := by
  simp only [SmoothAlmostComplexStructure.zeroOneFormLinearEquiv_apply, map_add]

-- The inverse comparison simplifies at a coordinate tangent vector in an importing module.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) (x : ℂ)
    (φ : ℂ ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)
    (hφ : ∀ z : ℂ, φ (Complex.I • z) = -(j x (φ z))) (L : ℂ →ₗ[ℂ] ℂ) (z : ℂ) :
    ((j.zeroOneFormLinearEquiv (V := Bundle.Trivial ℂ ℂ) x φ hφ).symm L).val (φ z) = L z := by
  simp

-- The inverse evaluation law proves antilinearity without using its range membership.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) (x : ℂ)
    (φ : ℂ ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)
    (hφ : ∀ z : ℂ, φ (Complex.I • z) = -(j x (φ z))) (L : ℂ →ₗ[ℂ] ℂ) :
    j.IsZeroOneForm
      ((j.zeroOneFormLinearEquiv (V := Bundle.Trivial ℂ ℂ) x φ hφ).symm L).val := by
  refine SmoothAlmostComplexStructure.isZeroOneForm_iff.mpr fun v ↦ ?_
  obtain ⟨z, rfl⟩ := φ.surjective v
  rw [← neg_neg (j x (φ z)), ← hφ, map_neg]
  simp only [SmoothAlmostComplexStructure.zeroOneFormLinearEquiv_symm_apply,
    LinearEquiv.symm_apply_apply, map_smul]

-- A smooth native rank-one coefficient bundle on a positive-dimensional base.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) :
    letI := TauCeti.subbundleTopology (ℂ →L[ℝ] ℂ)
      (F' := Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
      (j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ))
    letI := j.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
    letI := j.zeroOneVectorBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ) x)
    ContMDiffVectorBundle 0 (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ) x) 𝓘(ℝ, ℂ) ∧
    ContMDiffVectorBundle 3 (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ) x) 𝓘(ℝ, ℂ) := by
  let := TauCeti.subbundleTopology (ℂ →L[ℝ] ℂ)
    (F' := Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
    (j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ))
  let := j.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
  let := j.zeroOneVectorBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
  let := VectorBundle.restrictScalars ℝ ℂ (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
    (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ) x)
  have h := j.zeroOneContMDiffVectorBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
  exact ⟨h.of_le (by simp), h.of_le (by simp)⟩

-- Zero coefficient rank, using the actual native bundle constructors at arbitrary regularity.
example {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (j : SmoothAlmostComplexStructure I M) (n : ℕ∞ω) (hn : n ≤ ∞) :
    letI := TauCeti.subbundleTopology (E →L[ℝ] (Fin 0 → ℂ))
      (F' := Fin (finrank ℝ E / 2 * finrank ℂ (Fin 0 → ℂ)) → ℂ)
      (j.zeroOneFormSubmodule (V := Bundle.Trivial M (Fin 0 → ℂ)))
    letI := j.zeroOneFiberBundle (F := Fin 0 → ℂ) (V := Bundle.Trivial M (Fin 0 → ℂ)) n hn
    letI := j.zeroOneVectorBundle (F := Fin 0 → ℂ) (V := Bundle.Trivial M (Fin 0 → ℂ)) n hn
    letI := VectorBundle.restrictScalars ℝ ℂ
      (Fin (finrank ℝ E / 2 * finrank ℂ (Fin 0 → ℂ)) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial M (Fin 0 → ℂ)) x)
    ContMDiffVectorBundle n (Fin (finrank ℝ E / 2 * finrank ℂ (Fin 0 → ℂ)) → ℂ)
      (fun x ↦ j.zeroOneFormSubmodule (V := Bundle.Trivial M (Fin 0 → ℂ)) x) I :=
  j.zeroOneContMDiffVectorBundle (F := Fin 0 → ℂ) (V := Bundle.Trivial M (Fin 0 → ℂ)) n hn

-- The projection remains C^n on the single chosen infinity atlas.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) (n : ℕ∞ω) (hn : n ≤ ∞) :
    letI := TauCeti.subbundleTopology (ℂ →L[ℝ] ℂ)
      (F' := Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
      (j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ))
    letI := j.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
    ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ))
      (𝓘(ℝ, ℂ).prod 𝓘(ℝ, Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)) n
      (j.zeroOneFormProjection (F := ℂ) (V := Bundle.Trivial ℂ ℂ)
        (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)) := by
  let := TauCeti.subbundleTopology (ℂ →L[ℝ] ℂ)
    (F' := Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ) → ℂ)
    (j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ ℂ))
  let := j.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl
  exact (j.contMDiff_zeroOneFormProjection (F := ℂ) (V := Bundle.Trivial ℂ ℂ) ∞ le_rfl).of_le hn

-- A higher-rank coefficient model is accepted without identifying it with ℂ.
example (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) ℂ) (x : ℂ) :
    finrank ℂ (j.zeroOneFormSubmodule (V := Bundle.Trivial ℂ (Fin 2 → ℂ)) x) = 2 := by
  simpa [Module.finrank_pi_fintype] using
    j.finrank_zeroOneFormSubmodule (F := Fin 2 → ℂ) (V := Bundle.Trivial ℂ (Fin 2 → ℂ)) x


namespace TauCeti.Examples.ZeroOneForm

/-- The actual almost complex structure on the zero-dimensional real model. -/
private def zeroJ : SmoothAlmostComplexStructure 𝓘(ℝ, Fin 0 → ℝ) (Fin 0 → ℝ) :=
  SmoothAlmostComplexStructure.const 0 (fun _ ↦ Subsingleton.elim _ _)

-- A nonempty, zero-dimensional base with a nonzero coefficient rank.
example :
    letI := TauCeti.subbundleTopology ((Fin 0 → ℝ) →L[ℝ] ℂ)
      (F' := Fin (finrank ℝ (Fin 0 → ℝ) / 2 * finrank ℂ ℂ) → ℂ)
      (zeroJ.zeroOneFormSubmodule (V := Bundle.Trivial (Fin 0 → ℝ) ℂ))
    letI := zeroJ.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) ∞ le_rfl
    letI := zeroJ.zeroOneVectorBundle (F := ℂ) (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) ∞ le_rfl
    letI := VectorBundle.restrictScalars ℝ ℂ
      (Fin (finrank ℝ (Fin 0 → ℝ) / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ zeroJ.zeroOneFormSubmodule (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) x)
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ (Fin 0 → ℝ) / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ zeroJ.zeroOneFormSubmodule (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) x)
      𝓘(ℝ, Fin 0 → ℝ) :=
  zeroJ.zeroOneContMDiffVectorBundle (F := ℂ) (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) ∞ le_rfl

example (x : Fin 0 → ℝ) :
    finrank ℂ (zeroJ.zeroOneFormSubmodule (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) x) = 0 := by
  simpa using zeroJ.finrank_zeroOneFormSubmodule (F := ℂ) (V := Bundle.Trivial (Fin 0 → ℝ) ℂ) x

section Empty

/-- The standard empty atlas on the concrete empty base. -/
local instance emptyChartedSpace : ChartedSpace ℝ PEmpty.{1} := ChartedSpace.empty ℝ PEmpty.{1}

/-- An actual native almost complex structure on an empty base with odd-dimensional model. -/
private def emptyJ : SmoothAlmostComplexStructure 𝓘(ℝ, ℝ) PEmpty.{1} where
  toEndomorphism := ⟨fun x ↦ PEmpty.elim x, fun x ↦ PEmpty.elim x⟩
  square_neg := fun x ↦ PEmpty.elim x

-- No base point is required by any native range-bundle constructor.
example :
    letI := TauCeti.subbundleTopology (ℝ →L[ℝ] ℂ)
      (F' := Fin (finrank ℝ ℝ / 2 * finrank ℂ ℂ) → ℂ)
      (emptyJ.zeroOneFormSubmodule (V := Bundle.Trivial PEmpty.{1} ℂ))
    letI := emptyJ.zeroOneFiberBundle (F := ℂ) (V := Bundle.Trivial PEmpty.{1} ℂ) ∞ le_rfl
    letI := emptyJ.zeroOneVectorBundle (F := ℂ) (V := Bundle.Trivial PEmpty.{1} ℂ) ∞ le_rfl
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin (finrank ℝ ℝ / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ emptyJ.zeroOneFormSubmodule (V := Bundle.Trivial PEmpty.{1} ℂ) x)
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ ℝ / 2 * finrank ℂ ℂ) → ℂ)
      (fun x ↦ emptyJ.zeroOneFormSubmodule (V := Bundle.Trivial PEmpty.{1} ℂ) x) 𝓘(ℝ, ℝ) :=
  emptyJ.zeroOneContMDiffVectorBundle (F := ℂ) (V := Bundle.Trivial PEmpty.{1} ℂ) ∞ le_rfl

end Empty

-- The nontrivial native line bundle O(1) on the Riemann sphere, using only its real C⁰ structure.
example :
    let L := (OnePoint.twistCore (𝕜 := ℂ) (1 : ℤ)).Fiber
    let j := SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)
    letI := VectorBundle.restrictScalars ℝ ℂ ℂ L
    letI : ∀ x, IsTopologicalAddGroup (L x) := VectorBundle.isTopologicalAddGroup ℂ ℂ L
    letI : ∀ x, ContinuousSMul ℝ (L x) := VectorBundle.continuousSMul ℝ ℂ L
    letI : ∀ x, ContinuousSMul ℂ (L x) := VectorBundle.continuousSMul ℂ ℂ L
    HasLocalContMDiffSubbundleFrames 𝓘(ℝ, ℂ) 0 (ℂ →L[ℝ] ℂ)
      (Fin (finrank ℝ ℂ / 2 * finrank ℂ ℂ)) (j.zeroOneFormSubmodule (V := L)) ∧
      (∀ x, finrank ℂ (j.zeroOneFormSubmodule (V := L) x) = 1) ∧
      (∀ p : TotalSpace (Fin 1 → ℂ) (fun x ↦ j.zeroOneFormSubmodule (V := L) x),
        j.zeroOneFormProjection (F := ℂ) (V := L) (Fin 1 → ℂ)
          (j.zeroOneFormInclusion (F := ℂ) (V := L) (Fin 1 → ℂ) p) = p) := by
  let L := (OnePoint.twistCore (𝕜 := ℂ) (1 : ℤ)).Fiber
  let j := SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)
  let := VectorBundle.restrictScalars ℝ ℂ ℂ L
  let : ∀ x, IsTopologicalAddGroup (L x) := VectorBundle.isTopologicalAddGroup ℂ ℂ L
  let : ∀ x, ContinuousSMul ℝ (L x) := VectorBundle.continuousSMul ℝ ℂ L
  let : ∀ x, ContinuousSMul ℂ (L x) := VectorBundle.continuousSMul ℂ ℂ L
  refine ⟨j.hasLocalContMDiffSubbundleFrames_zeroOneFormSubmodule (F := ℂ) (V := L) (by simp),
    fun x ↦ ?_, fun p ↦ j.zeroOneFormProjection_inclusion _ p⟩
  simpa using j.finrank_zeroOneFormSubmodule (F := ℂ) (V := L) x

end TauCeti.Examples.ZeroOneForm
