/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.TestDual
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.CompactSupport
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Test forms and currents on a manifold

Let `M` be a smooth manifold modelled on a finite-dimensional real space `E`, let
`Aₖ = Λᵏ T*M` be its bundle of alternating `k`-forms and `D = |Λ|` its density line. A
`k`-current is a distributional section of `Vₖ = Hom(Aₖ, D)`, the bundle of `D`-valued
`k`-vectors, so it acts on the compactly supported smooth sections of `Vₖ* ⊗ D = Hom(Vₖ, D)`.
These are the **test `k`-forms** `TauCeti.TestForm I M k`, with the test topology of bundle tests,
and the **`k`-currents** `TauCeti.Current I M k` are the continuous linear functionals on them,
`TauCeti.BundleDistribution I M` for the bundle `Vₖ`. The density factor is what lets a smooth
`D`-valued `k`-vector field act on a test form without a choice of measure, orientation or metric.

Fibrewise evaluation `Aₖ ≅ Hom(Hom(Aₖ, D), D)` (`ModelWithCorners.formDensityDoubleDualEquiv`) is
a diffeomorphism of total spaces whose expression in the induced frames is the constant model map
`NormedSpace.inclusionInDoubleDual` (`Bundle.Trivialization.bundleLineDoubleDualEquiv_inFrame`).
Hence native transport of bundle tests (`TauCeti.BundleTest.mapCLE`) identifies test forms with
the compactly supported smooth `k`-forms: `TauCeti.TestForm.formEquiv` sends a test form `s` to the
form `α` with `φ (α x) = s x φ` for every `φ : Aₖ x → D x`. The identification is an isomorphism
of topological vector spaces for the test topologies on both sides, and it preserves the exact
support. It involves no orientation, metric or choice of frame.

## Main definitions

* `TauCeti.TestForm I M k`: the test `k`-forms, the bundle tests of `Hom(Hom(Λᵏ T*M, |Λ|), |Λ|)`.
* `TauCeti.Current I M k`: the `k`-currents, the distributional sections of `Hom(Λᵏ T*M, |Λ|)`.
* `TauCeti.TestForm.formEquiv`: the identification of test forms with compactly supported smooth
  `k`-forms, as topological vector spaces.

## References

* G. de Rham, *Variétés différentiables*, Hermann, 1955, Chapter III (currents on manifolds as
  continuous linear functionals on compactly supported smooth forms).
* H. Federer, *Geometric Measure Theory*, §4.1.7 (currents in Euclidean open sets).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ)

/-- The **test `k`-forms** on `M`: the compactly supported smooth sections of
`Hom(Hom(Λᵏ T*M, |Λ|), |Λ|)`, the dual densities of the bundle of density-valued `k`-vectors, with
the test topology of bundle tests. They are identified with compactly supported smooth `k`-forms by
`TauCeti.TestForm.formEquiv`. -/
abbrev TestForm :=
  DualDensityTest I M ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (fun x : M ↦ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)

/-- The real **`k`-currents** on `M`: the continuous linear functionals on test `k`-forms, that is
the distributional sections of the bundle `Hom(Λᵏ T*M, |Λ|)` of density-valued `k`-vectors. -/
abbrev Current :=
  BundleDistribution I M ((E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (fun x : M ↦ (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)

namespace TestForm

variable {I M k}

/-- Evaluation into the double dual of a finite-dimensional real space, as a topological linear
isomorphism. It is the model of `ModelWithCorners.formDensityDoubleDualEquiv` in frames. -/
private def modelDoubleDualEquiv (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] : F ≃L[ℝ] StrongDual ℝ (StrongDual ℝ F) :=
  let c : Module.Dual ℝ F ≃ₗ[ℝ] StrongDual ℝ F := LinearMap.toContinuousLinearMap
  let j := (Module.evalEquiv ℝ F).trans
    ((c.arrowCongr (LinearEquiv.refl ℝ ℝ)).trans LinearMap.toContinuousLinearMap)
  LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := F) (F := StrongDual ℝ (StrongDual ℝ F)) j

private theorem modelDoubleDualEquiv_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (v : F) :
    modelDoubleDualEquiv F v = NormedSpace.inclusionInDoubleDual ℝ F v := by
  ext φ
  simp [modelDoubleDualEquiv, NormedSpace.dual_def]

/-- Test `k`-forms are the compactly supported smooth `k`-forms, as topological vector spaces. A
test form `s` corresponds to the form `α` with `φ (α x) = s x φ` for every density-valued
`k`-vector `φ` at `x` (`TauCeti.TestForm.apply_formEquiv_apply`): the inverse of fibrewise
evaluation `ModelWithCorners.formDensityDoubleDualEquiv` is applied pointwise. -/
def formEquiv : TestForm I M k ≃L[ℝ]
    BundleTest I (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) := by
  let e := fun a : M ↦ trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) a
  let d := fun a : M ↦ trivializationAt ℝ (DensityBundle I M) a
  let U : M → TopologicalSpace.Opens M := fun a ↦
    ⟨(e a).baseSet ∩ (d a).baseSet, (e a).open_baseSet.inter (d a).open_baseSet⟩
  refine BundleTest.mapCLE (I := I) (fun a ↦ trivializationAt _ _ a) e U
    (fun _ _ hx ↦ ⟨hx, hx.2⟩) (fun _ _ hx ↦ hx.1)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt _ _ x, mem_baseSet_trivializationAt _ _ x⟩)
    -- Supplying the bounded-convergence topology directly lets elaboration resolve the inverse
    -- on the nested continuous-linear-map fibre.
    (fun x ↦
      letI := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
        (E := (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
        (F := DensityBundle I M x)
      (bundleLineDoubleDualEquiv (F := E [⋀^Fin k]→L[ℝ] ℝ)
        (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x).toLinearEquiv.symm)
    (contMDiff_bundle_symm _ (contMDiff_bundleLineDoubleDualEquiv (I := I) (n := ∞)
      (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M)))
    (contMDiff_bundleLineDoubleDualEquiv (I := I) (n := ∞)
      (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M))
    (fun _ ↦ ContMDiffMap.const (modelDoubleDualEquiv _).symm.toContinuousLinearMap)
    (fun _ ↦ ContMDiffMap.const (NormedSpace.inclusionInDoubleDual ℝ _)) ?_ ?_
  -- In the frames induced at `a`, the inverse of evaluation is the inverse model evaluation.
  · intro a s x
    have h := (e a).bundleLineDoubleDualEquiv_symm_inFrame (d a) x.property (s x)
    rw [← modelDoubleDualEquiv_apply] at h
    refine (Trivialization.frameCoordinates_apply _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Trivialization.frameCoordinates_apply _ _ _ _).symm)
    refine (congrArg (fun v ↦ (e a ⟨(x : M), v⟩).2)
      (ContMDiffSection.mapEquiv_apply _ _ _ s x)).trans ?_
    exact (ContinuousLinearEquiv.eq_symm_apply _).2 h
  -- In the same frames, evaluation is the model evaluation.
  · intro a s x
    refine (Trivialization.frameCoordinates_apply _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Trivialization.frameCoordinates_apply _ _ _ _).symm)
    refine (congrArg (fun v ↦ (trivializationAt _ _ a ⟨(x : M), v⟩).2) ?_).trans
      ((e a).bundleLineDoubleDualEquiv_inFrame (d a) x.property (s x))
    exact (DFunLike.congr_fun (DFunLike.congr_fun (ContMDiffSection.mapEquiv_symm _ _ _) s)
      (x : M)).trans (ContMDiffSection.mapEquiv_apply _ _ _ s x)

private theorem formEquiv_apply_eq (s : TestForm I M k) (x : M) :
    letI := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
      (E := (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
      (F := DensityBundle I M x)
    formEquiv s x = (bundleLineDoubleDualEquiv (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x).symm (s x) :=
  BundleTest.mapCLE_apply ..

private theorem formEquiv_symm_apply_eq
    (α : BundleTest I (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))
    (x : M) :
    formEquiv.symm α x = bundleLineDoubleDualEquiv (F := E [⋀^Fin k]→L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x (α x) :=
  BundleTest.mapCLE_symm_apply ..

/-- The `k`-form of a test form `s` is characterized by its pairings: a density-valued `k`-vector
`φ` at `x` takes on it the value `s x φ`. -/
@[simp]
theorem apply_formEquiv_apply (s : TestForm I M k) (x : M)
    (φ : (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) :
    φ (formEquiv s x) = s x φ := by
  rw [formEquiv_apply_eq]
  exact apply_bundleLineDoubleDualEquiv_symm (𝕜 := ℝ) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x (s x) φ

/-- Fibrewise evaluation of the `k`-form of a test form recovers the test form. -/
@[simp]
theorem formDensityDoubleDualEquiv_formEquiv_apply (s : TestForm I M k) (x : M) :
    I.formDensityDoubleDualEquiv k x (formEquiv s x) = s x := by
  ext φ
  rw [ModelWithCorners.formDensityDoubleDualEquiv_apply, apply_formEquiv_apply]

/-- The test form of a compactly supported smooth `k`-form `α` pairs a density-valued `k`-vector
`φ` at `x` with `α x`. -/
@[simp]
theorem formEquiv_symm_apply_apply
    (α : BundleTest I (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))
    (x : M) (φ : (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) :
    formEquiv.symm α x φ = φ (α x) := by
  rw [formEquiv_symm_apply_eq]
  exact bundleLineDoubleDualEquiv_apply (𝕜 := ℝ) (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] ℝ) (DensityBundle I M) x (α x) φ

/-- The test form of a compactly supported smooth `k`-form is computed pointwise by fibrewise
evaluation. -/
theorem formEquiv_symm_apply
    (α : BundleTest I (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ))
    (x : M) :
    formEquiv.symm α x = I.formDensityDoubleDualEquiv k x (α x) := by
  ext φ
  rw [formEquiv_symm_apply_apply, ModelWithCorners.formDensityDoubleDualEquiv_apply]

/-- A test form and its `k`-form vanish at the same points, so they have the same support. -/
@[simp]
theorem formEquiv_apply_eq_zero_iff {s : TestForm I M k} {x : M} :
    formEquiv s x = 0 ↔ s x = 0 := by
  let := ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℝ)
    (E := (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x)
    (F := DensityBundle I M x)
  rw [formEquiv_apply_eq, ContinuousLinearEquiv.map_eq_zero_iff]

end TestForm

end TauCeti
