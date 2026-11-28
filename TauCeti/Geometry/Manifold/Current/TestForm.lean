/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.TestDual
public import TauCeti.Geometry.Manifold.VectorBundle.Section.DualDensityTest
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
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

Fibrewise evaluation `Aₖ ≅ Hom(Hom(Aₖ, D), D)` (`ModelWithCorners.formDensityDoubleDualEquiv`)
identifies test forms with the compactly supported smooth `k`-forms: `TauCeti.TestForm.formEquiv`
is the case `V = Aₖ` of `TauCeti.DualDensityTest.doubleDualEquiv`, and it sends a test form `s` to
the form `α` with `φ (α x) = s x φ` for every `φ : Aₖ x → D x`. The identification is an
isomorphism of topological vector spaces for the test topologies on both sides, and it preserves
the exact support. It involves no orientation, metric or choice of frame.

## Main definitions

* `TauCeti.TestForm I M k`: the test `k`-forms, the bundle tests of `Hom(Hom(Λᵏ T*M, |Λ|), |Λ|)`.
* `TauCeti.Current I M k`: the `k`-currents, the distributional sections of `Hom(Λᵏ T*M, |Λ|)`.
* `TauCeti.TestForm.formEquiv`: the identification of test forms with compactly supported smooth
  `k`-forms, as topological vector spaces. It commutes with multiplication by smooth functions
  (`TauCeti.TestForm.formEquiv_smulLeftCLM`).

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

/-- Test `k`-forms are the compactly supported smooth `k`-forms, as topological vector spaces. A
test form `s` corresponds to the form `α` with `φ (α x) = s x φ` for every density-valued
`k`-vector `φ` at `x` (`TauCeti.TestForm.apply_formEquiv_apply`): the inverse of fibrewise
evaluation `ModelWithCorners.formDensityDoubleDualEquiv` is applied pointwise. -/
def formEquiv : TestForm I M k ≃L[ℝ]
    BundleTest I (E [⋀^Fin k]→L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) :=
  DualDensityTest.doubleDualEquiv (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)

/-- The `k`-form of a test form `s` is characterized by its pairings: a density-valued `k`-vector
`φ` at `x` takes on it the value `s x φ`. -/
@[simp]
theorem apply_formEquiv_apply (s : TestForm I M k) (x : M)
    (φ : (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] DensityBundle I M x) :
    φ (formEquiv s x) = s x φ :=
  DualDensityTest.apply_doubleDualEquiv_apply (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) s x φ

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
    formEquiv.symm α x φ = φ (α x) :=
  DualDensityTest.doubleDualEquiv_symm_apply_apply (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) α x φ

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
    formEquiv s x = 0 ↔ s x = 0 :=
  DualDensityTest.doubleDualEquiv_apply_eq_zero_iff (F := E [⋀^Fin k]→L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)

/-- The identification of test forms with compactly supported smooth forms commutes with
multiplication by smooth functions. -/
@[simp]
theorem formEquiv_smulLeftCLM (ρ : C^∞⟮I, M; ℝ⟯) (s : TestForm I M k) :
    formEquiv (BundleTest.smulLeftCLM ρ s) = BundleTest.smulLeftCLM ρ (formEquiv s) := by
  apply formEquiv.symm.injective
  ext x : 1
  rw [ContinuousLinearEquiv.symm_apply_apply, BundleTest.smulLeftCLM_apply, formEquiv_symm_apply,
    BundleTest.smulLeftCLM_apply, map_smul, formDensityDoubleDualEquiv_formEquiv_apply]

end TestForm

end TauCeti
