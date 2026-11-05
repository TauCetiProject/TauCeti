/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Continuous.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.Matrix
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuous generalized matrix traces

The generalized matrix trace extends continuous multilinear cochains to matrix algebras.
The extension is continuous for uniform convergence on products of bounded sets, commutes
with the Hochschild and mixed-complex operators, and recovers the original cochain on
any diagonal corner. It induces a continuous linear map on continuous cyclic cohomology,
with its quotient topology, compatible with forgetting continuity.

These are the continuous cochain and cohomology maps used in matrix Morita comparisons
and cyclic pairings. No Morita isomorphism is asserted here. In particular, boundaries
are not replaced by their closures, and cohomology need not be Hausdorff.

The algebraic identities are reused from
`TauCeti.RingTheory.CyclicCohomology.Matrix`. The construction uses Mathlib's
`ContinuousMultilinearMap.compContinuousLinearMapL`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §1.2.
-/

public section

noncomputable section

namespace TauCeti

section Cochains

variable {𝕜 A M : Type*} [NormedField 𝕜] [AddCommGroup A] [Module 𝕜 A]
  [TopologicalSpace A] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]

/-- The generalized matrix trace on continuous cochains, continuous for bounded convergence. -/
def continuousMatrixCochainExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ Matrix ι ι A) M :=
  ∑ p : Fin (n + 1) → ι, ContinuousMultilinearMap.compContinuousLinearMapL
    (fun j ↦ ⟨Matrix.entryLinearMap 𝕜 A (p j) (p (finRotate (n + 1) j)),
      (continuous_apply _).comp (continuous_apply _)⟩)

/-- Forgetting continuity recovers the algebraic generalized trace. -/
@[simp]
theorem toMultilinearMap_continuousMatrixCochainExtension (ι : Type*) [Fintype ι]
    (n : ℕ) (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M) :
    (continuousMatrixCochainExtension ι n φ).toMultilinearMap =
      matrixCochainExtension ι n φ.toMultilinearMap := by
  ext a
  simp [continuousMatrixCochainExtension, matrixCochainExtension_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL]

/-- The closed-index-path formula for the continuous generalized trace. -/
@[simp low]
theorem continuousMatrixCochainExtension_apply (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → Matrix ι ι A) :
    continuousMatrixCochainExtension ι n φ a =
      ∑ p : Fin (n + 1) → ι, φ (fun j ↦ a j (p j) (p (finRotate (n + 1) j))) := by
  rw [← ContinuousMultilinearMap.coe_coe,
    toMultilinearMap_continuousMatrixCochainExtension, matrixCochainExtension_apply]
  rfl

/-- Restricting the generalized trace to a diagonal corner recovers the cochain. -/
@[simp]
theorem continuousMatrixCochainExtension_single (ι : Type*) [Fintype ι] [DecidableEq ι]
    (r : ι) (n : ℕ) (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 1) → A) :
    continuousMatrixCochainExtension ι n φ (fun j ↦ Matrix.single r r (a j)) = φ a := by
  rw [← ContinuousMultilinearMap.coe_coe,
    toMultilinearMap_continuousMatrixCochainExtension, matrixCochainExtension_single]
  rfl

/-- Extension is injective when a diagonal corner exists. -/
theorem continuousMatrixCochainExtension_injective (ι : Type*) [Fintype ι] [Nonempty ι]
    (n : ℕ) : Function.Injective
      (continuousMatrixCochainExtension (𝕜 := 𝕜) (A := A) (M := M) ι n) := by
  intro φ ψ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply matrixCochainExtension_injective ι n
  simpa only [toMultilinearMap_continuousMatrixCochainExtension] using
    congrArg ContinuousMultilinearMap.toMultilinearMap h

/-- Continuous matrix extension commutes with signed cyclic rotation. -/
theorem continuousMatrixCochainExtension_cyclicOperator (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M) :
    continuousMatrixCochainExtension ι n (continuousCyclicOperator 𝕜 A M n φ) =
      continuousCyclicOperator 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCochainExtension ι n φ) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousMatrixCochainExtension,
    toMultilinearMap_continuousCyclicOperator] using
    matrixCochainExtension_cyclicOperator ι n φ.toMultilinearMap

/-- Continuous matrix extension commutes with the cyclic norm. -/
theorem continuousMatrixCochainExtension_cyclicNorm (ι : Type*) [Fintype ι] (n : ℕ)
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M) :
    continuousMatrixCochainExtension ι n (continuousCyclicNorm 𝕜 A M n φ) =
      continuousCyclicNorm 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCochainExtension ι n φ) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousMatrixCochainExtension,
    toMultilinearMap_continuousCyclicNorm] using
    matrixCochainExtension_cyclicNorm ι n φ.toMultilinearMap

/-- The continuous generalized trace preserves cyclicity. -/
theorem continuousMatrixCochainExtension_mem_continuousCyclicCochains (ι : Type*)
    [Fintype ι] {n : ℕ} {φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M}
    (hφ : φ ∈ continuousCyclicCochains 𝕜 A M n) :
    continuousMatrixCochainExtension ι n φ ∈
      continuousCyclicCochains 𝕜 (Matrix ι ι A) M n := by
  rw [mem_continuousCyclicCochains_iff, toMultilinearMap_continuousMatrixCochainExtension]
  exact matrixCochainExtension_mem_cyclicCochains ι n
    ⟨φ.toMultilinearMap, (mem_continuousCyclicCochains_iff 𝕜 A M).1 hφ⟩

/-- The generalized trace restricted to continuous cyclic cochains. -/
def continuousMatrixCyclicCochainExtension (ι : Type*) [Fintype ι] (n : ℕ) :
    continuousCyclicCochains 𝕜 A M n →L[𝕜]
      continuousCyclicCochains 𝕜 (Matrix ι ι A) M n :=
  ((continuousMatrixCochainExtension ι n).comp
    (continuousCyclicCochains 𝕜 A M n).subtypeL).codRestrict _
      (fun φ ↦ continuousMatrixCochainExtension_mem_continuousCyclicCochains ι φ.2)

/-- The cyclic extension has the same underlying continuous multilinear map. -/
@[simp]
theorem coe_continuousMatrixCyclicCochainExtension (ι : Type*) [Fintype ι] {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 A M n) :
    (continuousMatrixCyclicCochainExtension ι n φ).val =
      continuousMatrixCochainExtension ι n φ.val := (rfl)

variable [One A] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Matrix extension commutes with insertion of the unit. -/
theorem continuousMatrixCochainExtension_barContraction {n : ℕ}
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) M) :
    continuousMatrixCochainExtension ι n (continuousBarContraction 𝕜 A M n φ) =
      continuousBarContraction 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCochainExtension ι (n + 1) φ) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousMatrixCochainExtension,
    toMultilinearMap_continuousBarContraction] using
    matrixCochainExtension_barContraction ι n φ.toMultilinearMap

/-- Matrix extension commutes with the continuous Connes operator. -/
theorem continuousMatrixCochainExtension_connesB {n : ℕ}
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 2) ↦ A) M) :
    continuousMatrixCochainExtension ι n (continuousConnesB 𝕜 A M n φ) =
      continuousConnesB 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCochainExtension ι (n + 1) φ) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousMatrixCochainExtension,
    toMultilinearMap_continuousConnesB] using
    matrixCochainExtension_connesB ι n φ.toMultilinearMap

end Cochains

section Differential

variable {𝕜 A M : Type*} [NormedField 𝕜] [NonUnitalNonAssocRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousMul A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]
  (ι : Type*) [Fintype ι]

/-- The continuous generalized trace is a Hochschild cochain map. -/
theorem continuousMatrixCochainExtension_hochschildCoboundary {n : ℕ}
    (φ : ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) M) :
    continuousMatrixCochainExtension ι (n + 1) (continuousHochschildCoboundary 𝕜 A M n φ) =
      continuousHochschildCoboundary 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCochainExtension ι n φ) := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  simpa only [toMultilinearMap_continuousMatrixCochainExtension,
    toMultilinearMap_continuousHochschildCoboundary] using
    matrixCochainExtension_hochschildCoboundary ι n φ.toMultilinearMap

/-- Matrix extension commutes with the cyclic Hochschild differential. -/
theorem continuousMatrixCyclicCochainExtension_cyclicHochschildCoboundary {n : ℕ}
    (φ : continuousCyclicCochains 𝕜 A M n) :
    continuousMatrixCyclicCochainExtension ι (n + 1)
        (continuousCyclicHochschildCoboundary 𝕜 A M n φ) =
      continuousCyclicHochschildCoboundary 𝕜 (Matrix ι ι A) M n
        (continuousMatrixCyclicCochainExtension ι n φ) := by
  apply Subtype.ext
  simp only [coe_continuousMatrixCyclicCochainExtension,
    coe_continuousCyclicHochschildCoboundary,
    continuousMatrixCochainExtension_hochschildCoboundary]

end Differential

section Cocycles

variable {𝕜 A M : Type*} [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousMul A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]
  (ι : Type*) [Fintype ι]

/-- Continuous cyclic cocycles extend to continuous cyclic cocycles on matrices. -/
theorem continuousMatrixCyclicCochainExtension_mem_continuousCyclicCocycles {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M n} (hφ : φ ∈ continuousCyclicCocycles 𝕜 A M n) :
    continuousMatrixCyclicCochainExtension ι n φ ∈
      continuousCyclicCocycles 𝕜 (Matrix ι ι A) M n := by
  rw [mem_continuousCyclicCocycles_iff,
    ← continuousMatrixCyclicCochainExtension_cyclicHochschildCoboundary,
    (mem_continuousCyclicCocycles_iff 𝕜 A M).1 hφ, map_zero]

/-- Actual continuous coboundaries, not merely their closures, extend to coboundaries. -/
theorem continuousMatrixCyclicCochainExtension_mem_continuousCyclicCoboundaries {n : ℕ}
    {φ : continuousCyclicCochains 𝕜 A M n}
    (hφ : φ ∈ continuousCyclicCoboundaries 𝕜 A M n) :
    continuousMatrixCyclicCochainExtension ι n φ ∈
      continuousCyclicCoboundaries 𝕜 (Matrix ι ι A) M n := by
  cases n with
  | zero =>
    rw [continuousCyclicCoboundaries_zero, Submodule.mem_bot] at hφ
    simp [hφ]
  | succ n =>
    obtain ⟨ψ, rfl⟩ := (mem_continuousCyclicCoboundaries_succ_iff 𝕜 A M).1 hφ
    exact (mem_continuousCyclicCoboundaries_succ_iff 𝕜 (Matrix ι ι A) M).2
      ⟨continuousMatrixCyclicCochainExtension ι n ψ,
        (continuousMatrixCyclicCochainExtension_cyclicHochschildCoboundary ι ψ).symm⟩

end Cocycles

section Cohomology

variable {𝕜 A M : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
  [TopologicalSpace A] [ContinuousAdd A] [ContinuousMul A]
  [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul 𝕜 M]
  (ι : Type*) [Fintype ι] [DecidableEq ι]

namespace continuousCyclicCohomology

variable (𝕜 A M) in
/-- The continuous generalized matrix trace on cyclic cohomology with its quotient topology. -/
def matrixExtension (n : ℕ) :
    continuousCyclicCohomology 𝕜 A M n →L[𝕜]
      continuousCyclicCohomology 𝕜 (Matrix ι ι A) M n :=
  desc ((mk 𝕜 (Matrix ι ι A) M n).comp
    (((continuousMatrixCyclicCochainExtension ι n).comp
      (continuousCyclicCocycles 𝕜 A M n).subtypeL).codRestrict _
        (fun φ ↦ continuousMatrixCyclicCochainExtension_mem_continuousCyclicCocycles ι φ.2)))
    (fun _ hφ ↦ (mk_eq_zero_iff 𝕜 (Matrix ι ι A) M _).2
      (continuousMatrixCyclicCochainExtension_mem_continuousCyclicCoboundaries ι hφ))

/-- Matrix extension sends a class to the class of its generalized trace. -/
@[simp]
theorem matrixExtension_mk {n : ℕ} (φ : continuousCyclicCocycles 𝕜 A M n) :
    matrixExtension 𝕜 A M ι n (mk 𝕜 A M n φ) = mk 𝕜 (Matrix ι ι A) M n
      ⟨continuousMatrixCyclicCochainExtension ι n φ.1,
        continuousMatrixCyclicCochainExtension_mem_continuousCyclicCocycles ι φ.2⟩ :=
  desc_mk _ _ φ

/-- Matrix extension is compatible with the comparison to algebraic cyclic cohomology. -/
theorem toCyclicCohomology_matrixExtension {n : ℕ}
    (x : continuousCyclicCohomology 𝕜 A M n) :
    toCyclicCohomology 𝕜 (Matrix ι ι A) M n (matrixExtension 𝕜 A M ι n x) =
      cyclicCohomology.matrixExtension M ι n (toCyclicCohomology 𝕜 A M n x) := by
  obtain ⟨φ, rfl⟩ := mk_surjective 𝕜 A M n x
  rw [matrixExtension_mk, toCyclicCohomology_mk, toCyclicCohomology_mk,
    cyclicCohomology.matrixExtension_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp only [continuousCyclicCochains.coe_toCyclicCochains,
    coe_continuousMatrixCyclicCochainExtension, coe_matrixCyclicCochainExtension_apply,
    toMultilinearMap_continuousMatrixCochainExtension]

end continuousCyclicCohomology

end Cohomology

end TauCeti
