/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Algebra.Module.LinearMap.UnitSMul
import TauCeti.Analysis.InnerProductSpace.FoldedComplex
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Laplacians of complexes of differential operators

Let `⋯ → Γ(E₀) → Γ(E₁) → Γ(E₂) → ⋯` be a complex of differential operators `dᵢ` of a common
order at most `m` between the smooth sections of vector bundles of finite rank with fibre metrics
over a manifold `M`, and let `μ` be a measure on `M`. The complex is *elliptic* when the sequence of
principal symbols `σ(dᵢ)(ξ)` (`TauCeti.sectionPrincipalSymbol`) is exact at every nonzero covector
`ξ`. With formal adjoints `dᵢ*` (`LinearMap.IsFormalAdjoint`), its Laplacians
`Δᵢ = dᵢ₋₁ dᵢ₋₁* + dᵢ* dᵢ` are formally self-adjoint differential operators of order at most `2m`,
and the complex is elliptic exactly when all of its Laplacians are elliptic
(`TauCeti.IsSectionEllipticAt`). This is what makes the Hodge theory of an elliptic complex an
instance of the theory of a single elliptic operator.

This file proves these facts one position of the complex at a time. For differential operators
`A : Γ(U) → Γ(V)` and `B : Γ(V) → Γ(W)` of order at most `m`, with formal adjoints `A'` and `B'`
of order at most `m`, the Laplacian at `V` is

`Δ = A A' + B' B : Γ(V) → Γ(V)` (`TauCeti.sectionHodgeLaplacian`).

Its principal symbol is `σ(A) σ(A') + σ(B') σ(B)`, and since the principal symbol of a formal
adjoint is `(-1) ^ m` times the fibrewise adjoint
(`LinearMap.IsFormalAdjoint.sectionPrincipalSymbol_eq_smul_adjoint`), this is `(-1) ^ m` times the
Laplacian `σ(A) σ(A)† + σ(B)† σ(B)` of the two symbols (`ContinuousLinearMap.hodgeLaplacian`). The
fibres are finite-dimensional, so the latter is invertible exactly when the symbol sequence is
exact (`ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian`). Thus:

* `TauCeti.isSectionEllipticAt_sectionHodgeLaplacian_iff`: if `B A = 0`, the Laplacian is elliptic
  at `x` exactly when `σ(A)(ξ)` and `σ(B)(ξ)` are exact at every nonzero covector `ξ` at `x`;
* `TauCeti.isSectionEllipticAt_adjoint_comp_iff` and `TauCeti.isSectionEllipticAt_comp_adjoint_iff`
  treat the two ends of a finite complex, where the Laplacian is `B' B` or `A A'`: it is elliptic
  exactly when `σ(B)(ξ)` is injective, respectively `σ(A)(ξ)` is surjective, at every nonzero `ξ`.

A complex of a common order also folds into a two-periodic one, `A : Γ(V) → Γ(W)` on the bundles
of even degree and `B : Γ(W) → Γ(V)` on those of odd degree. Its *folded operator* `A + B'`, for
the de Rham complex `d + d* : Ω^even → Ω^odd`, has index the Euler characteristic of the complex.
By `TauCeti.isSectionEllipticAt_add_adjoint_iff`, it is elliptic exactly when the two-periodic
symbol sequence is exact at both of its positions (`ContinuousLinearMap.bijective_add_adjoint_iff`).

The Euclidean statements for homogeneous symbols are in
`TauCeti.Analysis.Pseudodifferential.HodgeLaplacian`.

## Main definitions

* `TauCeti.sectionHodgeLaplacian A A' B B'`: the Laplacian `A A' + B' B` at the middle bundle, as a
  differential operator of order at most `m + m`.

## Main results

* `TauCeti.isFormalAdjoint_sectionHodgeLaplacian`: the Laplacian is formally self-adjoint.
* `TauCeti.sectionPrincipalSymbol_sectionHodgeLaplacian`: its principal symbol.
* `TauCeti.isSectionEllipticAt_sectionHodgeLaplacian_iff`,
  `TauCeti.isSectionElliptic_sectionHodgeLaplacian_iff`: the Laplacian of a complex is elliptic
  exactly when its symbol sequence is exact at every nonzero covector.
* `TauCeti.isSectionEllipticAt_adjoint_comp_iff`, `TauCeti.isSectionEllipticAt_comp_adjoint_iff`:
  the Laplacians at the two ends of a complex.
* `TauCeti.isSectionEllipticAt_add_adjoint_iff`: the folded operator of a two-periodic complex.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7, pp. 520–522 (elliptic complexes, their Laplacians and the rolled-up operator).
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §5 (elliptic complexes).
-/

public section

open Bundle MeasureTheory Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F''] [FiniteDimensional ℝ F'']
  {U : M → Type*} [TopologicalSpace (TotalSpace F'' U)]
  [∀ x, NormedAddCommGroup (U x)] [∀ x, InnerProductSpace ℝ (U x)]
  [FiberBundle F'' U] [VectorBundle ℝ F'' U] [ContMDiffVectorBundle ∞ F'' U I]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  {m : ℕ} {x : M}

variable (A : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F'', U⟯ Cₛ^∞⟮I; F, V⟯ m)
  (A' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F'', U⟯ m)
  (B : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
  (B' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m)

/-- The **Laplacian** `A A' + B' B : Γ(V) → Γ(V)` at the middle bundle of two composable
differential operators `A : Γ(U) → Γ(V)` and `B : Γ(V) → Γ(W)` of order at most `m`, built from
operators `A' : Γ(V) → Γ(U)` and `B' : Γ(W) → Γ(V)` of order at most `m`, as a differential operator
of order at most `m + m`. When `A'` and `B'` are formal adjoints of `A` and `B`
(`LinearMap.IsFormalAdjoint`) and `B A = 0`, it is the Hodge Laplacian `d d* + d* d` of the complex
at `V`. -/
def sectionHodgeLaplacian :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ (m + m) :=
  ⟨(A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯),
      comp_mem_differentialOperators A.property A'.property⟩ +
    ⟨(B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
      comp_mem_differentialOperators B'.property B.property⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ F'']
  [ContMDiffVectorBundle ∞ F'' U I] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I] in
@[simp]
theorem coe_sectionHodgeLaplacian :
    (sectionHodgeLaplacian A A' B B' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) =
      (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) +
        (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) :=
  (rfl)

/-- The principal symbol of the Laplacian `A A' + B' B` is `σ(A) σ(A') + σ(B') σ(B)`. -/
theorem sectionPrincipalSymbol_sectionHodgeLaplacian (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx (sectionHodgeLaplacian A A' B B') ξ =
      sectionPrincipalSymbol I hx A ξ ∘ₗ sectionPrincipalSymbol I hx A' ξ +
        sectionPrincipalSymbol I hx B' ξ ∘ₗ sectionPrincipalSymbol I hx B ξ := by
  rw [sectionHodgeLaplacian, sectionPrincipalSymbol_add, sectionPrincipalSymbol_comp,
    sectionPrincipalSymbol_comp]

section Metric

variable [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle F'' U] [IsContinuousRiemannianBundle F V]
  [IsContinuousRiemannianBundle F' W]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {A A' B B'}

omit [FiniteDimensional ℝ F''] [ContMDiffVectorBundle ∞ F'' U I] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
  [SigmaCompactSpace M] [IsContinuousRiemannianBundle F'' U] [IsContinuousRiemannianBundle F' W]
  [μ.IsOpenPosMeasure] in
/-- **The Laplacian is formally self-adjoint.** If `A'` and `B'` are formal adjoints of `A` and `B`
with respect to `μ`, then the Laplacian `A A' + B' B` is its own formal adjoint. -/
theorem isFormalAdjoint_sectionHodgeLaplacian
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ)
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ) :
    (sectionHodgeLaplacian A A' B B' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (sectionHodgeLaplacian A A' B B') μ := by
  have hA's := tsupport_differentialOperators_section_apply_subset A'.property
  have hBs := tsupport_differentialOperators_section_apply_subset B.property
  have hAA's := tsupport_differentialOperators_section_apply_subset
    (comp_mem_differentialOperators A.property A'.property)
  have hB'Bs := tsupport_differentialOperators_section_apply_subset
    (comp_mem_differentialOperators B'.property B.property)
  rw [coe_sectionHodgeLaplacian]
  exact (hA.comp hA.symm hA's hA's).add (hB.symm.comp hB hBs hBs) hAA's hB'Bs hAA's hB'Bs

/-! ### Ellipticity -/

/-- At an interior point and a covector `ξ`, the principal symbol of the Laplacian `A A' + B' B`
is bijective exactly when the Laplacian of the principal symbols of `A` and `B`, read as continuous
linear maps, is invertible. -/
private theorem bijective_sectionPrincipalSymbol_sectionHodgeLaplacian_iff
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ)
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ)
    [FiniteDimensional ℝ (U x)] [FiniteDimensional ℝ (V x)] [FiniteDimensional ℝ (W x)] :
    Bijective (sectionPrincipalSymbol I hx (sectionHodgeLaplacian A A' B B') ξ) ↔
      ((LinearMap.toContinuousLinearMap (sectionPrincipalSymbol I hx A ξ)).hodgeLaplacian
        (LinearMap.toContinuousLinearMap (sectionPrincipalSymbol I hx B ξ))).IsInvertible := by
  rw [ContinuousLinearMap.isInvertible_iff_bijective, sectionPrincipalSymbol_sectionHodgeLaplacian,
    hA.sectionPrincipalSymbol_eq_smul_adjoint, hB.sectionPrincipalSymbol_eq_smul_adjoint,
    ← LinearMap.bijective_smul_iff (isUnit_neg_one.pow m : IsUnit ((-1 : ℝ) ^ m))]
  congr! 1
  ext v
  simp [smul_smul, ← pow_add, ← two_mul, pow_mul]

/-- **Exact symbol sequences give elliptic Laplacians.** If `A'` and `B'` are formal adjoints of
`A` and `B`, and the symbol sequence `σ(A)(ξ)`, `σ(B)(ξ)` is exact at every nonzero covector `ξ`
at `x`, then the Laplacian `A A' + B' B` is elliptic at `x`. -/
theorem isSectionEllipticAt_sectionHodgeLaplacian
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ)
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (h : ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
      Exact (sectionPrincipalSymbol I hx A ξ) (sectionPrincipalSymbol I hx B ξ)) :
    IsSectionEllipticAt (sectionHodgeLaplacian A A' B B') x := by
  refine isSectionEllipticAt_iff.2 fun hx ξ hξ ↦ ?_
  have := VectorBundle.finiteDimensional ℝ F'' U x
  have := VectorBundle.finiteDimensional ℝ F V x
  have := VectorBundle.finiteDimensional ℝ F' W x
  have hex := h hx ξ hξ
  rw [bijective_sectionPrincipalSymbol_sectionHodgeLaplacian_iff hA hB,
    ← ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian]
  · simpa using hex
  · rw [← LinearMap.toContinuousLinearMap_comp, hex.linearMap_comp_eq_zero, map_zero]

/-- **A complex is elliptic exactly when its Laplacian is.** If `B A = 0` and `A'` and `B'` are
formal adjoints of `A` and `B`, then the Laplacian `A A' + B' B` is elliptic at `x` exactly when the
symbol sequence `σ(A)(ξ)`, `σ(B)(ξ)` is exact at every nonzero covector `ξ` at `x`. -/
theorem isSectionEllipticAt_sectionHodgeLaplacian_iff
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ)
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (hBA : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∘ₗ
      (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) = 0) :
    IsSectionEllipticAt (sectionHodgeLaplacian A A' B B') x ↔
      ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
        Exact (sectionPrincipalSymbol I hx A ξ) (sectionPrincipalSymbol I hx B ξ) := by
  refine ⟨fun h hx ξ hξ ↦ ?_, isSectionEllipticAt_sectionHodgeLaplacian hA hB⟩
  -- The symbol of the Laplacian is bijective, and the symbol sequence is a complex.
  have := VectorBundle.finiteDimensional ℝ F'' U x
  have := VectorBundle.finiteDimensional ℝ F V x
  have := VectorBundle.finiteDimensional ℝ F' W x
  have hc := sectionPrincipalSymbol_comp_sectionPrincipalSymbol_eq_zero hx hBA ξ
  have hΔ := (bijective_sectionPrincipalSymbol_sectionHodgeLaplacian_iff hA hB hx ξ).1
    (h.sectionPrincipalSymbol_bijective hx hξ)
  rw [← ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian] at hΔ
  · simpa using hΔ
  · rw [← LinearMap.toContinuousLinearMap_comp, hc, map_zero]

/-- **A complex is elliptic exactly when its Laplacian is.** If `B A = 0` and `A'` and `B'` are
formal adjoints of `A` and `B`, then the Laplacian `A A' + B' B` is elliptic exactly when the symbol
sequence `σ(A)(ξ)`, `σ(B)(ξ)` is exact at every nonzero covector `ξ` at every interior point. -/
theorem isSectionElliptic_sectionHodgeLaplacian_iff
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ)
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (hBA : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∘ₗ
      (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) = 0) :
    IsSectionElliptic (sectionHodgeLaplacian A A' B B') ↔
      ∀ (x : M) (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
        Exact (sectionPrincipalSymbol I hx A ξ) (sectionPrincipalSymbol I hx B ξ) :=
  isSectionElliptic_iff.trans <|
    forall_congr' fun _ ↦ isSectionEllipticAt_sectionHodgeLaplacian_iff hA hB hBA

/-! ### The two ends of a complex -/

omit [IsContinuousRiemannianBundle F'' U] in
/-- **The Laplacian at the start of a complex.** If `B'` is a formal adjoint of
`B : Γ(V) → Γ(W)`, then `B' B` is elliptic at `x` exactly when `σ(B)(ξ)` is injective at every
nonzero covector `ξ` at `x`. This is the Laplacian at the first bundle of a finite complex. -/
theorem isSectionEllipticAt_adjoint_comp_iff
    (hB : (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ) :
    IsSectionEllipticAt (⟨(B' : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ
        (B : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          comp_mem_differentialOperators B'.property B.property⟩ :
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ (m + m)) x ↔
      ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
        Injective (sectionPrincipalSymbol I hx B ξ) := by
  refine isSectionEllipticAt_iff.trans (forall₂_congr fun hx ξ ↦ imp_congr_right fun _ ↦ ?_)
  have := VectorBundle.finiteDimensional ℝ F V x
  have := VectorBundle.finiteDimensional ℝ F' W x
  -- The symbol of `B' B` is `(-1) ^ m b† b`, where `b` is the symbol of `B`.
  rw [sectionPrincipalSymbol_comp, hB.sectionPrincipalSymbol_eq_smul_adjoint, LinearMap.smul_comp,
    LinearMap.bijective_smul_iff (isUnit_neg_one.pow m)]
  simpa [ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.coe_comp] using
    ContinuousLinearMap.isUnit_adjoint_comp_self_iff
      (LinearMap.toContinuousLinearMap (sectionPrincipalSymbol I hx B ξ))

/-- **The Laplacian at the end of a complex.** If `A'` is a formal adjoint of
`A : Γ(U) → Γ(V)`, then `A A'` is elliptic at `x` exactly when `σ(A)(ξ)` is surjective at every
nonzero covector `ξ` at `x`. This is the Laplacian at the last bundle of a finite complex. -/
theorem isSectionEllipticAt_comp_adjoint_iff
    (hA : (A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) μ) :
    IsSectionEllipticAt (⟨(A : Cₛ^∞⟮I; F'', U⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ
        (A' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯),
          comp_mem_differentialOperators A.property A'.property⟩ :
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ (m + m)) x ↔
      ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
        Surjective (sectionPrincipalSymbol I hx A ξ) := by
  -- `A` is a formal adjoint of `A'`, so this is the previous statement for `A'`, and the symbol of
  -- `A'` is `(-1) ^ m` times the adjoint of that of `A`, injective exactly when the latter is onto.
  refine (isSectionEllipticAt_adjoint_comp_iff hA.symm).trans
    (forall₂_congr fun hx ξ ↦ imp_congr_right fun _ ↦ ?_)
  have := VectorBundle.finiteDimensional ℝ F'' U x
  have := VectorBundle.finiteDimensional ℝ F V x
  rw [hA.sectionPrincipalSymbol_eq_smul_adjoint, ← LinearMap.ker_eq_bot,
    LinearMap.ker_smul _ _ (pow_ne_zero m (neg_ne_zero.2 one_ne_zero)), LinearMap.ker_eq_bot,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.adjoint_injective_iff_denseRange,
    LinearMap.coe_toContinuousLinearMap']
  exact ⟨LinearMap.surjective_of_denseRange, Surjective.denseRange⟩

/-! ### The folded operator of a two-periodic complex -/

omit [IsContinuousRiemannianBundle F'' U] in
/-- **The folded operator of a complex is elliptic exactly when the complex is.** Let
`A : Γ(V) → Γ(W)` and `B : Γ(W) → Γ(V)` be differential operators of order at most `m` with
`A B = 0` and `B A = 0`, and let `B'` be a formal adjoint of `B`. Then the folded operator
`A + B'` is elliptic at `x` exactly when the two-periodic symbol sequence `σ(A)(ξ)`, `σ(B)(ξ)` is
exact at `V` and at `W` at every nonzero covector `ξ` at `x`. -/
theorem isSectionEllipticAt_add_adjoint_iff
    {A : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
    {B : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m}
    {B' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
    (hB : (B : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯).IsFormalAdjoint
      (B' : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) μ)
    (hAB : (A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∘ₗ
      (B : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) = 0)
    (hBA : (B : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) ∘ₗ
      (A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) = 0) :
    IsSectionEllipticAt (A + B') x ↔
      ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
        Exact (sectionPrincipalSymbol I hx B ξ) (sectionPrincipalSymbol I hx A ξ) ∧
          Exact (sectionPrincipalSymbol I hx A ξ) (sectionPrincipalSymbol I hx B ξ) := by
  refine isSectionEllipticAt_iff.trans (forall₂_congr fun hx ξ ↦ imp_congr_right fun _ ↦ ?_)
  have := VectorBundle.finiteDimensional ℝ F V x
  have := VectorBundle.finiteDimensional ℝ F' W x
  have hc : IsUnit ((-1 : ℝ) ^ m) := isUnit_neg_one.pow m
  set a := LinearMap.toContinuousLinearMap (sectionPrincipalSymbol I hx A ξ)
  set b := LinearMap.toContinuousLinearMap (sectionPrincipalSymbol I hx B ξ)
  -- The symbol of `A + B'` is the folded operator `a + (c b)†` of the complex `a`, `c b`, where
  -- `c = (-1) ^ m`; rescaling `b` by `c` changes neither its kernel nor its range.
  have hσ : ⇑(sectionPrincipalSymbol I hx (A + B') ξ) =
      ⇑(a + ContinuousLinearMap.adjoint (((-1 : ℝ) ^ m) • b)) := by
    rw [sectionPrincipalSymbol_add, hB.sectionPrincipalSymbol_eq_smul_adjoint]
    ext v
    simp [a, b]
  have hab : a ∘L (((-1 : ℝ) ^ m) • b) = 0 := by
    rw [ContinuousLinearMap.comp_smul, ← LinearMap.toContinuousLinearMap_comp,
      sectionPrincipalSymbol_comp_sectionPrincipalSymbol_eq_zero hx hAB ξ, map_zero, smul_zero]
  have hba : (((-1 : ℝ) ^ m) • b) ∘L a = 0 := by
    rw [ContinuousLinearMap.smul_comp, ← LinearMap.toContinuousLinearMap_comp,
      sectionPrincipalSymbol_comp_sectionPrincipalSymbol_eq_zero hx hBA ξ, map_zero, smul_zero]
  rw [hσ, ContinuousLinearMap.bijective_add_adjoint_iff hab hba
    (Submodule.isClosed_of_finiteDimensional _) (Submodule.isClosed_of_finiteDimensional _),
    ← LinearMap.exact_smul_left_iff hc _ (sectionPrincipalSymbol I hx A ξ),
    ← LinearMap.exact_smul_right_iff hc (sectionPrincipalSymbol I hx A ξ)]
  simp [a, b]

end Metric

end TauCeti
