/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Differential operators on manifolds as pseudodifferential operators in charts

Let `M` be a manifold modelled on `ℝⁿ`, and let `D` be a differential operator of order at most `m`
on the smooth real functions on `M`, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`), with no continuity assumed. For a chart
`e` of the maximal smooth atlas and cutoffs `φ`, `ψ` with compact supports in the chart target, the
chart compression `f ↦ φ · (D ((ψ f) ∘ e)) ∘ e⁻¹`
(`OpenPartialHomeomorph.chartCompressionDifferentialOperators`) is a differential operator of order
at most `m` on `ℝⁿ`. Its classical symbol `TauCeti.ClassicalSymbol.ofDifferentialOperator` is the
polynomial `∑_{|α| ≤ m} c_α(x) (i ξ)^α` in the coefficients of the compression in the coordinates of
the chart. This file shows:

* `TauCeti.ClassicalSymbol.map_quantizeSchwartzValue_ofDifferentialOperator_chartCompression` and
  `TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_chartCompression`: on
  Schwartz input `u`, the quantization of this symbol is exactly the chart compression of `D`
  applied to `u`, componentwise for vector-valued `u` and through the real and imaginary parts for
  complex-valued `u`. There is no smoothing remainder.
* `hasCompactSpatialSupport_toSymbol_ofDifferentialOperator_chartCompression` (in the namespace
  `TauCeti.ClassicalSymbol`): the symbol vanishes at positions outside the support of `φ`, so it
  has compact spatial support, and hence its estimates are uniform in the position
  (`TauCeti.Symbol.HasCompactSpatialSupport.isUniform`).
* `TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialOperator_chartCompression`: at a
  point `x` of the chart target and a nonzero frequency `ξ`, its principal symbol is
  `i ^ m φ(x) ψ(x) σ(D)(e⁻¹ x)(⟪ξ, ·⟫ ∘ de)`, where `σ(D)` is the geometric principal symbol of
  `D` on the cotangent bundle of `M` (`TauCeti.smoothPrincipalSymbol`), read through the
  differential `de` of the chart. This is the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`.

So in every chart a differential operator on a manifold is exactly the quantization of a classical
symbol of order `m` with compact spatial support, and the principal symbols in all charts are read
from the single geometric principal symbol of `D`. Only the local symbol estimates enter: the
coefficients of `D` on a noncompact manifold need not be bounded.

The same holds for a differential operator `P : Γ(V₁) → Γ(V₂)` between vector bundles, read in a
chart and in frames `t₁`, `t₂` over the chart source. Along vectors `vⱼ` of the model fibre of `V₁`
and functionals `ℓᵢ` on that of `V₂`, the entries of its chart compression
(`OpenPartialHomeomorph.sectionChartCompressionDifferentialOperators`) are scalar differential
operators, and their matrix has the matrix-valued classical symbol
`TauCeti.ClassicalSymbol.ofDifferentialOperatorMatrix`. In the namespace `TauCeti.ClassicalSymbol`:

* `map_quantizeSchwartzValue_ofDifferentialOperatorMatrix_sectionChartCompression`: on Schwartz
  input, its quantization is exactly the chart compression of `P`;
* `hasCompactSpatialSupport_toSymbol_ofDifferentialOperatorMatrix_sectionChartCompression`: the
  symbol vanishes at positions outside the support of `φ`;
* `coefficient_principal_ofDifferentialOperatorMatrix_sectionChartCompression`: at a point `x` of
  the chart target and a nonzero frequency `ξ`, the entries of its principal symbol are
  `i ^ m φ(x) ψ(x)` times those of the geometric principal symbol `σ(P)` of `P`
  (`TauCeti.sectionPrincipalSymbol`) at `e⁻¹ x` and the covector `⟪ξ, ·⟫ ∘ de`, read in the frames;
* `isInvertible_coefficient_principal_ofDifferentialOperatorMatrix_sectionChartCompression`: hence,
  along bases of the model fibres, if `P` is elliptic at `e⁻¹ x` (`TauCeti.IsSectionEllipticAt`)
  and neither cutoff vanishes at `x`, the principal symbol is invertible at `x` and every nonzero
  frequency.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1 and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2.
-/

public section

noncomputable section

open scoped ContDiff Manifold Distributions SchwartzMap RealInnerProductSpace

namespace TauCeti.ClassicalSymbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {m : ℕ}
  (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m)

/-- **Differential operators on manifolds are pseudodifferential operators in charts.** On
Schwartz input `u`, the quantization of the classical symbol of the chart compression of `D` is the
chart compression of `D` acting on `V`-valued functions componentwise: for every real-linear
functional `ℓ` on `V`, its image under `ℓ` at `x` is `φ(x) D((ψ (ℓ ∘ u)) ∘ e)(e⁻¹ x)`. -/
theorem map_quantizeSchwartzValue_ofDifferentialOperator_chartCompression [CompleteSpace V]
    (ℓ : V →L[ℝ] ℝ) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    ℓ (quantizeSchwartzValue (ofDifferentialOperator V
        (e.chartCompressionDifferentialOperators he φ ψ m D)).toSymbol.coefficient u x) =
      φ x * D.val (e.cutoffPullback he ψ
        ⟨fun y ↦ ℓ (u y), (ℓ.contDiff.comp (u.smooth ⊤)).contMDiff⟩) (e.symm x) :=
  (map_quantizeSchwartzValue_ofDifferentialOperator _ ℓ u x).trans
    (e.chartCompressionDifferentialOperators_apply he φ ψ D _ x)

/-- **Scalar differential operators on manifolds are pseudodifferential operators in charts.**
On complex-valued Schwartz input `u`, the quantization of the classical symbol of the chart
compression of `D` is the chart compression of `D` applied separately to the real and imaginary
parts of `u`. -/
theorem quantizeSchwartzValue_ofDifferentialOperator_chartCompression
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialOperator ℂ
        (e.chartCompressionDifferentialOperators he φ ψ m D)).toSymbol.coefficient u x =
      φ x * (D.val (e.cutoffPullback he ψ
          ⟨fun y ↦ (u y).re, (Complex.reCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩) (e.symm x) +
        D.val (e.cutoffPullback he ψ
          ⟨fun y ↦ (u y).im, (Complex.imCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩) (e.symm x) *
          Complex.I) := by
  refine Complex.ext ?_ ?_
  · simpa using map_quantizeSchwartzValue_ofDifferentialOperator_chartCompression he φ ψ D
      Complex.reCLM u x
  · simpa using map_quantizeSchwartzValue_ofDifferentialOperator_chartCompression he φ ψ D
      Complex.imCLM u x

/-- The classical symbol of the chart compression of `D` vanishes at the positions outside the
support of the cutoff `φ`, so it has compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol_ofDifferentialOperator_chartCompression :
    (ofDifferentialOperator V
      (e.chartCompressionDifferentialOperators he φ ψ m D)).toSymbol.HasCompactSpatialSupport :=
  hasCompactSpatialSupport_toSymbol_ofDifferentialOperator _ φ.hasCompactSupport fun x hx f ↦
    (e.chartCompressionDifferentialOperators_apply he φ ψ D f x).trans <| by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- **The principal symbol of a differential operator in a chart.** At a point `x` of the chart
target and a nonzero frequency `ξ`, the principal symbol of the classical symbol of the chart
compression of `D` is `i ^ m φ(x) ψ(x)` times the geometric principal symbol of `D` at `e⁻¹ x`,
at the covector `⟪ξ, ·⟫ ∘ de` obtained by composing with the differential of the chart. -/
theorem coefficient_principal_ofDifferentialOperator_chartCompression
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {x : CoordinateSpace n} (hx : x ∈ e.target)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialOperator V
        (e.chartCompressionDifferentialOperators he φ ψ m D)).principal.coefficient (x, ξ) =
      (Complex.I ^ m * ((φ x * ψ x * smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
        (x := e.symm x) BoundarylessManifold.isInteriorPoint D
          ((innerSL ℝ ξ).comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e
            (e.symm x))) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_principal_ofDifferentialOperator _ hξ]
  exact congrArg (fun t : ℝ ↦ (Complex.I ^ m * (t : ℂ)) • ContinuousLinearMap.id ℂ V)
    (e.smoothPrincipalSymbol_chartCompressionDifferentialOperators he φ ψ D hx (innerSL ℝ ξ))

/-! ### Differential operators between vector bundles -/

section Section

open Bundle

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ 𝓘(ℝ, CoordinateSpace n)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, CoordinateSpace n)]
  (t₁ : Trivialization F₁ (π F₁ V₁)) [MemTrivializationAtlas t₁] (h₁ : e.source ⊆ t₁.baseSet)
  (t₂ : Trivialization F₂ (π F₂ V₂)) [MemTrivializationAtlas t₂] (h₂ : e.source ⊆ t₂.baseSet)
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (P : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
    Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F₁, V₁⟯ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); F₂, V₂⟯ m)

/-- **Differential operators between bundles are pseudodifferential operators in charts.** Read a
differential operator `P : Γ(V₁) → Γ(V₂)` in a chart and in frames `t₁`, `t₂` over the chart source,
along vectors `vⱼ` of the model fibre of `V₁` and functionals `ℓᵢ` on that of `V₂`. On Schwartz
input `u` with values in `ℂ^ι`, the quantization of the classical symbol of this matrix of
compressions is the compression of `P`: for every real-linear functional `ℓ'` on `ℂ`, such as the
real or the imaginary part, the image under `ℓ'` of its `i`-th component at `x` is
`φ(x) ℓᵢ (t₂ (P s) (e⁻¹ x))`, where `s` is the section with frame coefficients
`∑ⱼ (ψ (ℓ' ∘ uⱼ)) • vⱼ` in the chart. -/
theorem map_quantizeSchwartzValue_ofDifferentialOperatorMatrix_sectionChartCompression
    (ℓ : κ → F₂ →L[ℝ] ℝ) (v : ι → F₁) (ℓ' : ℂ →L[ℝ] ℝ) (u : 𝓢(CoordinateSpace n, ι → ℂ))
    (x : CoordinateSpace n) (i : κ) :
    ℓ' (quantizeSchwartzValue (ofDifferentialOperatorMatrix fun i j ↦
        e.sectionChartCompressionDifferentialOperators he t₁ h₁ t₂ h₂ φ ψ (ℓ i) (v j) m P
        ).toSymbol.coefficient u x i) =
      φ x * ℓ i (t₂.continuousLinearMapAt ℝ (e.symm x) (P.val (∑ j,
        e.sectionCutoffPullback he t₁ h₁ ψ (v j) ⟨fun y ↦ ℓ' (u y j), (ℓ'.contDiff.comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℂ) j).contDiff.comp
            (u.smooth ⊤))).contMDiff⟩) (e.symm x))) := by
  simp only [map_quantizeSchwartzValue_ofDifferentialOperatorMatrix, map_sum,
    ContMDiffSection.coe_sum, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦
    e.sectionChartCompressionDifferentialOperators_apply he t₁ h₁ t₂ h₂ φ ψ _ _ P _ x

/-- The classical symbol of the matrix of compressions of `P` vanishes at positions outside the
support of the cutoff `φ`, so it has compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol_ofDifferentialOperatorMatrix_sectionChartCompression
    (ℓ : κ → F₂ →L[ℝ] ℝ) (v : ι → F₁) :
    (ofDifferentialOperatorMatrix fun i j ↦
      e.sectionChartCompressionDifferentialOperators he t₁ h₁ t₂ h₂ φ ψ (ℓ i) (v j) m P
      ).toSymbol.HasCompactSpatialSupport :=
  hasCompactSpatialSupport_toSymbol_ofDifferentialOperatorMatrix _ φ.hasCompactSupport
    fun x hx i j f ↦
      (e.sectionChartCompressionDifferentialOperators_apply he t₁ h₁ t₂ h₂ φ ψ _ _ P f x).trans <|
        by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [FiniteDimensional ℝ F₁]

/-- **The principal symbol of a differential operator between bundles in a chart.** At a point
`x` of the chart target and a nonzero frequency `ξ`, the `(i, j)` entry of the principal symbol of
the classical symbol of the matrix of compressions of `P` is `i ^ m φ(x) ψ(x)` times the coefficient
along `ℓᵢ`, in the frame `t₂`, of the geometric principal symbol of `P` at `e⁻¹ x`, at the covector
`⟪ξ, ·⟫ ∘ de`, applied to the vector with coefficients `vⱼ` in the frame `t₁`. -/
theorem coefficient_principal_ofDifferentialOperatorMatrix_sectionChartCompression
    (ℓ : κ → F₂ →L[ℝ] ℝ) (v : ι → F₁) {x : CoordinateSpace n} (hx : x ∈ e.target)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) (u : ι → ℂ) (i : κ) :
    (ofDifferentialOperatorMatrix fun i j ↦
        e.sectionChartCompressionDifferentialOperators he t₁ h₁ t₂ h₂ φ ψ (ℓ i) (v j) m P
        ).principal.coefficient (x, ξ) u i =
      ∑ j, Complex.I ^ m * ((φ x * ψ x * ℓ i (t₂.continuousLinearMapAt ℝ (e.symm x)
        (sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := e.symm x)
          BoundarylessManifold.isInteriorPoint P ((innerSL ℝ ξ).comp
            (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e (e.symm x)))
          (t₁.symmL ℝ (e.symm x) (v j)))) : ℝ) : ℂ) * u j := by
  rw [coefficient_principal_ofDifferentialOperatorMatrix _ hξ]
  -- The covector `⟪ξ, ·⟫` is a cotangent vector at `x`, as in
  -- `coefficient_principal_ofDifferentialOperator_chartCompression`.
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (fun t : ℝ ↦ Complex.I ^ m * (t : ℂ) * u j)
    (OpenPartialHomeomorph.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators
      he t₁ h₁ t₂ h₂ φ ψ (ℓ i) (v j) P hx (innerSL ℝ ξ))

/-- **Ellipticity in charts.** Let `P : Γ(V₁) → Γ(V₂)` be elliptic at the point `e⁻¹ x` of the
chart source, and let the cutoffs `φ` and `ψ` not vanish at `x`. Read `P` in the chart and in
frames along a basis `b₁` of the model fibre of `V₁` and the coordinate functionals of a basis
`b₂` of that of `V₂`. Then the principal symbol of the classical symbol of this matrix of
compressions is invertible at `x` and at every nonzero frequency. -/
theorem isInvertible_coefficient_principal_ofDifferentialOperatorMatrix_sectionChartCompression
    [FiniteDimensional ℝ F₂] (b₁ : Module.Basis ι ℝ F₁) (b₂ : Module.Basis κ ℝ F₂)
    {x : CoordinateSpace n} (hx : x ∈ e.target) (hφ : φ x ≠ 0) (hψ : ψ x ≠ 0)
    (hP : IsSectionEllipticAt P (e.symm x)) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((ofDifferentialOperatorMatrix fun i j ↦
        e.sectionChartCompressionDifferentialOperators he t₁ h₁ t₂ h₂ φ ψ
          (LinearMap.toContinuousLinearMap (b₂.coord i)) (b₁ j) m P
        ).principal.coefficient (x, ξ)).IsInvertible := by
  classical
  have hy : e.symm x ∈ e.source := e.map_target hx
  -- The covector `⟪ξ, ·⟫ ∘ de` is nonzero, since the differential of the chart is invertible.
  set ζ : TangentSpace 𝓘(ℝ, CoordinateSpace n) (e.symm x) →L[ℝ] ℝ :=
    (innerSL ℝ ξ).comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e (e.symm x))
    with hζ_def
  have hζ : ζ ≠ 0 := by
    obtain ⟨w, hw⟩ := (isInvertible_mfderiv_chart
      (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy).surjective ξ
    have h2 : ζ w = innerSL ℝ ξ ξ := congrArg (innerSL ℝ ξ) hw
    intro h
    rw [h, zero_apply, innerSL_apply_apply, eq_comm,
      inner_self_eq_zero] at h2
    exact hξ h2
  -- The principal symbol of `P` at `ζ`, read in the frames, is a linear equivalence `T`.
  have hσ := hP.sectionPrincipalSymbol_bijective BoundarylessManifold.isInteriorPoint hζ
  set T : F₁ ≃ₗ[ℝ] F₂ := (t₁.linearEquivAt ℝ (e.symm x) (h₁ hy)).symm ≪≫ₗ
    LinearEquiv.ofBijective _ hσ ≪≫ₗ t₂.linearEquivAt ℝ (e.symm x) (h₂ hy)
  -- An operator which is a nonzero multiple `c` of the complex image `Am` of the matrix of `T` is
  -- invertible, since `Am` has the complex image `N` of the matrix of `T.symm` as inverse.
  set Am := (LinearMap.toMatrix b₁ b₂ T.toLinearMap).map Complex.ofRealHom
  set N := (LinearMap.toMatrix b₂ b₁ T.symm.toLinearMap).map Complex.ofRealHom
  have hAN : Am * N = 1 := T.map_toMatrix_mul_map_toMatrix_symm b₁ b₂ Complex.ofRealHom
  have hNA : N * Am = 1 := T.symm.map_toMatrix_mul_map_toMatrix_symm b₂ b₁ Complex.ofRealHom
  have key {A : (ι → ℂ) →L[ℂ] (κ → ℂ)} (c : ℂ) (hc : c ≠ 0) (hA : ∀ u, A u = c • Am.mulVec u) :
      A.IsInvertible := by
    refine .of_inverse (g := c⁻¹ • LinearMap.toContinuousLinearMap (Matrix.toLin' N)) ?_ ?_
    · ext1 u
      simp [hA, Matrix.mulVec_mulVec, hAN, smul_smul, hc]
    · ext1 u
      simp [hA, Matrix.mulVec_mulVec, hNA, smul_smul, hc]
  refine key (Complex.I ^ m * (φ x * ψ x : ℝ))
    (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (by exact_mod_cast mul_ne_zero hφ hψ))
    fun u ↦ funext fun i ↦ ?_
  have hsum : ((Complex.I ^ m * (φ x * ψ x : ℝ)) • Am.mulVec u) i =
      ∑ j, Complex.I ^ m * (φ x * ψ x : ℝ) * (b₂.coord i (T (b₁ j)) : ℂ) * u j := by
    simp [Am, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, LinearMap.toMatrix_apply]
  rw [hsum, coefficient_principal_ofDifferentialOperatorMatrix_sectionChartCompression he φ ψ t₁ h₁
    t₂ h₂ P _ _ hx hξ, ← hζ_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hT : t₂.continuousLinearMapAt ℝ (e.symm x) (sectionPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
      BoundarylessManifold.isInteriorPoint P ζ (t₁.symmL ℝ (e.symm x) (b₁ j))) = T (b₁ j) := by
    simp [T, Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_symm_apply,
      t₁.symmL_apply (R := ℝ) (h₁ hy), t₂.coe_linearMapAt_of_mem (h₂ hy)]
  rw [hT]
  simp only [LinearMap.coe_toContinuousLinearMap', Complex.ofReal_mul]
  ring

end Section

end TauCeti.ClassicalSymbol
