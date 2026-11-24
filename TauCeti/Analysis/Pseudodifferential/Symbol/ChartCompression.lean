/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression

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

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1 and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
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

end TauCeti.ClassicalSymbol
