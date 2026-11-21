/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Multiplication.Basic
public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel

/-!
# Multiplication von Neumann algebras of standard Borel probability spaces

Every atomless standard Borel probability space `(Ω, μ)` has multiplication von Neumann algebra
unitarily conjugate to `VonNeumannAlgebra.multiplicationAlgebra (volume : Measure unitInterval)`
(`VonNeumannAlgebra.exists_linearIsometryEquiv_conj_multiplicationAlgebra_unitInterval`).

## References

* M. Takesaki, *Theory of Operator Algebras I*, Springer, 2002, Chapter III, §1.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Academic Press, 1983, Example 5.1.6.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace VonNeumannAlgebra

/-- For any atomless standard Borel probability space `(Ω, μ)`, there exists a unitary equivalence
`U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure unitInterval)` conjugating `multiplicationAlgebra μ`
onto `multiplicationAlgebra (volume : Measure unitInterval)`. -/
theorem exists_linearIsometryEquiv_conj_multiplicationAlgebra_unitInterval
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure I),
      (multiplicationAlgebra μ).conj U = multiplicationAlgebra (volume : Measure I) := by
  obtain ⟨f, g, hf, hg, hgf, _⟩ := Measure.exists_mpModNull_equiv_unitInterval μ
  exact ⟨Lp.compMeasurePreservingₗᵢEquiv ℂ (E := ℂ) (p := 2) hg hf hgf,
    conj_multiplicationAlgebra_compMeasurePreservingₗᵢEquiv hg hf hgf⟩

end VonNeumannAlgebra
