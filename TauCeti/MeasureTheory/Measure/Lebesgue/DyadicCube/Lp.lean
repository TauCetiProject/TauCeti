/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.DenseSpan
public import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube

/-!
# Dyadic step functions are dense in Bochner `Lᵖ(ℝⁿ; E)`

For `1 ≤ p < ∞` and a normed space `E`, the indicator classes `𝟙_Q c` of the dyadic cubes `Q`
of `ι → ℝ`, `ι` finite, with constants `c ∈ E`, span a dense subspace of the Bochner space
`Lᵖ(ℝⁿ; E)` for Lebesgue measure
(`TauCeti.topologicalClosure_span_indicatorConstLp_dyadicCube_eq_top`). Thus finite sums
`∑ⱼ 𝟙_{Qⱼ} cⱼ` over dyadic cubes, and a fortiori over bounded axis-parallel cubes or boxes,
approximate every function of `Lᵖ(ℝⁿ; E)`. The constants may be restricted to any subset of `E`
with dense span.

The dyadic cubes form a π-system generating the Borel σ-algebra, and the cubes of level zero
cover the space by countably many sets of finite measure, so this is an instance of
`IsPiSystem.topologicalClosure_span_indicatorConstLp_eq_top`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, Lemma 1.2.19.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι 𝕜 E : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Let `1 ≤ p < ∞` and let `D ⊆ E` have dense span. The indicator classes `𝟙_Q c` of the dyadic
cubes `Q` of `ι → ℝ`, `ι` finite, with `c ∈ D`, span a dense subspace of the Bochner space
`Lᵖ(ℝⁿ; E)` for Lebesgue measure. -/
theorem topologicalClosure_span_indicatorConstLp_dyadicCube_eq_top (hp : p ≠ ∞) {D : Set E}
    (hD : (Submodule.span 𝕜 D).topologicalClosure = ⊤) :
    (Submodule.span 𝕜 {f : Lp E p (volume : Measure (ι → ℝ)) | ∃ (k : ℤ) (m : ι → ℤ), ∃ c ∈ D,
      indicatorConstLp p (measurableSet_dyadicCube k m) (volume_dyadicCube_ne_top k m) c = f}
      ).topologicalClosure = ⊤ := by
  -- the cubes of level zero, enumerated, cover `ι → ℝ` by countably many sets of finite volume
  obtain ⟨e, he⟩ := exists_surjective_nat (ι → ℤ)
  have S : (volume : Measure (ι → ℝ)).FiniteSpanningSetsIn
      {s : Set (ι → ℝ) | ∃ k m, dyadicCube k m = s} :=
    { set := fun n ↦ dyadicCube 0 (e n)
      set_mem := fun n ↦ ⟨0, e n, rfl⟩
      finite := fun n ↦ (volume_dyadicCube_ne_top 0 (e n)).lt_top
      spanning := eq_univ_of_forall fun x ↦ by
        obtain ⟨n, hn⟩ := he (dyadicIndex 0 x)
        exact mem_iUnion.2 ⟨n, hn ▸ mem_dyadicCube_dyadicIndex 0 x⟩ }
  have hset : {f : Lp E p (volume : Measure (ι → ℝ)) | ∃ (k : ℤ) (m : ι → ℤ), ∃ c ∈ D,
      indicatorConstLp p (measurableSet_dyadicCube k m) (volume_dyadicCube_ne_top k m) c = f} =
      {f | ∃ s ∈ {s : Set (ι → ℝ) | ∃ k m, dyadicCube k m = s}, ∃ (hs : MeasurableSet s)
        (hμs : volume s ≠ ∞), ∃ c ∈ D, indicatorConstLp p hs hμs c = f} := by
    ext f
    constructor
    · rintro ⟨k, m, c, hc, rfl⟩
      exact ⟨_, ⟨k, m, rfl⟩, _, _, c, hc, rfl⟩
    · rintro ⟨_, ⟨k, m, rfl⟩, _, _, c, hc, rfl⟩
      exact ⟨k, m, c, hc, rfl⟩
  rw [hset]
  exact isPiSystem_dyadicCube.topologicalClosure_span_indicatorConstLp_eq_top
    generateFrom_dyadicCube.symm S hp hD

end TauCeti
