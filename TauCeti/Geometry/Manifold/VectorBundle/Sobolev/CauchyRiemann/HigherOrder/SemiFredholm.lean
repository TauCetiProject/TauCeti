/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Estimate
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Perturbation
public import TauCeti.Analysis.Normed.Operator.Compact.Estimate

/-!
# The higher-order elliptic estimate for real Cauchy–Riemann operators with rough coefficients

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with a finite
bundle atlas `A` (so `M` is compact). Let `D = D₀ + α` be a real Cauchy–Riemann operator of class
`W^{k+1,p}`, `p > 2`: `D₀` is smooth and `α` is a `W^{k+1,p}` zeroth-order term. For `1 < q ≤ p`,
this file proves the elliptic estimate for its realization
`TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL :
W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)` at the top order of McDuff–Salamon, Theorem C.1.10:

`‖ξ‖_{W^{k+2,q}} ≤ C (‖(D₀ + α) ξ‖_{W^{k+1,q}} + ‖ξ‖_{L^q})`

(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_perturbedSobolevSuccL_add_norm`), and
deduces that this realization has finite-dimensional kernel and closed range. The case of order
one, `α ∈ L^p` on `W^{1,q}`, is
`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_perturbedSobolevL_add_norm`.

## The argument

The estimate for `D₀`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`) has the error
term `‖ξ‖_{L^q}`, a compact operator of `ξ` by Rellich's theorem
(`TauCeti.SobolevSection.isCompactOperator_lowerToZeroL`). The rough term `ξ ↦ (α ξ)^{0,1}` is
compact (`TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbedSobolevSuccL_sub`), so
`D₀ + α` satisfies an estimate with a compact error
(`ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub`). The rough term is not
small and cannot be absorbed. Instead, the compact error is replaced by the `L^q` norm, which is a
norm on the kernel of `D₀ + α`
(`ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate`). Peetre's lemma
gives finite-dimensional kernel and closed range from the compact-error estimate.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_perturbedSobolevSuccL_add_norm`: the
  elliptic estimate for `D₀ + α` on `W^{k+2,q}`.
* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_perturbedSobolevSuccL`,
  `TauCeti.IsRealCauchyRiemannOperator.isClosed_range_perturbedSobolevSuccL`: the realization of
  `D₀ + α` on `W^{k+2,q}` has finite-dimensional kernel and closed range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Definition C.1.5, Theorem C.1.10 and its proof in
  Appendix C.2 (Theorem C.2.3 and Lemma C.2.2).
* J. Peetre, *Another approach to elliptic boundary problems*, Comm. Pure Appl. Math. 14 (1961),
  711–731.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannHigherOrderSemiFredholm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (k : ℕ)

namespace IsRealCauchyRiemannOperator

/-
As in `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.SemiFredholm`, the abstract
estimates are applied with their type arguments, operators and constant named, and only then to
the compactness and estimate hypotheses, so that instance search on the Sobolev section spaces runs
first.
-/

include hD hDs in
/-- The elliptic estimate for a smooth real Cauchy–Riemann operator at order `k + 2`, with its
`L^q` error term written as a compact operator, the Rellich inclusion `W^{k+2,q} → L^q` rescaled
by a constant. -/
private theorem exists_compact_estimate_sobolevSuccL (hq : 1 < q) :
    ∃ (C : ℝ) (K : SobolevSection A volume q (k + 1 + 1) →L[ℝ] SobolevSection A volume q 0),
      IsCompactOperator K ∧ ∀ w, ‖w‖ ≤ C * ‖hD.sobolevSuccL A hDs volume q (k + 1) w‖ + ‖K w‖ := by
  obtain ⟨C, hC⟩ := hD.exists_norm_le_norm_sobolevSuccL_add_norm A hDs (p := (q : ℝ≥0∞))
    (by exact_mod_cast hq) ENNReal.coe_ne_top (k + 1)
  exact ContinuousLinearMap.exists_compact_estimate_of_norm_le_mul_add_norm (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := SobolevSection A volume q 0) (C := C) (T := hD.sobolevSuccL A hDs volume q (k + 1))
    (K := A.sectionChartData.lowerToZeroL volume q (k + 1 + 1))
    (SobolevSection.isCompactOperator_lowerToZeroL A volume q (k + 1)) hC

include hD hDs in
/-- The elliptic estimate for `D₀ + α` at order `k + 2` with a compact error term: the estimate
for `D₀`, whose compact error is the Rellich inclusion, survives the compact perturbation by the
rough term. -/
private theorem exists_compact_estimate_perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    ∃ (C : ℝ) (K : SobolevSection A volume q (k + 1 + 1) →L[ℝ]
        zeroOneSobolevSections A volume q (k + 1) × SobolevSection A volume q 0),
      IsCompactOperator K ∧
        ∀ w, ‖w‖ ≤ C * ‖hD.perturbedSobolevSuccL A hDs k hp hq hqp α w‖ + ‖K w‖ := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_sobolevSuccL A hD hDs k hq
  have hST := hD.isCompactOperator_perturbedSobolevSuccL_sub A hDs k hp hq hqp α
  have h := ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := SobolevSection A volume q 0) (C := C) (T := hD.sobolevSuccL A hDs volume q (k + 1))
    (S := hD.perturbedSobolevSuccL A hDs k hp hq hqp α) (K := K)
  -- `hST` is stated for the pointwise difference, which is the coercion of the operator `S - T`.
  exact h hK hC (by simpa only [FunLike.coe_sub, Pi.sub_def] using hST)

include hD hDs in
/-- **The elliptic estimate for real Cauchy–Riemann operators of class `W^{k+1,p}`.** On a closed
surface, let `D₀` be a smooth real Cauchy–Riemann operator, `p > 2`, `1 < q ≤ p` and `α` a
`W^{k+1,p}` zeroth-order term. There is a constant `C` such that every `ξ ∈ W^{k+2,q}(Σ, V)`
satisfies `‖ξ‖_{W^{k+2,q}} ≤ C (‖(D₀ + α) ξ‖_{W^{k+1,q}} + ‖ξ‖_{L^q})`, where `(D₀ + α) ξ` is the
realization `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevSuccL` and `‖ξ‖_{L^q}` is the norm
of `ξ` in `W^{0,q}(Σ, V)`, all derivatives forgotten (`TauCeti.SectionChartData.lowerToZeroL`). -/
theorem exists_norm_le_norm_perturbedSobolevSuccL_add_norm (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume q (k + 1 + 1),
      ‖w‖ ≤ C * (‖hD.perturbedSobolevSuccL A hDs k hp hq hqp α w‖ +
        ‖A.sectionChartData.lowerToZeroL volume q (k + 1 + 1) w‖) := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevSuccL A hD hDs k hp hq hqp α
  have hL : (A.sectionChartData.lowerToZeroL volume q (k + 1 + 1)).ker = ⊥ :=
    LinearMap.ker_eq_bot.2 (A.sectionChartData.lowerToZeroL_injective volume q (k + 1 + 1))
  have h := ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := zeroOneSobolevSections A volume q (k + 1) × SobolevSection A volume q 0)
    (Z := SobolevSection A volume q 0) (C := C) (hD.perturbedSobolevSuccL A hDs k hp hq hqp α)
    (K := K) (j := A.sectionChartData.lowerToZeroL volume q (k + 1 + 1))
  obtain ⟨C', -, hC'⟩ := h hK hC (by rw [hL]; exact disjoint_bot_right)
  exact ⟨C', hC'⟩

include hD hDs in
/-- **Finite-dimensional kernel.** On a closed surface, the realization
`D₀ + α : W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)` of a real Cauchy–Riemann operator with a
`W^{k+1,p}` zeroth-order term, `p > 2` and `1 < q ≤ p`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    FiniteDimensional ℝ (hD.perturbedSobolevSuccL A hDs k hp hq hqp α).ker := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevSuccL A hD hDs k hp hq hqp α
  have h := ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := zeroOneSobolevSections A volume q (k + 1) × SobolevSection A volume q 0) (C := C)
    (hD.perturbedSobolevSuccL A hDs k hp hq hqp α) (K := K)
  exact h hK hC

include hD hDs in
/-- **Closed range.** On a closed surface, the realization
`D₀ + α : W^{k+2,q}(Σ, V) → W^{k+1,q}(Σ, Λ^{0,1} ⊗ V)` of a real Cauchy–Riemann operator with a
`W^{k+1,p}` zeroth-order term, `p > 2` and `1 < q ≤ p`, has closed range. -/
theorem isClosed_range_perturbedSobolevSuccL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p
      (k + 1)) :
    IsClosed ((hD.perturbedSobolevSuccL A hDs k hp hq hqp α).range :
      Set (zeroOneSobolevSections A volume q (k + 1))) := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevSuccL A hD hDs k hp hq hqp α
  have h := ContinuousLinearMap.isClosed_range_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q (k + 1 + 1)) (F := zeroOneSobolevSections A volume q (k + 1))
    (G := zeroOneSobolevSections A volume q (k + 1) × SobolevSection A volume q 0) (C := C)
    (hD.perturbedSobolevSuccL A hDs k hp hq hqp α) (K := K)
  exact h hK hC

end IsRealCauchyRiemannOperator

end TauCeti
