/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Estimate
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich

/-!
# Closed range and finite-dimensional kernel of real Cauchy–Riemann operators on closed surfaces

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with a finite
bundle atlas `A` (so `M` is compact). This file proves that the realizations of real
Cauchy–Riemann operators on `V` have finite-dimensional kernel and closed range, the upper
semi-Fredholm half of McDuff–Salamon, Theorem C.1.10 (i), for closed surfaces:

* for a smooth real Cauchy–Riemann operator `D`, its realization
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)`, for every
  `1 < p < ∞`
  (`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_sobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.isClosed_range_sobolevL`);
* for an operator `D₀ + α` with a rough zeroth-order term `α ∈ L^p`, `p > 2`, its realization
  `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL : W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)`,
  for every `1 < q ≤ p`
  (`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_perturbedSobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.isClosed_range_perturbedSobolevL`).

For the rough operators the file also proves the elliptic estimate

`‖ξ‖_{W^{1,q}} ≤ C (‖(D₀ + α) ξ‖_{L^q} + ‖ξ‖_{L^q})`

(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_perturbedSobolevL_add_norm`), the case
`ℓ = k = 1` of the elliptic estimate for operators of class `W^{ℓ-1,p}` used in the proof of
McDuff–Salamon, Theorem C.2.3.

## The argument

For smooth `D` the elliptic estimate
`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm` bounds `‖ξ‖_{W^{1,p}}`
by `‖D ξ‖_{L^p}` and `‖ξ‖_{L^p}`, and the inclusion `W^{1,p} → L^p` is compact by Rellich's theorem
(`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`). Peetre's lemma
(`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
`ContinuousLinearMap.isClosed_range_of_compact_estimate`) turns such an estimate with a compact
error into finite-dimensional kernel and closed range.

For `D₀ + α`, the estimate for `D₀` gives
`‖ξ‖_{W^{1,q}} ≤ C (‖(D₀ + α) ξ‖_{L^q} + ‖(α ξ)^{0,1}‖_{L^q} + ‖ξ‖_{L^q})`, and the rough term is a
compact operator of `ξ`
(`TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbedSobolevL_sub`), so the error is
again compact (`ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub`) and
Peetre's lemma applies. The rough term cannot simply be absorbed, since it is not small.
Instead, the compact error may be replaced by any continuous seminorm which is a norm on the
kernel of `D₀ + α`, since together with `D₀ + α` it satisfies the same compact-error estimate and
is injective (`ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate`), here the
`L^q` norm.

The finite dimension of the cokernel, which completes the Fredholm property, is not proved here.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_sobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.isClosed_range_sobolevL`: a smooth real Cauchy–Riemann
  operator on `W^{1,p}` has finite-dimensional kernel and closed range.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_perturbedSobolevL_add_norm`: the
  elliptic estimate for `D₀ + α` on `W^{1,q}`.
* `TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_perturbedSobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.isClosed_range_perturbedSobolevL`: so has `D₀ + α`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Theorem C.1.10 and its proof in Appendix C.2
  (Theorem C.2.3 and Lemma C.2.2).
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

local instance instVectorBundleRealCauchyRiemannSemiFredholm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

namespace IsRealCauchyRiemannOperator

/-
The abstract estimates of `TauCeti.Analysis.Normed.Operator.Compact.Estimate` are applied below
with their type arguments, operators and constant named, and only then applied to the compactness
and estimate hypotheses, so that instance search on the Sobolev section spaces runs first. Left to
unification against those hypotheses, the instances are found through a different path, whose
comparison with the instances in the elliptic estimates exceeds the default heartbeat limit.
-/

/-! ### Smooth operators -/

section Smooth

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

include hD hDs in
/-- The elliptic estimate for a smooth real Cauchy–Riemann operator, with its `L^p` error term
written as a compact operator, the Rellich inclusion `W^{1,p} → L^p` rescaled by a constant. -/
private theorem exists_compact_estimate_sobolevL (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ (C : ℝ) (K : SobolevSection A volume p 1 →L[ℝ] SobolevSection A volume p 0),
      IsCompactOperator K ∧ ∀ w, ‖w‖ ≤ C * ‖hD.sobolevL A hDs volume p w‖ + ‖K w‖ := by
  obtain ⟨C, hC⟩ := hD.exists_norm_le_norm_sobolevL_add_norm A hDs hp hp_top
  exact ContinuousLinearMap.exists_compact_estimate_of_norm_le_mul_add_norm (𝕜 := ℝ)
    (E := SobolevSection A volume p 1) (F := zeroOneSobolevSections A volume p 0)
    (G := SobolevSection A volume p 0) (C := C) (T := hD.sobolevL A hDs volume p)
    (K := A.sectionChartData.lowerOrderL volume p 0)
    (SobolevSection.isCompactOperator_lowerOrderL (E := ℂ) (M := M) (F := F) (V := V) A volume p 0)
    hC

include hD hDs in
/-- **Finite-dimensional kernel.** On a closed surface, a smooth real Cauchy–Riemann operator
`D : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)`, `1 < p < ∞`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_sobolevL (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    FiniteDimensional ℝ (hD.sobolevL A hDs volume p).ker := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_sobolevL A hD hDs hp hp_top
  have h := ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume p 1) (F := zeroOneSobolevSections A volume p 0)
    (G := SobolevSection A volume p 0) (hD.sobolevL A hDs volume p) (C := C) (K := K)
  exact h hK hC

include hD hDs in
/-- **Closed range.** On a closed surface, a smooth real Cauchy–Riemann operator
`D : W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)`, `1 < p < ∞`, has closed range. -/
theorem isClosed_range_sobolevL (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    IsClosed ((hD.sobolevL A hDs volume p).range : Set (zeroOneSobolevSections A volume p 0)) := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_sobolevL A hD hDs hp hp_top
  have h := ContinuousLinearMap.isClosed_range_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume p 1) (F := zeroOneSobolevSections A volume p 0)
    (G := SobolevSection A volume p 0) (hD.sobolevL A hDs volume p) (C := C) (K := K)
  exact h hK hC

end Smooth

/-! ### Operators with a rough zeroth-order term -/

section Rough

variable {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

include hD hDs in
/-- The elliptic estimate for `D₀ + α` with a compact error term: the estimate for `D₀`, whose
compact error is the Rellich inclusion, survives the compact perturbation by the rough term. -/
private theorem exists_compact_estimate_perturbedSobolevL (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p)
    (α : SobolevSection
      (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0) :
    ∃ (C : ℝ) (K : SobolevSection A volume q 1 →L[ℝ]
        zeroOneSobolevSections A volume q 0 × SobolevSection A volume q 0),
      IsCompactOperator K ∧
        ∀ w, ‖w‖ ≤ C * ‖hD.perturbedSobolevL A hDs volume hp hqp α w‖ + ‖K w‖ := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_sobolevL A hD hDs (p := (q : ℝ≥0∞))
    (by exact_mod_cast hq) ENNReal.coe_ne_top
  have hST := isCompactOperator_perturbedSobolevL_sub A hD hDs volume hp hqp α
  have h := ContinuousLinearMap.exists_compact_estimate_of_isCompactOperator_sub (𝕜 := ℝ)
    (E := SobolevSection A volume q 1) (F := zeroOneSobolevSections A volume q 0)
    (G := SobolevSection A volume q 0) (C := C) (T := hD.sobolevL A hDs volume q)
    (S := hD.perturbedSobolevL A hDs volume hp hqp α) (K := K)
  -- `hST` is stated for the pointwise difference, which is the coercion of the operator `S - T`.
  exact h hK hC (by simpa only [FunLike.coe_sub, Pi.sub_def] using hST)

include hD hDs in
/-- **The elliptic estimate for real Cauchy–Riemann operators with a rough zeroth-order term.**
On a closed surface, let `D₀` be a smooth real Cauchy–Riemann operator, `p > 2`, `1 < q ≤ p` and
`α` an `L^p` zeroth-order term. There is a constant `C` such that every `ξ ∈ W^{1,q}(Σ, V)`
satisfies `‖ξ‖_{W^{1,q}} ≤ C (‖(D₀ + α) ξ‖_{L^q} + ‖ξ‖_{L^q})`, where `(D₀ + α) ξ` is the
realization `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL` and `‖ξ‖_{L^q}` is the norm of
`ξ` in `W^{0,q}(Σ, V)`. -/
theorem exists_norm_le_norm_perturbedSobolevL_add_norm (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection
      (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume q 1,
      ‖w‖ ≤ C * (‖hD.perturbedSobolevL A hDs volume hp hqp α w‖ +
        ‖A.sectionChartData.lowerOrderL volume q 0 w‖) := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevL A hD hDs hp hq hqp α
  -- The inclusion `W^{1,q} → L^q` is injective, in particular on the kernel of `D₀ + α`.
  have hL : (A.sectionChartData.lowerOrderL volume q 0).ker = ⊥ := by
    refine LinearMap.ker_eq_bot.2 ?_
    have h := A.sectionChartData.lowerOrdersL_injective volume (q : ℝ≥0∞) 0 1
    rwa [SectionChartData.lowerOrdersL_one] at h
  have h := ContinuousLinearMap.exists_norm_le_mul_norm_add_norm_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q 1) (F := zeroOneSobolevSections A volume q 0)
    (G := zeroOneSobolevSections A volume q 0 × SobolevSection A volume q 0)
    (Z := SobolevSection A volume q 0) (C := C) (hD.perturbedSobolevL A hDs volume hp hqp α)
    (K := K) (j := A.sectionChartData.lowerOrderL volume q 0)
  obtain ⟨C', -, hC'⟩ := h hK hC (by rw [hL]; exact disjoint_bot_right)
  exact ⟨C', hC'⟩

include hD hDs in
/-- **Finite-dimensional kernel with a rough zeroth-order term.** On a closed surface, the
realization `D₀ + α : W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` of a real Cauchy–Riemann operator with
an `L^p` zeroth-order term, `p > 2` and `1 < q ≤ p`, has finite-dimensional kernel. -/
theorem finiteDimensional_ker_perturbedSobolevL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection
      (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0) :
    FiniteDimensional ℝ (hD.perturbedSobolevL A hDs volume hp hqp α).ker := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevL A hD hDs hp hq hqp α
  have h := ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q 1) (F := zeroOneSobolevSections A volume q 0)
    (G := zeroOneSobolevSections A volume q 0 × SobolevSection A volume q 0) (C := C)
    (hD.perturbedSobolevL A hDs volume hp hqp α) (K := K)
  exact h hK hC

include hD hDs in
/-- **Closed range with a rough zeroth-order term.** On a closed surface, the realization
`D₀ + α : W^{1,q}(Σ, V) → L^q(Σ, Λ^{0,1} ⊗ V)` of a real Cauchy–Riemann operator with an `L^p`
zeroth-order term, `p > 2` and `1 < q ≤ p`, has closed range. -/
theorem isClosed_range_perturbedSobolevL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection
      (A.hom (𝕜 := ℝ) (A.tangentHom 𝓘(ℝ, ℂ)).closure_dom_subset_baseSet) volume p 0) :
    IsClosed ((hD.perturbedSobolevL A hDs volume hp hqp α).range :
      Set (zeroOneSobolevSections A volume q 0)) := by
  obtain ⟨C, K, hK, hC⟩ := exists_compact_estimate_perturbedSobolevL A hD hDs hp hq hqp α
  have h := ContinuousLinearMap.isClosed_range_of_compact_estimate (𝕜 := ℝ)
    (E := SobolevSection A volume q 1) (F := zeroOneSobolevSections A volume q 0)
    (G := zeroOneSobolevSections A volume q 0 × SobolevSection A volume q 0) (C := C)
    (hD.perturbedSobolevL A hDs volume hp hqp α) (K := K)
  exact h hK hC

end Rough

end IsRealCauchyRiemannOperator

end TauCeti
