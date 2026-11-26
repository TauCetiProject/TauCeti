/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Cokernel
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Perturbation.SobolevCoeff

/-!
# Real Cauchy–Riemann operators on closed surfaces are Fredholm

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F` and a finite bundle atlas `A` (so `M` is compact). This file
proves McDuff–Salamon, Theorem C.1.10 (i), at the exponents `ℓ = k = 1`, for closed surfaces:

* a smooth real Cauchy–Riemann operator `D`, realized as
  `TauCeti.IsRealCauchyRiemannOperator.sobolevL : W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`,
  is Fredholm for every `1 < p < ∞`;
* an operator `D₀ + α` with smooth `D₀` and a rough zeroth-order term `α ∈ Lᵖ`, `p > 2`, realized
  as `TauCeti.IsRealCauchyRiemannOperator.perturbedSobolevL : W^{1,q} → L^q`, is Fredholm for every
  `1 < q ≤ p`, with the index of `D₀` on `W^{1,q}`;
* the same holds for a zeroth-order term `α ∈ W^{1,p}`, `p ≥ 2`, realized as
  `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL`, at every exponent `q > 1`.

For smooth `D`, the kernel and the cokernel are finite-dimensional
(`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_ker_sobolevL`,
`TauCeti.IsRealCauchyRiemannOperator.finiteDimensional_quotient_range_sobolevL`), and between
Banach spaces this is the Fredholm property (`ContinuousLinearMap.IsFredholm.of_finite_ker_coker`).
The rough term is a compact operator
(`TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbationL`, McDuff–Salamon,
Lemma C.2.2), and a compact perturbation of a Fredholm operator is Fredholm with the same index
(`ContinuousLinearMap.IsFredholm.add_of_isCompactOperator`,
`ContinuousLinearMap.index_add_of_isCompactOperator`).

Since the index of `D₀ + α` does not depend on `α` at all, it is in particular constant along any
family of zeroth-order terms, continuous or not.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`: a smooth real Cauchy–Riemann
  operator is Fredholm on `W^{1,p}`.
* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_perturbedSobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.index_perturbedSobolevL`: `D₀ + α` with `α ∈ Lᵖ` is
  Fredholm on `W^{1,q}` with the index of `D₀`.
* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevCoeffPerturbedSobolevL`,
  `TauCeti.IsRealCauchyRiemannOperator.index_sobolevCoeffPerturbedSobolevL`: the same for
  `α ∈ W^{1,p}`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i) and its proof, Lemma C.2.2 and Theorem C.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannFredholm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- **Smooth real Cauchy–Riemann operators are Fredholm** (McDuff–Salamon, Theorem C.1.10 (i),
for smooth operators on closed surfaces). On a closed surface, the realization
`W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator `D`, `1 < p < ∞`, is
a Fredholm operator. -/
theorem isFredholm_sobolevL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD.sobolevL A hDs volume p).IsFredholm :=
  .of_finite_ker_coker _ (finiteDimensional_ker_sobolevL A hD hDs hp hp_top)
    (finiteDimensional_quotient_range_sobolevL A hD hDs hp hp_top)

variable {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

include hD hDs in
/-- An operator which is the realization of `D₀` on `W^{1,q}`, `q > 1`, plus a compact operator is
Fredholm with the index of `D₀`. -/
private theorem isFredholm_and_index_eq_of_eq_add (hq : 1 < q)
    {S C : SobolevSection A volume q 1 →L[ℝ] zeroOneSobolevSections A volume q 0}
    (hS : ∀ ξ, S ξ = hD.sobolevL A hDs volume q ξ + C ξ) (hC : IsCompactOperator C) :
    S.IsFredholm ∧ S.index = (hD.sobolevL A hDs volume q).index := by
  have hT := isFredholm_sobolevL A hD hDs (p := (q : ℝ≥0∞)) (by exact_mod_cast hq)
    ENNReal.coe_ne_top
  obtain rfl : S = hD.sobolevL A hDs volume q + C := ContinuousLinearMap.ext hS
  exact ⟨hT.add_of_isCompactOperator hC, ContinuousLinearMap.index_add_of_isCompactOperator hT hC⟩

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

include hD hDs in
/-- **Real Cauchy–Riemann operators with an `Lᵖ` zeroth-order term are Fredholm**
(McDuff–Salamon, Theorem C.1.10 (i), at `ℓ = k = 1`, on closed surfaces). For a smooth real
Cauchy–Riemann operator `D₀`, `p > 2`, `1 < q ≤ p` and an `Lᵖ` zeroth-order term `α`, the
realization `D₀ + α : W^{1,q}(M, V) → L^q(M, Λ^{0,1} ⊗ V)` is a Fredholm operator. -/
theorem isFredholm_perturbedSobolevL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0) :
    (hD.perturbedSobolevL A hDs volume hp hqp α).IsFredholm :=
  (isFredholm_and_index_eq_of_eq_add A hD hDs hq (perturbedSobolevL_apply A hD hDs volume hp hqp α)
    (isCompactOperator_perturbationL A volume hp hqp α)).1

include hD hDs in
/-- **A rough zeroth-order term does not change the index** (McDuff–Salamon, Theorem C.1.10 (i),
at `ℓ = k = 1`, on closed surfaces). For a smooth real Cauchy–Riemann operator `D₀`, `p > 2`,
`1 < q ≤ p` and an `Lᵖ` zeroth-order term `α`, the realization of `D₀ + α` on `W^{1,q}` has the
index of the realization of `D₀` on `W^{1,q}`. -/
theorem index_perturbedSobolevL (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 0) :
    (hD.perturbedSobolevL A hDs volume hp hqp α).index = (hD.sobolevL A hDs volume q).index :=
  (isFredholm_and_index_eq_of_eq_add A hD hDs hq (perturbedSobolevL_apply A hD hDs volume hp hqp α)
    (isCompactOperator_perturbationL A volume hp hqp α)).2

include hD hDs in
/-- **Real Cauchy–Riemann operators with a `W^{1,p}` zeroth-order term are Fredholm**
(McDuff–Salamon, Theorem C.1.10 (i), at `ℓ = 2`, `k = 1`, on closed surfaces). For a smooth real
Cauchy–Riemann operator `D₀`, `p ≥ 2`, `q > 1` and a `W^{1,p}` zeroth-order term `α`, the
realization `D₀ + α : W^{1,q}(M, V) → L^q(M, Λ^{0,1} ⊗ V)` is a Fredholm operator. -/
theorem isFredholm_sobolevCoeffPerturbedSobolevL (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 1) :
    (hD.sobolevCoeffPerturbedSobolevL A hDs volume (q := q) hp α).IsFredholm :=
  (isFredholm_and_index_eq_of_eq_add A hD hDs hq
    (sobolevCoeffPerturbedSobolevL_apply A hD hDs volume hp α)
    (isCompactOperator_sobolevCoeffPerturbationL A volume hp α)).1

include hD hDs in
/-- **A `W^{1,p}` zeroth-order term does not change the index** (McDuff–Salamon, Theorem C.1.10
(i), at `ℓ = 2`, `k = 1`, on closed surfaces). For a smooth real Cauchy–Riemann operator `D₀`,
`p ≥ 2`, `q > 1` and a `W^{1,p}` zeroth-order term `α`, the realization of `D₀ + α` on `W^{1,q}`
has the index of the realization of `D₀` on `W^{1,q}`. -/
theorem index_sobolevCoeffPerturbedSobolevL (hp : 2 ≤ p) (hq : 1 < q)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume p 1) :
    (hD.sobolevCoeffPerturbedSobolevL A hDs volume (q := q) hp α).index =
      (hD.sobolevL A hDs volume q).index :=
  (isFredholm_and_index_eq_of_eq_add A hD hDs hq
    (sobolevCoeffPerturbedSobolevL_apply A hD hDs volume hp α)
    (isCompactOperator_sobolevCoeffPerturbationL A volume hp α)).2

end IsRealCauchyRiemannOperator

end TauCeti
