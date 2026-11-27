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
  `TauCeti.IsRealCauchyRiemannOperator.sobolevCoeffPerturbedSobolevL`, at every exponent `q > 1`;
* the index does not depend on the smooth operator: two smooth real Cauchy–Riemann operators on the
  same bundle have realizations of equal index
  (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq`).

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

Two smooth real Cauchy–Riemann operators `D` and `D'` differ by a smooth zeroth-order term
`D' - D` (`TauCeti.IsRealCauchyRiemannOperator.difference`), a section of the hom bundle
`x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)` with values in `(0,1)`-forms. As a continuous section it lies in
`L^r` for every `r`, and the realization of `D'` is the realization of `D` perturbed by it, read
chart by chart (`TauCeti.IsRealCauchyRiemannOperator.chartValueL_sobolevL_sub_ae`). Choosing
`r > 2` with `p ≤ r`, the perturbation is compact, so the two indices agree.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`: a smooth real Cauchy–Riemann
  operator is Fredholm on `W^{1,p}`.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq`: its index does not depend on the
  operator.
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
open ContinuousLinearMap (complexAntilinearPartL_eq_self_iff)
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

/-! ### Independence of the operator -/

section Difference

variable {D' : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD' : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D')
  (hD's : ContMDiffCovariantDerivativeOn F ∞ D' univ) (μ : Measure ℂ) [μ.IsAddHaarMeasure]

include hD hDs hD' hD's in
/-- The difference `D' - D` of two smooth real Cauchy–Riemann operators, as a continuous section
of the hom bundle `x ↦ V x →L[ℝ] (T_x M →L[ℝ] V x)`. -/
private def differenceSection :
    Cₛ^0⟮𝓘(ℝ, ℂ); F →L[ℝ] ℂ →L[ℝ] F,
      fun x ↦ V x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯ :=
  ⟨fun x ↦ hD'.difference hD x,
    (contMDiffOn_univ.1 (hD'.contMDiffOn_difference hD le_rfl hD's hDs)).of_le (by simp)⟩

/-- In chart `i`, the difference section reads as the difference of the zeroth-order terms of the
two operators. -/
private theorem coord_differenceSection {i : Fin A.n} {y : ℂ} (hy : y ∈ A.image i) :
    (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet).coord i
        (differenceSection hD hDs hD' hD's) y =
      A.chartZeroOrder D' i y - A.chartZeroOrder D i y := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  ext1 v
  set σ : Π x : M, V x := fun x ↦ (A.triv i).symm x v
  have hx : (A.chart i).symm y ∈ (A.triv i).baseSet := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  -- The reading of `D' σ` is that of `D σ` plus the reading of the difference applied to `σ`.
  have hD'σ : A.tangentHom.coord i (D' σ) y =
      A.tangentHom.coord i (D σ) y +
        A.tangentHom.coord i (fun x ↦ hD'.difference hD x (σ x)) y := by
    rw [← A.tangentHom.coord_add i _ _ (by rwa [image_tangentHom]), A.coord_tangentHom,
      A.coord_tangentHom, Pi.add_apply,
      hD'.eq_add_difference hD (Manifold.mdifferentiableAt_symm_of_mem_baseSet v hx)]
  rw [sub_apply, A.chartZeroOrder_apply_eq_coord_tangentHom hD' hy,
    A.chartZeroOrder_apply_eq_coord_tangentHom hD hy, hD'σ, add_sub_cancel_left,
    ← A.coord_triv_symm v hy]
  exact A.coord_hom_apply A.tangentHom.closure_dom_subset_baseSet i _ σ hy

include hD' hD's in
/-- **The realization of `D'` is that of `D` perturbed by `D' - D`.** For finite exponents
`1 ≤ q ≤ r` with `r > 2`, the realization of `D'` on `W^{1,q}` is that of `D` plus the
zeroth-order term `TauCeti.IsRealCauchyRiemannOperator.perturbationL` of the difference section,
read as an `L^r` coefficient. -/
private theorem sobolevL_apply_eq_add_perturbationL {q r : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]
    [Fact (1 ≤ (r : ℝ≥0∞))] (hr : 2 < r) (hqr : q ≤ r) (ξ : SobolevSection A μ q 1) :
    hD'.sobolevL A hD's μ q ξ = hD.sobolevL A hDs μ q ξ +
      perturbationL A μ hr hqr
        (SobolevSection.ofContMDiffSection _ μ r 0 (differenceSection hD hDs hD' hD's)) ξ := by
  rw [← sub_eq_iff_eq_add']
  refine Subtype.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
    (ae_image_tangentHom_iff A μ i).2 ?_)
  have hα := SobolevSection.chartValueL_ofContMDiffSection_ae
    (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) μ r 0
    (differenceSection hD hDs hD' hD's) i
  rw [FiniteBundleAtlas.image_hom (A := A) (h := A.tangentHom.closure_dom_subset_baseSet)
    (𝕜 := ℝ) i] at hα
  filter_upwards [chartValueL_sobolevL_sub_ae A hD hDs μ q hD' hD's ξ i,
    chartValueL_perturbationL_ae A μ hr hqr _ ξ i,
    hα.trans (ae_restrict_of_forall_mem (A.image i).isOpen.measurableSet fun y hy ↦
      coord_differenceSection A hD hDs hD' hD's hy),
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h₁ h₂ h₃ hy
  rw [h₁, h₂, h₃]
  rw [complexAntilinearPartL_eq_self_iff.2 fun v ↦ ?_]
  simp only [sub_apply, A.chartZeroOrder_apply_I_smul hD hy, A.chartZeroOrder_apply_I_smul hD' hy,
    smul_sub, neg_sub_neg, neg_sub]

include hD hDs hD' hD's in
/-- For every finite exponent `p ≥ 1`, the realization of `D'` on `W^{1,p}` is that of `D` plus a
compact operator: the zeroth-order term of `D' - D`, read as an `L^{p+2}` coefficient. -/
private theorem exists_isCompactOperator_sobolevL_apply_eq_add {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_top : p ≠ ⊤) :
    ∃ K : SobolevSection A μ p 1 →L[ℝ] zeroOneSobolevSections A μ p 0,
      IsCompactOperator K ∧
        ∀ ξ, hD'.sobolevL A hD's μ p ξ = hD.sobolevL A hDs μ p ξ + K ξ := by
  lift p to ℝ≥0 using hp_top
  have : Fact (1 ≤ ((p + 2 : ℝ≥0) : ℝ≥0∞)) :=
    ⟨(Fact.out : (1 : ℝ≥0∞) ≤ p).trans (ENNReal.coe_le_coe.2 le_self_add)⟩
  have hr : 2 < p + 2 := lt_add_of_pos_left 2
    (ENNReal.coe_pos.1 (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)))
  exact ⟨_, isCompactOperator_perturbationL A μ hr le_self_add _,
    sobolevL_apply_eq_add_perturbationL A hD hDs hD' hD's μ hr le_self_add⟩

include hD hDs hD' hD's in
/-- **Two smooth real Cauchy–Riemann operators differ by a compact operator.** On a closed
surface, the realizations on `W^{1,p}` of two smooth real Cauchy–Riemann operators on the same
bundle differ by a compact operator, for every finite `p ≥ 1`. -/
theorem isCompactOperator_sobolevL_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_top : p ≠ ⊤) :
    IsCompactOperator fun ξ : SobolevSection A μ p 1 ↦
      hD'.sobolevL A hD's μ p ξ - hD.sobolevL A hDs μ p ξ := by
  obtain ⟨K, hK, hK'⟩ :=
    exists_isCompactOperator_sobolevL_apply_eq_add A hD hDs hD' hD's μ hp_top
  convert hK using 1
  funext ξ
  rw [hK' ξ]
  -- The `AddCommGroup` structure of the `(0,1)`-forms is only found once the type is given.
  exact add_sub_cancel_left (G := zeroOneSobolevSections A μ p 0) _ _

include hD hDs hD' hD's in
/-- **The index does not depend on the operator.** On a closed surface, the realizations
`W^{1,p}(Σ, V) → L^p(Σ, Λ^{0,1} ⊗ V)` of two smooth real Cauchy–Riemann operators on the same
bundle have the same index, `1 < p < ∞`. -/
theorem index_sobolevL_eq {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD'.sobolevL A hD's volume p).index = (hD.sobolevL A hDs volume p).index := by
  lift p to ℝ≥0 using hp_top
  obtain ⟨K, hK, hK'⟩ :=
    exists_isCompactOperator_sobolevL_apply_eq_add A hD hDs hD' hD's volume
      (p := p) ENNReal.coe_ne_top
  exact (isFredholm_and_index_eq_of_eq_add A hD hDs (q := p) (by exact_mod_cast hp) hK' hK).2

end Difference

end IsRealCauchyRiemannOperator

end TauCeti
