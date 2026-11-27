/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Perturbation
import TauCeti.Analysis.Fredholm.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Exponent
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm.Density

/-!
# Higher-order realizations of real Cauchy–Riemann operators are Fredholm

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre `F`, smooth as a real vector bundle, with a finite bundle atlas `A`
(so `M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves McDuff–Salamon, Theorem C.1.10 (i), at every order, for closed surfaces: the
realization `D_k : W^{k+1,p}(M, V) → W^{k,p}(M, Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`) is Fredholm
(`TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevSuccL`), its kernel is that of the
realization from `W^{1,p}` (`TauCeti.IsRealCauchyRiemannOperator.kerSobolevSuccLEquiv`), and its
index depends neither on `k` nor on `p`
(`TauCeti.IsRealCauchyRiemannOperator.index_sobolevSuccL_eq`). For a zeroth-order term `α` of class
`W^{k+1,r}`, `r > 2`, the realization of `D + α` from `W^{k+2,q}`, `1 < q ≤ r`, is Fredholm with the
same index (`TauCeti.IsRealCauchyRiemannOperator.isFredholm_perturbedSobolevSuccL`,
`TauCeti.IsRealCauchyRiemannOperator.index_perturbedSobolevSuccL`).

## The argument

The realizations at consecutive orders form a commutative square with the inclusions `i`
forgetting the highest weak derivative of a section and `j` forgetting that of a `(0,1)`-form
(`TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_sobolevSuccL`). Both are injective, and
`j` has dense range (`TauCeti.denseRange_zeroOneLowerOrdersL`). The square has the regularity
property: a section `ξ ∈ W^{k+1,p}` with `D ξ ∈ W^{k+1,p}` is in `W^{k+2,p}`, by the order-raising
regularity `TauCeti.IsRealCauchyRiemannOperator.exists_chartValuesL_eq_of_chartValuesL_sobolevL_eq`.
So the general comparison `ContinuousLinearMap.IsFredholm.of_regularity` passes the Fredholm
property and the index from order `k + 1` to order `k + 2`
(`ContinuousLinearMap.IsFredholm.index_eq_of_regularity`), and `LinearMap.kerEquivOfRegularity`
identifies the kernels. The case `k = 0` is
`TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`, and the index at order one does not
depend on `p` (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_of_exponent`). The
zeroth-order term is a compact perturbation
(`TauCeti.IsRealCauchyRiemannOperator.isCompactOperator_perturbedSobolevSuccL_sub`).

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevSuccL`: the realization from `W^{k+1,p}`
  is Fredholm.
* `TauCeti.IsRealCauchyRiemannOperator.kerSobolevSuccLEquiv`: its kernel is linearly equivalent to
  that of the realization from `W^{1,p}`, keeping the chart data
  (`TauCeti.IsRealCauchyRiemannOperator.chartValuesL_kerSobolevSuccLEquiv`).
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevSuccL`,
  `TauCeti.IsRealCauchyRiemannOperator.index_sobolevSuccL_eq`: its index is that of the realization
  from `W^{1,p}`, and does not depend on the order or on the exponent.
* `TauCeti.IsRealCauchyRiemannOperator.isFredholm_perturbedSobolevSuccL`,
  `TauCeti.IsRealCauchyRiemannOperator.index_perturbedSobolevSuccL`: `D + α` with `α ∈ W^{k+1,r}`
  is Fredholm on `W^{k+2,q}` with the index of `D`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 (i), Lemma C.2.2 and Theorem C.2.3.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
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

local instance instVectorBundleRealCauchyRiemannHigherOrderFredholm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)

namespace IsRealCauchyRiemannOperator

section Smooth

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

include hD hDs in
/-- **Regularity across consecutive orders.** For `1 < p < ∞`, a section `x ∈ W^{k+1,p}` whose
image under the realization of `D` is a `(0,1)`-form `y` of order `k + 1` lies in `W^{k+2,p}`. -/
private theorem exists_lowerOrderL_eq_of_sobolevSuccL_eq (hp : 1 < p) (hp_top : p ≠ ⊤) {k : ℕ}
    {x : SobolevSection A volume p (k + 1)} {y : zeroOneSobolevSections A volume p (k + 1)}
    (h : hD.sobolevSuccL A hDs volume p k x = zeroOneLowerOrdersL A volume p k 1 y) :
    ∃ x' : SobolevSection A volume p (k + 1 + 1),
      A.sectionChartData.lowerOrderL volume p (k + 1) x' = x := by
  -- The `W^{1,p}` section with the chart data of `x`.
  set ξ := A.sectionChartData.lowerOrdersL volume p 1 k ((Nat.add_comm k 1) ▸ x)
  have hξ : A.sectionChartData.chartValuesL volume p (k + 1) x =
      A.sectionChartData.chartValuesL volume p 1 ξ := by
    rw [SectionChartData.chartValuesL_lowerOrdersL, SectionChartData.chartValuesL_eqRec]
  have hDξ : A.tangentHom.sectionChartData.chartValuesL volume p 0
      (hD.sobolevL A hDs volume p ξ : SobolevSection A.tangentHom volume p 0) =
        A.tangentHom.sectionChartData.chartValuesL volume p (k + 1)
          (y : SobolevSection A.tangentHom volume p (k + 1)) := by
    rw [← chartValuesL_sobolevSuccL_eq_of_chartValuesL_eq A hD hDs volume p k hξ, h,
      coe_zeroOneLowerOrdersL, SectionChartData.chartValuesL_lowerOrdersL]
  obtain ⟨ζ, hζ, -⟩ := exists_chartValuesL_eq_of_chartValuesL_sobolevL_eq A hD hDs hp hp_top hDξ
  refine ⟨ζ, A.sectionChartData.chartValuesL_injective volume p (k + 1) ?_⟩
  rw [SectionChartData.chartValuesL_lowerOrderL, hζ, hξ]

include hD hDs in
/-- The realization from `W^{k+1,p}` is Fredholm with the index of the realization from
`W^{1,p}`, by induction on `k`. -/
private theorem isFredholm_sobolevSuccL_and_index_eq (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    (hD.sobolevSuccL A hDs volume p k).IsFredholm ∧
      (hD.sobolevSuccL A hDs volume p k).index = (hD.sobolevL A hDs volume p).index := by
  induction k with
  | zero =>
    rw [sobolevSuccL_zero]
    exact ⟨isFredholm_sobolevL A hD hDs hp hp_top, rfl⟩
  | succ k ih =>
    obtain ⟨hT, hidx⟩ := ih
    have hcomm (x : SobolevSection A volume p (k + 1 + 1)) :=
      (zeroOneLowerOrdersL_sobolevSuccL A hD hDs volume p k x).symm
    have hi := A.sectionChartData.lowerOrderL_injective volume p (k + 1)
    have hj := zeroOneLowerOrdersL_injective (A := A) (μ := volume) (p := p) (k := k) 1
    have hjd := denseRange_zeroOneLowerOrdersL A volume k hp_top 1
    have hreg (x) (y) (h) := exists_lowerOrderL_eq_of_sobolevSuccL_eq A hD hDs hp hp_top
      (k := k) (x := x) (y := y) h
    exact ⟨hT.of_regularity hcomm hi hj hjd hreg,
      (hT.index_eq_of_regularity hcomm hi hj hjd hreg).trans hidx⟩

include hD hDs in
/-- **Smooth real Cauchy–Riemann operators are Fredholm at every order** (McDuff–Salamon,
Theorem C.1.10 (i), for smooth operators on closed surfaces). On a closed surface, the realization
`W^{k+1,p}(M, V) → W^{k,p}(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator `D`,
`1 < p < ∞`, is a Fredholm operator. -/
theorem isFredholm_sobolevSuccL (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    (hD.sobolevSuccL A hDs volume p k).IsFredholm :=
  (isFredholm_sobolevSuccL_and_index_eq A hD hDs hp hp_top k).1

include hD hDs in
/-- **The index does not depend on the order.** The realization
`W^{k+1,p}(M, V) → W^{k,p}(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator, `1 < p < ∞`,
has the index of its realization `W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`. -/
theorem index_sobolevSuccL (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    (hD.sobolevSuccL A hDs volume p k).index = (hD.sobolevL A hDs volume p).index :=
  (isFredholm_sobolevSuccL_and_index_eq A hD hDs hp hp_top k).2

include hD hDs in
/-- **The index depends neither on the order nor on the exponent** (McDuff–Salamon, Theorem C.1.10
(i), for smooth operators on closed surfaces). For `1 < p, p' < ∞` and orders `k, k'`, the
realizations `W^{k+1,p}(M, V) → W^{k,p}(M, Λ^{0,1} ⊗ V)` and
`W^{k'+1,p'}(M, V) → W^{k',p'}(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator have the
same index. -/
theorem index_sobolevSuccL_eq {p' : ℝ≥0∞} [Fact (1 ≤ p')] (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hp' : 1 < p') (hp'_top : p' ≠ ⊤) (k k' : ℕ) :
    (hD.sobolevSuccL A hDs volume p k).index = (hD.sobolevSuccL A hDs volume p' k').index := by
  rw [index_sobolevSuccL A hD hDs hp hp_top, index_sobolevSuccL A hD hDs hp' hp'_top,
    index_sobolevL_eq_of_exponent A hD hDs hp hp_top hp' hp'_top]

/-- The kernels of the realizations at orders `k + 2` and `k + 1`, identified by forgetting the
highest weak derivative. -/
private def kerSobolevSuccLEquivSucc (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    (hD.sobolevSuccL A hDs volume p (k + 1)).ker ≃ₗ[ℝ] (hD.sobolevSuccL A hDs volume p k).ker :=
  LinearMap.kerEquivOfRegularity
    (fun x ↦ (zeroOneLowerOrdersL_sobolevSuccL A hD hDs volume p k x).symm)
    (A.sectionChartData.lowerOrderL_injective volume p (k + 1)) (zeroOneLowerOrdersL_injective 1)
    fun _ _ h ↦ exists_lowerOrderL_eq_of_sobolevSuccL_eq A hD hDs hp hp_top h

/-- **The kernel does not depend on the order** (McDuff–Salamon, Theorem C.1.10 (i), for smooth
operators on closed surfaces). For `1 < p < ∞`, the kernel of the realization
`W^{k+1,p}(M, V) → W^{k,p}(M, Λ^{0,1} ⊗ V)` of a smooth real Cauchy–Riemann operator is linearly
equivalent to the kernel of its realization `W^{1,p}(M, V) → Lᵖ(M, Λ^{0,1} ⊗ V)`, by an
equivalence keeping the chart data
(`TauCeti.IsRealCauchyRiemannOperator.chartValuesL_kerSobolevSuccLEquiv`). -/
def kerSobolevSuccLEquiv (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    (hD.sobolevSuccL A hDs volume p k).ker ≃ₗ[ℝ] (hD.sobolevL A hDs volume p).ker :=
  -- Recursion through `Nat.rec`: the equation compiler is very slow on these types.
  Nat.rec (motive := fun k ↦
      (hD.sobolevSuccL A hDs volume p k).ker ≃ₗ[ℝ] (hD.sobolevL A hDs volume p).ker)
    (LinearEquiv.ofEq _ _ (congrArg
      (fun T : SobolevSection A volume p 1 →L[ℝ] zeroOneSobolevSections A volume p 0 ↦ T.ker)
      (sobolevSuccL_zero A hD hDs volume p)))
    (fun k e ↦ (kerSobolevSuccLEquivSucc A hD hDs hp hp_top k).trans e) k

/-- The equivalence of kernels keeps the chart data. -/
@[simp]
theorem chartValuesL_kerSobolevSuccLEquiv (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    (x : (hD.sobolevSuccL A hDs volume p k).ker) :
    A.sectionChartData.chartValuesL volume p 1
        (kerSobolevSuccLEquiv A hD hDs hp hp_top k x : SobolevSection A volume p 1) =
      A.sectionChartData.chartValuesL volume p (k + 1) (x : SobolevSection A volume p (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    refine (ih (kerSobolevSuccLEquivSucc A hD hDs hp hp_top k x)).trans ?_
    rw [kerSobolevSuccLEquivSucc, LinearMap.coe_kerEquivOfRegularity_apply,
      ContinuousLinearMap.coe_coe, SectionChartData.chartValuesL_lowerOrderL]

include hD hDs in
/-- **The dimension of the kernel does not depend on the order.** -/
theorem finrank_ker_sobolevSuccL (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    Module.finrank ℝ (hD.sobolevSuccL A hDs volume p k).ker =
      Module.finrank ℝ (hD.sobolevL A hDs volume p).ker :=
  (kerSobolevSuccLEquiv A hD hDs hp hp_top k).finrank_eq

end Smooth

/-! ### Zeroth-order terms of class `W^{k+1,r}` -/

section Perturbed

variable {r q : ℝ≥0} [Fact (1 ≤ (r : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (k : ℕ)

include hD hDs in
/-- The realization of `D + α` from `W^{k+2,q}` is Fredholm with the index of the realization of
`D` from `W^{1,q}`. -/
private theorem isFredholm_perturbedSobolevSuccL_and_index_eq (hr : 2 < r) (hq : 1 < q)
    (hqr : q ≤ r)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume r
      (k + 1)) :
    (hD.perturbedSobolevSuccL A hDs k hr hq hqr α).IsFredholm ∧
      (hD.perturbedSobolevSuccL A hDs k hr hq hqr α).index =
        (hD.sobolevL A hDs volume q).index := by
  obtain ⟨hT, hidx⟩ := isFredholm_sobolevSuccL_and_index_eq A hD hDs (p := (q : ℝ≥0∞))
    (by exact_mod_cast hq) ENNReal.coe_ne_top (k + 1)
  set T := hD.sobolevSuccL A hDs volume q (k + 1)
  set S := hD.perturbedSobolevSuccL A hDs k hr hq hqr α
  have hC : IsCompactOperator (S - T) := by
    rw [FunLike.coe_sub]
    exact isCompactOperator_perturbedSobolevSuccL_sub A hD hDs k hr hq hqr α
  have hS : S = T + (S - T) := (add_sub_cancel T S).symm
  rw [hS]
  exact ⟨hT.add_of_isCompactOperator hC,
    (ContinuousLinearMap.index_add_of_isCompactOperator hT hC).trans hidx⟩

include hD hDs in
/-- **Real Cauchy–Riemann operators of class `W^{k+1,r}` are Fredholm** (McDuff–Salamon, Theorem
C.1.10 (i), at the top order, on closed surfaces). For a smooth real Cauchy–Riemann operator `D`,
`r > 2`, `1 < q ≤ r` and a `W^{k+1,r}` zeroth-order term `α`, the realization
`D + α : W^{k+2,q}(M, V) → W^{k+1,q}(M, Λ^{0,1} ⊗ V)` is a Fredholm operator. -/
theorem isFredholm_perturbedSobolevSuccL (hr : 2 < r) (hq : 1 < q) (hqr : q ≤ r)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume r
      (k + 1)) :
    (hD.perturbedSobolevSuccL A hDs k hr hq hqr α).IsFredholm :=
  (isFredholm_perturbedSobolevSuccL_and_index_eq A hD hDs k hr hq hqr α).1

include hD hDs in
/-- **A `W^{k+1,r}` zeroth-order term does not change the index** (McDuff–Salamon, Theorem
C.1.10 (i), at the top order, on closed surfaces). For a smooth real Cauchy–Riemann operator `D`,
`r > 2`, `1 < q ≤ r` and a `W^{k+1,r}` zeroth-order term `α`, the realization of `D + α` from
`W^{k+2,q}` has the index of the realization of `D` from `W^{1,q}`. -/
theorem index_perturbedSobolevSuccL (hr : 2 < r) (hq : 1 < q) (hqr : q ≤ r)
    (α : SobolevSection (A.hom (𝕜 := ℝ) A.tangentHom.closure_dom_subset_baseSet) volume r
      (k + 1)) :
    (hD.perturbedSobolevSuccL A hDs k hr hq hqr α).index = (hD.sobolevL A hDs volume q).index :=
  (isFredholm_perturbedSobolevSuccL_and_index_eq A hD hDs k hr hq hqr α).2

end Perturbed

end IsRealCauchyRiemannOperator

end TauCeti
