/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Hessian
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Morse indices of moment map components at a fixed point, from the weights

Let a compact commutative Lie group `G`, such as a torus, act on a symplectic manifold `(M, σ)`
with moment map `μ`, and let `p` be a fixed point. The weight normal form
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`) gives a chart `z = (q, p)` of `M` at
`p` with values in `ℂⁿ = ℝⁿ × ℝⁿ` in which

`μ^ξ = μ^ξ(p) - ½ Σₖ αₖ(ξ) (qₖ² + pₖ²)`

for the weights `αₖ` of the isotropy representation at `p`. This file reads the Morse–Bott data
of the component `μ^ξ` off the weights:

* the **Morse index** of `μ^ξ` at `p` is `2 #{k | αₖ(ξ) > 0}`;
* the **coindex**, the Morse index of `-μ^ξ`, is `2 #{k | αₖ(ξ) < 0}`;
* the **nullity**, the dimension of the null space of the Hessian, is `2 #{k | αₖ(ξ) = 0}`. That
  null space is the space of tangent vectors fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`
  (`TauCeti.SmoothTwoForm.IsMomentMap.criticalHessian_apply_eq_zero_iff`), so the zero weights
  count the fixed tangent directions;
* `p` is a nondegenerate critical point of `μ^ξ` exactly when `αₖ(ξ) ≠ 0` for every `k`.

The weights are those of the isotropy representation in a symplectic frame: the differential `L`
of the chart at `p` is a linear isomorphism `T_p M ≃ ℂⁿ` carrying `σ_p` to the standard form and
conjugating the differential of each `g ∈ G` at `p` to the rotation `zₖ ↦ χₖ(g) zₖ` by the
characters with `χₖ (exp ξ) = e^{i αₖ(ξ)}`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weights_manifoldMorseIndex`).

The chart-level statements hold for every chart in which a function `f` is a constant plus the
weight-model component, at every critical point of `f` in the chart, not just at its centre.
There the critical Hessian of `f` is the Hessian of the model component
(`TauCeti.hessianQuadraticForm_weightMomentMap_apply`) pulled back by the differential of the
chart, so its indices of inertia are those computed on the model
(`TauCeti.morseIndex_weightMomentMap_apply`,
`TauCeti.sigPos_hessianQuadraticForm_weightMomentMap_apply`,
`TauCeti.radical_hessianQuadraticForm_weightMomentMap_apply`). The critical points of `f` in the
chart are the points where the model generator `ξ_M` vanishes
(`TauCeti.mem_criticalPoints_iff_weightGenerator_eq_zero`).

## Main results

* `TauCeti.mem_criticalPoints_iff_weightGenerator_eq_zero`: in a weight chart, the critical points
  of `f` are the points where the model generator `ξ_M` vanishes.
* `TauCeti.toQuadraticMap_toBilinForm_criticalHessian_eq_comp_of_weightMomentMap`,
  `TauCeti.equivalent_toQuadraticMap_toBilinForm_criticalHessian_of_weightMomentMap`: in a weight
  chart, the critical Hessian of `f` is the model Hessian pulled back by the differential of the
  chart.
* `TauCeti.manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap`,
  `TauCeti.manifoldMorseIndex_neg_eq_two_mul_ncard_neg_of_weightMomentMap`,
  `TauCeti.ker_criticalHessian_eq_comap_ker_weightGenerator`,
  `TauCeti.finrank_ker_criticalHessian_eq_two_mul_ncard_of_weightMomentMap`,
  `TauCeti.isManifoldNondegenerateCriticalPoint_iff_forall_ne_zero_of_weightMomentMap`: the index,
  coindex, null space, nullity and nondegeneracy of `f` at its critical points in a weight chart.
* `TauCeti.SmoothTwoForm.IsMomentMap.exists_weights_manifoldMorseIndex`: at a fixed point of a
  Hamiltonian action of a compact commutative Lie group, the index, coindex and nullity of every
  component `μ^ξ` are twice the numbers of weights positive, negative and zero on `ξ`, for the
  weights of the isotropy representation in a symplectic frame.

## References

* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2.
* J. Hilgert, K.-H. Neeb and W. Plank, *Symplectic convexity theorems and coadjoint orbits*,
  Compositio Math. 94 (1994), 129–180, Lemmas 2.1–2.2 (the quadratic weight formula).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 27 and Homework 21.
-/

public section

noncomputable section

open Filter Set QuadraticForm
open scoped Manifold ContDiff Topology

namespace TauCeti

/-! ### Morse–Bott data read through a weight chart -/

section Chart

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {ι : Type*} [Fintype ι] {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]
  {α : ι → StrongDual ℝ 𝔱} {ξ : 𝔱}
  {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    M (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ∞}
  {f : M → ℝ} {c : ℝ} {x : M}

variable (hf : ∀ y ∈ chart.source, f y = c + weightMomentMap α (chart y) ξ)
  (hx : x ∈ chart.source)
include hf hx

omit [I'.Boundaryless] in
/-- Near a point of the chart, `f` is the constant plus the model component, read in the chart. -/
private theorem eventuallyEq_comp_weightMomentMap :
    f =ᶠ[𝓝 x] (fun z ↦ c + weightMomentMap α z ξ) ∘ chart :=
  eventually_of_mem (chart.open_source.mem_nhds hx) fun y hy ↦ hf y hy

omit [I'.Boundaryless] in
/-- In a weight chart, `f` is smooth at every point of the chart. -/
private theorem contMDiffAt_of_weightMomentMap : ContMDiffAt I' 𝓘(ℝ) ∞ f x :=
  (((contDiff_const.add (contDiff_weightMomentMap_apply α ξ)).contMDiff.comp_contMDiffOn
    chart.contMDiffOn).contMDiffAt (chart.open_source.mem_nhds hx)).congr_of_eventuallyEq
      (eventuallyEq_comp_weightMomentMap hf hx)

omit [I'.Boundaryless] hf in
/-- The differential of the chart is onto at every point of the chart. -/
private theorem isRegularPoint_chart :
    IsRegularPoint I' 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) chart x := by
  obtain ⟨L, hL⟩ := chart.isInvertible_mfderiv (by simp) hx
  rw [isRegularPoint_iff, ← hL]
  exact L.surjective

omit [I'.Boundaryless] in
/-- **Critical points in a weight chart.** If `f` is a constant plus the weight-model component
`μ^ξ`, read in the chart, then a point `x` of the chart is a critical point of `f` exactly when
the model generator `ξ_M` vanishes at its coordinates `z(x)`, that is, when `zₖ(x) = 0` for every
`k` with `αₖ(ξ) ≠ 0` (`TauCeti.weightGenerator_apply_eq_zero_iff`). -/
theorem mem_criticalPoints_iff_weightGenerator_eq_zero :
    x ∈ criticalPoints I' f ↔ weightGenerator (fun k ↦ α k ξ) (chart x) = 0 := by
  rw [(eventuallyEq_comp_weightMomentMap hf hx).mem_criticalPoints_iff,
    (isRegularPoint_chart hx).mem_criticalPoints_comp_iff (chart.mdifferentiableAt (by simp) hx)
      ((contDiff_const.add (contDiff_weightMomentMap_apply α ξ)).contMDiff.mdifferentiableAt
        (by simp)),
    mem_criticalPoints_iff_fderiv_eq_zero, fderiv_const_add,
    fderiv_weightMomentMap_apply_eq_zero_iff]

omit [I'.Boundaryless] in
/-- At a critical point `x` of `f` in the chart, its coordinates `z(x)` are a critical point of
the constant plus the model component. -/
private theorem mem_criticalPoints_chart (hcrit : x ∈ criticalPoints I' f) :
    chart x ∈ criticalPoints 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
      (fun z ↦ c + weightMomentMap α z ξ) := by
  rw [mem_criticalPoints_iff_fderiv_eq_zero, fderiv_const_add,
    fderiv_weightMomentMap_apply_eq_zero_iff]
  exact (mem_criticalPoints_iff_weightGenerator_eq_zero hf hx).1 hcrit

/-- **The critical Hessian in a weight chart.** If `f` is a constant plus the weight-model
component `μ^ξ`, read in the chart, then at a critical point `x` of `f` in the chart the quadratic
form of the critical Hessian of `f` is the Hessian `v ↦ -Σₖ αₖ(ξ) (v_{q,k}² + v_{p,k}²)` of the
model component (`TauCeti.hessianQuadraticForm_weightMomentMap_apply`), pulled back by the
differential of the chart at `x`. -/
theorem toQuadraticMap_toBilinForm_criticalHessian_eq_comp_of_weightMomentMap
    (hcrit : x ∈ criticalPoints I' f) :
    (criticalHessian I' f x).toBilinForm.toQuadraticMap =
      (hessianQuadraticForm (fun z ↦ weightMomentMap α z ξ) (chart x)).comp
        (mvfderiv I' chart x :
          TangentSpace I' x →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) := by
  rw [criticalHessian_congr_of_eventuallyEq (eventuallyEq_comp_weightMomentMap hf hx),
    toQuadraticMap_toBilinForm_criticalHessian_comp
      ((contDiff_const.add (contDiff_weightMomentMap_apply α ξ)).contMDiff.contMDiffAt.of_le
        (by simp))
      ((chart.contMDiffOn.contMDiffAt (chart.open_source.mem_nhds hx)).of_le (by simp))
      (mem_criticalPoints_chart hf hx hcrit)]
  ext u
  rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply,
    toQuadraticMap_toBilinForm_criticalHessian_modelSpace, hessianQuadraticForm_const_add]
  -- The two sides differ only in reading the model space as the tangent space at `chart x`.
  rfl

/-- The differential of the chart at a critical point `x` of `f` is an isometry from the quadratic
form of the critical Hessian of `f` at `x` to the Hessian of the model component. -/
private def criticalHessianIsometryEquiv (hcrit : x ∈ criticalPoints I' f) :
    (criticalHessian I' f x).toBilinForm.toQuadraticMap.IsometryEquiv
      (hessianQuadraticForm (fun z ↦ weightMomentMap α z ξ) (chart x)) where
  __ := LinearEquiv.ofBijective
    (mvfderiv I' chart x : TangentSpace I' x →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (chart.bijective_mvfderiv (by simp) hx)
  map_app' u := by
    rw [toQuadraticMap_toBilinForm_criticalHessian_eq_comp_of_weightMomentMap hf hx hcrit]
    -- `LinearEquiv.ofBijective` applies the underlying linear map by definition.
    rfl

/-- **The critical Hessian in a weight chart is a doubled weighted sum of squares.** If `f` is a
constant plus the weight-model component `μ^ξ`, read in the chart, then at a critical point `x` of
`f` in the chart the quadratic form of the critical Hessian of `f` is equivalent to the Hessian of
the model component, hence (`TauCeti.equivalent_hessianQuadraticForm_weightMomentMap_apply`) to the
weighted sum of squares in which each weight `-αₖ(ξ)` appears twice. -/
theorem equivalent_toQuadraticMap_toBilinForm_criticalHessian_of_weightMomentMap
    (hcrit : x ∈ criticalPoints I' f) :
    (criticalHessian I' f x).toBilinForm.toQuadraticMap.Equivalent
      (hessianQuadraticForm (fun z ↦ weightMomentMap α z ξ) (chart x)) :=
  ⟨criticalHessianIsometryEquiv hf hx hcrit⟩

/-- **The Morse index in a weight chart.** If `f` is a constant plus the weight-model component
`μ^ξ`, read in the chart, then at every critical point of `f` in the chart its Morse index is twice
the number of weights with `αₖ(ξ) > 0`. -/
theorem manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap
    (hcrit : x ∈ criticalPoints I' f) :
    manifoldMorseIndex I' f x = 2 * {k | 0 < α k ξ}.ncard := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian,
    (equivalent_toQuadraticMap_toBilinForm_criticalHessian_of_weightMomentMap hf hx
      hcrit).sigNeg_eq,
    ← morseIndex_def, morseIndex_weightMomentMap_apply]

/-- **The coindex in a weight chart.** If `f` is a constant plus the weight-model component
`μ^ξ`, read in the chart, then at every critical point of `f` in the chart the Morse index of `-f`
is twice the number of weights with `αₖ(ξ) < 0`. -/
theorem manifoldMorseIndex_neg_eq_two_mul_ncard_neg_of_weightMomentMap
    (hcrit : x ∈ criticalPoints I' f) :
    manifoldMorseIndex I' (-f) x = 2 * {k | α k ξ < 0}.ncard := by
  rw [manifoldMorseIndex_neg_eq_sigPos_criticalHessian,
    (equivalent_toQuadraticMap_toBilinForm_criticalHessian_of_weightMomentMap hf hx
      hcrit).sigPos_eq,
    sigPos_hessianQuadraticForm_weightMomentMap_apply]

/-- **The null space of the Hessian in a weight chart.** If `f` is a constant plus the weight-model
component `μ^ξ`, read in the chart, then at every critical point `x` of `f` in the chart the null
space of the critical Hessian of `f` is the preimage under the differential of the chart of the
kernel of the model generator `ξ_M`: the tangent vectors whose coordinates `v_{q,k}, v_{p,k}`
vanish whenever `αₖ(ξ) ≠ 0`. -/
theorem ker_criticalHessian_eq_comap_ker_weightGenerator (hcrit : x ∈ criticalPoints I' f) :
    (criticalHessian I' f x).ker =
      (LinearMap.ker (weightGenerator fun k ↦ α k ξ).toLinearMap).comap
        (mvfderiv I' chart x :
          TangentSpace I' x →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) := by
  have hg : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) 𝓘(ℝ) 2
      (fun z ↦ c + weightMomentMap α z ξ) (chart x) :=
    (contDiff_const.add (contDiff_weightMomentMap_apply α ξ)).contMDiff.contMDiffAt.of_le
      (by simp)
  rw [criticalHessian_congr_of_eventuallyEq (eventuallyEq_comp_weightMomentMap hf hx),
    (isRegularPoint_chart hx).ker_criticalHessian_comp hg
      ((chart.contMDiffOn.contMDiffAt (chart.open_source.mem_nhds hx)).of_le (by simp))
      (mem_criticalPoints_chart hf hx hcrit),
    ← radical_toQuadraticMap_toBilinForm_criticalHessian hg]
  ext u
  rw [Submodule.mem_comap, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply,
    ← radical_hessianQuadraticForm_weightMomentMap_apply α ξ (chart x),
    toQuadraticMap_toBilinForm_criticalHessian_modelSpace, hessianQuadraticForm_const_add]
  -- The two sides differ only in reading the model space as the tangent space at `chart x`.
  rfl

/-- **The nullity in a weight chart.** If `f` is a constant plus the weight-model component `μ^ξ`,
read in the chart, then at every critical point of `f` in the chart the null space of its critical
Hessian has dimension twice the number of weights with `αₖ(ξ) = 0`. -/
theorem finrank_ker_criticalHessian_eq_two_mul_ncard_of_weightMomentMap
    (hcrit : x ∈ criticalPoints I' f) :
    Module.finrank ℝ (criticalHessian I' f x).ker = 2 * {k | α k ξ = 0}.ncard := by
  rw [← radical_toQuadraticMap_toBilinForm_criticalHessian
      ((contMDiffAt_of_weightMomentMap hf hx).of_le (by simp)),
    (equivalent_toQuadraticMap_toBilinForm_criticalHessian_of_weightMomentMap hf hx
      hcrit).rank_radical_eq,
    radical_hessianQuadraticForm_weightMomentMap_apply, finrank_ker_weightGenerator]

/-- **Nondegeneracy in a weight chart.** If `f` is a constant plus the weight-model component
`μ^ξ`, read in the chart, then a critical point of `f` in the chart is nondegenerate exactly when
no weight vanishes on `ξ`. -/
theorem isManifoldNondegenerateCriticalPoint_iff_forall_ne_zero_of_weightMomentMap
    [FiniteDimensional ℝ E'] (hcrit : x ∈ criticalPoints I' f) :
    IsManifoldNondegenerateCriticalPoint I' f x ↔ ∀ k, α k ξ ≠ 0 := by
  have hker : (criticalHessian I' f x).ker = ⊥ ↔ ∀ k, α k ξ ≠ 0 := by
    rw [← Submodule.finrank_eq_zero,
      finrank_ker_criticalHessian_eq_two_mul_ncard_of_weightMomentMap hf hx hcrit,
      mul_eq_zero, Set.ncard_eq_zero]
    simp [Set.eq_empty_iff_forall_notMem]
  rw [isManifoldNondegenerateCriticalPoint_iff_criticalHessian, ← hker, LinearMap.ker_eq_bot]
  refine ⟨fun ⟨_, _, h⟩ ↦ h.injective, fun h ↦ ⟨(contMDiffAt_of_weightMomentMap hf hx).of_le
    (by simp), mem_criticalPoints.1 hcrit, criticalHessian_isInvertible_of_injective h⟩⟩

end Chart

/-! ### Morse–Bott data at a fixed point -/

namespace SmoothTwoForm.IsMomentMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  {σ : SmoothTwoForm I' M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Morse indices of moment map components at a fixed point.** Let a compact commutative Lie
group `G` act smoothly on a finite-dimensional symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and let `p` be a fixed point. Then there are continuous
characters `χₖ : G → S¹`, with real weights `αₖ ∈ 𝔤*` determined by `χₖ (exp ξ) = e^{i αₖ(ξ)}`,
and a linear isomorphism `L : T_p M ≃ ℂⁿ = ℝⁿ × ℝⁿ` carrying `σ_p` to the standard symplectic form
and conjugating the differential at `p` of each `g ∈ G` to the rotation `zₖ ↦ χₖ(g) zₖ`, such that
for every `ξ ∈ 𝔤`:

* the Morse index of the component `μ^ξ` at `p` is twice the number of `k` with `αₖ(ξ) > 0`;
* the Morse index of `-μ^ξ` at `p`, the coindex, is twice the number of `k` with `αₖ(ξ) < 0`;
* the space of tangent vectors at `p` fixed by the closure `T_ξ` of `{exp (t ξ) | t ∈ ℝ}`, the
  null space of the Hessian of `μ^ξ`, has dimension twice the number of `k` with `αₖ(ξ) = 0`;
* `p` is a nondegenerate critical point of `μ^ξ` exactly when `αₖ(ξ) ≠ 0` for every `k`. -/
theorem exists_weights_manifoldMorseIndex
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (L : TangentSpace I' p ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ)) ∧
      (∀ v w : TangentSpace I' p, σ.eval₂ p v w = stdSymplecticForm (L v) (L w)) ∧
      (∀ (g : G) (v : TangentSpace I' p), L (mfderiv I' I' (fun y : M ↦ g • y) p v) =
        weightRotation (fun k ↦ Complex.arg (χ k g)) (L v)) ∧
      ∀ ξ : GroupLieAlgebra I G,
        manifoldMorseIndex I' (fun y ↦ μ y ξ) p = 2 * {k | 0 < α k ξ}.ncard ∧
        manifoldMorseIndex I' (-fun y ↦ μ y ξ) p = 2 * {k | α k ξ < 0}.ncard ∧
        Module.finrank ℝ (fixedTangentSubspace I' (Lie.closedOneParameterSubgroup ξ) p) =
          2 * {k | α k ξ = 0}.ncard ∧
        (IsManifoldNondegenerateCriticalPoint I' (fun y ↦ μ y ξ) p ↔ ∀ k, α k ξ ≠ 0) := by
  obtain ⟨n, χ, α, chart, -, hα, -, hpchart, hchartp, -, -, hequiv, hform, -, hμchart⟩ :=
    hμ.exists_weightModelChart hσ hG hp
  obtain ⟨L₀, hL₀⟩ := chart.isInvertible_mfderiv (by simp) hpchart
  -- The differential of the chart at `p`, as an isomorphism onto the model space.
  let L : TangentSpace I' p ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := L₀
  have hLv (v : TangentSpace I' p) : L v = mvfderiv I' chart p v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← hL₀]
    -- `L` is `L₀` with its codomain read as the model space; both apply `L₀`.
    rfl
  refine ⟨n, χ, α, L, hα, fun v w ↦ by simpa only [hLv] using hform p hpchart v w, fun g v ↦ ?_,
    fun ξ ↦ ?_⟩
  · -- Differentiate `chart (g • y) = R (chart y)` at the fixed point `p`, for the rotation `R`.
    set R := weightRotation fun k ↦ Complex.arg (χ k g)
    have hchart := chart.mdifferentiableAt (by simp) hpchart
    have heq : (chart ∘ fun y : M ↦ g • y) =ᶠ[𝓝 p] R ∘ chart :=
      eventually_of_mem (chart.open_source.mem_nhds hpchart) fun y hy ↦ (hequiv g y hy).2
    have h := congr($(Filter.EventuallyEq.mfderiv_eq (I := I')
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) heq) v)
    rw [mfderiv_comp_apply_of_eq p hchart
      ((ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) g).mdifferentiableAt
        (by simp)) (hp g),
      ContinuousLinearMap.comp_apply, mfderiv_comp_apply _ R.mdifferentiableAt hchart,
      R.mfderiv_eq] at h
    rw [hLv v, mvfderiv_apply_eq_mfderiv_apply]
    refine (hLv _).trans ((mvfderiv_apply_eq_mfderiv_apply _ _ _).trans ?_)
    exact h
  · have hf : ∀ y ∈ chart.source, μ y ξ = μ p ξ + weightMomentMap α (chart y) ξ :=
      fun y hy ↦ hμchart y hy ξ
    have hcrit : p ∈ criticalPoints I' fun y ↦ μ y ξ := by
      rw [mem_criticalPoints_iff_weightGenerator_eq_zero hf hpchart, hchartp, map_zero]
    -- The null space of the Hessian is the space of tangent vectors fixed by `T_ξ`.
    have hfix : fixedTangentSubspace I' (Lie.closedOneParameterSubgroup ξ) p =
        (criticalHessian I' (fun y ↦ μ y ξ) p).ker := by
      ext v
      rw [mem_fixedTangentSubspace_iff_of_mem_fixedPoints (K := Lie.closedOneParameterSubgroup ξ)
          fun k ↦ hp k, LinearMap.mem_ker,
        ContinuousLinearMap.coe_coe, hμ.criticalHessian_apply_eq_zero_iff hσ.isNondegenerate
          (fundamentalVectorField_eq_zero_of_forall_smul_eq hp ξ), Subtype.forall]
      -- An element of the subgroup `T_ξ` acts on `M` as its image in `G`, by definition.
      rfl
    exact ⟨manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap hf hpchart hcrit,
      manifoldMorseIndex_neg_eq_two_mul_ncard_neg_of_weightMomentMap hf hpchart hcrit,
      hfix ▸ finrank_ker_criticalHessian_eq_two_mul_ncard_of_weightMomentMap hf hpchart hcrit,
      isManifoldNondegenerateCriticalPoint_iff_forall_ne_zero_of_weightMomentMap hf hpchart hcrit⟩

end SmoothTwoForm.IsMomentMap

end TauCeti
