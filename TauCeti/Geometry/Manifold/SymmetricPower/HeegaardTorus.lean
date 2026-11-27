/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold
public import TauCeti.Topology.Sym.Pi
import TauCeti.Geometry.Manifold.Complex.Orientation
import TauCeti.Geometry.Manifold.SymmetricPower.TotallyReal

/-!
# Heegaard tori are totally real embedded tori in the symmetric power, meeting transversally

Let `α` be a Hausdorff complex curve, and let `γ₁, …, γₙ : S¹ → α` be embeddings of the circle
`S¹ = AddCircle p` with pairwise disjoint images, such as the attaching circles `α₁, …, α_g` of a
Heegaard diagram on a Riemann surface `Σ`. The product of the circles

`Γ : (S¹)ⁿ → Sym α n`, `(θ₁, …, θₙ) ↦ {γ₁(θ₁), …, γₙ(θₙ)}`

parametrizes the torus `T_α = α₁ × ⋯ × αₙ` in the symmetric power, the boundary condition of the
holomorphic disks counted by Heegaard Floer homology; its image is
`Sym.pi fun i => Set.range (γ i)` (`Sym.range_ofFn_map`). This file shows that `Γ` is a totally
real embedding (`Sym.isTotallyRealEmbedding_ofFn_map`), of the same regularity `C^k`, `k ≥ 1`, as
the circles, for the elementary-symmetric charts of `Sym α n` (`TauCeti.symChartedSpace`) and the
almost complex structure of this complex manifold
(`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`). This is the form of a Lagrangian or
totally real boundary condition used by the compactness and Fredholm theory of holomorphic curves.

The three ingredients are the following.

* `Γ` is a closed embedding: the circles are compact, and since they are pairwise disjoint the
  unordered tuple `{γ₁(θ₁), …, γₙ(θₙ)}` determines the angles (`Sym.isClosedEmbedding_ofFn_map`).
* Read in a chart of `(S¹)ⁿ`, which lifts each angle to `ℝ`, and in an elementary-symmetric chart of
  `Sym α n`, `Γ` is the product of the lifted curves `t ↦ γᵢ([t])`. Near a tuple of distinct points
  the chart is an analytic function of the points, so `Γ` is as smooth as the curves
  (`Sym.contMDiff_ofFn_map`, from `TauCeti.contDiffAt_symChartAt_ofFn`).
* The derivative of `Γ` in these charts is a complex-linear injection applied to the diagonal map of
  the nonzero velocities of the curves, so its range is maximal totally real
  (`Sym.isMaximalTotallyRealMap_ofFn_map`, from
  `TauCeti.isMaximalTotallyReal_range_fderiv_symChartAt_ofFn`).

A second family of circles `δ₁, …, δₙ`, such as the `β`-curves, gives a second torus `T_β`. Its
points shared with `T_α` are the unordered tuples `{γ₁(x₁), …, γₙ(xₙ)} = {δ₁(y₁), …, δₙ(yₙ)}`, the
generators of the Heegaard Floer complex. At such a point the tangent spaces of `T_α` and `T_β` are
complementary, so that the two half-dimensional tori meet transversally, exactly when every point
`γᵢ(xᵢ) = δⱼ(yⱼ)` of the tuple is a transverse intersection of `γᵢ` and `δⱼ`
(`Sym.isCompl_range_mfderiv_ofFn_map_iff`, from
`TauCeti.isCompl_range_fderiv_symChartAt_ofFn_iff`). The intersections of the tori used as the
ends of holomorphic strips are thus transverse as soon as the attaching curves are.

## Main results

* `Sym.contMDiff_ofFn_map`: `Γ` is as smooth as the circles.
* `Sym.isMaximalTotallyRealMap_ofFn_map`: the tangent spaces of `T_α` are maximal totally real.
* `Sym.isTotallyRealEmbedding_ofFn_map`: `Γ` is a totally real embedding.
* `Sym.isCompl_range_mfderiv_ofFn_map_iff`: two such tori meet transversally at a common point
  exactly when the curves meet transversally at each point of the tuple.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.2 (the tori `T_α` and `T_β` in
  `Sym^g(Σ)` are totally real, and meet transversally when the attaching curves do).
-/

public section

open Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [ChartedSpace ℂ α]
  {n : ℕ} {p : ℝ} [Fact (0 < p)] {γ : Fin n → AddCircle p → α}

/-! ### Reading the torus and the curves in charts -/

/-- In the chart of the torus `(S¹)ⁿ` at `x`, which lifts the angles to `ℝ`, and the
elementary-symmetric chart at the image, a map `f` into the symmetric power reads as
`u ↦ f ([u₁], …, [uₙ])`. -/
private theorem writtenInExtChartAt_eventuallyEq [T2Space α] (x : Fin n → AddCircle p)
    (f : (Fin n → AddCircle p) → Sym α n) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    writtenInExtChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) x f
      =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x)]
        fun u => symChartAt (K := ℂ) (f x) (f fun i => (u i : AddCircle p)) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  filter_upwards [extChartAt_target_mem_nhds (I := ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x]
    with u hu
  simp only [writtenInExtChartAt, Function.comp_apply, AddCircle.extChartAt_pi_symm_apply x hu]
  simp

omit [TopologicalSpace α] [ChartedSpace ℂ α] in
/-- The lift of the angles of `x` by the chart of the torus at `x` returns the angles of `x`. -/
private theorem coe_extChartAt_pi_self_apply (x : Fin n → AddCircle p) (i : Fin n) :
    ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p) = x i := by
  simp only [extChartAt_pi_apply, AddCircle.coe_extChartAt_self]

omit [TopologicalSpace α] [ChartedSpace ℂ α] in
/-- At the lifts of the angles of `x`, curves with pairwise disjoint ranges pass through pairwise
distinct points. -/
private theorem injective_apply_coe_extChartAt_pi_self
    (hdisj : Pairwise (Function.onFun Disjoint fun i => range (γ i))) (x : Fin n → AddCircle p) :
    Function.Injective fun i =>
      γ i ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p) := by
  intro i j h
  by_contra hij
  simp only [coe_extChartAt_pi_self_apply] at h
  exact disjoint_left.1 (hdisj hij) (mem_range_self (x i)) ⟨x j, h.symm⟩

/-- At the lifts of the angles of `x`, the curves give the tuple at `x`, which lies in the source of
its chart. -/
private theorem ofFn_apply_coe_extChartAt_pi_self_mem_source [T2Space α] (x : Fin n → AddCircle p) :
    (Sym.ofFn fun i =>
      γ i ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p)) ∈
      (symChartAt (K := ℂ) (Sym.ofFn fun i => γ i (x i))).source := by
  simpa only [coe_extChartAt_pi_self_apply] using
    mem_symChartAt_source (K := ℂ) (Sym.ofFn fun i => γ i (x i))

/-- At the lift of the angle of `x i`, the `i`-th curve composed with the quotient map `ℝ → S¹` is
continuous, and read in the chart at its point, it has velocity the derivative of the curve at
`x i` on the unit vector. -/
private theorem continuousAt_and_hasDerivAt_apply_coe_extChartAt_pi_self
    {x : Fin n → AddCircle p} (hγ : ∀ i, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i))
    (i : Fin n) :
    ContinuousAt (fun t : ℝ => γ i t)
        (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i) ∧
      HasDerivAt (fun t : ℝ => chartAt ℂ
          (γ i (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ)) (γ i t))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i) (1 : ℝ))
        (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i) := by
  have hM : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i)
      ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i)) := by
    rw [coe_extChartAt_pi_self_apply]
    exact (hγ i).hasMFDerivAt
  exact ⟨hM.continuousAt.comp (AddCircle.contMDiff_coe p 0).continuous.continuousAt,
    (AddCircle.hasFDerivAt_chartAt_comp_coe hM).hasDerivAt⟩

/-! ### Smoothness and total reality -/

variable [T2Space α] [IsManifold 𝓘(ℂ) 1 α]

/-- The derivative of `(θᵢ)ᵢ ↦ {γ₁(θ₁), …, γₙ(θₙ)}` at `x` is the derivative, at the lifts of the
angles of `x`, of its expression in the chart of the torus and the elementary-symmetric chart at
its image, when the curves are differentiable and pass through pairwise distinct points. -/
private theorem hasMFDerivAt_ofFn_map {x : Fin n → AddCircle p}
    (hγ : ∀ i, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i))
    (hinj : Function.Injective fun i => γ i (x i)) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    HasMFDerivAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ)
      (fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i)) x
      (fderiv ℝ (fun t => symChartAt (K := ℂ) (Sym.ofFn fun i => γ i (x i))
        (Sym.ofFn fun i => γ i (t i : AddCircle p)))
        (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x)) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  have hinj' : Function.Injective fun i =>
      γ i ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p) := by
    simpa only [coe_extChartAt_pi_self_apply] using hinj
  have hc := continuousAt_and_hasDerivAt_apply_coe_extChartAt_pi_self hγ
  have hD := (differentiableAt_symChartAt_ofFn (γ := fun i (t : ℝ) => γ i t) hinj'
    (fun i => (hc i).1) (fun i => (hc i).2) _
    (ofFn_apply_coe_extChartAt_pi_self_mem_source (γ := γ) x)).hasFDerivAt
  have hcontx : ContinuousAt (fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i)) x :=
    Sym.continuous_ofFn.continuousAt.comp (continuousAt_pi.2 fun i =>
      ContinuousAt.comp (g := γ i) (f := fun y : Fin n → AddCircle p => y i)
        (hγ i).continuousAt (continuous_apply i).continuousAt)
  exact ⟨hcontx,
    (hD.congr_of_eventuallyEq (writtenInExtChartAt_eventuallyEq x _)).hasFDerivWithinAt⟩

/-- **The product of smooth circles is smooth in the symmetric power.** If the curves
`γᵢ : S¹ → α` are `C^k`, with pairwise disjoint ranges, then `(θᵢ)ᵢ ↦ {γ₁(θ₁), …, γₙ(θₙ)}` is a
`C^k` map from the torus `(S¹)ⁿ` to the symmetric power, for its elementary-symmetric charts. -/
theorem _root_.Sym.contMDiff_ofFn_map {k : ℕ∞ω} (hγ : ∀ i, ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) k (γ i))
    (hdisj : Pairwise (Function.onFun Disjoint fun i => range (γ i))) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    ContMDiff (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) k
      fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  intro x
  have hinj := injective_apply_coe_extChartAt_pi_self hdisj x
  have hs := ofFn_apply_coe_extChartAt_pi_self_mem_source (γ := γ) x
  set u₀ := extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x
  have hcont : Continuous fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i) :=
    Sym.continuous_ofFn.comp (continuous_pi fun i => (hγ i).continuous.comp (continuous_apply i))
  have hc (i : Fin n) : ContinuousAt (fun t : ℝ => γ i t) (u₀ i) :=
    ((hγ i).continuous.comp (AddCircle.contMDiff_coe p 0).continuous).continuousAt
  have hk (i : Fin n) : ContDiffAt ℝ k (fun t : ℝ => chartAt ℂ (γ i (u₀ i)) (γ i t)) (u₀ i) :=
    AddCircle.contDiffAt_chartAt_comp_coe ((hγ i).contMDiffAt)
  -- In charts, the map is the product of the lifted curves, which is as smooth as they are.
  have hd : ContDiffAt ℝ k (fun u : Fin n → ℝ => symChartAt (K := ℂ)
      (Sym.ofFn fun i => γ i (x i)) (Sym.ofFn fun i => γ i (u i : AddCircle p))) u₀ :=
    contDiffAt_symChartAt_ofFn (γ := fun i (t : ℝ) => γ i t) hinj hc hk _ hs
  rw [contMDiffAt_iff]
  refine ⟨hcont.continuousAt, ?_⟩
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  exact hd.congr_of_eventuallyEq (writtenInExtChartAt_eventuallyEq x
    fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i))

/-- **The torus `T_α` is totally real.** If the curves `γᵢ : S¹ → α` have injective derivatives and
pairwise disjoint ranges, then the tangent spaces of `(θᵢ)ᵢ ↦ {γ₁(θ₁), …, γₙ(θₙ)}` are maximal
totally real for the almost complex structure of the complex manifold `Sym α n`. -/
theorem _root_.Sym.isMaximalTotallyRealMap_ofFn_map
    (hγ : ∀ i y, Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) y))
    (hdisj : Pairwise (Function.onFun Disjoint fun i => range (γ i))) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    letI := isManifold_symChartedSpace (α := α) (n := n)
    IsMaximalTotallyRealMap (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ)
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin n → ℂ)
        (Sym α n)).almostComplexStructureAt
      fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  let := isManifold_symChartedSpace (α := α) (n := n)
  rw [isMaximalTotallyRealMap_iff]
  intro x
  have hdiff (i : Fin n) := mdifferentiableAt_of_mfderiv_injective (hγ i (x i))
  have hinj : Function.Injective fun i => γ i (x i) := by
    simpa only [coe_extChartAt_pi_self_apply] using injective_apply_coe_extChartAt_pi_self hdisj x
  have hc := continuousAt_and_hasDerivAt_apply_coe_extChartAt_pi_self hdiff
  have hv0 (i : Fin n) : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i) (1 : ℝ) ≠ 0 :=
    ((hγ i (x i)).ne (one_ne_zero' ℝ)).trans_eq (map_zero _)
  have hJ : ((SmoothAlmostComplexStructure.ofComplexManifold (Fin n → ℂ)
      (Sym α n)).almostComplexStructureAt (Sym.ofFn fun i => γ i (x i))).toLinearMap =
      (AlmostComplexStructure.ofComplexModule (Fin n → ℂ)).toLinearMap := by
    ext (v : Fin n → ℂ)
    exact (SmoothAlmostComplexStructure.almostComplexStructureAt_apply _ _ v).trans <|
      (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := Fin n → ℂ) (M := Sym α n)
        (Sym.ofFn fun i => γ i (x i)) v).trans
        (AlmostComplexStructure.ofComplexModule_apply (V := Fin n → ℂ) v).symm
  rw [(hasMFDerivAt_ofFn_map hdiff hinj).mfderiv, hJ]
  exact isMaximalTotallyReal_range_fderiv_symChartAt_ofFn (γ := fun i (t : ℝ) => γ i t)
    (injective_apply_coe_extChartAt_pi_self hdisj x) (fun i => (hc i).1)
    (fun i => (hc i).2) hv0 _ (ofFn_apply_coe_extChartAt_pi_self_mem_source (γ := γ) x)

/-- **The Heegaard torus is a totally real embedding.** If `γᵢ : S¹ → α` are `C^k` embeddings of a
circle, `k ≥ 1`, with pairwise disjoint images, such as the attaching circles of a Heegaard
diagram on a Riemann surface, then `(θᵢ)ᵢ ↦ {γ₁(θ₁), …, γₙ(θₙ)}` is a `C^k` totally real embedding
of the torus `(S¹)ⁿ` into the complex manifold `Sym α n`. Its image is the torus
`Sym.pi fun i => Set.range (γ i)` (`Sym.range_ofFn_map`). -/
theorem _root_.Sym.isTotallyRealEmbedding_ofFn_map {k : ℕ∞ω} (hk : 1 ≤ k)
    (hγ : ∀ i, Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℂ) k (γ i))
    (hdisj : Pairwise (Function.onFun Disjoint fun i => range (γ i))) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    letI := isManifold_symChartedSpace (α := α) (n := n)
    IsTotallyRealEmbedding (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ) k
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin n → ℂ)
        (Sym α n)).almostComplexStructureAt
      fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  let := isManifold_symChartedSpace (α := α) (n := n)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact absurd hk (by simp)
  refine isTotallyRealEmbedding_of_contMDiff hk
    (Sym.contMDiff_ofFn_map (fun i => (hγ i).isImmersion.contMDiff) hdisj)
    (Sym.isClosedEmbedding_ofFn_map (fun i => (hγ i).isEmbedding.continuous)
      (fun i => (hγ i).isEmbedding.injective) hdisj).isEmbedding ?_
    (Sym.isMaximalTotallyRealMap_ofFn_map
      (fun i y => (hγ i).isImmersion.mfderiv_injective hk0 y) hdisj)
  simp [Module.finrank_pi_fintype, mul_comm]

/-! ### Transversality of two tori -/

/-- **The tori `T_α` and `T_β` meet transversally exactly where the curves do.** Let
`γᵢ, δⱼ : S¹ → α` be curves in a complex curve, differentiable at the angles `x i` and `y j`,
such that the points `γᵢ(xᵢ)` are pairwise distinct and form the same unordered tuple as the
points `δⱼ(yⱼ)`. Then the tangent spaces at this common point of `Sym α n` of the two tori
`(θᵢ)ᵢ ↦ {γ₁(θ₁), …, γₙ(θₙ)}` and `(θⱼ)ⱼ ↦ {δ₁(θ₁), …, δₙ(θₙ)}` are complementary exactly when,
whenever `γᵢ(xᵢ) = δⱼ(yⱼ)`, the velocities of `γᵢ` and `δⱼ` there are linearly independent over
`ℝ`. For the attaching circles of a Heegaard diagram, whose `α`-curves are pairwise disjoint, a
generator is a transverse intersection point of `T_α` and `T_β` exactly when each of its points is
a transverse intersection of an `α`-curve and a `β`-curve. -/
theorem _root_.Sym.isCompl_range_mfderiv_ofFn_map_iff {δ : Fin n → AddCircle p → α}
    {x y : Fin n → AddCircle p} (hγ : ∀ i, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i))
    (hδ : ∀ j, MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (δ j) (y j))
    (hinj : Function.Injective fun i => γ i (x i))
    (hxy : (Sym.ofFn fun i => γ i (x i)) = Sym.ofFn fun j => δ j (y j)) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    IsCompl
        (LinearMap.range (mfderiv (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ)
          (fun x : Fin n → AddCircle p => Sym.ofFn fun i => γ i (x i)) x).toLinearMap)
        (LinearMap.range (mfderiv (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) 𝓘(ℝ, Fin n → ℂ)
          (fun y : Fin n → AddCircle p => Sym.ofFn fun j => δ j (y j)) y).toLinearMap) ↔
      ∀ i j, γ i (x i) = δ j (y j) →
        LinearIndependent ℝ ![mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (γ i) (x i) (1 : ℝ),
          mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (δ j) (y j) (1 : ℝ)] := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  -- the two ordered tuples differ by a permutation, so both families pass through distinct points
  obtain ⟨τ, hτ⟩ := Sym.ofFn_eq_ofFn_iff.1 hxy
  have hτj (j : Fin n) : γ (τ j) (x (τ j)) = δ j (y j) := congrFun hτ j
  have hinjδ : Function.Injective fun j => δ j (y j) := by
    rw [← hτ]
    exact hinj.comp τ.injective
  have hσ (i : Fin n) : δ (τ.symm i)
      ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) y y (τ.symm i) : ℝ) : AddCircle p) =
      γ i ((extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℝ)) x x i : ℝ) : AddCircle p) := by
    rw [coe_extChartAt_pi_self_apply, coe_extChartAt_pi_self_apply, ← hτj, τ.apply_symm_apply]
  have hcγ := continuousAt_and_hasDerivAt_apply_coe_extChartAt_pi_self hγ
  have hcδ := continuousAt_and_hasDerivAt_apply_coe_extChartAt_pi_self hδ
  -- in the chart at the common point, this is the transversality of the products of curves
  rw [(hasMFDerivAt_ofFn_map hγ hinj).mfderiv, (hasMFDerivAt_ofFn_map hδ hinjδ).mfderiv, ← hxy]
  refine (isCompl_range_fderiv_symChartAt_ofFn_iff (σ := τ.symm)
    (by simpa only [coe_extChartAt_pi_self_apply] using hinj) hσ (fun i => (hcγ i).1)
    (fun j => (hcδ j).1) (fun i => (hcγ i).2) (fun j => (hcδ j).2) _
    (ofFn_apply_coe_extChartAt_pi_self_mem_source x)).trans ?_
  -- the point `γ i (x i)` lies on `δ j` exactly for `j = τ⁻¹ i`
  refine ⟨fun h i j hij => ?_, fun h i => h i (τ.symm i) (by rw [← hτj, τ.apply_symm_apply])⟩
  obtain rfl : j = τ.symm i :=
    τ.injective (by rw [τ.apply_symm_apply]; exact hinj ((hτj j).trans hij.symm))
  exact h i

end TauCeti
