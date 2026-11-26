/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Smooth
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Strict convexity and strict concavity of the boundary are open conditions

Let `M` be a Riemannian manifold with boundary. The points of `∂M` at which the boundary is
strictly convex, respectively strictly concave, form an open subset of `∂M`
(`TauCeti.isOpen_setOf_isStrictlyConvexAt`, `TauCeti.isOpen_setOf_isStrictlyConcaveAt`).

The proof reads `II` in a local frame of `T∂M`: near `q₀`, transporting `II_q` to the model fibre
along a local trivialization of `T∂M` gives a family of bilinear forms on a fixed vector space
whose entries on a basis are continuous, because `II` pairs continuous tangent fields to a
continuous function. Positive definiteness is an open condition on such a family
(`LinearMap.BilinForm.eventually_posDef_of_continuousAt`), by compactness of the unit sphere of
the finite-dimensional model fibre.

## Main results

* `LinearMap.BilinForm.eventually_posDef_of_continuousAt`: a family of bilinear forms on a
  finite-dimensional real space, positive definite at `x₀` and with entries on a basis continuous
  at `x₀`, is positive definite near `x₀`.
* `TauCeti.IsStrictlyConvexAt.eventually`, `TauCeti.isOpen_setOf_isStrictlyConvexAt`:
  strict convexity of the boundary is an open condition.
* `TauCeti.IsStrictlyConcaveAt.eventually`, `TauCeti.isOpen_setOf_isStrictlyConcaveAt`:
  strict concavity of the boundary is an open condition.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Definition 3.1.7.
-/

public section

noncomputable section

open Bundle Filter Function Topology
open scoped Manifold ContDiff

namespace LinearMap.BilinForm

/-- **Positive definiteness is an open condition.** Let `B x` be bilinear forms on a real normed
space `E` with a finite basis `b`, depending on a parameter `x`, whose entries
`B x (b i) (b j)` on a basis `b` are continuous at `x₀`. If `B x₀` is positive definite, then so is
`B x` for every `x` near `x₀`. -/
theorem eventually_posDef_of_continuousAt {X ι E : Type*} [TopologicalSpace X] [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Module.Basis ι ℝ E)
    {B : X → LinearMap.BilinForm ℝ E} {x₀ : X}
    (hB : ∀ i j, ContinuousAt (fun x ↦ B x (b i) (b j)) x₀)
    (h₀ : (B x₀).toQuadraticMap.PosDef) :
    ∀ᶠ x in 𝓝 x₀, (B x).toQuadraticMap.PosDef := by
  have := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have key : ∀ x v, B x v v = ∑ i, ∑ j, b.repr v i * b.repr v j * B x (b i) (b j) := by
    intro x v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hr : ∀ i, Continuous fun v : E ↦ b.repr v i :=
    fun i ↦ (b.coord i).continuous_of_finiteDimensional
  have hcont : ∀ v₀ : E, ContinuousAt
      (fun p : X × E ↦ ∑ i, ∑ j, b.repr p.2 i * b.repr p.2 j * B p.1 (b i) (b j)) (x₀, v₀) := by
    intro v₀
    refine tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ ?_
    exact (((hr i).continuousAt.comp continuousAt_snd).mul
      ((hr j).continuousAt.comp continuousAt_snd)).mul
      (ContinuousAt.comp (f := Prod.fst) (x := ((x₀, v₀) : X × E)) (hB i j) continuousAt_fst)
  have hS : ∀ᶠ x in 𝓝 x₀, ∀ v ∈ Metric.sphere (0 : E) 1, 0 < B x v v := by
    refine (isCompact_sphere 0 1).eventually_forall_of_forall_eventually fun v hv ↦ ?_
    have hv0 : v ≠ 0 := ne_zero_of_mem_unit_sphere ⟨v, hv⟩
    have hpos : 0 < ∑ i, ∑ j, b.repr v i * b.repr v j * B x₀ (b i) (b j) := by
      rw [← key]
      exact h₀ v hv0
    filter_upwards [(hcont v).eventually (lt_mem_nhds hpos)] with p hp
    rw [key]
    exact hp
  filter_upwards [hS] with x hx v hv
  rw [LinearMap.BilinMap.toQuadraticMap_apply]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hw := hx (‖v‖⁻¹ • v) (by simp [norm_smul, hn.ne'])
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at hw
  nlinarith [mul_pos (inv_pos.2 hn) (inv_pos.2 hn)]

end LinearMap.BilinForm

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

/-- Near `q₀`, transporting a bilinear form on `T_q∂M` along the local trivialization of `T∂M` at
`q₀` gives a bilinear form on the model fibre; for `II` its entries on a basis are continuous at
`q₀`. -/
private theorem continuousAt_boundarySecondFundamentalForm_symmL (q₀ : (𝓡∂ (n + 1)).boundary M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun q : (𝓡∂ (n + 1)).boundary M ↦ boundarySecondFundamentalForm q
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀).symmL ℝ q v)
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀).symmL ℝ q w)) q₀ := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  have hq₀ : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  have hsec : ∀ y : EuclideanSpace ℝ (Fin n),
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent 0
        (T% (fun q ↦ e.symmL ℝ q y)) q₀ := by
    intro y
    refine (e.contMDiffOn_section_baseSet_iff.2 ((contMDiffOn_const (c := y)).congr ?_)).contMDiffAt
      (e.open_baseSet.mem_nhds hq₀)
    intro q hq
    simp [hq]
  exact (contMDiffAt_boundarySecondFundamentalForm_apply (k := 0) (m := 2) (l := 1) (by norm_num)
    (by norm_num) (hsec v) (hsec w)).continuousAt

/-- **Strict convexity of the boundary is an open condition**: if `∂M` is strictly convex at `q₀`,
it is strictly convex at every point of `∂M` near `q₀`. -/
theorem IsStrictlyConvexAt.eventually {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConvexAt q₀) : ∀ᶠ q in 𝓝 q₀, IsStrictlyConvexAt q := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  have hq₀ : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  let B : (𝓡∂ (n + 1)).boundary M → LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
    fun q ↦ (boundarySecondFundamentalForm q).compl₁₂ (e.symmL ℝ q).toLinearMap
      (e.symmL ℝ q).toLinearMap
  have hpos : ∀ q ∈ e.baseSet, IsStrictlyConvexAt q ↔ (B q).toQuadraticMap.PosDef := by
    intro q hq
    rw [isStrictlyConvexAt_iff]
    constructor
    · intro hII x hx
      refine hII _ fun h0 ↦ hx ?_
      rw [← e.continuousLinearMapAt_symmL (R := ℝ) hq x]
      simp only [ContinuousLinearMap.coe_coe] at h0 ⊢
      rw [h0, map_zero]
    · intro hB u hu
      have hx : e.continuousLinearMapAt ℝ q u ≠ 0 := fun h0 ↦ hu (by
        rw [← e.symmL_continuousLinearMapAt (R := ℝ) hq u, h0, map_zero])
      have := hB _ hx
      rwa [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₁₂_apply,
        ContinuousLinearMap.coe_coe, e.symmL_continuousLinearMapAt (R := ℝ) hq u] at this
  have hB : (B q₀).toQuadraticMap.PosDef := (hpos q₀ hq₀).1 h
  filter_upwards [LinearMap.BilinForm.eventually_posDef_of_continuousAt
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (fun i j ↦ continuousAt_boundarySecondFundamentalForm_symmL q₀ _ _) hB,
    e.open_baseSet.mem_nhds hq₀] with q hq hqe
  exact (hpos q hqe).2 hq

/-- **Strict concavity of the boundary is an open condition**: if `∂M` is strictly concave at
`q₀`, it is strictly concave at every point of `∂M` near `q₀`. -/
theorem IsStrictlyConcaveAt.eventually {q₀ : (𝓡∂ (n + 1)).boundary M}
    (h : IsStrictlyConcaveAt q₀) : ∀ᶠ q in 𝓝 q₀, IsStrictlyConcaveAt q := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  have hq₀ : q₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q₀
  let B : (𝓡∂ (n + 1)).boundary M → LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin n)) :=
    fun q ↦ -(boundarySecondFundamentalForm q).compl₁₂ (e.symmL ℝ q).toLinearMap
      (e.symmL ℝ q).toLinearMap
  have hpos : ∀ q ∈ e.baseSet, IsStrictlyConcaveAt q ↔ (B q).toQuadraticMap.PosDef := by
    intro q hq
    rw [isStrictlyConcaveAt_iff]
    constructor
    · intro hII x hx
      have hu : e.symmL ℝ q x ≠ 0 := fun h0 ↦ hx (by
        rw [← e.continuousLinearMapAt_symmL (R := ℝ) hq x, h0, map_zero])
      have := hII _ hu
      simp only [B, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.neg_apply,
        LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe]
      linarith [this]
    · intro hB u hu
      have hx : e.continuousLinearMapAt ℝ q u ≠ 0 := fun h0 ↦ hu (by
        rw [← e.symmL_continuousLinearMapAt (R := ℝ) hq u, h0, map_zero])
      have := hB _ hx
      simp only [B, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.neg_apply,
        LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe,
        e.symmL_continuousLinearMapAt (R := ℝ) hq u] at this
      linarith
  have hB : (B q₀).toQuadraticMap.PosDef := (hpos q₀ hq₀).1 h
  filter_upwards [LinearMap.BilinForm.eventually_posDef_of_continuousAt
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (fun i j ↦ (continuousAt_boundarySecondFundamentalForm_symmL q₀ _ _).neg) hB,
    e.open_baseSet.mem_nhds hq₀] with q hq hqe
  exact (hpos q hqe).2 hq

variable (n M) in
/-- The set of points of `∂M` at which the boundary is strictly convex is open in `∂M`. -/
theorem isOpen_setOf_isStrictlyConvexAt :
    IsOpen {q : (𝓡∂ (n + 1)).boundary M | IsStrictlyConvexAt q} :=
  isOpen_iff_mem_nhds.2 fun _ hq ↦ IsStrictlyConvexAt.eventually hq

variable (n M) in
/-- The set of points of `∂M` at which the boundary is strictly concave is open in `∂M`. -/
theorem isOpen_setOf_isStrictlyConcaveAt :
    IsOpen {q : (𝓡∂ (n + 1)).boundary M | IsStrictlyConcaveAt q} :=
  isOpen_iff_mem_nhds.2 fun _ hq ↦ IsStrictlyConcaveAt.eventually hq

end TauCeti
