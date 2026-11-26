/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Vertex
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Lattice
public import TauCeti.Geometry.Toric.Delzant.VertexCone
import TauCeti.Geometry.Manifold.GroupAction.IdentityPrinciple

/-!
# The moment polytope of a symplectic toric manifold is Delzant

Let a torus `G`, a compact connected commutative Lie group with Lie algebra `𝔤`, act smoothly and
effectively on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ : M → 𝔤*`, and suppose that `dim M = 2 dim G`. Let `i : N →+ 𝔤` be an integral
lattice which is the period lattice of `G`: `exp (2π ξ) = 1` exactly when `ξ ∈ i(N)`. This file
proves that the moment polytope `Δ = conv μ(M)` is a Delzant polytope for this lattice
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range`):
it is cut out by finitely many inequalities `⟨y, i(u)⟩ ≥ c` with primitive inward normals `u ∈ N`,
exactly `dim G` of them active at each vertex, with normals forming a `ℤ`-basis of `N`.

The vertices of `Δ` are the images of the finitely many fixed points
(`TauCeti.SmoothTwoForm.IsMomentMap.bijOn_fixedPoints_extremePoints_convexHull_range`), so by
`TauCeti.Toric.existsUnique_isDelzant_facetPolyhedron_eq` it suffices to show that `Δ` has a smooth
corner at the image `v = μ(p)` of each fixed point `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints`).
This is read off the weight normal form at `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`): in a chart `z = (q, p)` of `M` at
`p` onto a ball of `ℂⁿ`, the group acts by rotating `zₖ` by the character `χₖ` with real weight
`αₖ`, and `μ = μ(p) - ½ Σₖ |zₖ|² αₖ`.

* **The weights are dual to a lattice basis.** An element `ξ ∈ 𝔤` which rotates every coordinate
  by a multiple of `2π` fixes the chart pointwise. By the identity principle for compact group
  actions (`TauCeti.eq_one_of_eventuallyEq_id`) and effectiveness, `exp ξ = 1`, so
  `ξ ∈ 2π i(N)`. That is,
  the local model is an effective action of `𝔤 / 2π i(N)`, and its `n = dim G` weights are dual to
  a `ℤ`-basis `b` of `N` (`TauCeti.exists_basis_iff_forall_weightRotation_eq_id_iff`).
* **The corner inequalities hold globally.** For `ξ` on which every weight is positive, `μ^ξ` has a
  local maximum at `p`; when the one-parameter subgroup of `ξ` is moreover dense in `G`, `μ^ξ` is a
  Morse function with even indices, so this local maximum is global
  (`TauCeti.SmoothTwoForm.IsMomentMap.isMaxOn_of_isLocalMax`). Such `ξ` are dense in the open cone
  of positive weights, so by continuity `μ^ξ ≤ μ^ξ(p)` on `M` for every `ξ` in its closure
  (`TauCeti.SmoothTwoForm.IsMomentMap.apply_le_apply_of_mem_closure`), in particular for
  `ξ = i(bₖ)`. Hence `Δ` lies in the cone `{y | y(i(bₖ)) ≤ v(i(bₖ)) for all k}`.
* **The chart fills the cone near `v`.** The image of the weight model is exactly the simplicial
  cone of `b` (`TauCeti.range_weightMomentMap_of_basis`), and a point of the cone at distance
  `Σₖ -2 ⟨y - v, i(bₖ)⟩ < r²` from `v` is the image of a point of the chart ball of radius `r`.

So near `v` the polytope `Δ` is the cone with inward normals `-bₖ`, a `ℤ`-basis of `N`.

This is the polytope half of Delzant's theorem that the moment image of a symplectic toric
manifold is a Delzant polytope; the other half is convexity of `μ(M)` itself, `μ(M) = Δ`, which is
the Atiyah–Guillemin–Sternberg convexity theorem.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints`: at the image of a fixed point,
  the moment polytope is cut out by inequalities whose inward normals form a `ℤ`-basis of the
  lattice.
* `existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range`: the moment polytope of a
  symplectic toric manifold is a Delzant polytope, with a unique facet presentation.
* `existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range_periodLattice`: the same for the
  period lattice `TauCeti.periodLatticeMap I G` of `G` itself.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 28.2 and Sections 27–29.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, Section 2 (the local form of the moment map at a fixed point).
-/

public section

noncomputable section

open Filter Module Real Set Topology
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [FaithfulSMul G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {N : Type*} [AddCommGroup N] {i : N →+ E}

namespace SmoothTwoForm.IsMomentMap

/-! ### The weights at a fixed point -/

section WeightChart

variable {p : M} {n : ℕ} {χ : Fin n → G →ₜ* Circle} {α : Fin n → StrongDual ℝ E}
  {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}

omit [I.Boundaryless] [PreconnectedSpace G] in
/-- **The weight chart of an effective action is effective.** In a weight chart at a fixed point of
an effective action of a compact commutative Lie group on a connected manifold, an element `ξ` of
the Lie algebra rotating every coordinate by a multiple of `2π` has `exp ξ = 1`. -/
private theorem mulInvariantExp_eq_one_of_weightRotation_eq_id
    (hχ : ∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ))
    (hpchart : p ∈ chart.source)
    (hequiv : ∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧
      chart (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart x))
    {ξ : GroupLieAlgebra I G}
    (hξ : weightRotation (fun k ↦ α k ξ) = ContinuousLinearMap.id ℝ _) :
    mulInvariantExp (I := I) ξ = 1 := by
  -- `exp ξ` fixes every point of the chart, since it rotates every coordinate by a multiple of
  -- `2π`; by the identity principle and effectiveness, it is `1`.
  refine eq_one_of_eventuallyEq_id I' I (p := p)
    (eventually_of_mem (chart.open_source.mem_nhds hpchart) fun x hx ↦ ?_)
  obtain ⟨hgx, hchart⟩ := hequiv (mulInvariantExp (I := I) ξ) x hx
  refine chart.injOn hgx hx ?_
  rw [hchart]
  simp only [hχ, weightRotation_arg_circleExp, hξ, ContinuousLinearMap.id_apply, id_eq]

omit [I.Boundaryless] [PreconnectedSpace G] in
/-- **The weights at a fixed point are dual to a lattice basis.** In a weight chart at a fixed point
of a symplectic toric manifold, for an integral lattice `i : N →+ 𝔤` with `exp (2π ξ) = 1` exactly
when `ξ ∈ i(N)`, the weights `α` are dual to a `ℤ`-basis `b` of `N`. -/
private theorem exists_basis_apply_eq_coord (hi : Toric.IsIntegralLattice i)
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E)
    (hχ : ∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ))
    (hint : ∀ k (ξ : GroupLieAlgebra I G), mulInvariantExp (I := I) ((2 * π) • ξ) = 1 →
      ∃ m : ℤ, α k ξ = m)
    (hpchart : p ∈ chart.source)
    (hequiv : ∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧
      chart (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart x))
    (hgen : ∀ x ∈ chart.source, ∀ ξ : GroupLieAlgebra I G,
      mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) chart x
        (fundamentalVectorField I' ξ x) = weightInfinitesimalAction α (chart x) ξ) :
    ∃ b : Module.Basis (Fin n) ℤ N, ∀ j m, α j (i m) = b.coord j m := by
  -- There are `dim G` weights, since they are the coordinates of an isomorphism `𝔤 ≃ ℝⁿ`.
  have hcard : Fintype.card (Fin n) ≤ finrank ℝ E := by
    have h := (LinearEquiv.ofBijective _ (bijective_pi_of_mfderiv_eq hgen hpchart hdim)).finrank_eq
    rw [Module.finrank_fin_fun] at h
    exact (Fintype.card_fin n).trans_le h.ge
  refine (exists_basis_iff_forall_weightRotation_eq_id_iff hi hcard).2 fun ξ ↦ ⟨fun hξ ↦ ?_, ?_⟩
  · -- A trivially acting element of the local model has `exp ξ = 1`, so `ξ ∈ 2π i(N)`.
    have h1 := mulInvariantExp_eq_one_of_weightRotation_eq_id hχ hpchart hequiv hξ
    obtain ⟨m, hm⟩ := (hperiod ((2 * π)⁻¹ • ξ)).1 (by rwa [smul_inv_smul₀ two_pi_pos.ne'])
    exact ⟨m, by rw [hm, smul_inv_smul₀ two_pi_pos.ne']⟩
  · -- Conversely the weights are integral on the period lattice.
    rintro ⟨m, rfl⟩
    refine (weightRotation_eq_id_iff _).2 fun j ↦ ?_
    obtain ⟨k, hk⟩ := hint j (i m) ((hperiod (i m)).2 (mem_range_self m))
    exact ⟨k, by rw [map_smul, hk, smul_eq_mul, mul_comm]⟩

/-- **Components with nonnegative weights are maximal at the fixed point.** In a weight chart at a
fixed point `p` of a symplectic toric manifold, if every weight is nonnegative on `ξ`, then `μ^ξ`
attains its maximum at `p`. -/
private theorem apply_le_apply_of_forall_nonneg
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) (hpchart : p ∈ chart.source)
    (hgen : ∀ x ∈ chart.source, ∀ ξ : GroupLieAlgebra I G,
      mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) chart x
        (fundamentalVectorField I' ξ x) = weightInfinitesimalAction α (chart x) ξ)
    (hμchart : ∀ x ∈ chart.source, ∀ ξ, μ x ξ = μ p ξ + weightMomentMap α (chart x) ξ)
    {ξ : GroupLieAlgebra I G} (hξ : ∀ k, 0 ≤ α k ξ) (x : M) :
    μ x ξ ≤ μ p ξ := by
  -- On the chart, `μ^ξ' = μ^ξ'(p) - ½ Σₖ αₖ(ξ') |zₖ|²`, so `p` is a local maximum of `μ^ξ'` for
  -- every `ξ'` in the open cone `V` of elements on which every weight is positive.
  set V : Set (GroupLieAlgebra I G) := {ξ' | ∀ k, 0 < α k ξ'}
  have hV : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun k ↦ isOpen_lt continuous_const (α k).continuous
  have hmax (ξ' : GroupLieAlgebra I G) (hξ'V : ξ' ∈ V) : IsLocalMax (fun y ↦ μ y ξ') p :=
    Filter.mem_of_superset (chart.open_source.mem_nhds hpchart) fun y hy ↦ by
      dsimp only [mem_ofPred_eq]
      rw [hμchart y hy ξ', add_le_iff_nonpos_right, weightMomentMap_apply α (chart y) ξ']
      refine mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Finset.sum_nonneg fun k _ ↦ ?_)
      exact mul_nonneg (hξ'V k).le (by positivity)
  -- These local maxima are global on the closure of `V`, which contains `ξ`.
  refine h.apply_le_apply_of_mem_closure hσ hG hdim hV hmax ?_ x
  -- The weights are the coordinates of an isomorphism `𝔤 ≃ ℝⁿ`, so some `ξ₁` has all weights `1`,
  -- and `ξ + t ξ₁ ∈ V` for `t > 0` tends to `ξ`.
  set A : GroupLieAlgebra I G →ₗ[ℝ] Fin n → ℝ := LinearMap.pi fun k ↦ (α k).toLinearMap
  have hA (ξ' : GroupLieAlgebra I G) (k : Fin n) : A ξ' k = α k ξ' := LinearMap.pi_apply _ _ _
  obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ₁, A ξ₁ = fun _ ↦ (1 : ℝ) :=
    (bijective_pi_of_mfderiv_eq hgen hpchart hdim).2 _
  refine mem_closure_of_tendsto (f := fun t : ℝ ↦ ξ + t • ξ₁) (b := 𝓝[>] 0)
    ((Continuous.tendsto' (by fun_prop) 0 _ (by simp)).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht k
  rw [← hA, map_add, map_smul, hξ₁]
  simpa [hA] using add_pos_of_nonneg_of_pos (hξ k) ht

end WeightChart

/-! ### Smooth corners and the Delzant property -/

/-- **The moment polytope has a smooth corner at the image of each fixed point.** Let a torus `G`
act smoothly and effectively on a compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`; let `i : N →+ 𝔤` be an integral
lattice with `exp (2π ξ) = 1` exactly when `ξ ∈ i(N)`. At the image `v = μ(p)` of a fixed point
`p`, there is a `ℤ`-basis `s` of `N` such that near `v` the moment polytope `conv μ(M)` is cut out
by the inequalities `⟨v, i(u)⟩ ≤ ⟨y, i(u)⟩` for `u ∈ s`. -/
theorem exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) (hi : Toric.IsIntegralLattice i)
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i)
    {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∃ s : Set N, LinearIndepOn ℤ id s ∧ Submodule.span ℤ s = ⊤ ∧
      ∀ᶠ y in 𝓝 (LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E),
        y ∈ convexHull ℝ (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) ↔
          ∀ u ∈ s, (LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E) (i u) ≤ y (i u) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  set f : M → StrongDual ℝ E := fun x ↦ LinearMap.toContinuousLinearMap (μ x)
  obtain ⟨n, χ, α, chart, r, hχ, hint, hpchart, -, hr, htarget, hequiv, -, hgen, hμchart⟩ :=
    h.exists_weightModelChart hσ hG (MulAction.mem_fixedPoints.1 hp)
  obtain ⟨b, hα⟩ := exists_basis_apply_eq_coord hi hperiod hdim hχ hint hpchart hequiv hgen
  -- The inward normals are `-bₖ`.
  set b' := b.map (LinearEquiv.neg ℤ)
  have hb' (k : Fin n) : b' k = -b k := by simp [b']
  -- Every point of the polytope lies in the cone `{y | y(i(bₖ)) ≤ v(i(bₖ)) for all k}`, since
  -- each weight `αⱼ` is nonnegative on `i(bₖ)`.
  have hcone : convexHull ℝ (range f) ⊆ {y | ∀ k, y (i (b k)) ≤ f p (i (b k))} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨x, rfl⟩ k
      refine apply_le_apply_of_forall_nonneg h hσ hG hdim hpchart hgen hμchart (fun j ↦ ?_) x
      rw [hα, Module.Basis.coord_apply, Module.Basis.repr_self]
      exact Int.cast_nonneg (by rw [Finsupp.single_apply]; split_ifs <;> norm_num)
    · simp only [ofPred_forall]
      exact convex_iInter fun k ↦ convex_halfSpace_le
        ((ContinuousLinearMap.apply ℝ ℝ (i (b k))).isLinear) _
  -- Near `v = f p`, every point of that cone is the image of a point of the chart ball.
  set U : Set (StrongDual ℝ E) := {y | ∑ k, -2 * (y - f p) (i (b k)) < r ^ 2}
  have hU : U ∈ 𝓝 (f p) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp [hr])
  refine ⟨range b', (linearIndepOn_id_range_iff b'.injective).2 b'.linearIndependent,
    b'.span_eq, ?_⟩
  filter_upwards [hU] with y hy
  simp only [forall_mem_range, hb', map_neg, neg_le_neg_iff]
  refine ⟨fun hyΔ k ↦ hcone hyΔ k, fun hyc ↦ subset_convexHull ℝ _ ?_⟩
  obtain ⟨z, hz⟩ : y - f p ∈ range (weightMomentMap α) := by
    rw [range_weightMomentMap_of_basis hi b hα]
    exact fun k ↦ by rw [sub_apply, sub_nonpos]; exact hyc k
  -- The point `z` lies in the chart ball, since `‖z‖² = Σₖ -2 ⟨y - v, i(bₖ)⟩ < r²`.
  have hzt : z ∈ chart.target := by
    rw [htarget, mem_ofPred_eq, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun k _ ↦ ?_) hy
    rw [← hz, weightMomentMap_apply_basis b hα]
    ring
  refine ⟨chart.symm z, ContinuousLinearMap.ext fun ξ ↦ ?_⟩
  have hξ := hμchart _ (chart.map_target hzt) ξ
  rw [chart.right_inv hzt, hz, sub_apply] at hξ
  exact hξ.trans (add_sub_cancel _ _)

/-- **The moment polytope of a symplectic toric manifold is Delzant.** Let a torus `G` act smoothly
and effectively on a nonempty compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`; let `i : N →+ 𝔤` be an integral
lattice with `exp (2π ξ) = 1` exactly when `ξ ∈ i(N)`. Then the moment polytope `conv μ(M)` is a
Delzant polytope: there is a unique finite set `F` of pairs (inward normal, support constant) whose
Delzant presentation cuts out `conv μ(M)`. -/
theorem existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) (hi : Toric.IsIntegralLattice i)
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i) :
    ∃! F : Set (N × ℝ), F.Finite ∧
      Toric.IsDelzant i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) ∧
      Toric.facetPolyhedron i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) =
        convexHull ℝ (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  set f : M → StrongDual ℝ E := fun x ↦ LinearMap.toContinuousLinearMap (μ x)
  set L : Module.Dual ℝ (GroupLieAlgebra I G) →ₗ[ℝ] StrongDual ℝ E :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] StrongDual ℝ E).toLinearMap
  -- The polytope is the convex hull of the images of the finitely many fixed points.
  have hfin := h.finite_fixedPoints_of_faithfulSMul hσ hG hdim
  -- Here `f = L ∘ μ` by definition, so `conv f(M) = L (conv μ(M)) = L (conv μ(M^G))`.
  have hconv : convexHull ℝ (range f) = convexHull ℝ (f '' MulAction.fixedPoints G M) := by
    rw [show range f = L '' range μ from range_comp L μ, ← LinearMap.image_convexHull,
      h.convexHull_range_eq_convexHull_image_fixedPoints hσ.isNondegenerate,
      LinearMap.image_convexHull, image_image]
    rfl
  refine Toric.existsUnique_isDelzant_facetPolyhedron_eq hi
    ⟨f (Classical.arbitrary M), subset_convexHull ℝ _ (mem_range_self _)⟩
    ?_ (convex_convexHull ℝ _) ?_ fun v hv ↦ ?_
  · rw [hconv]
    exact (hfin.image f).isCompact_convexHull (𝕜 := ℝ)
  · rw [hconv]
    exact (hfin.image f).subset (extremePoints_convexHull_subset (𝕜 := ℝ))
  -- Each vertex is the image of a fixed point, where the polytope has a smooth corner.
  rw [hconv] at hv
  obtain ⟨p, hp, rfl⟩ := extremePoints_convexHull_subset hv
  exact h.exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints hσ hG hdim hi hperiod hp

/-- **The moment polytope is Delzant for the period lattice.** The moment polytope `conv μ(M)` of a
symplectic toric manifold is a Delzant polytope for the period lattice
`Λ_ℤ = {X | exp (2π X) = 1}` of `G` (`TauCeti.periodLattice`), read in `𝔤` through the
identification of left-invariant derivations with tangent vectors at `1`. -/
theorem existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range_periodLattice [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) :
    ∃! F : Set (periodLattice I G × ℝ), F.Finite ∧
      Toric.IsDelzant (periodLatticeMap I G) (fun j : F ↦ (j : periodLattice I G × ℝ).1)
        (fun j : F ↦ (j : periodLattice I G × ℝ).2) ∧
      Toric.facetPolyhedron (periodLatticeMap I G) (fun j : F ↦ (j : periodLattice I G × ℝ).1)
        (fun j : F ↦ (j : periodLattice I G × ℝ).2) =
        convexHull ℝ (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) :=
  h.existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range hσ hG hdim
    (isIntegralLattice_periodLatticeMap I G) (mulInvariantExp_two_pi_smul_eq_one_iff I G)

end SmoothTwoForm.IsMomentMap

end TauCeti
