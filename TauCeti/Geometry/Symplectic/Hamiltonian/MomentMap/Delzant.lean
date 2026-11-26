/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.IdentityPrinciple
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Vertex
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Lattice
public import TauCeti.Geometry.Toric.Delzant.VertexCone

/-!
# The moment polytope of a symplectic toric manifold is a Delzant polytope

Let a torus `G`, a compact connected commutative Lie group with Lie algebra `𝔤`, act smoothly and
effectively on a compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`,
with moment map `μ : M → 𝔤*`, and suppose that `dim M = 2 dim G`. Let `i : N →+ 𝔤` be an integral
lattice whose image is the period lattice of `G`: `exp (2π ξ) = 1` exactly when `ξ ∈ i(N)`. This
file proves that the moment polytope `Δ = conv μ(M)` is a Delzant polytope for this lattice: there
is a unique finite set `F ⊆ N × ℝ` of inward normals and support constants whose Delzant
presentation cuts out `Δ`
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range`).

By `TauCeti.Toric.existsUnique_isDelzant_facetPolyhedron_eq`, it suffices that `Δ` is a nonempty
compact convex set with finitely many vertices and a *smooth corner* at each vertex: near the vertex
`v`, `Δ` is cut out by the inequalities `⟨v, n⟩ ≤ ⟨y, n⟩` for the members `n` of a `ℤ`-basis of `N`.
The vertices are the images `μ(p)` of the finitely many fixed points
(`TauCeti.SmoothTwoForm.IsMomentMap.bijOn_fixedPoints_extremePoints_convexHull_range`), and the
corner at `μ(p)` comes from the weight normal form at `p`
(`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart`): in a chart `z` at `p` onto a ball of
`ℂⁿ`, `n = dim G`, the moment map is `μ = μ(p) - ½ Σₖ |zₖ|² αₖ` and `G` rotates the coordinate
`zₖ` through the character with weight `αₖ`.

* **The weights are dual to a lattice basis.** An element `ξ` of `𝔤` with `αₖ(ξ) ∈ 2πℤ` for every
  `k` exponentiates to an element of `G` acting as the identity on the chart, hence on all of `M`
  by the identity principle for compact group actions (`TauCeti.eq_one_of_eventuallyEq_id`), so it
  lies in `2π i(N)` by effectiveness. By `TauCeti.exists_basis_iff_forall_weightRotation_eq_id_iff`
  the weights are then dual to a `ℤ`-basis `b` of `N`: `αₖ(i n)` is the `k`-th coordinate of `n`.
* **The corner is the moment cone.** The image of the chart is a neighbourhood of `μ(p)` in the cone
  `μ(p) - cone{αₖ} = {y | y(i bₖ) ≤ μ(p)(i bₖ) for all k}`
  (`TauCeti.image_mem_nhdsWithin_vadd_range_weightMomentMap`). Conversely all of `Δ` lies in this
  cone. For `ξ` in the open cone where every weight is positive, `μ^ξ` has a local maximum at `p`;
  if moreover `ξ` generates a dense one-parameter subgroup, `μ^ξ` is a Morse function
  (`TauCeti.SmoothTwoForm.IsMomentMap.isMorse_of_eq_top`), so this local maximum is a global one
  (`TauCeti.SmoothTwoForm.IsMomentMap.isMaxOn_of_isLocalMax`). Such `ξ` are dense in the open cone,
  so by continuity `μ^ξ ≤ μ^ξ(p)` on `M` for `ξ` in its closure, which contains every `i(bₖ)`.

This statement is about the moment polytope `conv μ(M)`. That the moment image `μ(M)` is itself
convex, so that it equals the polytope, is the convexity theorem of Atiyah and Guillemin–Sternberg,
which is not proved here.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsMomentMap`.

* `exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints`: the moment polytope has a
  smooth corner at the image of every fixed point.
* `existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range`: the moment polytope is a Delzant
  polytope for every lattice whose image is the period lattice, with a unique facet set.
* `existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range_periodLattice`: the same for the
  period lattice `TauCeti.periodLatticeMap I G` of `G` itself.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull. Soc.
  Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 28.2 and Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

open Filter Module Set Topology
open scoped ContDiff Manifold Pointwise Real

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

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

namespace SmoothTwoForm.IsMomentMap

/-- If `μ^ξ` has a local maximum at `p` for every `ξ` in an open set `V` of the Lie algebra, then
`μ^ξ` attains its maximum at `p` for every `ξ` in the closure of `V`. -/
private theorem apply_le_apply_of_mem_closure
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {p : M} {V : Set (GroupLieAlgebra I G)}
    (hV : IsOpen V) (hmax : ∀ ξ ∈ V, IsLocalMax (fun y ↦ μ y ξ) p) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ closure V) (x : M) : μ x ξ ≤ μ p ξ := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  have : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  have hσG (a : G) (y : M) (u v : TangentSpace I' y) :
      σ.eval₂ (a • y) (mfderiv I' I' (a • ·) y u) (mfderiv I' I' (a • ·) y v) =
        σ.eval₂ y u v := by
    rw [← SmoothForm.eval₂_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) a), hG a]
  -- The elements `ζ` for which `μ^ζ` attains its maximum at `p` form a closed set.
  let S : Set (GroupLieAlgebra I G) := {ζ | ∀ y, μ y ζ ≤ μ p ζ}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun y ↦ isClosed_le (μ y).continuous_of_finiteDimensional
      (μ p).continuous_of_finiteDimensional
  -- For `ζ ∈ V` with dense one-parameter subgroup, `μ^ζ` is Morse, so its local maximum at `p` is
  -- global; such `ζ` are dense in `V`.
  have hD : V ∩ {ζ | Lie.closedOneParameterSubgroup ζ = ⊤} ⊆ S := fun ζ ⟨hζV, hζ⟩ y ↦
    h.isMaxOn_of_isLocalMax hσ.isNondegenerate hσG (h.isMorse_of_eq_top hσ.isNondegenerate hζ
      fun q hq ↦ h.eventually_mem_fixedPoints_imp_eq hσ hG hdim hq) (hmax ζ hζV) (mem_univ y)
  have hVS : V ⊆ S :=
    ((Lie.dense_setOf_closedOneParameterSubgroup_eq_top I G).open_subset_closure_inter hV).trans
      (closure_minimal hD hS)
  exact closure_minimal hVS hS hξ x

/-- In a weight chart at a fixed point whose weights are dual to a `ℤ`-basis `b` of `N`, the
component `μ^(i(bₖ))` of the moment map attains its maximum at the fixed point: the moment polytope
lies in the cone `{y | y(i bₖ) ≤ μ(p)(i bₖ) for all k}`. -/
private theorem apply_le_apply_of_weightModelChart
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {n : ℕ} {α : Fin n → StrongDual ℝ E}
    {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}
    {p : M} (hpchart : p ∈ chart.source)
    (hμchart : ∀ x ∈ chart.source, ∀ ξ, μ x ξ = μ p ξ + weightMomentMap α (chart x) ξ)
    {N : Type*} [AddCommGroup N] {i : N →+ E} (b : Module.Basis (Fin n) ℤ N)
    (hb : ∀ j m, α j (i m) = b.coord j m) (x : M) (k : Fin n) :
    μ x (i (b k)) ≤ μ p (i (b k)) := by
  -- On the open cone `V` where every weight is positive, `μ^ξ` has a local maximum at `p`.
  let V : Set E := {ξ | ∀ k, 0 < α k ξ}
  have hVo : IsOpen V := by
    simp only [V, ofPred_forall]
    exact isOpen_iInter_of_finite fun k ↦ isOpen_lt continuous_const (α k).continuous
  have hVmax (ξ : GroupLieAlgebra I G) (hξ : ξ ∈ V) : IsLocalMax (fun y ↦ μ y ξ) p :=
    mem_of_superset (chart.open_source.mem_nhds hpchart) fun x hx ↦ by
      simp only [mem_ofPred_eq]
      rw [hμchart x hx ξ, add_le_iff_nonpos_right, weightMomentMap_apply α (chart x) ξ]
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Finset.sum_nonneg fun k _ ↦
        mul_nonneg (hξ k).le (by positivity))
  -- `i(bₖ)` is the limit of `i(bₖ) + t ξ₁` as `t → 0⁺`, where every weight is `1` on `ξ₁`.
  obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ₁ : E, ∀ j, α j ξ₁ = 1 :=
    ⟨i (∑ l, b l), fun j ↦ by simp [hb, Finsupp.single_apply]⟩
  have hcl : i (b k) ∈ closure V := by
    refine mem_closure_of_tendsto (f := fun t : ℝ ↦ i (b k) + t • ξ₁) (b := 𝓝[>] 0) ?_ ?_
    · exact ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 _
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) j
      simp only [map_add, map_smul, hξ₁, hb, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, smul_eq_mul, mul_one]
      split_ifs <;> push_cast <;> linarith
  exact apply_le_apply_of_mem_closure h hσ hG hdim hVo hVmax hcl x

omit [PreconnectedSpace G] in
/-- **The weights of an effective toric action are dual to a lattice basis.** At a fixed point,
in a weight chart whose weights `αₖ` are the coordinates of an isomorphism `𝔤 ≃ ℝⁿ`, the elements of
the Lie algebra acting trivially in the model are exactly those of `2π i(N)`. -/
private theorem weightRotation_eq_id_iff_of_weightModelChart {n : ℕ} {χ : Fin n → G →ₜ* Circle}
    {α : Fin n → StrongDual ℝ E}
    {chart : PartialDiffeomorph I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}
    (hα : ∀ k (ξ : GroupLieAlgebra I G), χ k (mulInvariantExp (I := I) ξ) = Circle.exp (α k ξ))
    (hint : ∀ k (ξ : GroupLieAlgebra I G), mulInvariantExp (I := I) ((2 * π) • ξ) = 1 →
      ∃ m : ℤ, α k ξ = m)
    {p : M} (hpchart : p ∈ chart.source)
    (hequiv : ∀ g : G, ∀ x ∈ chart.source, g • x ∈ chart.source ∧
      chart (g • x) = weightRotation (fun k ↦ Complex.arg (χ k g)) (chart x))
    {N : Type*} [AddCommGroup N] {i : N →+ E}
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i)
    (ξ : E) :
    weightRotation (fun k ↦ α k ξ) = ContinuousLinearMap.id ℝ _ ↔
      ∃ m : N, ξ = (2 * π) • i m := by
  rw [weightRotation_eq_id_iff]
  constructor
  · intro hrot
    -- `exp ξ` rotates every coordinate of the chart trivially, so it acts trivially near `p`.
    have hχ (k : Fin n) : χ k (mulInvariantExp (I := I) (G := G) ξ) = 1 := by
      obtain ⟨m, hm⟩ := hrot k
      exact (hα k ξ).trans (Circle.exp_eq_one.2 ⟨m, hm.symm⟩)
    have hzero : (fun _ : Fin n ↦ (0 : ℝ)) = 0 := rfl
    have hev : (fun x : M ↦ mulInvariantExp (I := I) (G := G) ξ • x) =ᶠ[𝓝 p] id :=
      eventually_of_mem (chart.open_source.mem_nhds hpchart) fun x hx ↦ by
        obtain ⟨hgx, hchart⟩ := hequiv (mulInvariantExp (I := I) (G := G) ξ) x hx
        simp only [hχ, Circle.coe_one, Complex.arg_one, hzero, weightRotation_zero,
          ContinuousLinearMap.id_apply] at hchart
        exact chart.injOn hgx hx hchart
    -- By the identity principle and effectiveness, `exp ξ = 1`, so `ξ ∈ 2π i(N)`.
    have hg : mulInvariantExp (I := I) (G := G) ξ = 1 := eq_one_of_eventuallyEq_id I' I hev
    obtain ⟨m, hm⟩ := (hperiod ((2 * π)⁻¹ • ξ)).1 (by
      rwa [smul_inv_smul₀ (by positivity : (2 * π : ℝ) ≠ 0)])
    exact ⟨m, by rw [hm, smul_inv_smul₀ (by positivity : (2 * π : ℝ) ≠ 0)]⟩
  · rintro ⟨m, rfl⟩ k
    obtain ⟨z, hz⟩ := hint k (i m) ((hperiod (i m)).2 (mem_range_self m))
    exact ⟨z, by rw [map_smul, hz, smul_eq_mul, mul_comm]⟩

/-- **Smooth corners of the moment polytope.** Let a torus `G` act smoothly and effectively on a
compact connected symplectic manifold `(M, σ)` without boundary, preserving `σ`, with moment map
`μ`, and with `dim M = 2 dim G`, and let `i : N →+ 𝔤` be an integral lattice whose image is the
period lattice of `G`. Then the moment polytope `conv μ(M)` has a smooth corner at the image `μ(p)`
of every fixed point `p`: there is a `ℤ`-basis `s` of `N` such that near `μ(p)` the polytope is cut
out by the inequalities `⟨μ(p), i(n)⟩ ≤ ⟨y, i(n)⟩` for `n ∈ s`. -/
theorem exists_eventually_mem_convexHull_range_iff_of_mem_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {N : Type*} [AddCommGroup N] {i : N →+ E}
    (hi : Toric.IsIntegralLattice i)
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i)
    {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∃ s : Set N, LinearIndepOn ℤ id s ∧ Submodule.span ℤ s = ⊤ ∧
      ∀ᶠ y in 𝓝 (LinearMap.toContinuousLinearMap (μ p) : StrongDual ℝ E),
        y ∈ convexHull ℝ
            (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) ↔
          ∀ n ∈ s, LinearMap.toContinuousLinearMap (μ p) (i n) ≤ y (i n) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  set f : M → StrongDual ℝ E := fun x ↦ LinearMap.toContinuousLinearMap (μ x)
  obtain ⟨n, χ, α, chart, -, hα, hint, hpchart, -, -, -, hequiv, -, hgen, hμchart⟩ :=
    h.exists_weightModelChart hσ hG (MulAction.mem_fixedPoints.1 hp)
  -- The weights are the coordinates of an isomorphism `𝔤 ≃ ℝⁿ`.
  have hbij := bijective_pi_of_mfderiv_eq hgen hpchart hdim
  have hn : Fintype.card (Fin n) ≤ finrank ℝ E := by
    have hfr := (LinearEquiv.ofBijective _ hbij).finrank_eq
    rw [finrank_fin_fun] at hfr
    exact (Fintype.card_fin n).trans_le hfr.symm.le
  -- Effectiveness makes the weights dual to a `ℤ`-basis `b` of `N`.
  obtain ⟨b, hb⟩ := (exists_basis_iff_forall_weightRotation_eq_id_iff hi hn).2
    (weightRotation_eq_id_iff_of_weightModelChart hα hint hpchart hequiv hperiod)
  -- Near `p`, `μ` is the weight model, whose image is the cone cut out by the outward normals `bₖ`.
  have hf := toContinuousLinearMap_eq_add_weightMomentMap (E := E) hμchart
  let C : Set (StrongDual ℝ E) := {y | ∀ k, y (i (b k)) ≤ f p (i (b k))}
  have hcone : f p +ᵥ range (weightMomentMap α) = C := by
    ext y
    rw [range_weightMomentMap_of_basis hi b hb, mem_vadd_set]
    refine ⟨?_, fun hy ↦ ⟨y - f p, fun k ↦ ?_, by simp⟩⟩
    · rintro ⟨ν, hν, rfl⟩ k
      simpa using hν k
    · simpa using hy k
  have hCconv : Convex ℝ C := by
    simp only [C, ofPred_forall]
    exact convex_iInter fun k ↦
      convex_halfSpace_le (ContinuousLinearMap.apply ℝ ℝ (i (b k))).toLinearMap.isLinear _
  have hsub : convexHull ℝ (range f) ⊆ C := by
    refine convexHull_min ?_ hCconv
    rintro _ ⟨x, rfl⟩ k
    exact apply_le_apply_of_weightModelChart h hσ hG hdim hpchart hμchart b hb x k
  -- Near `μ(p)` the cone lies in the image of the chart.
  have hloc : ∀ᶠ y in 𝓝 (f p), y ∈ C → y ∈ convexHull ℝ (range f) := by
    have := image_mem_nhdsWithin_vadd_range_weightMomentMap hf hpchart univ_mem
    rw [hcone, image_univ] at this
    exact (mem_nhdsWithin_iff_eventually.1 this).mono fun y hy hyC ↦
      subset_convexHull ℝ _ (hy hyC)
  -- The basis of inward normals is `-b`.
  refine ⟨range (b.map (LinearEquiv.neg ℤ)),
    (linearIndepOn_id_range_iff (b.map _).injective).2 (b.map _).linearIndependent,
    (b.map _).span_eq, hloc.mono fun y hy ↦ ?_⟩
  have hneg (k : Fin n) : LinearMap.toContinuousLinearMap (μ p) (-i (b k)) = -f p (i (b k)) := by
    rw [LinearMap.coe_toContinuousLinearMap']
    exact (μ p).map_neg (i (b k))
  simp only [forall_mem_range, Module.Basis.map_apply, LinearEquiv.neg_apply, map_neg, hneg,
    neg_le_neg_iff]
  exact ⟨fun hyΔ ↦ hsub hyΔ, hy⟩

/-- **The moment polytope of a symplectic toric manifold is a Delzant polytope.** Let a torus `G`
act smoothly and effectively on a compact connected symplectic manifold `(M, σ)` without boundary,
preserving `σ`, with moment map `μ`, and with `dim M = 2 dim G`, and let `i : N →+ 𝔤` be an integral
lattice whose image is the period lattice of `G`. Then there is a unique finite set `F` of pairs
(inward normal, support constant) whose Delzant presentation cuts out the moment polytope
`conv μ(M)`. -/
theorem existsUnique_isDelzant_facetPolyhedron_eq_convexHull_range [Nonempty M]
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hdim : finrank ℝ E' = 2 * finrank ℝ E) {N : Type*} [AddCommGroup N] {i : N →+ E}
    (hi : Toric.IsIntegralLattice i)
    (hperiod : ∀ ξ : E, mulInvariantExp (I := I) (G := G) ((2 * π) • ξ) = 1 ↔ ξ ∈ range i) :
    ∃! F : Set (N × ℝ), F.Finite ∧
      Toric.IsDelzant i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) ∧
      Toric.facetPolyhedron i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) =
        convexHull ℝ (range fun x ↦ (LinearMap.toContinuousLinearMap (μ x) : StrongDual ℝ E)) := by
  have : IsMulCommutative G := ⟨⟨mul_comm⟩⟩
  set f : M → StrongDual ℝ E := fun x ↦ LinearMap.toContinuousLinearMap (μ x)
  -- The polytope is the convex hull of the images of the finitely many fixed points.
  have hfin := h.finite_fixedPoints_of_faithfulSMul hσ hG hdim
  -- `GroupLieAlgebra I G` is definitionally `E`, so Mathlib's equivalence applies to `μ`.
  let L : Module.Dual ℝ (GroupLieAlgebra I G) →ₗ[ℝ] StrongDual ℝ E :=
    (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E).toLinearMap
  have hΔ : convexHull ℝ (range f) = convexHull ℝ (f '' MulAction.fixedPoints G M) := by
    -- `f` is `L ∘ μ` by definition, and the linear map `L` commutes with convex hulls.
    rw [show f = L ∘ μ from rfl, range_comp L μ, image_comp L μ, ← L.image_convexHull,
      ← L.image_convexHull, h.convexHull_range_eq_convexHull_image_fixedPoints hσ.isNondegenerate]
  refine Toric.existsUnique_isDelzant_facetPolyhedron_eq hi ?_ ?_ (convex_convexHull ℝ _) ?_
    fun v hv ↦ ?_
  · exact (range_nonempty f).mono (subset_convexHull ℝ _)
  · rw [hΔ]
    exact (hfin.image f).isCompact_convexHull (𝕜 := ℝ)
  · rw [hΔ]
    exact (hfin.image f).subset extremePoints_convexHull_subset
  -- Each vertex is the image of a fixed point, where the polytope has a smooth corner.
  rw [hΔ] at hv
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
