/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System

/-!
# Isotopy invariance of the transport of local homology

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E`, and let
`F : P × M → M` be a continuous family of maps `F_p = F (p, ·)`, parametrized by a space `P`,
which admits a continuous family of left inverses `F' : P × M → M`, `F' (p, F (p, y)) = y`. Each
`F_p` is then injective, so it maps the pair `(M, M ∖ {x})` to `(M, M ∖ {F_p x})` and induces a
map `(F_p)_* : Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {F_p x})` on local homology. As `p` moves along a path
in `P`, the point `F_p x` moves along a path in `M`, and these maps are carried into each other by
the transport of local homology along that path
(`TauCeti.localHomologyMap_comp_localHomologyTransport_of_leftInverse`): for every path class
`f : p ⟶ q` of `P`,

`(F_p)_* ≫ transport (F (·, x) ∘ f) = (F_q)_*`.

For `P` the unit interval this is the classical statement that an isotopy of homeomorphisms acts
on local homology by transport along the track of the point. For `P` a topological group acting
on `M`, with `F (g, y) = g • y` and `F' (g, y) = g⁻¹ • y`, it says that the images of a local
homology class at `x` under the group elements form a flat section of the local homology system
pulled back along the orbit map `g ↦ g • x`.

The proof compares both sides through a compact neighbourhood `B` of `x` along which local
homology is constant. Near each parameter `p₀`, there is a compact convex set `K` in a chart
around `F_{p₀} x` such that `F_p` maps `M ∖ B` into `M ∖ K` for all `p` near `p₀`; this is where
the continuity of the left inverses enters. Along a path of such parameters the maps
`(M, M ∖ B) ⟶ (M, M ∖ K)` are homotopic, while the transport along a path inside `K` is the
comparison through `K`. The path classes along which the identity holds form a subgroupoid, and
paths inside such neighbourhoods of parameters generate the fundamental groupoid of `P`.

## Main results

* `TauCeti.localHomologyMap_comp_localHomologyTransport_of_leftInverse`: a family of maps with
  continuous left inverses acts on local homology compatibly with transport along the paths
  traced by a point.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, local homology and the orientation local system.
-/

public section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {P : Type*} [TopologicalSpace P] {M : Type w} [TopologicalSpace M] {E : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A map `F (p, ·)` with a left inverse `F' (p, ·)` sends no point other than `x` to the image of
`x`, so it induces a map of local homology at `x`. -/
theorem preimage_curry_singleton_subset_of_leftInverse {F F' : C(P × M, M)}
    (hF : ∀ p y, F' (p, F (p, y)) = y) (p : P) {x z : M} (hz : F (p, x) = z) :
    F.curry p ⁻¹' {z} ⊆ {x} := by
  intro y hy
  rw [mem_preimage, ContinuousMap.curry_apply, mem_singleton_iff, ← hz] at hy
  rw [mem_singleton_iff, ← hF p y, hy, hF p x]

variable [T2Space M] [FiniteDimensional ℝ E] [ChartedSpace E M]

/-- Along a path of parameters that stays where a single compact convex set `K` of a chart contains
the moving point and the maps `F_p` send `M ∖ B` into `M ∖ K`, the maps of local homology induced
by the endpoints are carried into each other by transport. -/
private theorem localHomologyMap_comp_localHomologyTransport_of_path {F : C(P × M, M)} (x : M)
    {o : C(P, M)} {B : Set M} (hxB : {x} ⊆ B) (k : ℕ)
    [IsIso (localHomologyRestriction R hxB k)] (φ : OpenPartialHomeomorph M E) {K : Set E}
    (hK : Convex ℝ K) (hKc : IsCompact K) (hKφ : K ⊆ φ.target) {a b : P} (γ : Path a b)
    (hγK : ∀ s, o (γ s) ∈ φ.symm '' K) (hγB : ∀ s, F.curry (γ s) ⁻¹' (φ.symm '' K) ⊆ B)
    (ha : F.curry a ⁻¹' {o a} ⊆ {x}) (hb : F.curry b ⁻¹' {o b} ⊆ {x}) :
    localHomologyMap R (F.curry a) ha k ≫
        localHomologyTransport R M E k
          (Path.Homotopic.Quotient.mk (γ.map o.continuous) :
            FundamentalGroupoid.mk (o a) ⟶ FundamentalGroupoid.mk (o b)) =
      localHomologyMap R (F.curry b) hb k := by
  -- The maps `(M, M ∖ B) ⟶ (M, M ∖ K)` induced by the two endpoints agree, through the homotopy
  -- `F (γ s, ·)`.
  have hBa : F.curry a ⁻¹' (φ.symm '' K) ⊆ B := γ.source ▸ hγB 0
  have hBb : F.curry b ⁻¹' (φ.symm '' K) ⊆ B := γ.target ▸ hγB 1
  let H : (F.curry a).Homotopy (F.curry b) :=
    { toFun s := F (γ s.1, s.2)
      continuous_toFun := by fun_prop
      map_zero_left y := by simp
      map_one_left y := by simp }
  have hH : localHomologyMap R (F.curry a) hBa k = localHomologyMap R (F.curry b) hBb k :=
    localHomologyMap_eq_of_homotopy R H (fun s y hy hyK ↦ hy (hγB s hyK)) hBa hBb k
  -- The transport along the moving point is the comparison through `K`.
  have hT := localHomologyRestriction_comp_localHomologyTransport R φ hK hKc hKφ
    (γ.map o.continuous) (fun s ↦ hγK s) k
  have hoa : {o a} ⊆ φ.symm '' K := singleton_subset_iff.2 (γ.source ▸ hγK 0)
  have hob : {o b} ⊆ φ.symm '' K := singleton_subset_iff.2 (γ.target ▸ hγK 1)
  rw [← cancel_epi (localHomologyRestriction R hxB k),
    localHomologyRestriction_comp_localHomologyMap_assoc,
    localHomologyRestriction_comp_localHomologyMap,
    ← localHomologyMap_comp_localHomologyRestriction R (F.curry a) hoa hBa,
    ← localHomologyMap_comp_localHomologyRestriction R (F.curry b) hob hBb, Category.assoc, hT, hH]

omit [T2Space M] in
/-- Near every parameter `p₀` there are a neighbourhood `J` and a compact convex set `K` in a
chart such that for all `p ∈ J` the moving point `o p = F (p, x)` lies in `K` and the map `F (p, ·)`
sends the complement of a given neighbourhood `B` of `x` into the complement of `K`. -/
private theorem exists_mem_nhds_preimage_subset {F F' : C(P × M, M)}
    (hF : ∀ p y, F' (p, F (p, y)) = y) {x : M} {o : C(P, M)} (ho : ∀ p, F (p, x) = o p)
    {B : Set M} (hB : B ∈ 𝓝 x) (p₀ : P) :
    ∃ J ∈ 𝓝 p₀, ∃ (φ : OpenPartialHomeomorph M E) (K : Set E), Convex ℝ K ∧ IsCompact K ∧
      K ⊆ φ.target ∧ (∀ p ∈ J, o p ∈ φ.symm '' K) ∧
        ∀ p ∈ J, F.curry p ⁻¹' (φ.symm '' K) ⊆ B := by
  -- Where `F' (p, ·)` maps a neighbourhood `V` of `o p₀` into `B`, so `F (p, ·)⁻¹' V ⊆ B`.
  have hW : F' ⁻¹' interior B ∈ 𝓝 (p₀, o p₀) := by
    refine F'.continuous.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds ?_)
    rw [← ho, hF]
    exact mem_interior_iff_mem_nhds.2 hB
  obtain ⟨J₁, hJ₁, V, hV, hJV⟩ := mem_nhds_prod_iff.1 hW
  -- A closed ball in the chart at `o p₀` whose image lies in `V`.
  let φ := chartAt E (o p₀)
  obtain ⟨ε, hε, hεV⟩ := isOpen_iff.1 (φ.isOpen_inter_preimage_symm isOpen_interior) (φ (o p₀))
    ⟨mem_chart_target E (o p₀), by
      rw [mem_preimage, φ.left_inv (mem_chart_source E (o p₀))]
      exact mem_interior_iff_mem_nhds.2 hV⟩
  have hKsub : closedBall (φ (o p₀)) (ε / 2) ⊆ φ.target ∩ φ.symm ⁻¹' interior V :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hKnhds : φ.symm '' closedBall (φ (o p₀)) (ε / 2) ∈ 𝓝 (o p₀) := by
    have h := φ.symm.image_mem_nhds (mem_chart_target E (o p₀))
      (closedBall_mem_nhds (φ (o p₀)) (half_pos hε))
    rwa [φ.left_inv (mem_chart_source E (o p₀))] at h
  refine ⟨J₁ ∩ o ⁻¹' (φ.symm '' closedBall (φ (o p₀)) (ε / 2)),
    Filter.inter_mem hJ₁ (o.continuous.continuousAt.preimage_mem_nhds hKnhds), φ, _,
    convex_closedBall _ _, isCompact_closedBall _ _, hKsub.trans inter_subset_left,
    fun p hp ↦ hp.2, fun p hp y hy ↦ ?_⟩
  -- If `F (p, y)` lies in `K`, then it lies in `V`, so `y = F' (p, F (p, y))` lies in `B`.
  obtain ⟨w, hw, hwy⟩ := hy
  have hFy : F (p, y) ∈ V := by
    rw [← ContinuousMap.curry_apply, ← hwy]
    exact interior_subset (hKsub hw).2
  rw [← hF p y]
  exact interior_subset (hJV ⟨hp.1, hFy⟩)

/-- **Isotopy invariance of the transport of local homology.** Let `F : P × M → M` be a continuous
family of maps with a continuous family of left inverses `F'`, and let `o : P → M` be the path of
a point `x`, `o p = F (p, x)`. For every path class `f : p ⟶ q` of `P`, the transport of local
homology along the image path class `o ∘ f` carries the map `Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {o p})`
induced by `F (p, ·)` to the map induced by `F (q, ·)`. -/
theorem localHomologyMap_comp_localHomologyTransport_of_leftInverse {F F' : C(P × M, M)}
    (hF : ∀ p y, F' (p, F (p, y)) = y) (x : M) {o : C(P, M)} (ho : ∀ p, F (p, x) = o p) (k : ℕ)
    {p q : FundamentalGroupoid P} (f : p ⟶ q) :
    localHomologyMap R (F.curry p.as)
        (preimage_curry_singleton_subset_of_leftInverse hF p.as (ho p.as)) k ≫
        localHomologyTransport R M E k ((FundamentalGroupoid.map o).map f) =
      localHomologyMap R (F.curry q.as)
        (preimage_curry_singleton_subset_of_leftInverse hF q.as (ho q.as)) k := by
  obtain ⟨B, hB, -, hBiso⟩ :=
    exists_isCompact_mem_nhds_isIso_localHomologyRestriction (E := E) R x k
  have hxB : {x} ⊆ B := singleton_subset_iff.2 (mem_of_mem_nhds hB)
  have := hBiso x (mem_of_mem_nhds hB)
  -- The sets of parameters along which a single compact convex set `K` of a chart contains the
  -- moving point while `F (p, ·)` maps `M ∖ B` into `M ∖ K`.
  let good : Set (Set P) := {J | ∃ (φ : OpenPartialHomeomorph M E) (K : Set E), Convex ℝ K ∧
    IsCompact K ∧ K ⊆ φ.target ∧ (∀ p ∈ J, o p ∈ φ.symm '' K) ∧
      ∀ p ∈ J, F.curry p ⁻¹' (φ.symm '' K) ⊆ B}
  -- Every parameter has a neighbourhood in `good`.
  have hcover (p₀ : P) : ∃ J : good, (J : Set P) ∈ 𝓝 p₀ := by
    obtain ⟨J, hJ, φ, K, hK⟩ := exists_mem_nhds_preimage_subset (E := E) hF ho hB p₀
    exact ⟨⟨J, φ, K, hK⟩, hJ⟩
  -- Paths inside the sets in `good` generate the fundamental groupoid of `P`.
  refine FundamentalGroupoid.comp_map_eq_of_forall_path (U := fun J : good ↦ (J : Set P)) hcover
    (FundamentalGroupoid.map o ⋙ localHomologySystem R M E k)
    (fun c ↦ localHomologyMap R (F.curry c.as)
      (preimage_curry_singleton_subset_of_leftInverse hF c.as (ho c.as)) k) (fun J _ _ γ ↦ ?_) f
  obtain ⟨φ, K, hK, hKc, hKφ, hJK, hJB⟩ := J.2
  exact localHomologyMap_comp_localHomologyTransport_of_path R x hxB k φ hK hKc hKφ
    (γ.map continuous_subtype_val) (fun s ↦ hJK _ (γ s).2) (fun s ↦ hJB _ (γ s).2) _ _

end TauCeti
