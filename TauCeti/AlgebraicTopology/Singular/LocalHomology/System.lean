/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic

/-!
# The local homology system of a manifold

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E`, that is,
a topological manifold without boundary. This file assembles the local homology groups
`Hₖ(M, M ∖ {x})` into a functor out of the fundamental groupoid of `M`,
`TauCeti.localHomologySystem R M E k`. For `k = dim E` and integer coefficients this is the
orientation local system of `M`: a local orientation at `x` is a generator of
`Hₙ(M, M ∖ {x}; ℤ)`, and the functor transports local orientations along paths. With
`A = ModuleCat S` for a ring `S` it is a `TauCeti.LocalCoefficientSystem`.

The transport is determined by compact convex sets in charts. Let `φ : M → E` be an open
partial homeomorphism and let `K ⊆ φ.target` be compact and convex. For every `x` with
`φ x ∈ K`, the restriction `Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` is an isomorphism
(`TauCeti.isIso_localHomologyRestriction_symm_image`). The transport along a path inside
`φ.symm '' K` is the unique map compatible with these restrictions at its two endpoints
(`TauCeti.localHomologyRestriction_comp_localHomologyTransport`), and this property together with
compatibility with composition characterizes the transport
(`TauCeti.eq_localHomologyTransport`).

## Main definitions and results

* `TauCeti.localHomology R S k`: the relative singular homology `Hₖ(M, M ∖ S)`.
* `TauCeti.localHomologyRestriction`: for `S ⊆ T`, the map `Hₖ(M, M ∖ T) ⟶ Hₖ(M, M ∖ S)`
  induced by the identity of `M`.
* `TauCeti.isZero_localHomology_empty`: `Hₖ(M, M) = 0`.
* `TauCeti.isIso_localHomologyRestriction_symm_image`: the restriction from a compact set in a
  chart, star-convex about one of its points, to that point is an isomorphism.
* `TauCeti.localHomologyTransport`: the transport of local homology along a path class.
* `TauCeti.localHomologySystem`: the local homology groups as a functor out of the fundamental
  groupoid, with these transport maps.
* `TauCeti.localHomologyRestriction_comp_localHomologyTransport`: the transport along a path
  inside a compact convex set in a chart.
* `TauCeti.eq_localHomologyTransport`: the transport is the only family of maps compatible with
  composition that has this property.

## Implementation notes

On each open convex patch of a chart there is a functor sending a path to the comparison of its
endpoints through the closure of the patch. Two patches give the same comparison near each point
of their overlap, since both factor through a small ball in one chart. So the local functors
agree on overlaps, and they glue (`TauCeti.FundamentalGroupoid.glue`) to a functor out of the
fundamental groupoid of `M`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, the local homology groups `Hₙ(M | x)`, local
  orientations, and the comparison through `Hₙ(M | B)` for balls `B` in charts, which Hatcher
  uses to topologize the orientation covering `M_R`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Restriction

variable {M : Type w} [TopologicalSpace M]

/-- The relative singular homology `Hₖ(M, M ∖ S)` of `M` modulo the complement of `S`. For
`S = {x}` it is the local homology of `M` at `x`. -/
abbrev localHomology (S : Set M) (k : ℕ) : A :=
  (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomology R k

/-- For `S ⊆ T`, the map `Hₖ(M, M ∖ T) ⟶ Hₖ(M, M ∖ S)` on relative singular homology induced by
the identity of `M`. -/
def localHomologyRestriction {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    localHomology R T k ⟶ localHomology R S k :=
  TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) (compl_subset_compl.2 h)) R k

lemma localHomologyRestriction_def {S T : Set M} (h : S ⊆ T) (k : ℕ) :
    localHomologyRestriction R h k =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M))
        (compl_subset_compl.2 h)) R k :=
  (rfl)

@[simp]
lemma localHomologyRestriction_refl (S : Set M) (k : ℕ) :
    localHomologyRestriction R (subset_refl S) k = 𝟙 _ :=
  (congrArg (TopPair.singularHomologyMap · R k) (TopPair.ofSubsetMap_id _)).trans
    (TopPair.singularHomologyMap_id _ R k)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma localHomologyRestriction_comp {S T W : Set M} (h₁ : S ⊆ T) (h₂ : T ⊆ W) (k : ℕ) :
    localHomologyRestriction R h₂ k ≫ localHomologyRestriction R h₁ k =
      localHomologyRestriction R (h₁.trans h₂) k := by
  rw [localHomologyRestriction, localHomologyRestriction, localHomologyRestriction,
    ← TopPair.singularHomologyMap_comp]
  -- `𝟙 ≫ 𝟙` is definitionally `𝟙` in `TopCat`, so `ofSubsetMap_comp` applies up to the `MapsTo`
  -- proofs; rewriting with `Category.id_comp` is blocked because those proofs depend on the map.
  exact congrArg (TopPair.singularHomologyMap · R k)
    (TopPair.ofSubsetMap_comp (𝟙 (TopCat.of M)) (𝟙 (TopCat.of M)) _ _ _).symm

/-- **Local homology along the empty set vanishes**: `Hₖ(M, M) = 0`, because the identity of the
pair `(M, M)` factors through its subspace. -/
theorem isZero_localHomology_empty (k : ℕ) : IsZero (localHomology R (∅ : Set M) k) := by
  rw [IsZero.iff_id_eq_zero, ← TopPair.singularHomologyMap_id]
  exact TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (⟨fun x ↦ ⟨x, by simp⟩, by fun_prop⟩ : C(M, ((∅ : Set M)ᶜ : Set M)))) rfl k

/-- Let `S ⊆ T` contain `x` and `y`, and let the restrictions from `S` and from `T` to `x` be
isomorphisms. Then comparing `x` with `y` through `T` and restricting from `S` to `x` gives the
restriction from `S` to `y`. -/
private lemma localHomologyRestriction_comp_inv_comp {S T : Set M} (hST : S ⊆ T) {x y : M}
    (hx : {x} ⊆ S) (hy : {y} ⊆ S) (k : ℕ) [IsIso (localHomologyRestriction R hx k)]
    [IsIso (localHomologyRestriction R (Set.Subset.trans hx hST) k)] :
    localHomologyRestriction R hx k ≫
        inv (localHomologyRestriction R (Set.Subset.trans hx hST) k) ≫
          localHomologyRestriction R (Set.Subset.trans hy hST) k =
      localHomologyRestriction R hy k := by
  have hfac := localHomologyRestriction_comp R hx hST k
  have := IsIso.of_isIso_fac_right hfac
  have hinv : localHomologyRestriction R hx k ≫
      inv (localHomologyRestriction R (Set.Subset.trans hx hST) k) =
        inv (localHomologyRestriction R hST k) :=
    IsIso.eq_inv_of_hom_inv_id (by rw [← Category.assoc, hfac, IsIso.hom_inv_id])
  rw [← Category.assoc, hinv, ← localHomologyRestriction_comp R hy hST, IsIso.inv_hom_id_assoc]

end Restriction

section Chart

variable {M : Type w} [TopologicalSpace M] {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local homology is constant along a compact star-convex set in a chart.** If
`K ⊆ φ.target` is compact and star-convex about `φ x ∈ K`, then the restriction
`Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` is an isomorphism. -/
theorem isIso_localHomologyRestriction_symm_image [T2Space M] (φ : OpenPartialHomeomorph M E)
    {K : Set E} {x : M} (hK : StarConvex ℝ (φ x) K) (hKc : IsCompact K) (hKφ : K ⊆ φ.target)
    (hx : x ∈ φ.source) (hxK : φ x ∈ K) (k : ℕ) :
    IsIso (localHomologyRestriction R
      (singleton_subset_iff.2 ⟨φ x, hxK, φ.left_inv hx⟩ : {x} ⊆ φ.symm '' K) k) :=
  isIso_singularHomologyMap_compl_of_chart R φ hx hK hxK hKc.isBounded
    hKc.isClosed (hKc.image_of_continuousOn (φ.continuousOn_symm.mono hKφ)).isClosed hKφ k

/-- An open, bounded, convex subset of the target of a chart whose closure also lies in the
target. These patches index the cover over which the local homology system is glued. -/
private structure Patch (M E : Type w) [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  chart : OpenPartialHomeomorph M E
  set : Set E
  isOpen : IsOpen set
  convex : Convex ℝ set
  isBounded : Bornology.IsBounded set
  closure_subset : closure set ⊆ chart.target

/-- The part of `M` lying over a patch. -/
private def Patch.domain (P : Patch M E) : Set M := P.chart.source ∩ P.chart ⁻¹' P.set

/-- The image in `M` of the closure of a patch. -/
private def Patch.closedImage (P : Patch M E) : Set M := P.chart.symm '' closure P.set

private lemma Patch.isOpen_domain (P : Patch M E) : IsOpen P.domain :=
  P.chart.isOpen_inter_preimage P.isOpen

private lemma Patch.singleton_subset_closedImage (P : Patch M E) {x : M} (hx : x ∈ P.domain) :
    {x} ⊆ P.closedImage :=
  singleton_subset_iff.2 ⟨P.chart x, subset_closure hx.2, P.chart.left_inv hx.1⟩

private lemma Patch.domain_subset_closedImage (P : Patch M E) : P.domain ⊆ P.closedImage :=
  fun _ hx ↦ P.singleton_subset_closedImage hx rfl

omit [NormedSpace ℝ E] in
private lemma closure_ball_half_subset_ball (c : E) {ε : ℝ} (hε : 0 < ε) :
    closure (ball c (ε / 2)) ⊆ ball c ε :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))

/-- The patch of `φ` given by the ball of radius `ε / 2` about `c`, where the ball of radius `ε`
lies in the target of `φ`. -/
private def Patch.ofBall (φ : OpenPartialHomeomorph M E) (c : E) {ε : ℝ} (hε : 0 < ε)
    (h : ball c ε ⊆ φ.target) : Patch M E where
  chart := φ
  set := ball c (ε / 2)
  isOpen := isOpen_ball
  convex := convex_ball _ _
  isBounded := isBounded_ball
  closure_subset := (closure_ball_half_subset_ball c hε).trans h

private lemma Patch.mem_domain_ofBall (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {ε : ℝ} (hε : 0 < ε) (h : ball (φ x) ε ⊆ φ.target) :
    x ∈ (Patch.ofBall φ (φ x) hε h).domain :=
  ⟨hx, mem_ball_self (by linarith)⟩

/-- Every point of `M` lies in the domain of a patch of a chart at that point. -/
private lemma Patch.exists_domain_mem_nhds [ChartedSpace E M] (x : M) :
    ∃ P : Patch M E, P.domain ∈ 𝓝 x := by
  let φ := chartAt E x
  obtain ⟨ε, hε, hεφ⟩ := Metric.isOpen_iff.1 φ.open_target (φ x) (φ.map_source
    (mem_chart_source E x))
  let P := Patch.ofBall φ (φ x) hε hεφ
  exact ⟨P, P.isOpen_domain.mem_nhds (Patch.mem_domain_ofBall φ (mem_chart_source E x) hε hεφ)⟩

/-- Near a point `z` of the domain of `P` lying in an open set `U`, there is a patch of the same
chart whose closed image lies in `U`. -/
private lemma Patch.exists_closedImage_subset (P : Patch M E) {z : M} (hz : z ∈ P.domain)
    {U : Set M} (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ Q : Patch M E, z ∈ Q.domain ∧ Q.closedImage ⊆ U := by
  have hopen : IsOpen (P.chart.target ∩ P.chart.symm ⁻¹' U) :=
    P.chart.isOpen_inter_preimage_symm hU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hopen (P.chart z)
    ⟨P.chart.map_source hz.1, by rwa [Set.mem_preimage, P.chart.left_inv hz.1]⟩
  have hεφ := hεU.trans inter_subset_left
  refine ⟨Patch.ofBall P.chart (P.chart z) hε hεφ, Patch.mem_domain_ofBall _ hz.1 hε hεφ, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (hεU (closure_ball_half_subset_ball _ hε hy)).2

variable [FiniteDimensional ℝ E]

private lemma Patch.isCompact_closure (P : Patch M E) : IsCompact (closure P.set) :=
  isCompact_of_isClosed_isBounded isClosed_closure P.isBounded.closure

variable [T2Space M]

private lemma Patch.isIso_localHomologyRestriction (P : Patch M E) {x : M}
    (hx : x ∈ P.domain) (k : ℕ) :
    IsIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k) :=
  isIso_localHomologyRestriction_symm_image R P.chart
    (P.convex.closure.starConvex (subset_closure hx.2)) P.isCompact_closure P.closure_subset
    hx.1 (subset_closure hx.2) k

/-- The restriction from the closed image of a patch to a point of its domain, as an
isomorphism. -/
private def Patch.iso (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ) :
    localHomology R P.closedImage k ≅ localHomology R {x} k :=
  haveI := P.isIso_localHomologyRestriction R hx k
  asIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k)

private lemma Patch.iso_hom (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ) :
    (P.iso R hx k).hom = localHomologyRestriction R (P.singleton_subset_closedImage hx) k :=
  rfl

private lemma Patch.iso_inv (P : Patch M E) {x : M} (hx : x ∈ P.domain) (k : ℕ)
    [IsIso (localHomologyRestriction R (P.singleton_subset_closedImage hx) k)] :
    (P.iso R hx k).inv = inv (localHomologyRestriction R (P.singleton_subset_closedImage hx) k) :=
  asIso_inv _

/-- The functor on the fundamental groupoid of the domain of a patch: a path is sent to the
comparison of the local homology groups at its endpoints through `Hₖ(M, M ∖ P.closedImage)`. -/
private def Patch.functor (P : Patch M E) (k : ℕ) : FundamentalGroupoid P.domain ⥤ A where
  obj a := localHomology R {a.as.1} k
  map {a b} _ := (P.iso R a.as.2 k).inv ≫ (P.iso R b.as.2 k).hom
  map_id _ := Iso.inv_hom_id _
  map_comp _ _ := by simp

/-- Comparing two points through a patch `P` agrees with comparing them through a patch `S`
whose closed image lies in that of `P`. -/
private lemma Patch.iso_inv_comp_iso_hom (P S : Patch M E) {x y : M} (hxP : x ∈ P.domain)
    (hyP : y ∈ P.domain) (hxS : x ∈ S.domain) (hyS : y ∈ S.domain)
    (hSP : S.closedImage ⊆ P.closedImage) (k : ℕ) :
    (P.iso R hxP k).inv ≫ (P.iso R hyP k).hom = (S.iso R hxS k).inv ≫ (S.iso R hyS k).hom := by
  have : IsIso (localHomologyRestriction R (S.singleton_subset_closedImage hxS) k) :=
    (S.iso R hxS k).isIso_hom
  have : IsIso (localHomologyRestriction R
      (Set.Subset.trans (S.singleton_subset_closedImage hxS) hSP) k) :=
    (P.iso R hxP k).isIso_hom
  rw [Iso.eq_inv_comp]
  simp only [Patch.iso_hom, Patch.iso_inv]
  exact localHomologyRestriction_comp_inv_comp R hSP (S.singleton_subset_closedImage hxS)
    (S.singleton_subset_closedImage hyS) k

/-- The local functors of two patches agree on the fundamental groupoid of the intersection of
their domains. -/
private lemma Patch.map_inclusion_comp_functor (P Q : Patch M E) (k : ℕ) :
    FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_left : P.domain ∩ Q.domain ⊆ P.domain)) ⋙ P.functor R k =
      FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_right : P.domain ∩ Q.domain ⊆ Q.domain)) ⋙ Q.functor R k := by
  -- Near each point of the overlap, a small patch of the chart of `P` has closed image inside
  -- the overlap, and both local functors agree with its comparison maps.
  let W : {S : Patch M E // S.closedImage ⊆ P.domain ∩ Q.domain} → Set ↥(P.domain ∩ Q.domain) :=
    fun S ↦ Subtype.val ⁻¹' S.1.domain
  refine FundamentalGroupoid.functor_ext (U := W) (fun z ↦ ?_) fun S ↦ ?_
  · obtain ⟨S, hzS, hS⟩ := P.exists_closedImage_subset z.2.1
      (P.isOpen_domain.inter Q.isOpen_domain) z.2
    exact ⟨⟨S, hS⟩, continuous_subtype_val.continuousAt.preimage_mem_nhds
      (S.isOpen_domain.mem_nhds hzS)⟩
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b _ ↦ heq_of_eq ?_
  exact (P.iso_inv_comp_iso_hom R S.1 _ _ a.as.2 b.as.2
    (S.2.trans (inter_subset_left.trans P.domain_subset_closedImage)) k).trans
    (Q.iso_inv_comp_iso_hom R S.1 _ _ a.as.2 b.as.2
      (S.2.trans (inter_subset_right.trans Q.domain_subset_closedImage)) k).symm

variable (M E) [ChartedSpace E M]

/-- The functor out of the fundamental groupoid of `M` glued from the local functors of the
patches. Its object at `x` is only propositionally `Hₖ(M, M ∖ {x})`. -/
private def gluedSystem (k : ℕ) : FundamentalGroupoid M ⥤ A :=
  FundamentalGroupoid.glue Patch.exists_domain_mem_nhds (fun P : Patch M E ↦ P.functor R k)
    fun P Q ↦ P.map_inclusion_comp_functor R Q k

private lemma gluedSystem_obj (k : ℕ) (x : FundamentalGroupoid M) :
    (gluedSystem R M E k).obj x = localHomology R {x.as} k := by
  obtain ⟨P, hP⟩ := Patch.exists_domain_mem_nhds (E := E) x.as
  exact FundamentalGroupoid.glue_obj_mk _ _ _ P (mem_of_mem_nhds hP)

/-- The transport `Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {y})` of local homology along a path class from
`x` to `y`, for a Hausdorff space `M` modelled on a finite-dimensional real normed space `E`.
Along a path inside a compact convex set of a chart it is described by
`TauCeti.localHomologyRestriction_comp_localHomologyTransport`. -/
def localHomologyTransport (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomology R {x.as} k ⟶ localHomology R {y.as} k :=
  eqToHom (gluedSystem_obj R M E k x).symm ≫ (gluedSystem R M E k).map f ≫
    eqToHom (gluedSystem_obj R M E k y)

@[simp]
theorem localHomologyTransport_id (k : ℕ) (x : FundamentalGroupoid M) :
    localHomologyTransport R M E k (𝟙 x) = 𝟙 _ := by
  simp [localHomologyTransport]

@[simp]
theorem localHomologyTransport_comp (k : ℕ) {x y z : FundamentalGroupoid M} (f : x ⟶ y)
    (g : y ⟶ z) :
    localHomologyTransport R M E k (f ≫ g) =
      localHomologyTransport R M E k f ≫ localHomologyTransport R M E k g := by
  simp [localHomologyTransport]

/-- **The local homology system.** For a Hausdorff space `M` modelled on a finite-dimensional
real normed space `E`, the local homology groups `Hₖ(M, M ∖ {x})` form a functor out of the
fundamental groupoid of `M`, with the transport maps `TauCeti.localHomologyTransport`. For
`k = dim E` and integer coefficients it is the orientation local system of `M`. -/
@[expose, simps]
def localHomologySystem (k : ℕ) : FundamentalGroupoid M ⥤ A where
  obj x := localHomology R {x.as} k
  map f := localHomologyTransport R M E k f
  map_id := localHomologyTransport_id R M E k
  map_comp := localHomologyTransport_comp R M E k

variable {M E}

/-- Along a path inside the domain of a patch, the transport is the comparison of the endpoints
through the closed image of the patch. -/
private lemma Patch.localHomologyTransport_mk (P : Patch M E) {x y : M} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ P.domain) (k : ℕ) :
    localHomologyTransport R M E k
        (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      (P.iso R (γ.source ▸ hγ 0) k).inv ≫ (P.iso R (γ.target ▸ hγ 1) k).hom := by
  let γ' : Path (⟨x, γ.source ▸ hγ 0⟩ : P.domain) ⟨y, γ.target ▸ hγ 1⟩ := γ.codRestrict hγ
  have hγ' : (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal P.domain)).map
        (Path.Homotopic.Quotient.mk γ') :=
    congrArg Path.Homotopic.Quotient.mk
      (Path.map_codRestrict (x := ⟨x, γ.source ▸ hγ 0⟩) (y := ⟨y, γ.target ▸ hγ 1⟩) γ hγ).symm
  have h := Functor.hcongr_hom (FundamentalGroupoid.map_subtypeVal_comp_glue
    Patch.exists_domain_mem_nhds (fun P : Patch M E ↦ P.functor R k)
    (fun P Q ↦ P.map_inclusion_comp_functor R Q k) P) (Path.Homotopic.Quotient.mk γ')
  apply eq_of_heq
  rw [localHomologyTransport, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, hγ']
  -- `gluedSystem` is the glued functor, and the local functor of `P` sends a path to the
  -- comparison through `P`.
  exact h

/-- **Transport of local homology along a path in a chart.** Let `K ⊆ φ.target` be compact and
convex, and let `γ` be a path from `x` to `y` inside `φ.symm '' K`. Then the transport along `γ`
is compatible with the restrictions `Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {x})` and
`Hₖ(M, M ∖ φ.symm '' K) ⟶ Hₖ(M, M ∖ {y})`. Since the first of these is an isomorphism
(`TauCeti.isIso_localHomologyRestriction_symm_image`), this determines the transport. -/
theorem localHomologyRestriction_comp_localHomologyTransport (φ : OpenPartialHomeomorph M E)
    {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) (hKφ : K ⊆ φ.target) {x y : M}
    (γ : Path x y) (hγ : ∀ t, γ t ∈ φ.symm '' K) (k : ℕ) :
    localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
        localHomologyTransport R M E k
          (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
      localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k := by
  -- A thickening of `K` is a patch of `φ` containing `γ`; compare through its closed image.
  obtain ⟨δ, hδ, hδK⟩ := hKc.exists_cthickening_subset_open φ.open_target hKφ
  let P : Patch M E :=
    { chart := φ
      set := thickening δ K
      isOpen := isOpen_thickening
      convex := hK.thickening δ
      isBounded := hKc.isBounded.thickening
      closure_subset := (closure_thickening_subset_cthickening δ K).trans hδK }
  have hγP (t : unitInterval) : γ t ∈ P.domain := by
    obtain ⟨z, hz, hzt⟩ := hγ t
    refine hzt ▸ ⟨φ.map_target (hKφ hz), ?_⟩
    rw [Set.mem_preimage, φ.right_inv (hKφ hz)]
    exact self_subset_thickening hδ K hz
  have hKP : φ.symm '' K ⊆ P.closedImage :=
    image_mono fun z hz ↦ subset_closure (self_subset_thickening hδ K hz)
  rw [P.localHomologyTransport_mk R γ hγP k]
  obtain ⟨z, hz, hzx⟩ := γ.source ▸ hγ 0
  have : IsIso (localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k) := by
    subst hzx
    exact isIso_localHomologyRestriction_symm_image R φ
      (hK.starConvex ((φ.right_inv (hKφ hz)).symm ▸ hz)) hKc hKφ (φ.map_target (hKφ hz))
      ((φ.right_inv (hKφ hz)).symm ▸ hz) k
  have : IsIso (localHomologyRestriction R
      (Set.Subset.trans (singleton_subset_iff.2 (γ.source ▸ hγ 0)) hKP) k) :=
    (P.iso R (γ.source ▸ hγP 0) k).isIso_hom
  rw [Patch.iso_inv, Patch.iso_hom]
  exact localHomologyRestriction_comp_inv_comp R hKP _ _ k

/-- **Uniqueness of the transport.** A family of maps `Hₖ(M, M ∖ {x}) ⟶ Hₖ(M, M ∖ {y})` indexed by
path classes from `x` to `y`, compatible with composition and satisfying the conclusion of
`TauCeti.localHomologyRestriction_comp_localHomologyTransport` along paths inside compact convex
sets of charts, is the transport `TauCeti.localHomologyTransport`. -/
theorem eq_localHomologyTransport (k : ℕ)
    (t : ∀ {x y : FundamentalGroupoid M}, (x ⟶ y) →
      (localHomology R {x.as} k ⟶ localHomology R {y.as} k))
    (ht : ∀ {x y z : FundamentalGroupoid M} (f : x ⟶ y) (g : y ⟶ z), t (f ≫ g) = t f ≫ t g)
    (hchart : ∀ (φ : OpenPartialHomeomorph M E) {K : Set E}, Convex ℝ K → IsCompact K →
      K ⊆ φ.target → ∀ {x y : M} (γ : Path x y) (hγ : ∀ s, γ s ∈ φ.symm '' K),
        localHomologyRestriction R (singleton_subset_iff.2 (γ.source ▸ hγ 0)) k ≫
            t (Path.Homotopic.Quotient.mk γ :
              FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
          localHomologyRestriction R (singleton_subset_iff.2 (γ.target ▸ hγ 1)) k)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) : t f = localHomologyTransport R M E k f := by
  -- Along a path in the domain of a patch, `t` is the comparison through the patch.
  have hpatch (P : Patch M E) {a b : M} (γ : Path a b) (hγ : ∀ s, γ s ∈ P.domain) :
      t (Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) =
        (P.iso R (γ.source ▸ hγ 0) k).inv ≫ (P.iso R (γ.target ▸ hγ 1) k).hom := by
    rw [Iso.eq_inv_comp, Patch.iso_hom, Patch.iso_hom]
    exact hchart P.chart P.convex.closure P.isCompact_closure P.closure_subset γ
      fun s ↦ P.domain_subset_closedImage (hγ s)
  -- The maps `t` form a functor, which agrees with the local homology system on every patch.
  let G : FundamentalGroupoid M ⥤ A :=
    { obj x := localHomology R {x.as} k
      map := t
      map_id x := by
        obtain ⟨P, hP⟩ := Patch.exists_domain_mem_nhds (E := E) x.as
        have hx := mem_of_mem_nhds hP
        -- The identity of `x` is the class of the constant path, which lies in `P`.
        rw [FundamentalGroupoid.id_eq_path_refl]
        refine (hpatch P (Path.refl x.as) fun _ ↦ hx).trans ?_
        exact Iso.inv_hom_id _
      map_comp := ht }
  have hG : G = localHomologySystem R M E k := by
    refine FundamentalGroupoid.functor_ext (U := Patch.domain (M := M) (E := E))
      Patch.exists_domain_mem_nhds
      fun P ↦ CategoryTheory.Functor.hext (fun _ ↦ rfl) fun a b g ↦ heq_of_eq ?_
    induction g using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The image of `γ` in `M` is `γ.map continuous_subtype_val`, a path in the domain of `P`.
    exact (hpatch P (γ.map continuous_subtype_val) fun s ↦ (γ s).2).trans
      (P.localHomologyTransport_mk R (γ.map continuous_subtype_val) (fun s ↦ (γ s).2) k).symm
  exact eq_of_heq (Functor.hcongr_hom hG f)

end Chart

end TauCeti
