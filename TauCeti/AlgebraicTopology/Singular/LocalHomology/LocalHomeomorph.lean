/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.CoverGeneration
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Local homology along local homeomorphisms

A local homeomorphism `π : M → N`, such as a covering map, is an open embedding near each point,
so by excision it identifies the local homology `Hₖ(M, M ∖ {x})` with `Hₖ(N, N ∖ {π x})`
(`TauCeti.localHomologyIsoOfIsLocalHomeomorph`). The identification is read through any open
embedding `j : W → M` along which `π ∘ j` is again an open embedding: the isomorphism of `j`
followed by that of `π` at `j w` is the isomorphism of `π ∘ j`
(`TauCeti.localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph`). In
particular it does not depend on the neighbourhood of `x` used to define it.

For Hausdorff spaces modelled on the same finite-dimensional real normed space these
isomorphisms intertwine the transport of local homology along paths
(`TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsLocalHomeomorph_hom`): the local
homology system of `M` is the pullback along `π` of the local homology system of `N`. On each
open set on which `π` is an open embedding this is the corresponding statement for open embeddings
(`TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom`), and two functors
out of the fundamental groupoid that agree on the members of an open cover agree
(`TauCeti.FundamentalGroupoid.functor_ext`). Unlike an open embedding, `π` need not be injective
along a path, so the transport along a long path is not computed in a single chart of `N`.

## Main definitions

* `TauCeti.localHomologyIsoOfIsLocalHomeomorph`: for a local homeomorphism `π`, the isomorphism
  `Hₖ(M, M ∖ {x}) ≅ Hₖ(N, N ∖ {π x})`.

## Main results

* `TauCeti.localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph`: the
  isomorphism of `π` restricted along an open embedding.
* `TauCeti.localHomologyIsoOfIsLocalHomeomorph_eq_symm_trans`: the isomorphism of `π` read on an
  open set on which `π` is an open embedding.
* `TauCeti.localHomologyIsoOfIsLocalHomeomorph_eq_localHomologyIsoOfIsOpenEmbedding`: for an open
  embedding it is the excision isomorphism.
* `TauCeti.localHomologyTransport_comp_localHomologyIsoOfIsLocalHomeomorph_hom`: local
  homeomorphisms intertwine the transport of local homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3: local homology is computed by excision in a neighbourhood, and transported along
  paths through balls in charts.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section LocalHomeomorph

variable {M N W : Type w} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace W]
  [T1Space M] [T1Space N] {π : M → N}

/-- The isomorphism `Hₖ(M, M ∖ {x}) ≅ Hₖ(N, N ∖ {π x})` read through an open set `S ∋ x` on
which `π` is an open embedding: excision into `S`, followed by the map induced by `π` on `S`. -/
private def isoOfOpen {S : Set M} (hS : IsOpen S)
    (hπS : IsOpenEmbedding (π ∘ (Subtype.val : S → M))) {x : M} (hx : x ∈ S) (k : ℕ) :
    localHomology R {x} k ≅ localHomology R {π x} k :=
  (localHomologyIsoOfIsOpenEmbedding R hS.isOpenEmbedding_subtypeVal ⟨x, hx⟩ k).symm ≪≫
    localHomologyIsoOfIsOpenEmbedding R hπS ⟨x, hx⟩ k

/-- Through the open set `j⁻¹(S)`, which `j` embeds into `S`, the isomorphism of local homology of
an open embedding `ρ ∘ j` factors through the isomorphism of `ρ` on `S`. -/
private theorem localHomologyIsoOfIsOpenEmbedding_eq_symm_trans_trans [T1Space W] {X : Type w}
    [TopologicalSpace X] [T1Space X] {ρ : M → X} {S : Set M}
    (hρS : IsOpenEmbedding (ρ ∘ (Subtype.val : S → M))) {j : W → M}
    (hρj : IsOpenEmbedding (ρ ∘ j)) (hi : IsOpenEmbedding (Subtype.val : j ⁻¹' S → W))
    (hj' : IsOpenEmbedding fun z : j ⁻¹' S ↦ (⟨j z, z.property⟩ : S)) {w : W} (hw : j w ∈ S)
    (k : ℕ) :
    localHomologyIsoOfIsOpenEmbedding R hρj w k =
      (localHomologyIsoOfIsOpenEmbedding R hi ⟨w, hw⟩ k).symm ≪≫
        localHomologyIsoOfIsOpenEmbedding R hj' ⟨w, hw⟩ k ≪≫
          localHomologyIsoOfIsOpenEmbedding R hρS ⟨j w, hw⟩ k := by
  -- Both sides are the isomorphism of `ρ ∘ j` restricted to `j⁻¹(S)`, as a map `j⁻¹(S) → X`.
  ext : 1
  rw [Iso.trans_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Iso.trans_hom,
    localHomologyIsoOfIsOpenEmbedding_trans, localHomologyIsoOfIsOpenEmbedding_trans]

/-- Read through an open set `S` on which `π` is an open embedding, the isomorphism of local
homology induced by `π` restricts along every open embedding `j` with `π ∘ j` an open embedding:
the isomorphism of `j` followed by it is the isomorphism of `π ∘ j`. -/
private theorem localHomologyIsoOfIsOpenEmbedding_trans_isoOfOpen {S : Set M} (hS : IsOpen S)
    (hπS : IsOpenEmbedding (π ∘ (Subtype.val : S → M))) {j : W → M} (hj : IsOpenEmbedding j)
    (hπj : IsOpenEmbedding (π ∘ j)) {w : W} (hw : j w ∈ S) (k : ℕ) :
    localHomologyIsoOfIsOpenEmbedding R hj w k ≪≫ isoOfOpen R hS hπS hw k =
      localHomologyIsoOfIsOpenEmbedding R hπj w k := by
  have := hj.isEmbedding.t1Space
  -- Compare on the open set `j⁻¹(S)`, which `j` embeds into `S`.
  have hi : IsOpenEmbedding (Subtype.val : j ⁻¹' S → W) :=
    (hS.preimage hj.continuous).isOpenEmbedding_subtypeVal
  have hj' : IsOpenEmbedding fun z : j ⁻¹' S ↦ (⟨j z, z.property⟩ : S) :=
    (IsOpenEmbedding.of_comp_iff _ hS.isOpenEmbedding_subtypeVal).1 (hj.comp hi)
  -- Through `j⁻¹(S)`, the isomorphisms of `j = id ∘ j` and of `π ∘ j` factor through `S`.
  have e₁ : localHomologyIsoOfIsOpenEmbedding R hj w k =
      (localHomologyIsoOfIsOpenEmbedding R hi ⟨w, hw⟩ k).symm ≪≫
        localHomologyIsoOfIsOpenEmbedding R hj' ⟨w, hw⟩ k ≪≫
          localHomologyIsoOfIsOpenEmbedding R hS.isOpenEmbedding_subtypeVal ⟨j w, hw⟩ k :=
    localHomologyIsoOfIsOpenEmbedding_eq_symm_trans_trans R (ρ := id)
      hS.isOpenEmbedding_subtypeVal hj hi hj' hw k
  rw [e₁, localHomologyIsoOfIsOpenEmbedding_eq_symm_trans_trans R hπS hπj hi hj' hw k, isoOfOpen]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

/-- **The local homology isomorphism of a local homeomorphism.** A local homeomorphism
`π : M → N` between `T₁` spaces identifies the local homology of `M` at `x` with that of `N` at
`π x`, through excision into an open neighbourhood of `x` on which `π` is an open embedding. It
does not depend on that neighbourhood
(`TauCeti.localHomologyIsoOfIsLocalHomeomorph_eq_symm_trans`). -/
def localHomologyIsoOfIsLocalHomeomorph (hπ : IsLocalHomeomorph π) (x : M) (k : ℕ) :
    localHomology R {x} k ≅ localHomology R {π x} k :=
  let e : OpenPartialHomeomorph M N := Classical.choose (hπ x)
  have he : x ∈ e.source ∧ π = e := Classical.choose_spec (hπ x)
  isoOfOpen R e.open_source (by rw [he.2]; exact e.isOpenEmbedding_restrict) he.1 k

/-- **The local homology isomorphism of a local homeomorphism, along an open embedding.** For an
open embedding `j : W → M` such that `π ∘ j` is an open embedding, the isomorphism of local
homology induced by `j` at `w`, followed by that of `π` at `j w`, is the isomorphism induced by
`π ∘ j` at `w`. -/
@[simp]
theorem localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph
    (hπ : IsLocalHomeomorph π) {j : W → M} (hj : IsOpenEmbedding j)
    (hπj : IsOpenEmbedding (π ∘ j)) (w : W) (k : ℕ) :
    localHomologyIsoOfIsOpenEmbedding R hj w k ≪≫
        localHomologyIsoOfIsLocalHomeomorph R hπ (j w) k =
      localHomologyIsoOfIsOpenEmbedding R hπj w k := by
  rw [localHomologyIsoOfIsLocalHomeomorph]
  exact localHomologyIsoOfIsOpenEmbedding_trans_isoOfOpen R _ _ hj hπj _ k

/-- On an open set `S` on which `π` is an open embedding, the local homology isomorphism of `π`
is excision into `S` followed by the map induced by `π` on `S`. -/
theorem localHomologyIsoOfIsLocalHomeomorph_eq_symm_trans (hπ : IsLocalHomeomorph π) {S : Set M}
    (hS : IsOpen S) (hπS : IsOpenEmbedding (π ∘ (Subtype.val : S → M))) {x : M} (hx : x ∈ S)
    (k : ℕ) :
    localHomologyIsoOfIsLocalHomeomorph R hπ x k =
      (localHomologyIsoOfIsOpenEmbedding R hS.isOpenEmbedding_subtypeVal ⟨x, hx⟩ k).symm ≪≫
        localHomologyIsoOfIsOpenEmbedding R hπS ⟨x, hx⟩ k := by
  rw [← localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph R hπ
    hS.isOpenEmbedding_subtypeVal hπS ⟨x, hx⟩ k, ← Iso.trans_assoc, Iso.symm_self_id,
    Iso.refl_trans]

/-- For an open embedding, the local homology isomorphism of `π` as a local homeomorphism is its
local homology isomorphism as an open embedding. -/
theorem localHomologyIsoOfIsLocalHomeomorph_eq_localHomologyIsoOfIsOpenEmbedding
    (hπ : IsLocalHomeomorph π) (hπ' : IsOpenEmbedding π) (x : M) (k : ℕ) :
    localHomologyIsoOfIsLocalHomeomorph R hπ x k = localHomologyIsoOfIsOpenEmbedding R hπ' x k := by
  simpa using localHomologyIsoOfIsOpenEmbedding_trans_localHomologyIsoOfIsLocalHomeomorph R hπ
    IsOpenEmbedding.id hπ' x k

end LocalHomeomorph

section Transport

variable {M N E : Type w} [TopologicalSpace M] [T2Space M] [TopologicalSpace N] [T2Space N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [ChartedSpace E N] {π : M → N}

/-- The local homology isomorphism of `π`, with target indexed by the image object of the
fundamental groupoid, so that composites with the transport of `N` typecheck syntactically. -/
private def isoAt (hπ : IsLocalHomeomorph π) (k : ℕ) (z : FundamentalGroupoid M) :
    localHomology R {z.as} k ≅
      localHomology R {((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).obj z).as} k :=
  localHomologyIsoOfIsLocalHomeomorph R hπ z.as k

variable (E) in
/-- The transport of local homology of `N` along the images of path classes, conjugated back to
`M` by the local homology isomorphisms of `π`. -/
private def conjFunctor (hπ : IsLocalHomeomorph π) (k : ℕ) : FundamentalGroupoid M ⥤ A where
  obj z := localHomology R {z.as} k
  map {x y} f := (isoAt R hπ k x).hom ≫
    localHomologyTransport R N E k ((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map f) ≫
      (isoAt R hπ k y).inv
  map_id z := by
    rw [CategoryTheory.Functor.map_id, localHomologyTransport_id, Category.id_comp,
      Iso.hom_inv_id]
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, localHomologyTransport_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- On an open set on which `π` is an open embedding, the local homology isomorphisms of `π`
intertwine the transports of `M` and `N` along path classes inside the set. -/
private lemma localHomologyTransport_map_subtypeVal (hπ : IsLocalHomeomorph π) (k : ℕ)
    (S : TopologicalSpace.Opens M) (hπS : IsOpenEmbedding (π ∘ (Subtype.val : S → M)))
    {a b : FundamentalGroupoid S} (f : a ⟶ b) :
    localHomologyTransport R M E k
        ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).map f) =
      (isoAt R hπ k
          ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).obj a)).hom ≫
        localHomologyTransport R N E k ((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map
          ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).map f)) ≫
        (isoAt R hπ k
          ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).obj b)).inv := by
  let _ : ChartedSpace E S := TopologicalSpace.Opens.instChartedSpace S
  have hS : IsOpenEmbedding (Subtype.val : S → M) := S.isOpen.isOpenEmbedding_subtypeVal
  -- Both transports are the transport of `S`, through the open embeddings of `S` into `M` and,
  -- by `π`, into `N`.
  have hM := localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom R (E := E)
    hS k f
  have hN := localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom R (E := E)
    hπS k f
  have hI (c : FundamentalGroupoid S) :
      isoAt R hπ k ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).obj c) =
        (localHomologyIsoOfIsOpenEmbedding R hS c.as k).symm ≪≫
          localHomologyIsoOfIsOpenEmbedding R hπS c.as k :=
    localHomologyIsoOfIsLocalHomeomorph_eq_symm_trans R hπ S.isOpen hπS c.as.property k
  have hF : (FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map
      ((FundamentalGroupoid.map ⟨Subtype.val, continuous_subtypeVal⟩).map f) =
        (FundamentalGroupoid.map ⟨π ∘ Subtype.val, hπS.continuous⟩).map f :=
    -- Functoriality of `FundamentalGroupoid.map`; the composite of the two continuous maps is
    -- `π ∘ Subtype.val` by definition.
    eq_of_heq (Functor.hcongr_hom (FundamentalGroupoid.map_comp ⟨π, hπ.continuous⟩
      ⟨Subtype.val, continuous_subtypeVal⟩) f).symm
  rw [hI, hI, hF]
  -- Move the transport of `M` to `S` by `hM`, insert the isomorphism of `π` on `S` at the end,
  -- and move the transport of `S` to `N` by `hN`. The objects of these composites agree with
  -- those of the goal only up to unfolding `FundamentalGroupoid.map`, so the steps are chained by
  -- `Eq.trans`, which compares them up to definitional equality.
  refine (Iso.inv_hom_id_assoc (localHomologyIsoOfIsOpenEmbedding R hS a.as k) _).symm.trans ?_
  rw [← hM, ← Iso.hom_inv_id_assoc (localHomologyIsoOfIsOpenEmbedding R hπS b.as k)
    (localHomologyIsoOfIsOpenEmbedding R hS b.as k).hom, reassoc_of% hN]
  exact (congrArg (_ ≫ ·) (Category.assoc (obj := A) _ _ _)).trans
    (Category.assoc _ _ _).symm

/-- **Local homeomorphisms intertwine the transport of local homology.** For a local
homeomorphism `π : M → N` of Hausdorff spaces modelled on the same finite-dimensional real normed
space, the isomorphisms `Hₖ(M, M ∖ {x}) ≅ Hₖ(N, N ∖ {π x})` induced by `π` carry the transport of
local homology of `M` along a path class to the transport of local homology of `N` along its
image. -/
@[reassoc]
theorem localHomologyTransport_comp_localHomologyIsoOfIsLocalHomeomorph_hom
    (hπ : IsLocalHomeomorph π) (k : ℕ) {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport R M E k f ≫ (localHomologyIsoOfIsLocalHomeomorph R hπ y.as k).hom =
      (localHomologyIsoOfIsLocalHomeomorph R hπ x.as k).hom ≫
        localHomologyTransport R N E k (x := (FundamentalGroupoid.map ⟨π, hπ.continuous⟩).obj x)
          (y := (FundamentalGroupoid.map ⟨π, hπ.continuous⟩).obj y)
          ((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map f) := by
  -- The open sets on which `π` is an open embedding cover `M`, and on each of them the transport
  -- of `M` is the conjugated transport of `N`; so the two functors agree.
  let U (i : {S : TopologicalSpace.Opens M // IsOpenEmbedding (π ∘ (Subtype.val : S → M))}) :
    Set M := i.val
  have hU (z : M) : ∃ i, U i ∈ nhds z := by
    obtain ⟨e, hz, he⟩ := hπ z
    exact ⟨⟨⟨e.source, e.open_source⟩, he ▸ e.isOpenEmbedding_restrict⟩,
      e.open_source.mem_nhds hz⟩
  -- The two functors have the same objects, so they agree as soon as their maps agree.
  have key : localHomologySystem R M E k = conjFunctor R E hπ k :=
    FundamentalGroupoid.functor_ext hU fun i ↦ CategoryTheory.Functor.hext (fun _ ↦ rfl)
      fun a b f ↦ heq_of_eq (localHomologyTransport_map_subtypeVal R hπ k i.val i.property f)
  have h : localHomologyTransport R M E k f = (isoAt R hπ k x).hom ≫
      localHomologyTransport R N E k ((FundamentalGroupoid.map ⟨π, hπ.continuous⟩).map f) ≫
        (isoAt R hπ k y).inv :=
    eq_of_heq (CategoryTheory.Functor.hcongr_hom key f)
  -- Move the isomorphism at `y` across. `simp` cannot cancel it after `rw [h]`: the objects of
  -- `isoAt` agree with those of the goal only up to unfolding `FundamentalGroupoid.map`.
  exact (Iso.eq_comp_inv (isoAt R hπ k y)).1 (h.trans (Category.assoc _ _ _).symm)

end Transport

end TauCeti
