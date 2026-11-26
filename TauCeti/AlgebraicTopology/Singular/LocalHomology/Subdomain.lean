/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.Data.Set.Image
import TauCeti.Topology.Homeomorph.IsEmbedding

/-!
# The shriek map of a codimension-zero subdomain

Let `W` be a space and `Y ⊆ W` a closed subspace which is a compact manifold with collared
boundary, such as the closure `Ū` of a relatively compact open set `U` with smooth boundary inside
a manifold. Formally, `g : Y → W` is a closed embedding, `κ : V → Y` an open embedding whose
complement `∂Y = Y ∖ κ(V)` is the image of a collared map `f : N → Y` (`TauCeti.IsCollar`), and the
interior `g(κ(V))` is open in `W`. Then `g` identifies the homology of `Y` relative to its boundary
with the local homology of `W` along the interior:

`Hₖ(Y, ∂Y) ≅ Hₖ(W, W ∖ g(κ(V)))`

(`TauCeti.subdomainLocalHomologyIso`), for coefficients in any abelian category. This is excision
thickened by the collar. Write `Cₜ` for the part of depth less than `t` of the collar and
`Kₜ = Y ∖ Cₜ`, a closed subset of the interior. Then

* `Hₖ(Y, ∂Y) → Hₖ(Y, Y ∖ Kₜ)` is an isomorphism, since the collar deforms onto the boundary
  (`TauCeti.IsCollar.isIso_localHomologyRestriction_compl_collarPart`);
* `Hₖ(Y, Y ∖ Kₜ) → Hₖ(W, W ∖ g(Kₜ))` is an isomorphism, since both sides are the local homology of
  `V` along `κ⁻¹(Kₜ)` by excision (`TauCeti.isIso_localHomologyMap`);
* `Hₖ(W, W ∖ g(κ(V))) → Hₖ(W, W ∖ g(Kₜ))` is an isomorphism, since `W ∖ g(Kₜ)` deforms onto
  `W ∖ g(κ(V))`: on the image of the collar the deformation is that of the collar, and outside it
  the identity. The two pieces are closed in `W ∖ g(Kₜ)` and the deformation of the collar fixes
  their intersection `g(∂Y)`.

Restricting from a larger set `S ⊇ g(κ(V))` and then inverting this isomorphism gives the **shriek
map of the codimension-zero subdomain** (`TauCeti.subdomainShriek`)

`j_! : Hₖ(W, W ∖ S) → Hₖ(Y, ∂Y)`.

For a compact manifold `W` with collared boundary and `S` its interior, this is the map
`H_*(W, ∂W) → H_*(Ū, ∂U)` of a domain `U` whose closure lies in the interior of `W`. It sends the
fundamental class of `W` relative to its boundary to that of `Ū`, oriented by restriction
(`TauCeti.HomologicalOrientation.subdomainShriek_fundamentalClassRel`), so it is nonzero as soon as
`U` is nonempty (`TauCeti.HomologicalOrientation.subdomainShriek_fundamentalClassRel_ne_zero`).
With coefficients in a ring, it sends a class generating the local homology at every point of `U`
to a class with the same property
(`TauCeti.span_localHomologyRestriction_subdomainShriek_eq_top`), which identifies the images of
the mod `2` fundamental classes without orientations.

In symplectic topology this is the map `j_{U!}` along which Barraud, Damian, Humilière and Oancea
compare a Liouville domain `W` with a domain `U` bounded by a closed hypersurface: their criterion
for contractible almost existence asks for a class `α ∈ H_*(W, ∂W)` with `j_{U!} α ≠ 0` that dies in
symplectic homology, and for the unit ball the class `[W, ∂W]` qualifies for every such `U`.

## Main definitions

* `TauCeti.subdomainLocalHomologyIso`: `Hₖ(Y, ∂Y) ≅ Hₖ(W, W ∖ g(κ(V)))`, induced by `g`.
* `TauCeti.subdomainShriek`: the shriek map `Hₖ(W, W ∖ S) → Hₖ(Y, ∂Y)`.

## Main results

* `TauCeti.isIso_localHomologyMap_of_isCollared`: `g` induces an isomorphism
  `Hₖ(Y, ∂Y) → Hₖ(W, W ∖ g(κ(V)))`.
* `TauCeti.subdomainShriek_comp_localHomologyMap`, `TauCeti.eq_subdomainShriek_iff`: the shriek map
  is the unique map which, followed by the map induced by `g`, is the restriction.
* `TauCeti.HomologicalOrientation.subdomainShriek_fundamentalClassRel`: `j_![W, ∂W] = [Y, ∂Y]`.
* `TauCeti.HomologicalOrientation.subdomainShriek_fundamentalClassRel_ne_zero`: so `j_![W, ∂W]` is
  nonzero when the interior of `Y` is nonempty.
* `TauCeti.span_localHomologyRestriction_subdomainShriek_eq_top`: the shriek map preserves classes
  generating the local homology at every interior point.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (excision) and
  Section 3.3 (collars and the fundamental class of a manifold with boundary, proof of
  Theorem 3.43).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.1 and Remark 5.2, where `j_{U!}`
  enters the criterion for contractible almost existence.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology unitInterval

universe w v u

namespace TauCeti

/-! ### The deformation of the complement of a shrunk interior -/

section Deformation

variable {W Y V : Type w} {N : Type*} [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace N]
  {g : C(Y, W)} {κ : V → Y} {f : N → Y} {c : N × Ico (0 : ℝ) 1 → Y} {t : ℝ}

omit [TopologicalSpace N] in
/-- A point of `g(Cₜ)` is sent by `g⁻¹` into `Cₜ`. -/
private lemma symm_mem_collarPart (hg : IsClosedEmbedding g) {x : W}
    (hx : x ∈ g '' collarPart c t) :
    hg.isEmbedding.toHomeomorph.symm ⟨x, image_subset_range _ _ hx⟩ ∈ collarPart c t := by
  obtain ⟨z, hz, rfl⟩ := hx
  rwa [hg.isEmbedding.toHomeomorph_symm_apply]

omit [TopologicalSpace N] in
/-- Inside `W ∖ g(Kₜ)`, the points of `g(Y)` are the points of `g(Cₜ)`. -/
private lemma mem_image_collarPart_iff {x : W} (hx : x ∉ g '' (collarPart c t)ᶜ) :
    x ∈ g '' collarPart c t ↔ x ∈ range g := by
  refine ⟨fun h ↦ image_subset_range _ _ h, ?_⟩
  rintro ⟨z, rfl⟩
  by_cases hz : z ∈ collarPart c t
  · exact mem_image_of_mem _ hz
  · exact (hx (mem_image_of_mem _ hz)).elim

omit [TopologicalSpace N] in
/-- Every point of `W ∖ g(Kₜ)` lies in `g(Cₜ)` or outside the interior `g(κ(V))`. -/
private lemma mem_image_collarPart_or_notMem {x : W} (hx : x ∉ g '' (collarPart c t)ᶜ) :
    x ∈ g '' collarPart c t ∨ x ∉ range (g ∘ κ) := by
  by_cases h : x ∈ range (g ∘ κ)
  · obtain ⟨v, rfl⟩ := h
    exact Or.inl ((mem_image_collarPart_iff hx).2 (mem_range_self _))
  · exact Or.inr h

omit [TopologicalSpace N] in
/-- A point of `g(Cₜ)` outside the interior `g(κ(V))` comes from the boundary of `Y`. -/
private lemma symm_mem_range_of_notMem (hg : IsClosedEmbedding g) (hκf : range κ = (range f)ᶜ)
    {x : W} (hx : x ∈ g '' collarPart c t) (hxκ : x ∉ range (g ∘ κ)) :
    (hg.isEmbedding.toHomeomorph.symm ⟨x, image_subset_range _ _ hx⟩ : Y) ∈ range f := by
  rw [← compl_compl (range f), ← hκf]
  rintro ⟨v, hv⟩
  refine hxκ ⟨v, ?_⟩
  rw [Function.comp_apply, hv, hg.isEmbedding.apply_toHomeomorph_symm]

open scoped Classical in
/-- The deformation of `W ∖ g(Kₜ)`: on `g(Cₜ)` the deformation of the collar onto the boundary,
read through `g`, and outside `g(Cₜ)` the identity. -/
private def complDeformation (hg : IsClosedEmbedding g) (hc : IsCollar f c) (ht : 0 < t)
    (q : I × ((g '' (collarPart c t)ᶜ)ᶜ : Set W)) : W :=
  if h : (q.2 : W) ∈ g '' collarPart c t then
    g (hc.collarDeformation ht
      (q.1, ⟨hg.isEmbedding.toHomeomorph.symm ⟨q.2, image_subset_range _ _ h⟩,
        symm_mem_collarPart hg h⟩))
  else q.2

/-- On `g(Cₜ)` the deformation is that of the collar. -/
private lemma complDeformation_of_mem (hg : IsClosedEmbedding g) (hc : IsCollar f c) (ht : 0 < t)
    (q : I × ((g '' (collarPart c t)ᶜ)ᶜ : Set W)) (h : (q.2 : W) ∈ g '' collarPart c t) :
    complDeformation hg hc ht q = g (hc.collarDeformation ht
      (q.1, ⟨hg.isEmbedding.toHomeomorph.symm ⟨q.2, image_subset_range _ _ h⟩,
        symm_mem_collarPart hg h⟩)) :=
  dite_eq_left h

/-- Outside the interior the deformation is stationary. -/
private lemma complDeformation_of_notMem (hg : IsClosedEmbedding g) (hc : IsCollar f c)
    (hκf : range κ = (range f)ᶜ) (ht : 0 < t) (q : I × ((g '' (collarPart c t)ᶜ)ᶜ : Set W))
    (hq : (q.2 : W) ∉ range (g ∘ κ)) : complDeformation hg hc ht q = q.2 := by
  by_cases h : (q.2 : W) ∈ g '' collarPart c t
  · rw [complDeformation_of_mem hg hc ht q h,
      (hc.collarDeformation ht).eq_snd q.1 (symm_mem_range_of_notMem hg hκf h hq),
      ContinuousMap.id_apply, hg.isEmbedding.apply_toHomeomorph_symm]
  · exact dite_eq_right h

private lemma continuous_complDeformation (hg : IsClosedEmbedding g) (hc : IsCollar f c)
    (hκf : range κ = (range f)ᶜ) (hκ : IsOpen (range (g ∘ κ))) (ht : 0 < t) :
    Continuous (complDeformation hg hc ht) := by
  set T := ((g '' (collarPart c t)ᶜ)ᶜ : Set W)
  -- The deformation is continuous on the two closed pieces `g(Cₜ)` and the complement of the
  -- interior, which cover `W ∖ g(Kₜ)`.
  set P₁ := {q : I × T | (q.2 : W) ∈ g '' collarPart c t}
  set P₂ := {q : I × T | (q.2 : W) ∉ range (g ∘ κ)}
  have h₁ : IsClosed P₁ := by
    have : P₁ = {q : I × T | (q.2 : W) ∈ range g} :=
      Set.ext fun q ↦ mem_image_collarPart_iff q.2.property
    rw [this]
    exact hg.isClosed_range.preimage (continuous_subtypeVal.comp continuous_snd)
  have h₂ : IsClosed P₂ :=
    hκ.isClosed_compl.preimage (continuous_subtypeVal.comp continuous_snd)
  have hcov : P₁ ∪ P₂ = univ :=
    eq_univ_of_forall fun q ↦ mem_image_collarPart_or_notMem q.2.property
  rw [← continuousOn_univ, ← hcov]
  refine ContinuousOn.union_of_isClosed ?_ ?_ h₁ h₂
  · rw [continuousOn_iff_continuous_domRestrict]
    have : P₁.domRestrict (complDeformation hg hc ht) = fun q : P₁ ↦ g (hc.collarDeformation ht
        ((q : I × T).1, ⟨hg.isEmbedding.toHomeomorph.symm
          ⟨(q : I × T).2, image_subset_range _ _ q.property⟩,
          symm_mem_collarPart hg q.property⟩)) :=
      funext fun q ↦ complDeformation_of_mem hg hc ht q q.property
    rw [this]
    fun_prop
  · refine (continuous_subtypeVal.comp continuous_snd).continuousOn.congr fun q hq ↦ ?_
    exact complDeformation_of_notMem hg hc hκf ht q hq

/-- The deformation stays in `W ∖ g(Kₜ)`. -/
private lemma complDeformation_mem (hg : IsClosedEmbedding g) (hc : IsCollar f c) (ht : 0 < t)
    (q : I × ((g '' (collarPart c t)ᶜ)ᶜ : Set W)) :
    complDeformation hg hc ht q ∈ ((g '' (collarPart c t)ᶜ)ᶜ : Set W) := by
  by_cases h : (q.2 : W) ∈ g '' collarPart c t
  · rw [complDeformation_of_mem hg hc ht q h]
    rintro ⟨z, hz, hzq⟩
    exact hz (hg.injective hzq ▸ (hc.collarDeformation ht _).property)
  · rw [complDeformation, dite_eq_right h]
    exact q.2.property

/-- At time `0` the deformation lands outside the interior `g(κ(V))`. -/
private lemma complDeformation_zero_notMem (hg : IsClosedEmbedding g) (hc : IsCollar f c)
    (hκf : range κ = (range f)ᶜ) (ht : 0 < t) (x : ((g '' (collarPart c t)ᶜ)ᶜ : Set W)) :
    complDeformation hg hc ht (0, x) ∉ range (g ∘ κ) := by
  by_cases h : (x : W) ∈ g '' collarPart c t
  · rw [complDeformation_of_mem hg hc ht _ h, ContinuousMap.HomotopyWith.apply_zero,
      ContinuousMap.comp_apply, ContinuousMap.inclusion_apply_coe, hc.coe_collarRetraction]
    rintro ⟨v, hv⟩
    rw [Function.comp_apply] at hv
    have hκv : κ v ∈ (range f)ᶜ := hκf ▸ mem_range_self v
    exact hκv ⟨_, (hg.injective hv).symm⟩
  · rw [complDeformation, dite_eq_right h]
    exact (mem_image_collarPart_or_notMem x.property).resolve_left h

/-- At time `1` the deformation is the identity. -/
private lemma complDeformation_one (hg : IsClosedEmbedding g) (hc : IsCollar f c) (ht : 0 < t)
    (x : ((g '' (collarPart c t)ᶜ)ᶜ : Set W)) : complDeformation hg hc ht (1, x) = x := by
  by_cases h : (x : W) ∈ g '' collarPart c t
  · rw [complDeformation_of_mem hg hc ht _ h, ContinuousMap.HomotopyWith.apply_one,
      ContinuousMap.id_apply, hg.isEmbedding.apply_toHomeomorph_symm]
  · exact dite_eq_right h

/-- The shrunk interior `g(Kₜ)` lies in the interior `g(κ(V))`. -/
private lemma image_compl_collarPart_subset (hc : IsCollar f c) (hκf : range κ = (range f)ᶜ)
    (ht : 0 < t) : g '' (collarPart c t)ᶜ ⊆ range (g ∘ κ) := by
  rw [range_comp]
  exact image_mono (hc.compl_collarPart_subset_range hκf ht)

/-- **The complement of the shrunk interior deforms onto the complement of the interior.** The
restriction `Hₖ(W, W ∖ g(κ(V))) ⟶ Hₖ(W, W ∖ g(Kₜ))` is an isomorphism, by the long exact sequence
of the triple `(W, W ∖ g(Kₜ), W ∖ g(κ(V)))`. -/
private theorem isIso_localHomologyRestriction_image_compl_collarPart {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] (R : C) (hg : IsClosedEmbedding g) (hc : IsCollar f c)
    (hκf : range κ = (range f)ᶜ) (hκ : IsOpen (range (g ∘ κ))) (ht : 0 < t) (k : ℕ) :
    IsIso (localHomologyRestriction R (image_compl_collarPart_subset (g := g) hc hκf ht) k) := by
  have hST : (range (g ∘ κ))ᶜ ⊆ (g '' (collarPart c t)ᶜ)ᶜ :=
    compl_subset_compl.2 (image_compl_collarPart_subset hc hκf ht)
  have hcont := continuous_complDeformation hg hc hκf hκ ht
  let r : C(((g '' (collarPart c t)ᶜ)ᶜ : Set W), ((range (g ∘ κ))ᶜ : Set W)) :=
    ⟨fun x ↦ ⟨complDeformation hg hc ht (0, x), complDeformation_zero_notMem hg hc hκf ht x⟩,
      (hcont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let G : ((ContinuousMap.inclusion hST).comp r).HomotopyRel (ContinuousMap.id _)
      {x | (x : W) ∈ (range (g ∘ κ))ᶜ} :=
    { toFun := fun q ↦ ⟨complDeformation hg hc ht q, complDeformation_mem hg hc ht q⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun x ↦ Subtype.ext (complDeformation_one hg hc ht x)
      prop' := fun τ x hx ↦
        -- Outside the interior both the deformation and the retraction fix the point.
        Subtype.ext ((complDeformation_of_notMem hg hc hκf ht (τ, x) hx).trans
          (complDeformation_of_notMem hg hc hκf ht (0, x) hx).symm) }
  have hz (m : ℕ) :=
    TopPair.isZero_singularHomology_ofInclusion_of_homotopyRel (X := TopCat.of W) hST r G R m
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := TopCat.of W) hST) R k (hz k) fun m _ ↦ hz m
  rw [TopTriple.totalToOuter_app_ofSubset] at this
  rw [localHomologyRestriction_def]
  exact this

end Deformation

/-! ### Excision thickened by a collar -/

section Excision

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {W Y V : Type w} {N : Type*} [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace V]
  [TopologicalSpace N] {g : C(Y, W)} {κ : V → Y} {f : N → Y}

/-- **Excision thickened by a collar.** Let `g : Y → W` be a closed embedding and `κ : V → Y` an
open embedding whose complement `∂Y` is collared, with `g(κ(V))` open in `W`. Then `g` induces an
isomorphism `Hₖ(Y, ∂Y) ≅ Hₖ(W, W ∖ g(κ(V)))` from the homology of `Y` relative to its boundary to
the local homology of `W` along the interior of `Y`. -/
theorem isIso_localHomologyMap_of_isCollared (hg : IsClosedEmbedding g) (hκ : IsOpenEmbedding κ)
    (hf : IsCollared f) (hκf : range κ = (range f)ᶜ) (hgκ : IsOpenEmbedding (g ∘ κ))
    (h : g ⁻¹' range (g ∘ κ) ⊆ range κ) (k : ℕ) : IsIso (localHomologyMap R g h k) := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hf
  -- Work with the complement `K` of the collar of depth less than `1`.
  have hK : IsClosed (collarPart c 1)ᶜ := (hc.isOpen_collarPart 1).isClosed_compl
  have hgK : g ⁻¹' (g '' (collarPart c 1)ᶜ) ⊆ (collarPart c 1)ᶜ :=
    (hg.injective.preimage_image _).subset
  -- Both `Hₖ(Y, Y ∖ K)` and `Hₖ(W, W ∖ g(K))` are the local homology of `V` along `κ⁻¹(K)`.
  have h₁ := isIso_localHomologyMap R ⟨κ, hκ.continuous⟩ hκ rfl hK
    (hc.compl_collarPart_subset_range hκf one_pos) k
  have h₂ := isIso_localHomologyMap R (g.comp ⟨κ, hκ.continuous⟩) hgκ
    (S := κ ⁻¹' (collarPart c 1)ᶜ) (Set.ext fun _ ↦ hg.injective.mem_set_image)
    (hg.isClosedMap _ hK)
    (by rw [ContinuousMap.coe_comp, ContinuousMap.coe_mk]
        exact image_compl_collarPart_subset hc hκf one_pos) k
  have hb : IsIso (localHomologyMap R g hgK k) := by
    have : IsIso (localHomologyMap R ⟨κ, hκ.continuous⟩ subset_rfl k ≫
        localHomologyMap R g hgK k) := by
      rw [localHomologyMap_comp]
      exact h₂
    exact IsIso.of_isIso_comp_left (localHomologyMap R ⟨κ, hκ.continuous⟩ subset_rfl k) _
  -- The restrictions to `K` and to `g(K)` are isomorphisms, and they commute with `g`.
  have := isIso_localHomologyRestriction_image_compl_collarPart R hg hc hκf hgκ.isOpen_range
    one_pos k
  have := hc.isIso_localHomologyRestriction_compl_collarPart R hκf one_pos k
  have hsq : localHomologyMap R g h k ≫
      localHomologyRestriction R (image_compl_collarPart_subset (g := g) hc hκf one_pos) k =
      localHomologyRestriction R (hc.compl_collarPart_subset_range hκf one_pos) k ≫
        localHomologyMap R g hgK k := by
    rw [localHomologyMap_comp_localHomologyRestriction,
      localHomologyRestriction_comp_localHomologyMap]
  have : IsIso (localHomologyMap R g h k ≫
      localHomologyRestriction R (image_compl_collarPart_subset (g := g) hc hκf one_pos) k) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (localHomologyRestriction R (image_compl_collarPart_subset (g := g) hc hκf one_pos) k)

/-- **Excision thickened by a collar**, as an isomorphism: for a closed embedding `g : Y → W` and
an open embedding `κ : V → Y` with collared complement `∂Y` and open image `g(κ(V))`, the map
`Hₖ(Y, ∂Y) ≅ Hₖ(W, W ∖ g(κ(V)))` induced by `g`. -/
def subdomainLocalHomologyIso (hg : IsClosedEmbedding g) (hκ : IsOpenEmbedding κ)
    (hf : IsCollared f) (hκf : range κ = (range f)ᶜ) (hgκ : IsOpenEmbedding (g ∘ κ)) (k : ℕ) :
    localHomology R (range κ) k ≅ localHomology R (range (g ∘ κ)) k :=
  have h := (hg.injective.preimage_range_comp κ).subset
  have := isIso_localHomologyMap_of_isCollared R hg hκ hf hκf hgκ h k
  asIso (localHomologyMap R g h k)

@[simp]
lemma subdomainLocalHomologyIso_hom (hg : IsClosedEmbedding g) (hκ : IsOpenEmbedding κ)
    (hf : IsCollared f) (hκf : range κ = (range f)ᶜ) (hgκ : IsOpenEmbedding (g ∘ κ)) (k : ℕ) :
    (subdomainLocalHomologyIso R hg hκ hf hκf hgκ k).hom =
      localHomologyMap R g (hg.injective.preimage_range_comp κ).subset k :=
  (rfl)

variable (hg : IsClosedEmbedding g) (hκ : IsOpenEmbedding κ) (hf : IsCollared f)
  (hκf : range κ = (range f)ᶜ) (hgκ : IsOpenEmbedding (g ∘ κ)) {S : Set W}
  (hS : range (g ∘ κ) ⊆ S) (k : ℕ)

/-- **The shriek map of a codimension-zero subdomain** `j_! : Hₖ(W, W ∖ S) → Hₖ(Y, ∂Y)`: restriction
to the local homology of `W` along the interior `g(κ(V)) ⊆ S` of `Y`, followed by the inverse of the
excision isomorphism `TauCeti.subdomainLocalHomologyIso`. For a compact manifold `W` with collared
boundary, `S` its interior and `Y` the closure of a domain `U` in the interior, this is the map
`j_{U!} : H_*(W, ∂W) → H_*(Ū, ∂U)`. -/
def subdomainShriek : localHomology R S k ⟶ localHomology R (range κ) k :=
  localHomologyRestriction R hS k ≫ (subdomainLocalHomologyIso R hg hκ hf hκf hgκ k).inv

lemma subdomainShriek_def :
    subdomainShriek R hg hκ hf hκf hgκ hS k =
      localHomologyRestriction R hS k ≫ (subdomainLocalHomologyIso R hg hκ hf hκf hgκ k).inv :=
  (rfl)

/-- The shriek map followed by the map induced by `g` is the restriction to the interior of `Y`. -/
@[reassoc (attr := simp)]
theorem subdomainShriek_comp_localHomologyMap (h : g ⁻¹' range (g ∘ κ) ⊆ range κ) :
    subdomainShriek R hg hκ hf hκf hgκ hS k ≫ localHomologyMap R g h k =
      localHomologyRestriction R hS k := by
  rw [subdomainShriek_def, Category.assoc, ← subdomainLocalHomologyIso_hom R hg hκ hf hκf hgκ,
    Iso.inv_hom_id, Category.comp_id]

/-- **Characterization of the shriek map**: it is the unique map which, followed by the map induced
by `g`, is the restriction to the interior of `Y`. -/
theorem eq_subdomainShriek_iff (h : g ⁻¹' range (g ∘ κ) ⊆ range κ)
    {φ : localHomology R S k ⟶ localHomology R (range κ) k} :
    φ = subdomainShriek R hg hκ hf hκf hgκ hS k ↔
      φ ≫ localHomologyMap R g h k = localHomologyRestriction R hS k := by
  rw [← cancel_mono (subdomainLocalHomologyIso R hg hκ hf hκf hgκ k).hom,
    subdomainLocalHomologyIso_hom R hg hκ hf hκf hgκ, subdomainShriek_comp_localHomologyMap]

/-- On the local homology along the interior of `Y` itself, the shriek map inverts the map induced
by `g`. -/
@[reassoc (attr := simp)]
theorem localHomologyMap_comp_subdomainShriek (h : g ⁻¹' range (g ∘ κ) ⊆ range κ) :
    localHomologyMap R g h k ≫ subdomainShriek R hg hκ hf hκf hgκ subset_rfl k = 𝟙 _ := by
  rw [subdomainShriek_def, localHomologyRestriction_refl, Category.id_comp,
    ← subdomainLocalHomologyIso_hom R hg hκ hf hκf hgκ, Iso.hom_inv_id]

/-- Restricting before the shriek map is the shriek map from the larger set. -/
@[reassoc (attr := simp)]
theorem localHomologyRestriction_comp_subdomainShriek {S' : Set W} (hSS' : S ⊆ S') :
    localHomologyRestriction R hSS' k ≫ subdomainShriek R hg hκ hf hκf hgκ hS k =
      subdomainShriek R hg hκ hf hκf hgκ (hS.trans hSS') k := by
  rw [subdomainShriek_def, subdomainShriek_def, localHomologyRestriction_comp_assoc]

/-- **Local images of the shriek map.** At an interior point `κ x` of `Y`, the local image of
`j_! α`, carried to `W` by `g`, is the local image of `α` at `g (κ x)`. -/
@[reassoc, elementwise]
theorem subdomainShriek_comp_localHomologyRestriction_comp_localHomologyMap (x : V) {p : W}
    (hp : g (κ x) = p) (h : g ⁻¹' {p} ⊆ {κ x}) :
    subdomainShriek R hg hκ hf hκf hgκ hS k ≫
        localHomologyRestriction R (singleton_subset_iff.2 (mem_range_self x)) k ≫
          localHomologyMap R g h k =
      localHomologyRestriction R (singleton_subset_iff.2 (hS ⟨x, hp⟩)) k := by
  have hpκ : ({p} : Set W) ⊆ range (g ∘ κ) := singleton_subset_iff.2 ⟨x, hp⟩
  have h' := (hg.injective.preimage_range_comp κ).subset
  rw [localHomologyRestriction_comp_localHomologyMap,
    ← localHomologyMap_comp_localHomologyRestriction R g hpκ h',
    subdomainShriek_comp_localHomologyMap_assoc, localHomologyRestriction_comp]

end Excision

/-! ### Fundamental classes -/

section FundamentalClass

variable {W Y V : Type w} {N : Type*} [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace V]
  [TopologicalSpace N] {g : C(Y, W)} {κ : V → Y} {f : N → Y}

/-- At an interior point `κ x` of `Y`, the map `g` induces an isomorphism of local homology. -/
private lemma isIso_localHomologyMap_singleton {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] (R : C) [T1Space Y] [T1Space W] (hκ : IsOpenEmbedding κ)
    (hgκ : IsOpenEmbedding (g ∘ κ)) (x : V) {p : W} (hp : g (κ x) = p) (h : g ⁻¹' {p} ⊆ {κ x})
    (k : ℕ) : IsIso (localHomologyMap R g h k) := by
  subst hp
  exact isIso_localHomologyMap_singleton_of_isOpenEmbedding_comp R ⟨κ, hκ.continuous⟩ hκ g hgκ x h
    k

/-- **The shriek map preserves generators of local homology.** With coefficients in a ring `K`, if
`α` generates the local homology of `W` at the image `g (κ x)` of an interior point of `Y`, then
`j_! α` generates the local homology of `Y` at `κ x`. With `K = ZMod 2`, and since the mod `2`
fundamental class relative to the boundary is the unique class generating at every interior point
(`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`), the shriek map sends the
mod `2` fundamental class of `W` to that of `Y`. -/
theorem span_localHomologyRestriction_subdomainShriek_eq_top (K : Type w) [Ring K] [T1Space W]
    (hg : IsClosedEmbedding g) (hκ : IsOpenEmbedding κ) (hf : IsCollared f)
    (hκf : range κ = (range f)ᶜ) (hgκ : IsOpenEmbedding (g ∘ κ)) {S : Set W}
    (hS : range (g ∘ κ) ⊆ S) {k : ℕ}
    {α : localHomology (A := ModuleCat.{w} K) (ModuleCat.of K K) S k} (x : V)
    (hα : Submodule.span K
      {localHomologyRestriction (ModuleCat.of K K) (singleton_subset_iff.2 (hS (mem_range_self x)))
        k α} = ⊤) :
    Submodule.span K
      {localHomologyRestriction (ModuleCat.of K K) (singleton_subset_iff.2 (mem_range_self x)) k
        (subdomainShriek (ModuleCat.of K K) hg hκ hf hκf hgκ hS k α)} = ⊤ := by
  have : T1Space Y := hg.isEmbedding.t1Space
  have h : g ⁻¹' {(g ∘ κ) x} ⊆ {κ x} := (hg.injective.preimage_singleton (κ x)).subset
  have := isIso_localHomologyMap_singleton (ModuleCat.of K K) hκ hgκ x rfl h k
  rw [← ModuleCat.span_singleton_apply_eq_top_iff (localHomologyMap (ModuleCat.of K K) g h k),
    subdomainShriek_comp_localHomologyRestriction_comp_localHomologyMap_apply (hp := rfl)]
  exact hα

end FundamentalClass

namespace HomologicalOrientation

variable {W M Y V : Type} {N N' : Type*} [TopologicalSpace W] [TopologicalSpace M]
  [TopologicalSpace Y] [TopologicalSpace V] [TopologicalSpace N] [TopologicalSpace N']
  [T2Space W] [CompactSpace W] [T2Space M] [T2Space Y] [CompactSpace Y] [T2Space V] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  [ChartedSpace E V] {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n)
  {ι : M → W} {f : N → W} (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ)
  (hf : IsCollared f) {g : C(Y, W)} (hg : Function.Injective g) {κ : V → Y} {f' : N' → Y}
  (hκ : IsOpenEmbedding κ) (hκf : range κ = (range f')ᶜ) (hf' : IsCollared f') {j : V → M}
  (hj : IsOpenEmbedding j) (hjκ : ι ∘ j = g ∘ κ)

/-- **The shriek map sends the fundamental class to the fundamental class.** Let `W` and `Y` be
compact Hausdorff spaces with collared boundaries and interiors `ι : M → W` and `κ : V → Y`, and
let `g : Y → W` be injective and continuous, mapping the interior of `Y` into that of `W` through
an open embedding `j : V → M`, as the inclusion of the closure of a domain `U` with collared
boundary in the interior of a compact manifold `W`. For an orientation `o` of `M`, the shriek map
sends the relative fundamental class `[W, ∂W]` of `o` to the relative fundamental class `[Y, ∂Y]`
of the restricted orientation `o.comap hj`. -/
theorem subdomainShriek_fundamentalClassRel :
    subdomainShriek (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.continuous.isClosedEmbedding hg) hκ hf' hκf
        (hjκ ▸ hι.comp hj) (hjκ ▸ range_comp_subset_range j ι) n
        (o.fundamentalClassRel hn hι hιf hf) =
      (o.comap hj).fundamentalClassRel hn hκ hκf hf' := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  refine (o.comap hj).eq_fundamentalClassRel hn hκ hκf hf' fun x ↦ ?_
  have hp : g (κ x) = ι (j x) := (congrFun hjκ x).symm
  have h : g ⁻¹' {ι (j x)} ⊆ {κ x} := hp ▸ (hg.preimage_singleton (κ x)).subset
  have := isIso_localHomologyMap_singleton R hκ (hjκ ▸ hι.comp hj) x hp h n
  -- Compare the local images in `W`, where `g` is injective on local homology at `ι (j x)`.
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (localHomologyMap R g h n)
  have hmaps : (localHomologyIsoOfIsOpenEmbedding R hκ x n).hom ≫ localHomologyMap R g h n =
      (localHomologyIsoOfIsOpenEmbedding R hj x n).hom ≫
        (localHomologyIsoOfIsOpenEmbedding R hι (j x) n).hom := by
    simp only [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyMap_comp]
    exact localHomologyMap_congr R (ContinuousMap.ext fun y ↦ (congrFun hjκ y).symm) _ n
  rw [subdomainShriek_comp_localHomologyRestriction_comp_localHomologyMap_apply (hp := hp),
    o.localHomologyRestriction_fundamentalClassRel hn hι hιf hf,
    ← ConcreteCategory.comp_apply, hmaps, ConcreteCategory.comp_apply,
    ← hj.coe_localOrientationEquiv x (o.comap hj x), localOrientationEquiv_comap_apply]

/-- **The shriek map detects the fundamental class.** If the interior of `Y` is nonempty, the shriek
map sends the relative fundamental class `[W, ∂W]` to a nonzero class: its image `[Y, ∂Y]`
restricts to a local orientation at every interior point. -/
theorem subdomainShriek_fundamentalClassRel_ne_zero [Nonempty V] :
    subdomainShriek (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.continuous.isClosedEmbedding hg) hκ hf' hκf
        (hjκ ▸ hι.comp hj) (hjκ ▸ range_comp_subset_range j ι) n
        (o.fundamentalClassRel hn hι hιf hf) ≠ 0 := by
  rw [o.subdomainShriek_fundamentalClassRel hn hι hιf hf hg hκ hκf hf' hj hjκ]
  exact (o.comap hj).fundamentalClassRel_ne_zero hn hκ hκf hf'

end HomologicalOrientation

end TauCeti
