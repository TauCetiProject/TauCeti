/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.FaceGluing
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.BoundaryFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton

/-!
# Representing chain systems of fundamental classes when `1` is the only unit

Let `M x y` be compact Hausdorff spaces, indexed by pairs of elements of a finite set `P` graded by
`ind`, each containing a manifold `N x y` of dimension `ind x - ind y - 1` as an open subset whose
complement `∂ M x y` is collared, such as the compactified trajectory spaces of a Morse function.
With coefficients in a commutative ring `k` whose only unit is `1`, such as `ZMod 2`, let
`μ x y ∈ H(M x y, ∂ M x y; k)` generate the local homology at every interior point, as the mod `2`
fundamental class relative to the boundary does
(`TauCeti.existsUnique_span_localHomologyRestriction_range_eq_top`). Suppose that the boundary is a
closed manifold of dimension `ind x - ind y - 2`, glued along the composition maps
`ι x z y : M x z × M z y → M x y` from faces whose interiors are the images of `N x z × N z y`.
Then some twisting chain system represents the classes `μ`
(`TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`): the fundamental
chains rel boundary can be chosen so that the boundary of each is the sum of the cross products of
the fundamental chains of its faces.

This discharges the face condition of `TauCeti.TwistingChainSystem.exists_isRepresenting_of_faces`
at each interior point `a` of a face. In the local homology `H(∂ M x y, ∂ M x y ∖ {a}; k) ≅ k`:

* the image of the boundary `∂ μ x y` generates
  (`TauCeti.span_homologyMap_cubicalHomologyδ_eq_top`), the cubical form of
  `TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`;
* the image of the cross product `μ x z × μ z y` under the face map generates
  (`TauCeti.span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top`): by the
  Künneth theorem for the local pairs
  (`TauCeti.span_homologyMap_cubicalHomologyKunnethPair_tmul_eq_top`) it generates the local
  homology of the product at the preimage of `a`, and the face map is an open embedding near that
  point
  (`TauCeti.isIso_localHomologyMap_singleton_of_isOpenEmbedding_comp`);
* a module isomorphic to `k` has only one generator when `1` is the only unit of `k`
  (`TauCeti.eq_of_span_cubicalHomology_eq_top`), and the sign `(-1) ^ (ind x - ind z)` acts
  trivially, since `-1 = 1` in `k`.

No orientations enter: with integral coefficients the face condition compares the boundary
orientation of each face with its product orientation, which is not done here.

## Main results

* `TauCeti.span_homologyMap_cubicalHomologyδ_eq_top`: the boundary of a relative class generating
  at the interior points generates the local cubical homology of a collared boundary.
* `TauCeti.span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top`: the cross
  product of two such classes, carried along a face map, generates the local cubical homology at
  an interior point of the face.
* `TauCeti.eq_of_span_cubicalHomology_eq_top`: the local cubical homology of a manifold in top
  degree has a single generator when `1` is the only unit of the coefficients.
* `TauCeti.TwistingChainSystem.exists_isRepresenting_of_subsingleton_units`: representing twisting
  chain systems of fundamental classes exist when `1` is the only unit of the coefficients.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Annals of
  Mathematics 166 (2007), Lemma 2.2 and Appendix A, the representing chain systems of
  compactified trajectory spaces over `ℤ/2`.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Proposition 5.2.6.
* A. Hatcher, *Algebraic Topology*, Section 3.3, the mod `2` fundamental class.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology MonoidalCategory TopPair HomologicalComplex
open scoped TensorProduct

universe u

namespace TauCeti

section Ring

variable {k : Type u} [Ring k]

/-- **The boundary of a class generating at the interior points generates the local homology of
the boundary.** Let `j : N → X` have collared complement `∂X = X ∖ j(N)` in a Hausdorff space `X`,
and let `μ` be a class of the relative cubical homology `Hₙ(X, ∂X; k)` whose image in the local
homology `Hₙ(X, X ∖ {j q}; k)` generates it at every point `q` of `N`. Then for `m + 1 = n` the
image of the boundary `∂ μ ∈ Hₘ(∂X; k)` in the local cubical homology `Hₘ(∂X, ∂X ∖ {a}; k)`
generates it at every point `a` of `∂X`. This is the cubical form of
`TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`. -/
theorem span_homologyMap_cubicalHomologyδ_eq_top {X : TopCat.{u}} [T2Space X] {N : Type u}
    {j : N → X} (hcol : IsCollared (Subtype.val : ↥(range j)ᶜ → X))
    {n m : ℕ} (hnm : m + 1 = n)
    (μ : ((TopPair.ofSubset (range j)ᶜ).cubicalChainComplex k).homology n)
    (hμ : ∀ q : N, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self q)) n
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) n).inv.hom μ)) = ⊤)
    (a : ↥(range j)ᶜ) :
    (k ∙ (HomologicalComplex.homologyMap (cokernel.π
      ((normalizedCubicalChainComplex k).map (TopPair.ofSubset ({a}ᶜ : Set ↥(range j)ᶜ)).map))
        m).hom (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k n m hnm).hom μ)) = ⊤ := by
  subst hnm
  have hδ := isFundamentalClass_singularHomologyδ_of_forall_span_eq_top (ModuleCat.of k k)
    (ι := j) (f := Subtype.val) (by rw [Subtype.range_coe, compl_compl]) hcol (n := m)
    (γ := (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) (m + 1)).inv.hom μ)
    (by rintro _ ⟨q, rfl⟩; exact hμ q)
  -- Read through the cubical–singular comparisons, the image of `∂ μ` at `a` is the image at `a`
  -- of the singular boundary, a fundamental class of `∂X`.
  refine (ModuleCat.span_singleton_apply_eq_top_iff (TopPair.singularCubicalHomologyIso k
    (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ) m).inv).1 ?_
  have e₁ : HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ).map)) m ≫
        (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ)
          m).inv = (singularCubicalHomologyIso k (TopCat.of ↥(range j)ᶜ) m).inv ≫
        (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ).singularHomologyπ
          (ModuleCat.of k k) m :=
      TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv k _ m
  have e₂ : (TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k (m + 1) m rfl ≫
        (singularCubicalHomologyIso k (TopCat.of ↥(range j)ᶜ) m).inv =
        (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) (m + 1)).inv ≫
          (TopPair.ofSubset (range j)ᶜ).singularHomologyδ (ModuleCat.of k k) (m + 1) m rfl :=
      (TopPair.singularCubicalHomologyIso_inv_singularHomologyδ k _ (m + 1) m rfl).symm
  convert (isFundamentalClass_iff _).1 hδ a using 3
  refine Eq.trans ?_ (singularHomologyToLocalHomology_eq_singularHomologyπ _ a _).symm
  exact (congrArg (fun f ↦ f.hom (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k (m + 1) m
    rfl).hom μ)) e₁).trans (congrArg (fun v ↦ ((TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ)
      {a}ᶜ).singularHomologyπ (ModuleCat.of k k) m).hom v) (congrArg (fun f ↦ f.hom μ) e₂))

/-- **The local cubical homology of a manifold has a single generator when `1` is the only unit
of the coefficients.** On a manifold `Y` of dimension `m`, with coefficients in a ring `k` whose
only unit is `1` and in which one-sided inverses are inverses, two generators of the local cubical
homology `Hₘ(Y, Y ∖ {a}; k) ≅ k` are equal. This is the cubical form of
`TauCeti.eq_of_span_localHomology_eq_top`. -/
theorem eq_of_span_cubicalHomology_eq_top [IsDedekindFiniteMonoid k] [Subsingleton kˣ] {Y : Type u}
    [TopologicalSpace Y]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E Y] {m : ℕ} (hm : finrank ℝ E = m) (a : Y)
    {v w : ((TopPair.ofSubset (X := TopCat.of Y) {a}ᶜ).cubicalChainComplex k).homology m}
    (hv : k ∙ v = ⊤) (hw : k ∙ w = ⊤) : v = w := by
  have hinj := (ModuleCat.mono_iff_injective
    (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of Y) {a}ᶜ) m).inv).1
      inferInstance
  exact hinj (eq_of_span_localHomology_eq_top k hm
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hv)
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hw))

end Ring

variable {k : Type u} [CommRing k]

variable {X₁ X₂ : TopCat.{u}} {N₁ N₂ : Type u} [TopologicalSpace N₁] [TopologicalSpace N₂]
  {j₁ : N₁ → X₁} {j₂ : N₂ → X₂} {Y : Type u} [TopologicalSpace Y]

omit [TopologicalSpace N₁] [TopologicalSpace N₂] in
/-- A face map sending the boundary of the product off `f (j₁ r.1, j₂ r.2)` and injective on the
interior sends every point other than `(j₁ r.1, j₂ r.2)` off it. -/
private theorem mapsTo_compl_singleton_of_mapsTo_prodSubspace (f : X₁ ⊗ X₂ ⟶ TopCat.of Y)
    (hf : Function.Injective fun r : N₁ × N₂ ↦ f (j₁ r.1, j₂ r.2)) (r : N₁ × N₂)
    (h : MapsTo f ((TopPair.ofSubset (range j₁)ᶜ).prodSubspace (TopPair.ofSubset (range j₂)ᶜ))
      {f (j₁ r.1, j₂ r.2)}ᶜ) :
    MapsTo f (CartesianMonoidalCategory.fst X₁ X₂ ⁻¹' ({j₁ r.1}ᶜ : Set X₁) ∪
      CartesianMonoidalCategory.snd X₁ X₂ ⁻¹' ({j₂ r.2}ᶜ : Set X₂)) {f (j₁ r.1, j₂ r.2)}ᶜ := by
  intro z hz hfz
  by_cases hzP : z ∈ (TopPair.ofSubset (range j₁)ᶜ).prodSubspace (TopPair.ofSubset (range j₂)ᶜ)
  · exact h hzP hfz
  · -- Off the boundary of the product, both coordinates are interior points.
    obtain ⟨s₁, hs₁⟩ : z.1 ∈ range j₁ := not_not.1 fun hc ↦ hzP (Or.inl
      ((range_ofSubset_map (B := (range j₁)ᶜ)).symm ▸ hc))
    obtain ⟨s₂, hs₂⟩ : z.2 ∈ range j₂ := not_not.1 fun hc ↦ hzP (Or.inr
      ((range_ofSubset_map (B := (range j₂)ᶜ)).symm ▸ hc))
    obtain rfl : (s₁, s₂) = r := hf (by
      dsimp only
      rw [hs₁, hs₂]
      exact hfz)
    exact hz.elim (fun h ↦ h hs₁.symm) (fun h ↦ h hs₂.symm)

/-- A face map which is an open embedding on the interior of the product and sends every point
other than `(j₁ r.1, j₂ r.2)` off its image induces an isomorphism from the local homology of the
product there, written along `{j₁ r.1}ᶜ × X₂ ∪ X₁ × {j₂ r.2}ᶜ`, to the local homology of `Y`. -/
private theorem isIso_singularHomologyMap_ofSubsetMap_preimage_union [T1Space X₁] [T1Space X₂]
    [T1Space Y] (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (f : X₁ ⊗ X₂ ⟶ TopCat.of Y)
    (hf : IsOpenEmbedding fun r : N₁ × N₂ ↦ f (j₁ r.1, j₂ r.2)) (r : N₁ × N₂)
    (h : MapsTo f (CartesianMonoidalCategory.fst X₁ X₂ ⁻¹' ({j₁ r.1}ᶜ : Set X₁) ∪
      CartesianMonoidalCategory.snd X₁ X₂ ⁻¹' ({j₂ r.2}ᶜ : Set X₂)) {f (j₁ r.1, j₂ r.2)}ᶜ)
    (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (ofSubsetMap f h) (ModuleCat.of k k) n) := by
  -- The complement of `{j₁ r.1}ᶜ × X₂ ∪ X₁ × {j₂ r.2}ᶜ` is the point `(j₁ r.1, j₂ r.2)`.
  have hS : (CartesianMonoidalCategory.fst X₁ X₂ ⁻¹' ({j₁ r.1}ᶜ : Set X₁) ∪
      CartesianMonoidalCategory.snd X₁ X₂ ⁻¹' ({j₂ r.2}ᶜ : Set X₂)) = {(j₁ r.1, j₂ r.2)}ᶜ := by
    ext z
    exact ⟨fun hz hzr ↦ hz.elim (fun h ↦ h (congrArg Prod.fst hzr : z.1 = j₁ r.1))
        (fun h ↦ h (congrArg Prod.snd hzr : z.2 = j₂ r.2)),
      fun hz ↦ by_contra fun hc ↦ hz (Prod.ext (not_not.1 fun h₁ ↦ hc (Or.inl h₁))
        (not_not.1 fun h₂ ↦ hc (Or.inr h₂)))⟩
  have hf' : f.hom ⁻¹' {f.hom (j₁ r.1, j₂ r.2)} ⊆ {(j₁ r.1, j₂ r.2)} := fun z hz ↦
    not_not.1 fun hzr ↦ h (hS.symm ▸ hzr) hz
  have hloc : IsIso (localHomologyMap (ModuleCat.of k k) f.hom hf' n) :=
    isIso_localHomologyMap_singleton_of_isOpenEmbedding_comp (ModuleCat.of k k)
      (j := ContinuousMap.prodMap ⟨j₁, hj₁.continuous⟩ ⟨j₂, hj₂.continuous⟩) (hj₁.prodMap hj₂)
      f.hom hf r hf' n
  rw [localHomologyMap_def] at hloc
  -- With the subspace written as the complement of the point, the map of pairs is the one
  -- inducing `hloc`.
  have key : ∀ (S : Set ↑(X₁ ⊗ X₂)) (_ : S = {(j₁ r.1, j₂ r.2)}ᶜ)
      (hm : MapsTo f S {f (j₁ r.1, j₂ r.2)}ᶜ),
      IsIso (TopPair.singularHomologyMap (ofSubsetMap f hm) (ModuleCat.of k k) n) := by
    rintro S rfl _
    exact hloc
  exact key _ hS h

omit [TopologicalSpace N₂] in
/-- The Künneth class of two relative classes generating the local homology at interior points
`j₁ r₁` and `j₂ r₂`, the first a point of a manifold, generates the local homology of the product
at `(j₁ r₁, j₂ r₂)`. -/
private theorem span_homologyMap_cubicalHomologyKunnethPair_eq_top_of_isOpenEmbedding
    [T1Space X₁] [T1Space X₂] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [ChartedSpace F N₁] (hj₁ : IsOpenEmbedding j₁) {q : ℕ}
    (μ₁ : ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplex k).homology (finrank ℝ F))
    (μ₂ : ((TopPair.ofSubset (range j₂)ᶜ).cubicalChainComplex k).homology q) (r₁ : N₁) (r₂ : N₂)
    (hμ₁ : (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r₁)) _
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j₁)ᶜ) _).inv.hom μ₁)) = ⊤)
    (hμ₂ : (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r₂)) q
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j₂)ᶜ) q).inv.hom μ₂)) = ⊤) :
    (k ∙ (homologyMap (cubicalChainComplexProdMap k _ _
        (ofSubsetMap (𝟙 X₁) (compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self r₁))))
        (ofSubsetMap (𝟙 X₂) (compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self r₂)))))
          (finrank ℝ F + q) ≫
      homologyMap (cubicalChainComplexProdToSingular k ({j₁ r₁}ᶜ : Set X₁) ({j₂ r₂}ᶜ : Set X₂))
        (finrank ℝ F + q)).hom
      ((GradedObject.Monoidal.ιTensorObj _ _ _ q _ rfl ≫
        cubicalHomologyKunnethPair k (TopPair.ofSubset (range j₁)ᶜ) (TopPair.ofSubset (range j₂)ᶜ)
          (finrank ℝ F + q)).hom (μ₁ ⊗ₜ μ₂))) = ⊤ := by
  have := hj₁.isEmbedding.t1Space
  -- At the interior point `j₁ r₁`, the local homology of `X₁` is that of `N₁`, computed by a
  -- chart.
  have hX (p' : ℕ) (hp' : p' ≠ finrank ℝ F) :
      IsZero (localHomology (ModuleCat.of k k) ({j₁ r₁} : Set X₁) p') :=
    (isZero_singularHomology_complSingleton_of_ne (ModuleCat.of k k) (chartAt F r₁)
      (mem_chart_source F r₁) rfl hp').of_iso (localHomologyIsoOfIsOpenEmbedding _ hj₁ r₁ p').symm
  have : Projective (localHomology (ModuleCat.of k k) ({j₁ r₁} : Set X₁) (finrank ℝ F)) :=
    Projective.of_iso ((localHomologyIsoOfIsOpenEmbedding _ hj₁ r₁ _).symm ≪≫
      singularHomologyComplSingletonFinrankIso (ModuleCat.of k k) (chartAt F r₁)
        (mem_chart_source F r₁)).symm inferInstance
  have hw := span_homologyMap_cubicalHomologyKunnethPair_tmul_eq_top (X := X₁) (Y := X₂)
    (mem_range_self r₁) (mem_range_self r₂) hX _ _ hμ₁ hμ₂
  simp only [Iso.inv_hom_id_apply] at hw
  exact hw

/-- **The cross product of classes generating at interior points, carried along a face map,
generates.** Let `j₁ : N₁ → X₁` and `j₂ : N₂ → X₂` be open embeddings into `T₁` spaces, with
`N₁` a manifold of dimension `p`, and let `μ₁ ∈ Hₚ(X₁, X₁ ∖ j₁(N₁); k)` and
`μ₂ ∈ H_q(X₂, X₂ ∖ j₂(N₂); k)` be relative cubical classes generating the local homology at
`j₁ r.1` and at `j₂ r.2`. Let `g : X₁ × X₂ → Y` be a face map into a `T₁` space, an open embedding
on `N₁ × N₂`, sending the boundary `∂X₁ × X₂ ∪ X₁ × ∂X₂` off `a = g (j₁ r.1, j₂ r.2)`. Then the
cross product `μ₁ × μ₂`, carried by `g` to the local cubical homology `Hₚ₊_q(Y, Y ∖ {a}; k)`,
generates it. -/
theorem span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top
    [T1Space X₁] [T1Space X₂] [T1Space Y]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F N₁] (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) {p q n : ℕ}
    (hp : finrank ℝ F = p) (hpq : p + q = n)
    (μ₁ : ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplex k).homology p)
    (μ₂ : ((TopPair.ofSubset (range j₂)ᶜ).cubicalChainComplex k).homology q)
    (g : C(X₁ × X₂, Y)) (hg : IsOpenEmbedding fun r : N₁ × N₂ ↦ g (j₁ r.1, j₂ r.2))
    (r : N₁ × N₂)
    (hμ₁ : (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r.1)) p
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j₁)ᶜ) p).inv.hom μ₁)) = ⊤)
    (hμ₂ : (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r.2)) q
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j₂)ᶜ) q).inv.hom μ₂)) = ⊤)
    (h : MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range j₁)ᶜ).fst ⊗
        (TopPair.ofSubset (range j₂)ᶜ).fst)) g)
      ((TopPair.ofSubset (range j₁)ᶜ).prodSubspace (TopPair.ofSubset (range j₂)ᶜ))
      {g (j₁ r.1, j₂ r.2)}ᶜ) :
    (k ∙ (homologyMap (cubicalChainComplexMap k (ofSubsetMap _ h)) n).hom
      ((homologyMap ((TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplexProdComparison k
        (TopPair.ofSubset (range j₂)ᶜ)) n).hom
        ((GradedObject.Monoidal.ιTensorObj _ _ p q n hpq ≫
          cubicalHomologyKunnethPair k _ _ n).hom (μ₁ ⊗ₜ μ₂)))) = ⊤ := by
  subst hpq hp
  set x := j₁ r.1
  set y := j₂ r.2
  -- The face map as a morphism out of `X₁ ⊗ X₂`, the ambient space of the product pairs.
  let gt : X₁ ⊗ X₂ ⟶ TopCat.of Y := TopCat.ofHom g
  -- The face map carries every point other than `(x, y)` off `g (x, y)`.
  have h' : MapsTo gt (CartesianMonoidalCategory.fst X₁ X₂ ⁻¹' ({x}ᶜ : Set X₁) ∪
      CartesianMonoidalCategory.snd X₁ X₂ ⁻¹' ({y}ᶜ : Set X₂)) {g (x, y)}ᶜ :=
    mapsTo_compl_singleton_of_mapsTo_prodSubspace gt hg.injective r h
  have hx : MapsTo (𝟙 X₁) (range j₁)ᶜ ({x}ᶜ : Set X₁) :=
    compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self r.1))
  have hy : MapsTo (𝟙 X₂) (range j₂)ᶜ ({y}ᶜ : Set X₂) :=
    compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self r.2))
  -- On chains, the face map factors through the product of the local pairs at `x` and `y`.
  have key : (TopPair.ofSubset (range j₁)ᶜ).cubicalChainComplexProdComparison k
      (TopPair.ofSubset (range j₂)ᶜ) ≫ cubicalChainComplexMap k (ofSubsetMap _ h) ≫
      cubicalToSingularRel k (TopPair.ofSubset (X := TopCat.of Y) {g (x, y)}ᶜ) =
      cubicalChainComplexProdMap k _ _ (ofSubsetMap (𝟙 X₁) hx) (ofSubsetMap (𝟙 X₂) hy) ≫
        cubicalChainComplexProdToSingular k ({x}ᶜ : Set X₁) ({y}ᶜ : Set X₂) ≫
          TopPair.singularChainComplexMap (ofSubsetMap (X := X₁ ⊗ X₂) _ h') (ModuleCat.of k k) := by
    refine coequalizer.hom_ext ?_
    rw [π_cubicalChainComplexProdComparison_assoc, ← Category.assoc, ← cubicalChainComplexMap_comp,
      cubicalToSingularRel_naturality, π_cubicalChainComplexProdMap_assoc,
      π_cubicalChainComplexProdToSingular_assoc, cubicalToSingularRel_naturality_assoc,
      ← singularChainComplexMap_comp, ← singularChainComplexMap_comp]
    refine congrArg (_ ≫ singularChainComplexMap · _) (hom_ext_of_fst _ ?_)
    -- `prodLeftMap_fst` must fire before `ofSubsetMap_fst` rewrites its argument.
    simp only [Hom.fst_comp, prodLeftToProdSubspace_fst, prodLeftMap_fst,
      prodLeftToPreimageUnion_fst]
    simp only [ofSubsetMap_fst]
    ext; rfl
  -- The cross product restricts to a generator of the local homology of the product at `(x, y)`.
  have hw := span_homologyMap_cubicalHomologyKunnethPair_eq_top_of_isOpenEmbedding hj₁ μ₁ μ₂ r.1 r.2
    hμ₁ hμ₂
  -- The face map is an isomorphism from the local homology at `(x, y)` to that at `g (x, y)`.
  have hG := isIso_singularHomologyMap_ofSubsetMap_preimage_union (k := k) hj₁ hj₂ gt hg r h'
    (finrank ℝ F + q)
  refine (ModuleCat.span_singleton_apply_eq_top_iff (TopPair.singularCubicalHomologyIso k
    (TopPair.ofSubset (X := TopCat.of Y) {g (x, y)}ᶜ) (finrank ℝ F + q)).inv).1 ?_
  convert (ModuleCat.span_singleton_apply_eq_top_iff
    (TopPair.singularHomologyMap (ofSubsetMap (X := X₁ ⊗ X₂) _ h') (ModuleCat.of k k) _)).2 hw
    using 3
  have hkey₀ := congrArg (homologyMap · (finrank ℝ F + q)) key
  simp only [homologyMap_comp] at hkey₀
  have hkey := congrArg (fun f ↦ f.hom ((GradedObject.Monoidal.ιTensorObj _ _ _ q _ rfl ≫
    cubicalHomologyKunnethPair k _ _ _).hom (μ₁ ⊗ₜ μ₂))) hkey₀
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hkey
  rw [TopPair.singularCubicalHomologyIso_inv]
  convert hkey using 3

variable {P : Type*} [Fintype P] {ind : P → ℤ} {M : P → P → TopCat.{u}}
  {ι : ∀ x y z, C(M x y × M y z, M x z)}

/-- **Representing chain systems of fundamental classes when `1` is the only unit.** Let `k` be a
commutative ring whose only unit is `1`, such as `ZMod 2`. Suppose that:

* each `M x y` is a compact Hausdorff space containing an open subset `j x y (N x y)`, a copy of
  `N x y`, whose complement is the boundary `∂ M x y`; when `ind y < ind x`, `N x y` is a manifold
  of dimension `ind x - ind y - 1`, and when `ind y + 1 < ind x`, `∂ M x y` is collared and a
  manifold of dimension `ind x - ind y - 2`;
* when `ind y < ind x`, `μ x y ∈ H(M x y, ∂ M x y; k)` generates the local homology at every
  interior point, as the fundamental class relative to the boundary does;
* the composition maps `ι x z y : M x z × M z y → M x y` are associative, land in `∂ M x y`, and are
  open embeddings into `∂ M x y` on the interiors `N x z × N z y`;
* the images of these interiors, the interiors of the faces, are together dense in `∂ M x y`, the
  face of every other `z'` misses the interior of the face of `z`, and `ι x z y` carries the
  boundary `∂ M x z × M z y ∪ M x z × ∂ M z y` of the product off the interior of its face.

Then some twisting chain system represents the classes `μ`. For the compactified trajectory
spaces of a Morse function this is the existence of representing chain systems over `ℤ/2`
(Barraud–Cornea, Lemma 2.2; BDHO, Proposition 5.2.6). -/
theorem TwistingChainSystem.exists_isRepresenting_of_subsingleton_units [Subsingleton kˣ]
    [∀ x y, T2Space (M x y)] [∀ x y, CompactSpace (M x y)]
    {N : P → P → Type u} [∀ x y, TopologicalSpace (N x y)] {j : ∀ x y, N x y → M x y}
    (hj : ∀ x y, IsOpenEmbedding (j x y))
    {F : P → P → Type u} [∀ x y, NormedAddCommGroup (F x y)] [∀ x y, NormedSpace ℝ (F x y)]
    [∀ x y, FiniteDimensional ℝ (F x y)] [∀ x y, ChartedSpace (F x y) (N x y)]
    (hF : ∀ x y, ind y < ind x → finrank ℝ (F x y) = (ind x - ind y - 1).toNat)
    {E : P → P → Type u} [∀ x y, NormedAddCommGroup (E x y)] [∀ x y, NormedSpace ℝ (E x y)]
    [∀ x y, FiniteDimensional ℝ (E x y)] [∀ x y, ChartedSpace (E x y) ↥(range (j x y))ᶜ]
    (hE : ∀ x y, ind y + 1 < ind x → finrank ℝ (E x y) = (ind x - ind y - 2).toNat)
    (hcol : ∀ x y, ind y + 1 < ind x → IsCollared (Subtype.val : ↥(range (j x y))ᶜ → M x y))
    {μ : ∀ x y, ((TopPair.ofSubset (range (j x y))ᶜ).cubicalChainComplex k).homology
      (ind x - ind y - 1).toNat}
    (hμ : ∀ x y, ind y < ind x → ∀ r : N x y, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) _
        ((TopPair.singularCubicalHomologyIso k _ _).inv.hom (μ x y))) = ⊤)
    (hι : ∀ x w z y (a : M x w) (b : M w z) (c : M z y),
      ι x z y (ι x w z (a, b), c) = ι x w y (a, ι w z y (b, c)))
    (hιA : ∀ x z y, ind y < ind z → ind z < ind x → ∀ p, ι x z y p ∈ (range (j x y))ᶜ)
    (hιj : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      IsOpenEmbedding fun r : N x z × N z y ↦
        (ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx) (j x z r.1, j z y r.2))
    (hU : ∀ x y, ind y + 1 < ind x → Dense {a : ↥(range (j x y))ᶜ | ∃ z, ind y < ind z ∧
      ind z < ind x ∧ (a : M x y) ∈ range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)})
    (hUι : ∀ x z z' y, ind y < ind z' → ind z' < ind x → z' ≠ z →
      Disjoint (range (ι x z' y)) (range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)))
    (hUA : ∀ x z y (hyz : ind y < ind z) (hzx : ind z < ind x),
      MapsTo (TopCat.ofHom (X := ↑((TopPair.ofSubset (range (j x z))ᶜ).fst ⊗
          (TopPair.ofSubset (range (j z y))ᶜ).fst))
          ((ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx)))
        ((TopPair.ofSubset (range (j x z))ᶜ).prodSubspace (TopPair.ofSubset (range (j z y))ᶜ))
        (Subtype.val ⁻¹' range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2))ᶜ) :
    ∃ S : TwistingChainSystem ind ι k, S.IsRepresenting (fun x y ↦ (range (j x y))ᶜ) μ := by
  have (x y : P) : CompactSpace ↥(range (j x y))ᶜ :=
    isCompact_iff_compactSpace.1 (hj x y).isOpen_range.isClosed_compl.isCompact
  refine TwistingChainSystem.exists_isRepresenting_of_faces (E := E) hE hι hιA
    (fun x z y ↦ range fun r : N x z × N z y ↦ ι x z y (j x z r.1, j z y r.2)) hU hUι hUA
    fun x z y hyz hzx a ha ↦ ?_
  obtain ⟨r, hr⟩ := ha
  obtain rfl : a = (ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx)
      (j x z r.1, j z y r.2) :=
    Subtype.ext (hr.symm.trans (ContinuousMap.coe_codRestrict_apply _ _ _ _).symm)
  -- Both sides generate the local homology of the boundary at `a`, which has a single generator.
  have hneg : ∀ v : ((TopPair.ofSubset (X := TopCat.of ↥(range (j x y))ᶜ)
      {(ι x z y).codRestrict (range (j x y))ᶜ (hιA x z y hyz hzx) (j x z r.1, j z y r.2)}ᶜ
      ).cubicalChainComplex k).homology (ind x - ind y - 2).toNat,
      (ind x - ind z).negOnePow • v = v := by
    intro v
    have h1 : (-1 : k) = 1 := congrArg Units.val (Subsingleton.elim (-1 : kˣ) 1)
    rcases Int.units_eq_one_or (ind x - ind z).negOnePow with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, ← neg_one_smul k v, h1, one_smul]
  rw [hneg]
  exact eq_of_span_cubicalHomology_eq_top (hE x y (by omega)) _
    (span_homologyMap_cubicalChainComplexMap_cubicalHomologyKunnethPair_eq_top (hj x z) (hj z y)
      (hF x z hzx) (by omega) (μ x z) (μ z y) _ (hιj x z y hyz hzx) r (hμ x z hzx r.1)
      (hμ z y hyz r.2) _)
    (span_homologyMap_cubicalHomologyδ_eq_top (hcol x y (by omega)) (by omega) (μ x y)
      (hμ x y (by omega)) _)

end TauCeti
