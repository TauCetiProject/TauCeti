/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Biprod
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative

/-!
# Mayer–Vietoris connecting morphisms and cup products

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`, and let `A ⊆ U` and `B ⊆ V` be
subsets with `A` and `B` open in `A ∪ B`. Singular cohomology has two Mayer–Vietoris connecting
morphisms here: the absolute one `δ : Hᵖ(U ∩ V) ⟶ Hᵖ⁺¹(X)` of the cover `{U, V}`
(`TopCat.singularCohomologyMayerVietorisδ`), and the one
`δ : Hⁿ(U ∩ V, A ∩ B) ⟶ Hⁿ⁺¹(U ∪ V, A ∪ B)` of the pairs `(U, A)` and `(V, B)`
(`TopCat.singularCohomologyPairMayerVietorisδ`). This file proves that cupping with a relative
class `b ∈ H^q(U ∪ V, A ∪ B)` intertwines them: for `a ∈ Hᵖ(U ∩ V)`,

`δ (a ⌣ b|_{(U ∩ V, A ∩ B)}) = δ a ⌣ b`

(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`), where `⌣` is the cup product of
absolute and relative cohomology `TopPair.singularCup` and `δ a` is restricted from `X` to
`U ∪ V`. There is no sign, since `a` stands to the left of `b`.

The proof is the usual diagram chase. Represent `a` by a cocycle `α` on `U ∩ V` and `δ a` by a
cocycle `ζ` on `X`. Since restricting cochains of `X` to the singular simplices lying in `U` or in
`V` is an isomorphism on cohomology, `α` lifts to a pair of cochains `(y_U, y_V)` on `U` and `V`
whose coboundary is the restriction of `ζ`, on the nose
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_d_eq_of_δ_eq`). Representing `b` by a
cocycle `β`, the pair `(y_U ⌣ β|_{(U, A)}, y_V ⌣ β|_{(V, B)})` lifts `α ⌣ β|_{(U ∩ V, A ∩ B)}` in
the relative Mayer–Vietoris sequence, and by the Leibniz rule its coboundary is the restriction
of `ζ ⌣ β` to the singular simplices lying in `U` or in `V`. So the connecting morphism of the
pairs sends the class of `α ⌣ β|` to that of `ζ ⌣ β`. All cup products in the chase are taken on
pairs of spaces, along the Alexander–Whitney diagonal, so no cup product on the small chains is
needed.

For the Thom pairs of a vector bundle restricted to two open sets of the base, and `b` a Thom
class, this is the compatibility of the Thom map `a ↦ π^*a ⌣ u` with the Mayer–Vietoris
sequences, which the proof that it is an isomorphism by induction over trivializing open sets
uses.

## Main results

* `TopCat.singularCohomologyPairMayerVietorisδ_singularCup`: the connecting morphism of the
  Mayer–Vietoris sequence of two pairs, applied to `a ⌣ b|`, is `δ a ⌣ b`.
* `TopCat.interToUnionMap`: the map of pairs `(U ∩ V, A ∩ B) ⟶ (U ∪ V, A ∪ B)` along which `b`
  is restricted.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (the Mayer–Vietoris sequences in cohomology) and Section 3.2 (cup products).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open TauCeti.ChainComplex (cupCochain cupCycles iCycles_cupCycles d_comp_cupCochain
  iCycles_cyclesMap_linearYonedaFunctor_map_apply d_comp_linearYonedaObj_iCycles)

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}


namespace TopCat

attribute [local instance] TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_left
  TopPair.mono_toSSetPair_map_ofInclusionMap_inclusion_right

/-! ### The connecting morphism and the cup product -/

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X : TopCat.{w}}
  {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
  {A B : Set X} (hAU : A ⊆ U) (hBV : B ⊆ V)
  (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))

/-- The map of pairs `(U ∩ V, A ∩ B) ⟶ (U ∪ V, A ∪ B)` induced by the inclusion. -/
abbrev interToUnionMap :
    TopPair.ofInclusion (Set.inter_subset_inter hAU hBV) ⟶
      TopPair.ofInclusion (Set.union_subset_union hAU hBV) :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion (Set.inter_subset_left.trans
    Set.subset_union_left)) fun _ hx ↦ Set.subset_union_left hx.1

/-- The map of pairs `(U ∩ V, A ∩ B) ⟶ (U, A)` induced by the inclusion. -/
private abbrev interToLeftMap :
    TopPair.ofInclusion (Set.inter_subset_inter hAU hBV) ⟶ TopPair.ofInclusion hAU :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion Set.inter_subset_left)
    fun _ hx ↦ Set.inter_subset_left hx

/-- The map of pairs `(U ∩ V, A ∩ B) ⟶ (V, B)` induced by the inclusion. -/
private abbrev interToRightMap :
    TopPair.ofInclusion (Set.inter_subset_inter hAU hBV) ⟶ TopPair.ofInclusion hBV :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion Set.inter_subset_right)
    fun _ hx ↦ Set.inter_subset_right hx

/-- The map of pairs `(U, A) ⟶ (U ∪ V, A ∪ B)` induced by the inclusion. -/
private abbrev leftToUnionMap :
    TopPair.ofInclusion hAU ⟶ TopPair.ofInclusion (Set.union_subset_union hAU hBV) :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion Set.subset_union_left)
    fun _ hx ↦ Set.subset_union_left hx

/-- The map of pairs `(V, B) ⟶ (U ∪ V, A ∪ B)` induced by the inclusion. -/
private abbrev rightToUnionMap :
    TopPair.ofInclusion hBV ⟶ TopPair.ofInclusion (Set.union_subset_union hAU hBV) :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion Set.subset_union_right)
    fun _ hx ↦ Set.subset_union_right hx

/-- The pair `(U ∩ V, A ∩ B)`. -/
private abbrev interPair : TopPair.{w} := TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)

/-- The pair `(U ∪ V, A ∪ B)`. -/
private abbrev unionPair : TopPair.{w} := TopPair.ofInclusion (Set.union_subset_union hAU hBV)

/-- Restricting the cup lift from a member of the cover to the intersection uses the
same restricted relative cocycle on both members. -/
private lemma cupLift_restrict_component {W D : Set X} (hDW : D ⊆ W)
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (f : interPair hAU hBV ⟶ TopPair.ofInclusion hDW)
    (g : TopPair.ofInclusion hDW ⟶ unionPair hAU hBV)
    (hfg : f ≫ g = interToUnionMap hAU hBV) {p q n : ℕ} (h : p + q = n)
    (φ : ((toSSet.obj (of ↥W)).chainComplex R).X p ⟶ M)
    (ψ : ((unionPair hAU hBV).singularChainComplex S).X q ⟶ N) :
    (TopPair.singularChainComplexMap f T).f n ≫
        cupCochain k ((TopPair.ofInclusion hDW).rightAlexanderWhitneyDiagonal u) μ p q n h
          φ ((TopPair.singularChainComplexMap g S).f q ≫ ψ) =
      cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q n h
        ((SSet.chainComplexMap (toSSet.map (TopPair.Hom.fst f)) R).f p ≫ φ)
        ((TopPair.singularChainComplexMap (interToUnionMap hAU hBV) S).f q ≫ ψ) :=
  (TopPair.singularChainComplexMap_f_cupCochain_rightAlexanderWhitneyDiagonal (k := k)
    f u μ p q n h _ _).trans (congrArg
      (cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q n h _)
      (by rw [← Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
        ← Functor.map_comp, hfg]))

/-- Restricting the cup cochain from the union through the small pair to any cover member
is the cup of the two ordinary restrictions. -/
private lemma cupLift_union_component {W D : Set X} (hDW : D ⊆ W) {i : Fin 2}
    (hWi : W ⊆ ![U, V] i) (hDi : D ⊆ ![A, B] i)
    (hW : W ⊆ U ∪ V) (hD : D ⊆ A ∪ B)
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q n : ℕ} (h : p + q = n)
    (z : ((toSSet.obj X).chainComplex R).X p ⟶ M)
    (ψ : ((unionPair hAU hBV).singularChainComplex S).X q ⟶ N) :
    (SSetPair.chainComplexMap (toSmallSingularPair hAU hBV hDW hWi hDi) T).f n ≫
        (SSetPair.chainComplexMap (smallSingularPairToUnion hAU hBV) T).f n ≫
          cupCochain k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q n h
            ((SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) R).f p ≫
              z) ψ =
      cupCochain k ((TopPair.ofInclusion hDW).rightAlexanderWhitneyDiagonal u) μ p q n h
        ((SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) R).f p ≫ z)
        ((TopPair.singularChainComplexMap (TopPair.ofInclusionMap hDW
          (Set.union_subset_union hAU hBV) (ContinuousMap.inclusion hW)
            (fun _ hx ↦ hD hx)) S).f q ≫ ψ) := by
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp,
    toSmallSingularPair_comp_smallSingularPairToUnion hAU hBV hDW hWi hDi hW hD]
  refine (TopPair.singularChainComplexMap_f_cupCochain_rightAlexanderWhitneyDiagonal (k := k)
    _ u μ p q n h _ _).trans (congrArg
      (fun a ↦ cupCochain k ((TopPair.ofInclusion hDW).rightAlexanderWhitneyDiagonal u)
        μ p q n h a _) ?_)
  refine chainComplexMap_f_comp_subtypeVal _ ?_ _ z
  exact fun x ↦ congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
/-- The coboundary of a component of the absolute lift restricts its coboundary class.
Only the projection of the actual Mayer–Vietoris lift is used. -/
private lemma cupLift_component_d {W : Set X} {i : Fin 2} (hWi : W ⊆ ![U, V] i)
    {p : ℕ} (x₂ : ((of ↥U).singularCochainComplex R k M ⊞
      (of ↥V).singularCochainComplex R k M).X p)
    (π : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      (of ↥W).singularCochainComplex R k M)
    (z : ((toSSet.obj X).chainComplex R).X (p + 1) ⟶ M)
    (hd : ((of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M).d p
      (p + 1) x₂ = ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).f.f (p + 1))
          ((SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R).f (p + 1) ≫ z))
    (hπ : (SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).f ≫ π =
      SSet.cochainComplexMap (toSmallSingularSubcomplex ![U, V] hWi)) :
    ((toSSet.obj (of ↥W)).chainComplex R).d (p + 1) p ≫ π.f p x₂ =
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) R).f (p + 1) ≫ z := by
  refine (HomologicalComplex.Hom.comm_apply π p (p + 1) x₂).trans
    ((congrArg (π.f _) hd).trans ?_)
  refine ((ModuleCat.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.f (p + 1)) hπ) _)).trans ?_
  exact (SSet.cochainComplexMap_f_apply _ _ _).trans
    (chainComplexMap_f_toSmallSingularSubcomplex_comp _ _ _ _)

/-- For a relative cocycle, the coboundary of the cupped lift component is the restriction of
`ζ ⌣ β`; the formula is uniform over the two cover members. -/
private lemma cupLift_component_coboundary {W D : Set X} (hDW : D ⊆ W) {i : Fin 2}
    (hWi : W ⊆ ![U, V] i) (hDi : D ⊆ ![A, B] i)
    (hW : W ⊆ U ∪ V) (hD : D ⊆ A ∪ B)
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q : ℕ} (h : p + 1 + q = p + q + 1)
    (φ : ((toSSet.obj (of ↥W)).chainComplex R).X p ⟶ M)
    (z : ((toSSet.obj X).chainComplex R).X (p + 1) ⟶ M)
    (ψ : ((unionPair hAU hBV).singularChainComplex S).X q ⟶ N)
    (hψ : ((unionPair hAU hBV).singularChainComplex S).d (q + 1) q ≫ ψ = 0)
    (hφ : ((toSSet.obj (of ↥W)).chainComplex R).d (p + 1) p ≫ φ =
      (SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal W))) R).f (p + 1) ≫ z) :
    (SSetPair.chainComplexMap (toSmallSingularPair hAU hBV hDW hWi hDi) T).f (p + q + 1) ≫
        (SSetPair.chainComplexMap (smallSingularPairToUnion hAU hBV) T).f (p + q + 1) ≫
          cupCochain k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ
            (p + 1) q (p + q + 1) h
            ((SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) R).f
              (p + 1) ≫ z) ψ =
      ((TopPair.ofInclusion hDW).singularChainComplex T).d (p + q + 1) (p + q) ≫
        cupCochain k ((TopPair.ofInclusion hDW).rightAlexanderWhitneyDiagonal u) μ p q (p + q)
          rfl φ ((TopPair.singularChainComplexMap (TopPair.ofInclusionMap hDW
            (Set.union_subset_union hAU hBV) (ContinuousMap.inclusion hW)
              (fun _ hx ↦ hD hx)) S).f q ≫ ψ) := by
  rw [cupLift_union_component k hAU hBV hDW hWi hDi hW hD u μ h]
  symm
  refine (TopPair.d_comp_cupCochain_rightAlexanderWhitneyDiagonal (n := p + q)
    (TopPair.ofInclusion hDW) u μ rfl h φ _ ?_).trans (congrArg
      (fun a ↦ cupCochain k ((TopPair.ofInclusion hDW).rightAlexanderWhitneyDiagonal u)
        μ (p + 1) q (p + q + 1) h a _) hφ)
  rw [← Category.assoc, ← HomologicalComplex.Hom.comm, Category.assoc, hψ, Limits.comp_zero]

/-- The cup product of the restricted absolute cocycle `ζ` with the relative cocycle `β`, restricted
to the small singular pair, is the restriction of the cup product of the underlying cochains. -/
private lemma cupLift_iCycles_cyclesMap (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q : ℕ}
    (h' : p + 1 + q = p + q + 1) (ζ : (singularCochainComplex R k M X).cycles (p + 1))
    (β : ((unionPair hAU hBV).singularCochainComplex S k N).cycles q) :
    ((SSetPair.mayerVietorisCochainShortComplex T k L
      (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).X₁.iCycles (p + q + 1)).hom
      (cyclesMap (SSetPair.cochainComplexMap (smallSingularPairToUnion hAU hBV)) (p + q + 1)
        (cupCycles k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u)
          μ (p + 1) q (p + q + 1) h' (cyclesMap (singularCochainComplexMap
            (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) (p + 1) ζ) β)) =
      (SSetPair.chainComplexMap (smallSingularPairToUnion hAU hBV) T).f (p + q + 1) ≫
        cupCochain k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ
          (p + 1) q (p + q + 1) h'
          ((SSet.chainComplexMap (toSSet.map (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) R).f
            (p + 1) ≫ (X.singularCochainComplex R k M).iCycles (p + 1) ζ)
          (((unionPair hAU hBV).singularCochainComplex S k N).iCycles q β) :=
  (iCycles_cyclesMap_linearYonedaFunctor_map_apply _ _ _).trans (congrArg (_ ≫ ·)
    ((iCycles_cupCycles _ _ _ _ _ _ _ _).trans (congrArg (fun a ↦ cupCochain k
      ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal
        u) μ (p + 1) q (p + q + 1) h' a _)
          (iCycles_cyclesMap_linearYonedaFunctor_map_apply _ _ _))))

/-- The lift of `α ⌣ β|` in the Mayer–Vietoris sequence of the pairs: the pair of cups of the
components `y_U`, `y_V` of a lift `x₂` of `α` with the restrictions of the relative cocycle `β`
maps to the cup product of `α` with the restriction of `β` to `(U ∩ V, A ∩ B)`. -/
private lemma cupLift_g_eq (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q : ℕ}
    (x₂ : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₂.X p))
    (α : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₃.cycles p))
    (β : ((unionPair hAU hBV).singularCochainComplex S k N).cycles q)
    (hg : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).g.f p).hom x₂ =
      ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₃.iCycles p).hom α) :
    ((SSetPair.mayerVietorisCochainShortComplex T k L
        (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).g.f (p + q)).hom
      (((biprod.inl : (TopPair.ofInclusion hAU).singularCochainComplex T k L ⟶
        _ ⊞ (TopPair.ofInclusion hBV).singularCochainComplex T k L).f (p + q)).hom
        (cupCochain k ((TopPair.ofInclusion hAU).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl
            (((biprod.fst : (of ↥U).singularCochainComplex R k M ⊞
              (of ↥V).singularCochainComplex R k M ⟶ _).f p).hom x₂)
            ((TopPair.singularChainComplexMap (leftToUnionMap hAU hBV) S).f q ≫
              (((unionPair hAU hBV).singularCochainComplex S k N).iCycles q β))) +
       ((biprod.inr : (TopPair.ofInclusion hBV).singularCochainComplex T k L ⟶
        (TopPair.ofInclusion hAU).singularCochainComplex T k L ⊞ _).f (p + q)).hom
        (cupCochain k ((TopPair.ofInclusion hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl
            (((biprod.snd : (of ↥U).singularCochainComplex R k M ⊞
              (of ↥V).singularCochainComplex R k M ⟶ _).f p).hom x₂)
            ((TopPair.singularChainComplexMap (rightToUnionMap hAU hBV) S).f q ≫
              (((unionPair hAU hBV).singularCochainComplex S k N).iCycles q β)))) =
      ((SSetPair.mayerVietorisCochainShortComplex T k L
        (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).X₃.iCycles (p + q)).hom
        (cupCycles k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl α
          (cyclesMap (TopPair.singularCochainComplexMap (interToUnionMap hAU hBV)) q β)) := by
  -- Names for the cochains in the chase, as morphisms of `C`.
  set yU : ((toSSet.obj (of ↥U)).chainComplex R).X p ⟶ M :=
    ((biprod.fst : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyU
  set yV : ((toSSet.obj (of ↥V)).chainComplex R).X p ⟶ M :=
    ((biprod.snd : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyV
  set b' : ((unionPair hAU hBV).singularChainComplex S).X q ⟶
    N := ((unionPair hAU hBV).singularCochainComplex
      S k N).iCycles q β with hb'
  have hgx := hg
  rw [HomologicalComplex.biprod_desc_f_apply, HomologicalComplex.neg_f_apply, ModuleCat.hom_neg,
    LinearMap.neg_apply] at hgx
  -- Restricting the components of the lift to `(U ∩ V, A ∩ B)`.
  have eU := cupLift_restrict_component k hAU hBV _ u μ (interToLeftMap hAU hBV)
    (leftToUnionMap hAU hBV) (by rw [← TopPair.ofInclusionMap_comp]; congr 1) rfl yU b'
  have eV := cupLift_restrict_component k hAU hBV _ u μ (interToRightMap hAU hBV)
    (rightToUnionMap hAU hBV) (by rw [← TopPair.ofInclusionMap_comp]; congr 1) rfl yV b'
  -- Cupping is linear in its first argument.
  have hlin : ∀ (a₁ a₂ : ((toSSet.obj (TopPair.ofInclusion
      (Set.inter_subset_inter hAU hBV)).fst).chainComplex R).X p ⟶ M)
      (c : ((interPair hAU hBV).singularChainComplex S).X q ⟶
        N),
      cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl a₁ c +
        -(cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl a₂
          c) =
        cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl
          (a₁ + -a₂) c := fun a₁ a₂ c ↦ by
    rw [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply]
  refine (map_add _ _ _).trans ?_
  refine (congrArg₂ (· + ·) ((ModuleCat.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (HomologicalComplex.biprod_inl_desc_f _ _ _) _))
    ((ModuleCat.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (HomologicalComplex.biprod_inr_desc_f _ _ _) _))).trans ?_
  refine (congrArg₂ (· + ·) eU (Eq.trans (by
    -- Negation in the linear-Yoneda cochain module is pointwise negation of morphisms of C.
    rw [HomologicalComplex.neg_f_apply]
    rfl)
    (congrArg Neg.neg eV))).trans ?_
  refine (hlin _ _ _).trans (Eq.trans ?_
    ((congrArg (fun a ↦ cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q
      (p + q) rfl a ((TopPair.singularChainComplexMap (interToUnionMap hAU hBV) S).f q ≫ b'))
        hgx).trans ?_))
  · exact congrArg (fun a ↦ cupCochain k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p
      q (p + q) rfl a ((TopPair.singularChainComplexMap (interToUnionMap hAU hBV) S).f q ≫ b'))
      (congrArg₂ (fun f g ↦ (SSet.chainComplexMap f R).f p ≫ yU +
        -((SSet.chainComplexMap g R).f p ≫ yV))
        (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _)
        (TopPair.toSSetPair_map_ofInclusionMap_inclusion_right _ _ _ _))
  · exact ((iCycles_cupCycles _ _ _ _ _ _ _ _).trans
      (congrArg _ (iCycles_cyclesMap_linearYonedaFunctor_map_apply _ _ _))).symm

/-- The coboundary of the lift of `α ⌣ β|` is the restriction of `ζ ⌣ β` from `(U ∪ V, A ∪ B)` to
the small singular pair: the components over `U` and over `V` are given by the uniform formula
`cupLift_component_coboundary`. -/
private lemma cupLift_d_eq (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q : ℕ}
    (h' : p + 1 + q = p + q + 1)
    (x₂ : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₂.X p))
    (ζ : (singularCochainComplex R k M X).cycles (p + 1))
    (β : ((unionPair hAU hBV).singularCochainComplex S k N).cycles q)
    (hd : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₂.d p (p + 1)).hom x₂ =
      ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).f.f (p + 1)).hom
        (((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₁.iCycles (p + 1)).hom
          (cyclesMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
            (X.smallSingularSubcomplex ![U, V]).ι) (p + 1) ζ))) :
    ((SSetPair.mayerVietorisCochainShortComplex T k L
        (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).f.f (p + q + 1)).hom
      (((SSetPair.mayerVietorisCochainShortComplex T k L
        (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).X₁.iCycles (p + q + 1)).hom
        (cyclesMap (SSetPair.cochainComplexMap (smallSingularPairToUnion hAU hBV))
          (p + q + 1)
          (cupCycles k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ (p + 1) q
            (p + q + 1) h'
            (cyclesMap (singularCochainComplexMap
              (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) (p + 1) ζ) β))) =
      ((SSetPair.mayerVietorisCochainShortComplex T k L
        (MorphismProperty.Arrow.Hom.ext (isPushout_toSmallSingularPair_left hAU hBV).w
        (isPushout_toSmallSingularPair_right hAU hBV).w)).X₂.d (p + q) (p + q + 1)).hom
        (((biprod.inl : (TopPair.ofInclusion hAU).singularCochainComplex T k L ⟶
          _ ⊞ (TopPair.ofInclusion hBV).singularCochainComplex T k L).f (p + q)).hom
          (cupCochain k ((TopPair.ofInclusion hAU).rightAlexanderWhitneyDiagonal u) μ p q (p + q)
            rfl
            (((biprod.fst : (of ↥U).singularCochainComplex R k M ⊞
              (of ↥V).singularCochainComplex R k M ⟶ _).f p).hom x₂)
            ((TopPair.singularChainComplexMap (leftToUnionMap hAU hBV) S).f q ≫
              (((unionPair hAU hBV).singularCochainComplex S k N).iCycles q β))) +
         ((biprod.inr : (TopPair.ofInclusion hBV).singularCochainComplex T k L ⟶
          (TopPair.ofInclusion hAU).singularCochainComplex T k L ⊞ _).f (p + q)).hom
          (cupCochain k ((TopPair.ofInclusion hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q)
            rfl
            (((biprod.snd : (of ↥U).singularCochainComplex R k M ⊞
              (of ↥V).singularCochainComplex R k M ⟶ _).f p).hom x₂)
            ((TopPair.singularChainComplexMap (rightToUnionMap hAU hBV) S).f q ≫
              (((unionPair hAU hBV).singularCochainComplex S k N).iCycles q β)))) := by
  -- Names for the cochains in the chase, as morphisms of `C`.
  set yU : ((toSSet.obj (of ↥U)).chainComplex R).X p ⟶ M :=
    ((biprod.fst : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyU
  set yV : ((toSSet.obj (of ↥V)).chainComplex R).X p ⟶ M :=
    ((biprod.snd : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyV
  set b' : ((unionPair hAU hBV).singularChainComplex S).X q ⟶
    N := ((unionPair hAU hBV).singularCochainComplex
      S k N).iCycles q β with hb'
  have hdb : ((unionPair hAU hBV).singularChainComplex S).d
      (q + 1) q ≫ b' = 0 := d_comp_linearYonedaObj_iCycles q (q + 1) β
  refine (HomologicalComplex.biprod_lift_f_apply _ _ _ _).trans (Eq.trans ?_
    ((map_add _ _ _).trans (congrArg₂ (· + ·) (HomologicalComplex.Hom.comm_apply _ _ _ _)
      (HomologicalComplex.Hom.comm_apply _ _ _ _))).symm)
  -- On the restriction of `ζ ⌣ β` from `(U ∪ V, A ∪ B)` to the singular simplices lying in `U`
  -- or in `V`, the absolute class `ζ` restricts to `U ∪ V`.
  have hζβ := cupLift_iCycles_cyclesMap k hAU hBV u μ h' ζ β
  refine congrArg₂ (· + ·) (congrArg _ ?_) (congrArg _ ?_)
  · -- The component over `U` is the generic lift-coboundary formula for index zero.
    have hdy := cupLift_component_d k (U := U) (V := V)
      (W := U) (i := 0) (Matrix.cons_val_zero U ![V]).superset x₂
      (biprod.fst : _ ⟶ (of ↥U).singularCochainComplex R k M)
      ((X.singularCochainComplex R k M).iCycles (p + 1) ζ)
      (hd.trans (congrArg _ (iCycles_cyclesMap_linearYonedaFunctor_map_apply _ _ _)))
      (biprod.lift_fst _ _)
    exact ((congrArg _ hζβ).trans (cupLift_component_coboundary k hAU hBV hAU
      (i := 0) (Matrix.cons_val_zero U ![V]).superset
      (Matrix.cons_val_zero A ![B]).superset Set.subset_union_left Set.subset_union_left
      u μ h' yU _ b' hdb hdy))
  · -- The component over `V` is the same formula for index one.
    have hdy := cupLift_component_d k (U := U) (V := V)
      (W := V) (i := 1) ((Matrix.cons_val_one U ![V]).trans
        (Matrix.cons_val_zero V ![])).superset x₂
      (biprod.snd : _ ⟶ (of ↥V).singularCochainComplex R k M)
      ((X.singularCochainComplex R k M).iCycles (p + 1) ζ)
      (hd.trans (congrArg _ (iCycles_cyclesMap_linearYonedaFunctor_map_apply _ _ _)))
      (biprod.lift_snd _ _)
    exact ((congrArg _ hζβ).trans (cupLift_component_coboundary k hAU hBV hBV
      (i := 1) ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset
      ((Matrix.cons_val_one A ![B]).trans (Matrix.cons_val_zero B ![])).superset
      Set.subset_union_right Set.subset_union_right u μ h' yV _ b' hdb hdy))


/-- The final step of the diagram chase: the connecting morphism of the pairs sends the class of
`α ⌣ β|` to the class of `ζ ⌣ β`, for a lift `x₂` of `α` whose coboundary is the restriction of
`ζ`. -/
private lemma pairMayerVietorisδ_cup_eq (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {p q : ℕ}
    (h' : p + 1 + q = p + q + 1)
    (x₂ : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₂.X p))
    (α : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₃.cycles p))
    (ζ : (singularCochainComplex R k M X).cycles (p + 1))
    (β : ((unionPair hAU hBV).singularCochainComplex S k N).cycles q)
    (hd : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₂.d p (p + 1)).hom x₂ =
      ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).f.f (p + 1)).hom
        (((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₁.iCycles (p + 1)).hom
          (cyclesMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
            (X.smallSingularSubcomplex ![U, V]).ι) (p + 1) ζ)))
    (hg : ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).g.f p).hom x₂ =
      ((SSet.mayerVietorisCochainShortComplex R k M
        (isPushout_toSSet_inter_smallSingularSubcomplex U V).toCommSq).X₃.iCycles p).hom α) :
    (SSetPair.shortExact_mayerVietorisCochainShortComplex T k L
      (isPushout_toSmallSingularPair_left hAU hBV)
      (isPushout_toSmallSingularPair_right hAU hBV)).δ (p + q) (p + q + 1) rfl
      (homologyπ ((interPair hAU hBV).singularCochainComplex T k L) (p + q)
        (cupCycles k ((interPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl α
          (cyclesMap (TopPair.singularCochainComplexMap (interToUnionMap hAU hBV)) q β))) =
      homologyπ (((smallSingularPair hAU hBV).chainComplex T).linearYonedaObj k L) (p + q + 1)
        (cyclesMap (SSetPair.cochainComplexMap (smallSingularPairToUnion hAU hBV)) (p + q + 1)
          (cupCycles k ((unionPair hAU hBV).rightAlexanderWhitneyDiagonal u) μ (p + 1) q
            (p + q + 1) h'
            (cyclesMap (singularCochainComplexMap
              (ofHom (ContinuousMap.subtypeVal (U ∪ V)))) (p + 1) ζ) β)) := by
  -- Names for the cochains in the chase, as morphisms of `C`.
  set yU : ((toSSet.obj (of ↥U)).chainComplex R).X p ⟶ M :=
    ((biprod.fst : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyU
  set yV : ((toSSet.obj (of ↥V)).chainComplex R).X p ⟶ M :=
    ((biprod.snd : (of ↥U).singularCochainComplex R k M ⊞ (of ↥V).singularCochainComplex R k M ⟶
      _).f p).hom x₂ with hyV
  set b' : ((unionPair hAU hBV).singularChainComplex S).X q ⟶
    N := ((unionPair hAU hBV).singularCochainComplex
      S k N).iCycles q β with hb'
  -- The pair sequence: `x₂ ⌣ β|` lifts `α ⌣ β|`, and its coboundary is the restriction of
  -- `ζ ⌣ β`.
  refine (SSetPair.shortExact_mayerVietorisCochainShortComplex T k L
    (isPushout_toSmallSingularPair_left hAU hBV)
    (isPushout_toSmallSingularPair_right hAU hBV)).moduleCat_δ_homologyπ (p + q) (p + q + 1) rfl _
    (((biprod.inl : (TopPair.ofInclusion hAU).singularCochainComplex T k L ⟶
        _ ⊞ (TopPair.ofInclusion hBV).singularCochainComplex T k L).f (p + q)).hom
      (cupCochain k ((TopPair.ofInclusion hAU).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl
        yU ((TopPair.singularChainComplexMap (leftToUnionMap hAU hBV) S).f q ≫ b')) +
     ((biprod.inr : (TopPair.ofInclusion hBV).singularCochainComplex T k L ⟶
        (TopPair.ofInclusion hAU).singularCochainComplex T k L ⊞ _).f (p + q)).hom
      (cupCochain k ((TopPair.ofInclusion hBV).rightAlexanderWhitneyDiagonal u) μ p q (p + q) rfl
        yV ((TopPair.singularChainComplexMap (rightToUnionMap hAU hBV) S).f q ≫ b'))) ?_ _ ?_
  · exact cupLift_g_eq k hAU hBV u μ x₂ α β hg
  · exact cupLift_d_eq k hAU hBV u μ h' x₂ ζ β hd

/-- **The Mayer–Vietoris connecting morphism commutes with cup products.** Let `U` and `V` be open
subsets covering `X`, and let `A ⊆ U` and `B ⊆ V` be open in `A ∪ B`. For `a ∈ Hᵖ(U ∩ V)` and
`b ∈ H^q(U ∪ V, A ∪ B)`, the connecting morphism of the Mayer–Vietoris sequence of the pairs
`(U, A)` and `(V, B)` sends `a ⌣ b|_{(U ∩ V, A ∩ B)}` to `δ a ⌣ b`, where `δ` is the connecting
morphism of the absolute Mayer–Vietoris sequence of the cover `{U, V}` and `δ a` is restricted from
`X` to `U ∪ V`. -/
theorem singularCohomologyPairMayerVietorisδ_singularCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    {p q n p' m : ℕ} (h : p + q = n) (hp : p + 1 = p') (hm : n + 1 = m) (h' : p' + q = m)
    (a : (of ↥(U ∩ V)).singularCohomology R k M p)
    (b : (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCohomology S k N q) :
    singularCohomologyPairMayerVietorisδ T k L hAU hBV
        (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val) hA hB n m hm
        ((TopPair.ofInclusion (Set.inter_subset_inter hAU hBV)).singularCup k u μ p q n h a
          (TopPair.singularCohomologyMap (interToUnionMap hAU hBV) q b)) =
      (TopPair.ofInclusion (Set.union_subset_union hAU hBV)).singularCup k u μ p' q m h'
        (TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal (U ∪ V))) p'
          (singularCohomologyMayerVietorisδ R k M hU hV hUV p p' hp a)) b := by
  subst hp hm h
  obtain ⟨β, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  obtain ⟨ζ, hζ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (p + 1)
    (singularCohomologyMayerVietorisδ R k M hU hV hUV p (p + 1) rfl a)
  -- The absolute sequence: `a` is the class of a cocycle `α` lifting to `x₂`, whose coboundary is
  -- the restriction of `ζ` to the singular simplices lying in `U` or in `V`.
  have hS := SSet.shortExact_mayerVietorisCochainShortComplex R k M
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
  have hδ : (hS.δ p (p + 1) rfl).hom a =
      (((X.smallSingularSubcomplex ![U, V] : SSet).chainComplex R).linearYonedaObj k M).homologyπ
        (p + 1) (cyclesMap (SSet.cochainComplexMap (R := R) (k := k) (M := M)
          (X.smallSingularSubcomplex ![U, V]).ι) (p + 1) ζ) := by
    have := ConcreteCategory.congr_hom
      (singularCohomologyMayerVietorisδ_comp_homologyMap R k M hU hV hUV p (p + 1) rfl) a
    rw [ConcreteCategory.comp_apply, ← hζ, moduleCat_homologyMap_homologyπ,
      SSet.mayerVietorisCochainδ_def R k M
      (isPushout_toSSet_inter_smallSingularSubcomplex U V) p (p + 1) rfl] at this
    exact this.symm
  obtain ⟨x₂, α, hd, hg, rfl⟩ := hS.moduleCat_exists_d_eq_of_δ_eq p (p + 1) rfl a _ hδ
  -- It suffices to compare both sides after restricting to the singular simplices lying in `U` or
  -- in `V`, which is injective on cohomology.
  have hU' : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)) := hU.preimage continuous_subtype_val
  have hV' : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)) := hV.preimage continuous_subtype_val
  have := isIso_homologyMap_cochainComplexMap_smallSingularPairToUnion T k L hAU hBV hU' hV' hA hB
    (p + q + 1)
  apply (ModuleCat.mono_iff_injective (homologyMap (SSetPair.cochainComplexMap (R := T) (k := k)
    (M := L) (smallSingularPairToUnion hAU hBV)) (p + q + 1))).1 inferInstance
  rw [← ConcreteCategory.comp_apply, singularCohomologyPairMayerVietorisδ_comp_homologyMap T k L
      hAU hBV hU' hV' hA hB (p + q) (p + q + 1) rfl,
    SSetPair.mayerVietorisCochainδ_def T k L (isPushout_toSmallSingularPair_left hAU hBV)
      (isPushout_toSmallSingularPair_right hAU hBV) (p + q) (p + q + 1) rfl,
    ← hζ, TopPair.singularCohomologyMap, moduleCat_homologyMap_homologyπ,
    TopCat.singularCohomologyMap, moduleCat_homologyMap_homologyπ]
  -- The pair abbreviations `interPair` and `unionPair` unfold to `ofInclusion`; `erw` also
  -- identifies the native relative chain model with its cochain-complex presentation.
  erw [TopPair.singularCup_homologyπ k (interPair hAU hBV) u μ
      p q (p + q) rfl α,
    TopPair.singularCup_homologyπ k (unionPair hAU hBV) u μ
      (p + 1) q (p + q + 1) h', moduleCat_homologyMap_homologyπ]
  exact pairMayerVietorisδ_cup_eq k hAU hBV u μ h' x₂ α ζ β hd hg
end TopCat
