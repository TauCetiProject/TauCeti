/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Shuffle.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The relative cross product and the relative Künneth theorem for singular homology

Let `X` and `Y` be topological spaces and `B ⊆ X`. The product pair `(X, B) × Y` is
`(X × Y, B × Y)`; here `B × Y` is written as the preimage `fst⁻¹(B)` of `B` under the first
projection, so that the pair is `TopPair.ofSubset (Prod.fst ⁻¹' B)`. The shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` (`TopCat.shuffle`) descends to the **relative shuffle map**
(`TopCat.shuffleRel`)

`C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B); R ⊗ S)`.

The inclusion `C(B; R) ⟶ C(X; R)` splits in each degree, so tensoring on the right with
`C(Y; S)` preserves the short exact sequence `C(B) ⟶ C(X) ⟶ C(X, B)`. The three shuffle maps form
a morphism from this tensored sequence to the sequence of the pair `(X × Y, fst⁻¹(B))`
(`TopCat.shuffleShortComplexMap`). The absolute shuffle maps are quasi-isomorphisms by the
Eilenberg–Zilber theorem, and `B × Y ⟶ fst⁻¹(B)` is a homeomorphism, so by the five lemma the
relative shuffle map is a quasi-isomorphism (`TopCat.quasiIso_shuffleRel`). This is the
**relative Eilenberg–Zilber theorem**, with the pair in the first factor.

On homology this gives the **relative cross product** (`TopCat.singularHomologyCrossRel`)

`Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)`, for `p + q = n`,

which is compatible with the absolute cross product: the image of `a × b` in relative homology
is the relative cross product of the image of `a` with `b`
(`TopCat.singularHomologyCross_comp_singularHomologyπ`). It is also compatible with the
connecting morphisms of the long exact sequences of the pairs: the connecting morphism of
`(X, B) × Y` sends `a × b` to `δ a × b` (`TopCat.singularHomologyCrossRel_comp_singularHomologyδ`),
because the shuffle maps form a morphism of short exact sequences and the connecting morphism of
the tensored sequence is computed by `HomologicalComplex.homologyCross_comp_δ_right`.

The relative Künneth map `⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)`
(`TopCat.singularHomologyKunnethRel`) is an isomorphism exactly when the algebraic Künneth map of
the chain complexes is (`TopCat.isIso_singularHomologyKunnethRel_iff`), for instance over a
commutative semisimple ring such as a field (`TopCat.isIso_singularHomologyKunnethRel`). Whenever
the cycles of the two chain complexes split off their terms, for instance for projective
coefficients over a principal ideal domain, it is a split monomorphism
(`TopCat.isSplitMono_singularHomologyKunnethRel`), so the relative cross product is injective
(`TopCat.mono_singularHomologyCrossRel`).

The chain-level constructions and the relative cross product are stated for coefficients in any
abelian monoidal category with coproducts, as for the absolute Künneth map
(`TopCat.singularHomologyKunneth`); only the splitting results are specific to modules over a
commutative ring.

The pair is written with a subset rather than an arbitrary `TopPair` because relative homology
modulo the complement of a fibre, which this cross product is used to compute, is stated for
pairs of the form `TopPair.ofSubset`.

This adapts the relative cubical cross product `TauCeti.cubicalCrossProductRel`
(`TauCeti/AlgebraicTopology/Singular/Cubical/Kunneth/Relative.lean`), which has the pair in the
second factor, to the simplicial shuffle map, with the pair in the first factor.

## Main definitions

* `TopCat.singularHomologyCrossRel`: the relative cross product in singular homology, and
  `TopCat.singularHomologyCrossRelOfInclusion`: its version for nested subspaces.
* `TopCat.singularHomologyKunnethRel`: the relative Künneth map, and
  `TopCat.singularHomologyKunnethRelIso`: the relative Künneth isomorphism when the cycles and the
  homology split off.

## Main results

* `TopCat.quasiIso_shuffleRel`: the relative Eilenberg–Zilber theorem.
* `TopCat.singularHomologyCrossRel_naturality`: naturality in maps of pairs
  `(X, B) ⟶ (X', B')` and in maps `Y ⟶ Y'`.
* `TopCat.singularHomologyCross_comp_singularHomologyπ`: the absolute cross product followed by
  the map to relative homology is the relative cross product of the image of the first factor.
* `TopCat.singularHomologyCrossRel_comp_singularHomologyδ`: the connecting morphism of the pair
  `(X, B) × Y` on a relative cross product.
* `TopCat.isIso_singularHomologyKunnethRel`: the relative Künneth theorem.
* `TopCat.isSplitMono_singularHomologyKunnethRel`, `TopCat.mono_singularHomologyCrossRel`: the
  relative Künneth map is a split monomorphism, and the relative cross product injective, when the
  cycles split off.
* `TopCat.isIso_singularHomologyCrossRel_of_isZero`: the relative cross product is an isomorphism
  when the cycles and the homology split off and the pair has relative homology in one degree only.
* `TopCat.whiskerRight_singularHomologyπ_comp_singularHomologyCrossRelOfInclusion`,
  `TopCat.singularHomologyCrossRelOfInclusion_comp_singularHomologyδ`,
  `TopCat.whiskerRight_singularHomologyδ_comp_singularHomologyCrossRelOfInclusion`: the relative
  cross product `TopCat.singularHomologyCrossRelOfInclusion` for nested subspaces `s ⊆ t` of `Y`
  and the subspaces of `Y × F` with the points of `s × F` and `t × F`, on absolute classes, and
  under the connecting maps of pairs and of triples.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product and the relative Künneth formula.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

section General

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (B : Set X) (R S : C)

/-- The morphism of short exact sequences from `(C(B) ⟶ C(X) ⟶ C(X, B)) ⊗ C(Y)` to
`C(fst⁻¹(B)) ⟶ C(X × Y) ⟶ C(X × Y, fst⁻¹(B))` given by the shuffle maps, the first one followed
by the map induced by `B × Y ≅ fst⁻¹(B)`. -/
def shuffleShortComplexMap :
    tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
        ((TopPair.ofSubset B).singularChainComplexShortComplex R) ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexShortComplex
        (R ⊗ S) where
  τ₁ := shuffle (TopPair.ofSubset B).snd Y R S ≫
    SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S)
  τ₂ := shuffle X Y R S
  τ₃ := shuffleRel X Y B R S
  comm₁₂ := ((chainComplexMap_tensorHom_id_shuffle X Y B R S).trans
    (Category.assoc _ _ _).symm).symm
  comm₂₃ := (singularChainComplexπ_tensorHom_id_shuffleRel X Y B R S).symm

@[simp]
theorem shuffleShortComplexMap_τ₁ :
    (shuffleShortComplexMap X Y B R S).τ₁ = shuffle (TopPair.ofSubset B).snd Y R S ≫
      SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S) :=
  (rfl)

@[simp]
theorem shuffleShortComplexMap_τ₂ : (shuffleShortComplexMap X Y B R S).τ₂ = shuffle X Y R S :=
  (rfl)

@[simp]
theorem shuffleShortComplexMap_τ₃ :
    (shuffleShortComplexMap X Y B R S).τ₃ = shuffleRel X Y B R S :=
  (rfl)

/-- **The relative Eilenberg–Zilber theorem**: the relative shuffle map
`C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B); R ⊗ S)` is a quasi-isomorphism. By the five lemma, this
follows from the absolute Eilenberg–Zilber theorem for `B × Y` and `X × Y`. -/
instance quasiIso_shuffleRel : QuasiIso (shuffleRel X Y B R S) :=
  HomologySequence.quasiIso_τ₃ (shuffleShortComplexMap X Y B R S)
    (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' B)).shortExact_singularChainComplexShortComplex (R ⊗ S))
    (inferInstanceAs (QuasiIso (shuffle (TopPair.ofSubset B).snd Y R S ≫
      SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S))))
    (inferInstanceAs (QuasiIso (shuffle X Y R S)))

section Cross

variable (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset B).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The relative cross product** `Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` for
`p + q = n`: the cross product of the chain complexes `C(X, B; R)` and `C(Y; S)` followed by the
map induced by the relative shuffle map. -/
def singularHomologyCrossRel :
    (TopPair.ofSubset B).singularHomology R p ⊗ ((singularHomologyFunctor _ q).obj S).obj Y ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
    p q n h ≫ homologyMap (shuffleRel X Y B R S) n

/-- The relative cross product is the cross product of the chain complexes followed by the map
induced by the relative shuffle map. -/
theorem singularHomologyCrossRel_def :
    singularHomologyCrossRel X Y B R S p q n h =
      homologyCross ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
        p q n h ≫ homologyMap (shuffleRel X Y B R S) n :=
  (rfl)

/-- **Naturality of the relative cross product** in maps of pairs `(X, B) ⟶ (X', B')` and in maps
`Y ⟶ Y'`: `f_* a × g_* b = (f × g)_* (a × b)`. -/
@[reassoc]
theorem singularHomologyCrossRel_naturality {X' Y' : TopCat.{w}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset B').singularChainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        ((singularHomologyFunctor _ q).obj S).map g) ≫
          singularHomologyCrossRel X' Y' B' R S p q n h =
      singularHomologyCrossRel X Y B R S p q n h ≫ TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S) n :=
  -- The relative and absolute singular homology maps are by definition the maps induced on the
  -- homology of the singular chain complexes, so the algebraic naturality applies; as above, the
  -- composites are reassociated by hand.
  (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shuffleRel X' Y' B' R S) n)
      (homologyCross_naturality (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R)
        (SSet.chainComplexMap (toSSet.map g) S) p q n h)).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) ((homologyMap_comp _ _ n).symm.trans
      ((congrArg (homologyMap · n) (shuffleRel_naturality X Y B R S f hf g)).trans
        (homologyMap_comp _ _ n)))).trans (Category.assoc _ _ _).symm

/-- **The relative cross product of an absolute class.** Mapping the cross product `a × b` of
`a ∈ Hₚ(X; R)` and `b ∈ H_q(Y; S)` to the relative homology of `(X × Y, fst⁻¹(B))` gives the
relative cross product of the image of `a` in `Hₚ(X, B; R)` with `b`. -/
@[reassoc]
theorem singularHomologyCross_comp_singularHomologyπ
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))] :
    singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n =
      ((TopPair.ofSubset B).singularHomologyπ R p ▷ ((singularHomologyFunctor _ q).obj S).obj Y) ≫
        singularHomologyCrossRel X Y B R S p q n h := by
  -- Naturality of the algebraic cross product along `π ⊗ 𝟙`, and the defining property of the
  -- relative shuffle map; the singular homology maps are by definition maps on homology.
  have hn := homologyCross_naturality (K := (toSSet.obj X).chainComplex R)
    ((TopPair.ofSubset B).singularChainComplexπ R) (𝟙 ((toSSet.obj Y).chainComplex S)) p q n h
  rw [homologyMap_id, tensorHom_id] at hn
  refine (congrArg (· ≫ _) (singularHomologyCross_def X Y R S p q n h)).trans ?_
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (homologyMap_comp _ _ n).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ homologyMap φ n)
      (singularChainComplexπ_tensorHom_id_shuffleRel X Y B R S).symm).trans <|
    (congrArg (_ ≫ ·) (homologyMap_comp _ _ n)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shuffleRel X Y B R S) n) hn.symm).trans (Category.assoc _ _ _)

/-- **The connecting morphism on a relative cross product.** The connecting morphism
`Hₙ(X × Y, fst⁻¹(B)) ⟶ Hₙ₋₁(fst⁻¹(B))` of the pair `(X, B) × Y` sends the relative cross product
`a × b` of `a ∈ Hₚ(X, B; R)` and `b ∈ H_q(Y; S)` to `δ a × b`, where `δ a ∈ Hₚ₋₁(B; R)` is the
connecting morphism of `(X, B)` and `δ a × b ∈ Hₙ₋₁(B × Y; R ⊗ S)` is carried to `fst⁻¹(B)` by
`B × Y ≅ fst⁻¹(B)`. There is no sign, since the pair is the first factor. -/
@[reassoc]
theorem singularHomologyCrossRel_comp_singularHomologyδ {p' n' : ℕ} (hp : p' + 1 = p)
    (h' : p' + q = n')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex R).homology p'))] :
    singularHomologyCrossRel X Y B R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomologyδ (R ⊗ S) n n' (by omega) =
      ((TopPair.ofSubset B).singularHomologyδ R p p' hp ▷
          ((singularHomologyFunctor _ q).obj S).obj Y) ≫
        singularHomologyCross (TopPair.ofSubset B).snd Y R S p' q n' h' ≫
          ((singularHomologyFunctor C n').obj (R ⊗ S)).map (prodPreimageFstIso X Y B).hom := by
  have hS := (TopPair.ofSubset B).shortExact_singularChainComplexShortComplex R
  have hSK := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have hrel : (ComplexShape.down ℕ).Rel p p' := by simp [hp]
  -- the shuffle maps form a morphism of short exact sequences, so they commute with the
  -- connecting morphisms; on the tensored sequence the connecting morphism is computed by
  -- `HomologicalComplex.homologyCross_comp_δ_right`
  have hδ := HomologySequence.δ_naturality (shuffleShortComplexMap X Y B R S) hSK
    ((TopPair.ofSubset (fst X Y ⁻¹' B)).shortExact_singularChainComplexShortComplex (R ⊗ S)) n n'
    (by simp; omega)
  -- the instances on the terms of the short exact sequence, which instance search does not
  -- identify with those on the singular chain complexes
  have : PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset B).singularChainComplexShortComplex R).X₃.homology p)) :=
    ‹PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset B).singularChainComplex R).homology p))›
  have : PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset B).singularChainComplexShortComplex R).X₁.homology p')) :=
    ‹PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj (TopPair.ofSubset B).snd).chainComplex R).homology p'))›
  have hc := homologyCross_comp_δ_right ((toSSet.obj Y).chainComplex S) hS hSK hrel h h'
  have key : homologyMap (shuffleRel X Y B R S) n ≫
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomologyδ (R ⊗ S) n n' (by omega) =
        hSK.δ n n' (by simp; omega) ≫ homologyMap (shuffleShortComplexMap X Y B R S).τ₁ n' :=
    hδ.symm
  rw [singularHomologyCrossRel_def, singularHomologyCross_def]
  refine (Category.assoc _ _ _).trans ?_
  rw [key]
  -- the objects here are the singular complexes, which agree with the terms of the short exact
  -- sequences only up to unfolding, so `hc` and `homologyMap_comp` are applied as terms
  exact ((reassoc_of% hc) _).trans <| congrArg (_ ≫ ·) <|
    (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n')).trans
      (Category.assoc _ _ _).symm

end Cross

section Kunneth

variable (n : ℕ)
  [∀ p, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset B).singularChainComplex R).homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The relative Künneth map**
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)`: the algebraic Künneth map of
the chain complexes `C(X, B; R)` and `C(Y; S)` followed by the map induced by the relative shuffle
map. -/
def singularHomologyKunnethRel :
    GradedObject.Monoidal.tensorObj (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) n ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyKunneth ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
    n ≫ homologyMap (shuffleRel X Y B R S) n

/-- The relative Künneth map is the algebraic Künneth map followed by the map induced by the
relative shuffle map. -/
theorem singularHomologyKunnethRel_def :
    singularHomologyKunnethRel X Y B R S n =
      homologyKunneth ((TopPair.ofSubset B).singularChainComplex R)
        ((toSSet.obj Y).chainComplex S) n ≫ homologyMap (shuffleRel X Y B R S) n :=
  (rfl)

/-- The relative Künneth map restricts to the relative cross product on each summand. -/
@[reassoc (attr := simp)]
theorem ι_singularHomologyKunnethRel (p q : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) p q n h ≫
      singularHomologyKunnethRel X Y B R S n = singularHomologyCrossRel X Y B R S p q n h :=
  ι_homologyKunneth_assoc ((TopPair.ofSubset B).singularChainComplex R)
    ((toSSet.obj Y).chainComplex S) n p q h _

/-- The relative Künneth map is an isomorphism exactly when the algebraic Künneth map of the
chain complexes `C(X, B; R)` and `C(Y; S)` is, since the relative shuffle map is a
quasi-isomorphism. -/
theorem isIso_singularHomologyKunnethRel_iff :
    IsIso (singularHomologyKunnethRel X Y B R S n) ↔
      IsIso (homologyKunneth ((TopPair.ofSubset B).singularChainComplex R)
        ((toSSet.obj Y).chainComplex S) n) :=
  have := (quasiIsoAt_iff_isIso_homologyMap (shuffleRel X Y B R S) n).1 inferInstance
  isIso_comp_right_iff _ (homologyMap (shuffleRel X Y B R S) n)

end Kunneth

end General

section Split

variable {k : Type w} [CommRing k] (X Y : TopCat.{w}) (B : Set X) (R S : ModuleCat.{w} k)

/-- **The relative Künneth theorem**: if the cycles of `C(X, B; R)` and `C(Y; S)` split off their
terms and their homology splits off their cycles, the relative Künneth map
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` is an isomorphism. This
holds for all coefficient modules over a commutative semisimple ring, for instance a field. -/
instance isIso_singularHomologyKunnethRel
    [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (n : ℕ) :
    IsIso (singularHomologyKunnethRel X Y B R S n) :=
  (isIso_singularHomologyKunnethRel_iff X Y B R S n).2 inferInstance

/-- **The relative Künneth isomorphism**
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ≅ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` when the cycles and the
homology of `C(X, B; R)` and `C(Y; S)` split off, for instance over a field. -/
def singularHomologyKunnethRelIso
    [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) n ≅
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  asIso (singularHomologyKunnethRel X Y B R S n)

@[simp]
theorem singularHomologyKunnethRelIso_hom
    [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (n : ℕ) :
    (singularHomologyKunnethRelIso X Y B R S n).hom = singularHomologyKunnethRel X Y B R S n :=
  (rfl)

variable [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
  [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]

/-- **The relative Künneth map is a split monomorphism** when the cycles of `C(X, B; R)` and
`C(Y; S)` split off their terms, for instance for projective coefficient modules over a principal
ideal domain. The retraction depends on chosen splittings of the cycles and need not be natural. -/
theorem isSplitMono_singularHomologyKunnethRel (n : ℕ) :
    IsSplitMono (singularHomologyKunnethRel X Y B R S n) :=
  have := isSplitMono_homologyKunneth ((TopPair.ofSubset B).singularChainComplex R)
    ((toSSet.obj Y).chainComplex S) n
  have := (quasiIsoAt_iff_isIso_homologyMap (shuffleRel X Y B R S) n).1 inferInstance
  inferInstanceAs (IsSplitMono (homologyKunneth _ _ n ≫ homologyMap (shuffleRel X Y B R S) n))

/-- When the cycles of `C(X, B; R)` and `C(Y; S)` split off their terms, for instance over a
commutative semisimple ring or for projective coefficients over a principal ideal domain, each
relative cross product `Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B))` is a monomorphism: it is the
inclusion of a summand followed by the relative Künneth map, a split monomorphism. -/
instance mono_singularHomologyCrossRel (p q n : ℕ) (h : p + q = n) :
    Mono (singularHomologyCrossRel X Y B R S p q n h) :=
  have := isSplitMono_singularHomologyKunnethRel X Y B R S n
  ι_singularHomologyKunnethRel X Y B R S n p q h ▸ mono_comp _ _

/-- **A relative cross product that is the whole relative Künneth map.** If the cycles and the
homology of `C(X, B; R)` and `C(Y; S)` split off, for instance over a field, and `(X, B)` has no
relative homology outside degree `p`, the relative cross product
`Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` is an isomorphism: it is the summand
`(p, q)` of the relative Künneth isomorphism, whose other summands vanish. -/
theorem isIso_singularHomologyCrossRel_of_isZero
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (p q n : ℕ) (h : p + q = n)
    (hB : ∀ a ≠ p, IsZero ((TopPair.ofSubset B).singularHomology R a)) :
    IsIso (singularHomologyCrossRel X Y B R S p q n h) := by
  have := GradedObject.Monoidal.isIso_ιTensorObj_of_isZero_left
    (fun a ↦ (TopPair.ofSubset B).singularHomology R a)
    (fun b ↦ ((singularHomologyFunctor _ b).obj S).obj Y) hB q n h
  rw [← ι_singularHomologyKunnethRel]
  infer_instance

end Split

/-! ### The relative cross product for nested subspaces

For nested subsets `s ⊆ t` of a space `Y` and subsets `s' ⊆ t'` of `Y × F` with the same points
as `s × F` and `t × F`, the relative cross product of the pair `(t, s)` with `F` lands in the
relative homology of `(t', s')`. -/

section OfInclusion

variable {k : Type w} [CommRing k] {Y F : TopCat.{w}} {s t r : Set Y} {s' t' r' : Set ↑(Y ⊗ F)}
  (R S : ModuleCat.{w} k)

/-- **The relative cross product for nested subspaces** `Hₐ(t, s; R) ⊗ H_b(F; S) ⟶
Hₙ(t', s'; R ⊗ S)`: the relative cross product `TopCat.singularHomologyCrossRel` of the pair
`(t, s)` with `F`, transported along the identifications of `(t, s)` with the pair of `t` and the
preimage of `s` (`TopPair.ofSubsetPreimageValIso`), and of the product pair with `(t', s')`
(`TopCat.prodSubspacePairIso`). -/
def singularHomologyCrossRelOfInclusion (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s) (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (a b n : ℕ)
    (h : a + b = n) :
    (TopPair.ofInclusion hst).singularHomology R a ⊗ ((singularHomologyFunctor _ b).obj S).obj F ⟶
      (TopPair.ofInclusion hst').singularHomology (R ⊗ S) n :=
  (TopPair.singularHomologyMap (TopPair.ofSubsetPreimageValIso hst).inv _ a ▷ _) ≫
    singularHomologyCrossRel (TopCat.of t) F (Subtype.val ⁻¹' s) R S a b n h ≫
    TopPair.singularHomologyMap (prodSubspacePairIso hst' hs ht).hom _ n

/-- The relative cross product for nested subspaces is the relative cross product
`TopCat.singularHomologyCrossRel` of `(t, s)` with `F`, transported along the identifications of
the pairs. -/
theorem singularHomologyCrossRelOfInclusion_def (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s) (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (a b n : ℕ)
    (h : a + b = n) :
    singularHomologyCrossRelOfInclusion R S hst hst' hs ht a b n h =
      (TopPair.singularHomologyMap (TopPair.ofSubsetPreimageValIso hst).inv _ a ▷ _) ≫
        singularHomologyCrossRel (TopCat.of t) F (Subtype.val ⁻¹' s) R S a b n h ≫
        TopPair.singularHomologyMap (prodSubspacePairIso hst' hs ht).hom _ n :=
  (rfl)

/-- **The relative cross product for nested subspaces of an absolute class.** The relative cross
product of the image in `Hₐ(t, s; R)` of a class of `Hₐ(t; R)` is the image in relative homology
of the absolute cross product, carried to `t'` by `TopCat.prodSubspaceMap`. -/
@[reassoc]
theorem whiskerRight_singularHomologyπ_comp_singularHomologyCrossRelOfInclusion (hst : s ⊆ t)
    (hst' : s' ⊆ t') (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s) (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t)
    (a b n : ℕ) (h : a + b = n) :
    ((TopPair.ofInclusion hst).singularHomologyπ R a ▷
        ((singularHomologyFunctor _ b).obj S).obj F) ≫
      singularHomologyCrossRelOfInclusion R S hst hst' hs ht a b n h =
    singularHomologyCross (TopCat.of t) F R S a b n h ≫
      ((singularHomologyFunctor _ n).obj _).map (prodSubspaceMap F ht) ≫
        (TopPair.ofInclusion hst').singularHomologyπ _ n := by
  have h₁ : (TopPair.ofInclusion hst).singularHomologyπ R a ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetPreimageValIso hst).inv _ a =
        (TopPair.ofSubset (X := TopCat.of t) (Subtype.val ⁻¹' s)).singularHomologyπ _ a := by
    exact (HomologicalComplex.homologyMap_comp _ _ a).symm.trans
      (congrArg (HomologicalComplex.homologyMap · a)
        (TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id _
          (TopPair.ofSubsetPreimageValIso hst).inv TopPair.ofSubsetPreimageValIso_inv_fst))
  have h₂ := singularHomologyCross_comp_singularHomologyπ (TopCat.of t) F (Subtype.val ⁻¹' s) R S
    a b n h
  have h₃ := TopPair.singularHomologyπ_naturality (prodSubspacePairIso hst' hs ht).hom (R ⊗ S) n
  rw [prodSubspacePairIso_hom_fst] at h₃
  unfold singularHomologyCrossRelOfInclusion
  rw [← comp_whiskerRight_assoc, h₁]
  exact ((reassoc_of% h₂) _).symm.trans (congrArg (_ ≫ ·) h₃.symm)

/-- **The connecting map of a pair on a relative cross product for nested subspaces.** The
connecting map of the pair `(r', t')` sends the relative cross product `a × b` to the absolute
cross product `∂a × b`, carried to `t'` by `TopCat.prodSubspaceMap`. -/
@[reassoc]
theorem singularHomologyCrossRelOfInclusion_comp_singularHomologyδ (htr : t ⊆ r)
    (htr' : t' ⊆ r') (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (hr : ∀ x, x ∈ r' ↔ fst Y F x ∈ r)
    (a b n : ℕ) (h : a + b = n) :
    singularHomologyCrossRelOfInclusion R S htr htr' ht hr (a + 1) b (n + 1) (by omega) ≫
        (TopPair.ofInclusion htr').singularHomologyδ (R ⊗ S) (n + 1) n =
      ((TopPair.ofInclusion htr).singularHomologyδ R (a + 1) a ▷
          ((singularHomologyFunctor _ b).obj S).obj F) ≫
        singularHomologyCross (TopCat.of t) F R S a b n h ≫
        ((singularHomologyFunctor _ n).obj _).map (prodSubspaceMap F ht) := by
  have h₁ := TopPair.singularHomologyδ_naturality (R ⊗ S) (prodSubspacePairIso htr' ht hr).hom
    (n + 1) n
  have h₂ := singularHomologyCrossRel_comp_singularHomologyδ (TopCat.of r) F
    (Subtype.val ⁻¹' t) R S (a + 1) b (n + 1) (by omega) (p' := a) rfl h
  have h₃ := TopPair.singularHomologyδ_naturality R (TopPair.ofSubsetPreimageValIso htr).inv
    (a + 1) a
  have h₄ := singularHomologyCross_naturality
    (TopPair.Hom.snd (TopPair.ofSubsetPreimageValIso htr).inv) (𝟙 F) R S a b n h
  rw [CategoryTheory.Functor.map_id, tensorHom_id] at h₄
  -- The composite of `t × F ⟶ t₀ × F ⟶ fst⁻¹(t₀) ⟶ t'`, where `t₀` is the preimage of `t` in
  -- `r`, is the map `(x, y) ↦ (x, y)`.
  have h₅ : (TopPair.Hom.snd (TopPair.ofSubsetPreimageValIso htr).inv ▷ F) ≫
      (prodPreimageFstIso (TopCat.of r) F (Subtype.val ⁻¹' t)).hom ≫
        TopPair.Hom.snd (prodSubspacePairIso htr' ht hr).hom = prodSubspaceMap F ht := by
    ext x
    have hP : ((prodPreimageFstIso (TopCat.of r) F (Subtype.val ⁻¹' t)).hom
        ((TopPair.Hom.snd (TopPair.ofSubsetPreimageValIso htr).inv ▷ F) x)).val =
          ((TopPair.Hom.snd (TopPair.ofSubsetPreimageValIso htr).inv x.1).val, x.2) :=
      ConcreteCategory.congr_hom (prodPreimageFstIso_hom_comp_map (TopCat.of r) F
        (Subtype.val ⁻¹' t)) _
    have hi := TopPair.ofSubsetPreimageValIso_inv_snd_apply (hst := htr) x.1
    refine Subtype.ext (((prodSubspacePairIso_hom_snd_apply htr' ht hr _).trans ?_).trans
      (prodSubspaceMap_apply ht x).symm)
    exact Prod.ext ((congrArg (fun z ↦ (fst (TopCat.of r) F z).val) hP).trans
      (congrArg Subtype.val hi)) (congrArg (snd (TopCat.of r) F) hP)
  -- The connecting maps are moved from the pair `(r', t')` to the product pair (`h₁`), across the
  -- relative cross product (`h₂`), and to the pair `(r, t)` (`h₃`); the cross product is then
  -- natural in the subspace (`h₄`). The composites mix the two descriptions of absolute homology,
  -- as the homology of a subobject of a pair and as singular homology, which agree only up to
  -- unfolding, so they are assembled as terms.
  unfold singularHomologyCrossRelOfInclusion
  simp only [Category.assoc]
  refine (congrArg (_ ≫ _ ≫ ·) h₁.symm).trans ?_
  refine (congrArg (_ ≫ ·) (((reassoc_of% h₂) _).trans (Category.assoc _ _ _))).trans ?_
  refine (comp_whiskerRight_assoc (C := ModuleCat.{w} k) _ _ _ _).symm.trans ?_
  refine (congrArg (fun f ↦ MonoidalCategory.whiskerRight (C := ModuleCat.{w} k) f _ ≫ _)
    h₃.symm).trans ?_
  refine (comp_whiskerRight_assoc (C := ModuleCat.{w} k) _ _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
    ((reassoc_of% h₄) _))).trans ?_
  refine congrArg (_ ≫ _ ≫ ·) ?_
  exact (congrArg (_ ≫ ·) (((singularHomologyFunctor _ n).obj (R ⊗ S)).map_comp _ _).symm).trans
    ((((singularHomologyFunctor _ n).obj _).map_comp _ _).symm.trans (congrArg _ h₅))

/-- **The relative cross product for nested subspaces commutes with the connecting maps of
triples.** For nested subsets `s ⊆ t ⊆ r` and the corresponding subsets `s' ⊆ t' ⊆ r'` of `Y × F`,
the connecting map `H_{n+1}(r', t') ⟶ Hₙ(t', s')` of the triple sends `a × b` to `∂a × b`, where
`∂` is the connecting map of the triple `(r, t, s)`. -/
theorem whiskerRight_singularHomologyδ_comp_singularHomologyCrossRelOfInclusion (hst : s ⊆ t)
    (htr : t ⊆ r) (hst' : s' ⊆ t') (htr' : t' ⊆ r') (hs : ∀ x, x ∈ s' ↔ fst Y F x ∈ s)
    (ht : ∀ x, x ∈ t' ↔ fst Y F x ∈ t) (hr : ∀ x, x ∈ r' ↔ fst Y F x ∈ r) (a b n : ℕ)
    (h : a + b = n) :
    ((TauCeti.TopTriple.ofInclusions hst htr).singularHomologyδ R (a + 1) a ▷
        ((singularHomologyFunctor _ b).obj S).obj F) ≫
      singularHomologyCrossRelOfInclusion R S hst hst' hs ht a b n h =
    singularHomologyCrossRelOfInclusion R S htr htr' ht hr (a + 1) b (n + 1) (by omega) ≫
      (TauCeti.TopTriple.ofInclusions hst' htr').singularHomologyδ _ (n + 1) n := by
  rw [TauCeti.TopTriple.singularHomologyδ_eq_comp_singularHomologyπ _ _ (a + 1) a,
    TauCeti.TopTriple.singularHomologyδ_eq_comp_singularHomologyπ _ _ (n + 1) n]
  -- The homology of `t` is the source of `π` as the subspace of the inner pair and the target of
  -- `δ` as the subspace of the outer pair; these agree only up to unfolding, so
  -- `rw [comp_whiskerRight_assoc]` gives an ill-typed motive and the steps are composed as terms.
  refine (comp_whiskerRight_assoc (C := ModuleCat.{w} k) _ _ _ _).trans ?_
  refine (congrArg (_ ≫ ·)
    (whiskerRight_singularHomologyπ_comp_singularHomologyCrossRelOfInclusion R S hst hst' hs ht
      a b n h)).trans ?_
  refine Eq.symm (((reassoc_of% (singularHomologyCrossRelOfInclusion_comp_singularHomologyδ R S
    htr htr' ht hr a b n h)) _).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

end OfInclusion

end TopCat
