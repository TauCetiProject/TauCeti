/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# The relative cross product and the relative Künneth theorem for singular homology

Let `X` and `Y` be topological spaces and `B ⊆ X`. The product pair `(X, B) × Y` is
`(X × Y, B × Y)`; here `B × Y` is written as the preimage `fst⁻¹(B)` of `B` under the first
projection, so that the pair is `TopPair.ofSubset (Prod.fst ⁻¹' B)`. The shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` (`TopCat.shuffle`) carries `C(B; R) ⊗ C(Y; S)` into the
singular chains of `fst⁻¹(B)`, so it descends to the **relative shuffle map**
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
(`TopCat.singularHomologyCross_comp_singularHomologyπ`). The relative Künneth map
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)`
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

* `TopCat.shuffleRel`: the relative shuffle map `C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B))`.
* `TopCat.singularHomologyCrossRel`: the relative cross product in singular homology.
* `TopCat.singularHomologyKunnethRel`: the relative Künneth map, and
  `TopCat.singularHomologyKunnethRelIso`: the relative Künneth isomorphism when the cycles and the
  homology split off.

## Main results

* `TopCat.quasiIso_shuffleRel`: the relative Eilenberg–Zilber theorem.
* `TopCat.shuffleRel_naturality`, `TopCat.singularHomologyCrossRel_naturality`: naturality in maps
  of pairs `(X, B) ⟶ (X', B')` and in maps `Y ⟶ Y'`.
* `TopCat.singularHomologyCross_comp_singularHomologyπ`: the absolute cross product followed by
  the map to relative homology is the relative cross product of the image of the first factor.
* `TopCat.isIso_singularHomologyKunnethRel`: the relative Künneth theorem.
* `TopCat.isSplitMono_singularHomologyKunnethRel`, `TopCat.mono_singularHomologyCrossRel`: the
  relative Künneth map is a split monomorphism, and the relative cross product injective, when the
  cycles split off.

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

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- Tensoring on the right with `C(Y; S)` preserves the short exact sequence
`C(B; R) ⟶ C(X; R) ⟶ C(X, B; R)` of singular chains of the pair `(X, B)`, since the inclusion of
the singular chains of `B` splits in each degree. -/
theorem shortExact_tensorRightShortComplex_singularChainComplexShortComplex :
    (tensorRightShortComplex ((toSSet.obj Y).chainComplex S)
      ((TopPair.ofSubset B).singularChainComplexShortComplex R)).ShortExact :=
  shortExact_tensorRightShortComplex _ _
    ((TopPair.ofSubset B).shortExact_singularChainComplexShortComplex R)

/-- On `C(B; R) ⊗ C(Y; S)` the shuffle map is the shuffle map of `B` and `Y` followed by the map
induced by `B × Y ≅ fst⁻¹(B)` and the inclusion of `fst⁻¹(B)` into `X × Y`. -/
@[reassoc]
theorem chainComplexMap_tensorHom_id_shuffle :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S =
      shuffle (TopPair.ofSubset B).snd Y R S ≫
        SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S) ≫
          SSet.chainComplexMap
            (toSSet.map (TopPair.ofSubset (fst X Y ⁻¹' B)).map) (R ⊗ S) := by
  have h := shuffle_naturality (TopPair.ofSubset B).map (𝟙 Y) R S
  simp only [CategoryTheory.Functor.map_id] at h
  refine h.trans (congrArg (_ ≫ ·) ?_)
  simp only [← CategoryTheory.Functor.map_comp, prodPreimageFstIso_hom_comp_map]
  rfl

/-- The shuffle map carries `C(B; R) ⊗ C(Y; S)` into the chains of `fst⁻¹(B)`, which vanish in
the relative chains of `(X × Y, fst⁻¹(B))`. -/
private theorem shuffle_cokernel_condition :
    (SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffle X Y R S ≫
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) = 0 := by
  -- The composite factors through the singular chains of `fst⁻¹(B)`, which `π` kills. The
  -- composites are reassociated by hand: the singular chains of `X × Y` appear both as those of
  -- the ambient space of the pair and as `(toSSet.obj (X ⊗ Y)).chainComplex`, which agree only up
  -- to unfolding `TopPair.ofSubset`, so `rw [Category.assoc]` does not apply.
  refine (Category.assoc _ _ _).symm.trans
    ((chainComplexMap_tensorHom_id_shuffle X Y B R S =≫ _).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (TopPair.chainComplexMap_comp_singularChainComplexπ _ _)).trans
        comp_zero))).trans comp_zero)))

/-- **The relative shuffle map** `C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B); R ⊗ S)`, induced by
the shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on the cokernels; it is characterized by
`TopCat.singularChainComplexπ_tensorHom_id_shuffleRel`. -/
def shuffleRel :
    (TopPair.ofSubset B).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (shuffle_cokernel_condition X Y B R S))

/-- The relative shuffle map is induced by the shuffle map: on `C(X; R) ⊗ C(Y; S)` it is the
shuffle map followed by the projection to the relative chains of `(X × Y, fst⁻¹(B))`. -/
@[reassoc (attr := simp)]
theorem singularChainComplexπ_tensorHom_id_shuffleRel :
    ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫ shuffleRel X Y B R S =
      shuffle X Y R S ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.fac _ WalkingParallelPair.one

/-- **Naturality of the relative shuffle map** in maps of pairs `(X, B) ⟶ (X', B')` and in maps
`Y ⟶ Y'`. -/
@[reassoc]
theorem shuffleRel_naturality {X' Y' : TopCat.{w}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y') :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        SSet.chainComplexMap (toSSet.map g) S) ≫ shuffleRel X' Y' B' R S =
      shuffleRel X Y B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S) := by
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have : Epi ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S)) := hS.epi_g
  refine (cancel_epi ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S))).1 ?_
  -- Both sides are the shuffle map followed by the map of pairs induced by `f × g`.
  have hπ := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap f hf) R
  simp only [TopPair.ofSubsetMap_fst] at hπ
  have h₁ : ((TopPair.ofSubset B).singularChainComplexπ R ⊗ₘ
        𝟙 ((toSSet.obj Y).chainComplex S)) ≫
          (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
            SSet.chainComplexMap (toSSet.map g) S) =
      (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset B').singularChainComplexπ R ⊗ₘ
          𝟙 ((toSSet.obj Y').chainComplex S)) :=
    -- The tensor product of chain complexes is `mapBifunctorMap`, which is bifunctorial; the full
    -- monoidal structure on chain complexes is not available over a general `C`.
    (mapBifunctorMap_comp _ _ _ _ _ _).symm.trans <| (congrArg₂ (· ⊗ₘ ·)
      hπ.symm ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
        (mapBifunctorMap_comp _ _ _ _ _ _)
  have h₂ := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S)
  have hfst := TopPair.ofSubsetMap_fst (B := fst X Y ⁻¹' B) (B' := fst X' Y' ⁻¹' B') (f ⊗ₘ g)
    (mapsTo_tensorHom_preimage_fst f g hf)
  -- `rw [Category.assoc]` does not see through the wrappers: the chain complexes of the pairs
  -- appear both as `TopPair.singularChainComplex` and as the singular chain complexes of their
  -- ambient spaces, which agree only up to unfolding, so the composites are reassociated by `calc`.
  calc _ = (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset B').singularChainComplexπ R ⊗ₘ
          𝟙 ((toSSet.obj Y').chainComplex S)) ≫ shuffleRel X' Y' B' R S :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _))
    _ = shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S) :=
        (congrArg (_ ≫ ·) (singularChainComplexπ_tensorHom_id_shuffleRel X' Y' B' R S)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
            (shuffle_naturality f g R S)).trans (Category.assoc _ _ _)))
    _ = _ := (congrArg (fun φ ↦ shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map φ) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S)) hfst.symm).trans <|
      (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (singularChainComplexπ_tensorHom_id_shuffleRel X Y B R S).symm).trans
          (Category.assoc _ _ _)))

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

end Split

end TopCat
