/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative
import TauCeti.LinearAlgebra.TensorProduct.Separation

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

The last section compares `(E × Y, A × Y)` with the product taken modulo a second subspace
`B ⊆ Y`. For open `A` and `B`, the exact sequence of the triple `(E × Y, A × Y ∪ E × B, A × Y)`
and excision show that a class of `Hₙ(E × Y, A × Y)` vanishing in `Hₙ(E × Y, A × Y ∪ E × B)` comes
from `Hₙ(E × B, A × B)` (`TopCat.exists_singularHomologyMap_ofSubsetMap_tensorHom_eq`). Over a
field, or more generally where the relative Künneth theorem applies, the relative cross product
`a × β` of a nonzero `a ∈ Hᵢ(E, A)` with a class `β ∈ Hⱼ(Y)` not coming from `B` does not come
from `Hₙ(E × B, A × B)`
(`TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel`,
`TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel_of_field`). Together
they compute localizations of cross products at a product of two closed sets, which is how classes
living over the fundamental class of a product are detected.

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
* `TopCat.shuffleRel_naturality`, `TopCat.singularHomologyCrossRel_naturality`,
  `TopCat.singularHomologyKunnethRel_naturality`: naturality in maps of pairs `(X, B) ⟶ (X', B')`
  and in maps `Y ⟶ Y'`.
* `TopCat.singularHomologyCross_comp_singularHomologyπ`: the absolute cross product followed by
  the map to relative homology is the relative cross product of the image of the first factor.
* `TopCat.isIso_singularHomologyKunnethRel`: the relative Künneth theorem.
* `TopCat.isSplitMono_singularHomologyKunnethRel`, `TopCat.mono_singularHomologyCrossRel`: the
  relative Künneth map is a split monomorphism, and the relative cross product injective, when the
  cycles split off.
* `TopCat.exists_singularHomologyMap_ofSubsetMap_tensorHom_eq`: excision for a product modulo
  `A × Y ∪ E × B`.
* `TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel`,
  `TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel_of_field`:
  `a × β` does not come from `Hₙ(E × B, A × B)` when `a ≠ 0` and `β` does not come from `B`, for
  instance over a field.

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

/-- **Naturality of the relative Künneth map** in maps of pairs `(X, B) ⟶ (X', B')` and in maps
`Y ⟶ Y'`: on each summand it is the naturality of the relative cross product. -/
@[reassoc]
theorem singularHomologyKunnethRel_naturality {X' Y' : TopCat.{w}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y')
    [∀ p, PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset B').singularChainComplex R).homology p))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).cycles q))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    GradedObject.Monoidal.tensorHom
        (fun p ↦ TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).map g) n ≫
          singularHomologyKunnethRel X' Y' B' R S n =
      singularHomologyKunnethRel X Y B R S n ≫ TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (mapsTo_tensorHom_preimage_fst f g hf)) (R ⊗ S) n := by
  ext p q h
  simp only [GradedObject.Monoidal.ι_tensorHom_assoc, ι_singularHomologyKunnethRel,
    ι_singularHomologyKunnethRel_assoc]
  exact singularHomologyCrossRel_naturality X Y B R S p q n h f hf g

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

section TwoSubspaces

/-! ### Products modulo two subspaces -/

open TauCeti

variable {Λ : Type*} [Ring Λ] (R : ModuleCat.{w} Λ) {E Y : TopCat.{w}} {A : Set E} {B : Set Y}

/-- **Excision for a product modulo two subspaces.** Let `A ⊆ E` and `B ⊆ Y` be open and let `Z` be
the union `A × Y ∪ E × B` in `E × Y`. A class of `Hₙ(E × Y, A × Y)` which vanishes in
`Hₙ(E × Y, Z)` comes from `Hₙ(E × B, A × B)`: by the exact sequence of the triple
`(E × Y, Z, A × Y)` it comes from `Hₙ(Z, A × Y)`, which excision identifies with
`Hₙ(E × B, A × B)`. -/
theorem exists_singularHomologyMap_ofSubsetMap_tensorHom_eq (hA : IsOpen A) (hB : IsOpen B)
    {Z : Set ↑(E ⊗ Y)} (hAZ : fst E Y ⁻¹' A ⊆ Z) (hBZ : snd E Y ⁻¹' B ⊆ Z)
    (hZ : Z ⊆ fst E Y ⁻¹' A ∪ snd E Y ⁻¹' B) {n : ℕ}
    {x : ((TopPair.ofSubset (fst E Y ⁻¹' A)).singularHomology R n : ModuleCat.{w} Λ)}
    (hx : (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (E ⊗ Y)) fun _ h ↦ hAZ h) R
      n).hom x = 0) :
    ∃ y, (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E ⊗ₘ (TopPair.ofSubset B).map)
      (mapsTo_tensorHom_preimage_fst _ _ fun _ hx ↦ hx)) R n).hom y = x := by
  let T := TopTriple.ofSubset hAZ
  -- By the exact sequence of the triple, `x` comes from `Hₙ(Z, A × Y)`.
  have hT : TopTriple.totalToOuter.app T = TopPair.ofSubsetMap (𝟙 (E ⊗ Y)) fun _ h ↦ hAZ h :=
    TopTriple.totalToOuter_app_ofSubset hAZ
  have hx' : (TopPair.singularHomologyMap (TopTriple.totalToOuter.app T) R n).hom x = 0 := by
    rw [hT]
    exact hx
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.singularHomology_exact_total R n) x
    hx'
  -- The inclusion `g : E × B → E × Y` maps `E × B` into `Z` and `A × B` into `A × Y`.
  let g : E ⊗ TopCat.of B ⟶ E ⊗ Y := 𝟙 E ⊗ₘ (TopPair.ofSubset B).map
  have hgA : Set.MapsTo g (fst E (TopCat.of B) ⁻¹' A) (fst E Y ⁻¹' A) :=
    mapsTo_tensorHom_preimage_fst _ _ fun _ hx ↦ hx
  have hgZ : ∀ x, g x ∈ Z := fun x ↦ hBZ x.2.2
  let f : TopPair.ofSubset (fst E (TopCat.of B) ⁻¹' A) ⟶ TopTriple.innerPair.obj T :=
    TopPair.ofHom (TopCat.ofHom ⟨Set.codRestrict g Z hgZ, g.hom.continuous.codRestrict hgZ⟩)
      (TopCat.ofHom ⟨Set.MapsTo.restrict g _ _ hgA, g.hom.continuous.restrict hgA⟩) rfl
  -- Excision: `A × Y` and `E × B` are open and cover `Z`, and `f` is onto `E × B`.
  have : IsIso (TopPair.singularHomologyMap f R n) := by
    refine TopPair.isIso_singularHomologyMap_of_open_cover R f ?_ ?_
      (fun t : Bool ↦ bif t then Subtype.val ⁻¹' (fst E Y ⁻¹' A)
        else Subtype.val ⁻¹' (snd E Y ⁻¹' B)) ?_ ?_ ?_ n
    · exact (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal).codRestrict Z hgZ
    · rintro x ⟨y, hy⟩
      have hy' : y.1 = g x := congrArg Subtype.val hy
      have hyA : y.1 ∈ fst E Y ⁻¹' A := y.2
      rw [hy'] at hyA
      exact ⟨⟨x, hyA⟩, rfl⟩
    · rintro (_ | _)
      · exact (hB.preimage (snd E Y).hom.continuous).preimage continuous_subtype_val
      · exact (hA.preimage (fst E Y).hom.continuous).preimage continuous_subtype_val
    · refine Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 ?_
      rcases hZ z.2 with hz | hz
      · exact ⟨true, hz⟩
      · exact ⟨false, hz⟩
    · rintro (_ | _)
      · exact Or.inr fun z hz ↦ ⟨(z.1.1, ⟨z.1.2, hz⟩), rfl⟩
      · exact Or.inl fun z hz ↦ ⟨⟨z.1, hz⟩, rfl⟩
  obtain ⟨y₀, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (TopPair.singularHomologyMap f R n)) y
  refine ⟨y₀, ?_⟩
  -- Excision followed by the inclusion of the triple is the inclusion of pairs given by `g`.
  have hfg : f ≫ TopTriple.innerToTotal.app T = TopPair.ofSubsetMap
      (𝟙 E ⊗ₘ (TopPair.ofSubset B).map) (mapsTo_tensorHom_preimage_fst _ _ fun _ hx ↦ hx) := by
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopTriple.innerToTotal_app_fst, TopPair.ofSubsetMap_fst]
    exact ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  rw [← hfg]
  exact congrArg (fun φ ↦ φ.hom y₀)
    (TopPair.singularHomologyMap_comp f R (TopTriple.innerToTotal.app T) n)

end TwoSubspaces

section NotFromSubspace

variable {k : Type w} [CommRing k] (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
  (R S : ModuleCat.{w} k)

/-- **Relative cross products with a class not coming from a subspace.** Let `a ∈ Hᵢ(X, A)` be
nonzero and let `β ∈ Hⱼ(Y)` have nonzero image in `Hⱼ(Y, B)`, that is, not come from `B`. If the
relative Künneth theorem holds for `(X, A) × B` and its map is injective for `(X, A) × Y`, and
nonzero vectors of `Hᵢ(X, A)` and `Hⱼ(Y, B)` have nonzero tensor product, then the relative cross
product `a × β ∈ Hₙ(X × Y, A × Y)` does not come from `Hₙ(X × B, A × B)`. By the Künneth theorem
a class coming from `Hₙ(X × B, A × B)` lies in the image of `⨁ Hₚ(X, A) ⊗ H_q(B)`, which
localizing the second factor at `(Y, B)` kills, whereas it sends `a × β` to `a ⊗ [β] ≠ 0`. -/
theorem singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel [NoZeroDivisors k]
    [∀ m, IsSplitMono (((TopPair.ofSubset A).singularChainComplex R).iCycles m)]
    [∀ m, IsSplitEpi (((TopPair.ofSubset A).singularChainComplex R).homologyπ m)]
    [∀ m, IsSplitMono (((toSSet.obj (TopCat.of B)).chainComplex S).iCycles m)]
    [∀ m, IsSplitEpi (((toSSet.obj (TopCat.of B)).chainComplex S).homologyπ m)]
    [∀ m, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles m)] {i j n : ℕ} (h : i + j = n)
    [Module.Projective k ((TopPair.ofSubset A).singularHomology R i : ModuleCat.{w} k)]
    [Module.Projective k ((TopPair.ofSubset B).singularHomology S j : ModuleCat.{w} k)]
    {a : ((TopPair.ofSubset A).singularHomology R i : ModuleCat.{w} k)}
    {β : (((singularHomologyFunctor _ j).obj S).obj Y : ModuleCat.{w} k)} (ha : a ≠ 0)
    (hβ : ((TopPair.ofSubset B).singularHomologyπ S j).hom β ≠ 0)
    (y : ((TopPair.ofSubset (fst X (TopCat.of B) ⁻¹' A)).singularHomology (R ⊗ S) n :
      ModuleCat.{w} k)) :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X ⊗ₘ (TopPair.ofSubset B).map)
      (mapsTo_tensorHom_preimage_fst _ _ fun _ hx ↦ hx)) (R ⊗ S) n).hom y ≠
        (singularHomologyCrossRel X Y A R S i j n h).hom (a ⊗ₜ β) := by
  intro hy
  -- By the Künneth theorem for `X × B`, `y` is the image of a class `w` of `⨁ Hₚ(X, A) ⊗ H_q(B)`.
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (singularHomologyKunnethRel X (TopCat.of B) A R S n)) y
  have hA : Set.MapsTo (𝟙 X) A A := fun _ hx ↦ hx
  -- `F` includes `⨁ Hₚ(X, A) ⊗ H_q(B)` into `⨁ Hₚ(X, A) ⊗ H_q(Y)`, and `Φ` maps the latter to
  -- `⨁ Hₚ(X, A) ⊗ H_q(Y, B)`; their composite vanishes.
  let F : GradedObject.Monoidal.tensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
        (fun m ↦ ((singularHomologyFunctor _ m).obj S).obj (TopCat.of B)) n ⟶
      GradedObject.Monoidal.tensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
        (fun m ↦ ((singularHomologyFunctor _ m).obj S).obj Y) n :=
    GradedObject.Monoidal.tensorHom
      (fun m ↦ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) hA) R m)
      (fun m ↦ ((singularHomologyFunctor _ m).obj S).map (TopPair.ofSubset B).map) n
  let Φ : GradedObject.Monoidal.tensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
        (fun m ↦ ((singularHomologyFunctor _ m).obj S).obj Y) n ⟶
      GradedObject.Monoidal.tensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
        (fun m ↦ (TopPair.ofSubset B).singularHomology S m) n :=
    GradedObject.Monoidal.tensorHom (fun m ↦ 𝟙 ((TopPair.ofSubset A).singularHomology R m))
      (fun m ↦ (TopPair.ofSubset B).singularHomologyπ S m) n
  have hFΦ : F ≫ Φ = 0 := GradedObject.Monoidal.tensorHom_comp_tensorHom_eq_zero _ _ _ _
    (fun m ↦ (TopPair.ofSubset B).homologyMap_comp_singularHomologyπ S m) n
  -- The Künneth map for `X × Y` is injective, so `a ⊗ β` is the image of `w` under `F`.
  have heq : (GradedObject.Monoidal.ιTensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
      (fun m ↦ ((singularHomologyFunctor _ m).obj S).obj Y) i j n h).hom (a ⊗ₜ β) = F.hom w := by
    have := isSplitMono_singularHomologyKunnethRel X Y A R S n
    refine (ModuleCat.mono_iff_injective _).1
      (inferInstance : Mono (singularHomologyKunnethRel X Y A R S n)) ?_
    have e₁ := congrArg (fun φ ↦ φ.hom (a ⊗ₜ β)) (ι_singularHomologyKunnethRel X Y A R S n i j h)
    have e₂ := congrArg (fun φ ↦ φ.hom w)
      (singularHomologyKunnethRel_naturality X (TopCat.of B) A R S n (𝟙 X) hA
        (TopPair.ofSubset B).map)
    -- The equations compose up to the definitional unfolding of composites.
    exact e₁.trans (hy.symm.trans e₂.symm)
  -- Applying `Φ`, the summand `a ⊗ [β]` vanishes, which contradicts `a ≠ 0` and `[β] ≠ 0`.
  have h₁ := congrArg (fun φ ↦ φ.hom w) hFΦ
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h₁
  have h₂ := congrArg (fun φ ↦ φ.hom (a ⊗ₜ β))
    (GradedObject.Monoidal.ι_tensorHom (fun m ↦ 𝟙 ((TopPair.ofSubset A).singularHomology R m))
      (fun m ↦ ((TopPair.ofSubset B).singularHomologyπ S m :
        ((singularHomologyFunctor _ m).obj S).obj Y ⟶ _)) i j n h)
  have hι := (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono
    (GradedObject.Monoidal.ιTensorObj (fun m ↦ (TopPair.ofSubset A).singularHomology R m)
      (fun m ↦ (TopPair.ofSubset B).singularHomology S m) i j n h))
  exact TauCeti.tmul_ne_zero ha hβ
    (hι (h₂.symm.trans ((congrArg Φ.hom heq).trans (h₁.trans (map_zero _).symm))))

end NotFromSubspace

section Field

variable {K : Type w} [Field K] (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
  (R S : ModuleCat.{w} K)

/-- Over a field, the relative cross product `a × β ∈ Hₙ(X × Y, A × Y)` of a nonzero
`a ∈ Hᵢ(X, A)` with a class `β ∈ Hⱼ(Y)` not coming from `B` does not come from
`Hₙ(X × B, A × B)`: the Künneth hypotheses of
`TopCat.singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel` hold since all
modules over a field are semisimple and free. -/
theorem singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel_of_field
    {i j n : ℕ} (h : i + j = n)
    {a : ((TopPair.ofSubset A).singularHomology R i : ModuleCat.{w} K)}
    {β : (((singularHomologyFunctor _ j).obj S).obj Y : ModuleCat.{w} K)} (ha : a ≠ 0)
    (hβ : ((TopPair.ofSubset B).singularHomologyπ S j).hom β ≠ 0)
    (y : ((TopPair.ofSubset (fst X (TopCat.of B) ⁻¹' A)).singularHomology (R ⊗ S) n :
      ModuleCat.{w} K)) :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X ⊗ₘ (TopPair.ofSubset B).map)
      (mapsTo_tensorHom_preimage_fst _ _ fun _ hx ↦ hx)) (R ⊗ S) n).hom y ≠
        (singularHomologyCrossRel X Y A R S i j n h).hom (a ⊗ₜ β) :=
  -- Over a field the cycles and the homology of the singular chain complexes split off. These
  -- instances are provided by hand, since synthesizing them through the chain complexes times out.
  have := fun m ↦ HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule
    ((TopPair.ofSubset A).singularChainComplex R) m
  have := fun m ↦ HomologicalComplex.isSplitEpi_homologyπ_of_isSemisimpleModule
    ((TopPair.ofSubset A).singularChainComplex R) m
  have := fun m ↦ HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule
    ((toSSet.obj (TopCat.of B)).chainComplex S) m
  have := fun m ↦ HomologicalComplex.isSplitEpi_homologyπ_of_isSemisimpleModule
    ((toSSet.obj (TopCat.of B)).chainComplex S) m
  have := fun m ↦ HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule
    ((toSSet.obj Y).chainComplex S) m
  singularHomologyMap_ofSubsetMap_tensorHom_ne_singularHomologyCrossRel X Y A B R S h ha hβ y

end Field

end TopCat
