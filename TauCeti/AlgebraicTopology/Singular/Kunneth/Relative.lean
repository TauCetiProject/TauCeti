/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative
import Mathlib.CategoryTheory.Limits.MonoCoprod

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
(`TopCat.singularHomologyKunnethRel`) is an isomorphism whenever the algebraic Künneth map of the
chain complexes is, for instance over a commutative semisimple ring such as a field
(`TopCat.isIso_singularHomologyKunnethRel`). Over such a ring the relative cross product is
therefore injective (`TopCat.mono_singularHomologyCrossRel`).

The pair is written with a subset rather than an arbitrary `TopPair` because relative homology
modulo the complement of a fibre, which this cross product is used to compute, is stated for
pairs of the form `TopPair.ofSubset`.

## Main definitions

* `TopCat.shuffleRel`: the relative shuffle map `C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B))`.
* `TopCat.singularHomologyCrossRel`: the relative cross product in singular homology.
* `TopCat.singularHomologyKunnethRel`: the relative Künneth map.

## Main results

* `TopCat.quasiIso_shuffleRel`: the relative Eilenberg–Zilber theorem.
* `TopCat.shuffleRel_naturality`, `TopCat.singularHomologyCrossRel_naturality`: naturality in maps
  of pairs `(X, B) ⟶ (X', B')` and in maps `Y ⟶ Y'`.
* `TopCat.singularHomologyCross_comp_singularHomologyπ`: the absolute cross product followed by
  the map to relative homology is the relative cross product of the image of the first factor.
* `TopCat.isIso_singularHomologyKunnethRel`: the relative Künneth theorem, and
  `TopCat.mono_singularHomologyCrossRel`: the injectivity of the relative cross product under the
  same hypotheses.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product and the relative Künneth formula.
* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 3.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe u

namespace TopCat

variable {k : Type u} [CommRing k] (X Y : TopCat.{u}) (B : Set X) (R S : ModuleCat.{u} k)

/-- The homeomorphism `B × Y ≅ fst⁻¹(B)` between the product of the subspace `B ⊆ X` with `Y`
and the preimage of `B` under the first projection `X × Y ⟶ X`. -/
def prodPreimageFstIso :
    (TopPair.ofSubset B).snd ⊗ Y ≅ (TopPair.ofSubset (fst X Y ⁻¹' B)).snd where
  hom := ofHom ⟨fun x ↦ ⟨((TopPair.ofSubset B).map ⊗ₘ 𝟙 Y) x, (fst (TopPair.ofSubset B).snd Y x).2⟩,
    ((TopPair.ofSubset B).map ⊗ₘ 𝟙 Y).hom.continuous.subtype_mk _⟩
  inv := lift (ofHom ⟨fun x ↦ ⟨fst X Y x.1, x.2⟩, by fun_prop⟩)
    ((TopPair.ofSubset (fst X Y ⁻¹' B)).map ≫ snd X Y)

/-- Followed by the inclusion of `fst⁻¹(B)` into `X × Y`, the homeomorphism `B × Y ≅ fst⁻¹(B)` is
the product of the inclusion of `B` with the identity of `Y`. -/
@[reassoc]
theorem prodPreimageFstIso_hom_comp_map :
    (prodPreimageFstIso X Y B).hom ≫ (TopPair.ofSubset (fst X Y ⁻¹' B)).map =
      (TopPair.ofSubset B).map ⊗ₘ 𝟙 Y :=
  (rfl)

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
theorem tensorHom_chainComplexMap_shuffle :
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
  -- The composite factors through the singular chains of `fst⁻¹(B)`, which `π` kills.
  refine (Category.assoc _ _ _).symm.trans ((tensorHom_chainComplexMap_shuffle X Y B R S =≫ _).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (TopPair.chainComplexMap_comp_singularChainComplexπ _ _)).trans
        Limits.comp_zero))).trans Limits.comp_zero)))

/-- **The relative shuffle map** `C(X, B; R) ⊗ C(Y; S) ⟶ C(X × Y, fst⁻¹(B); R ⊗ S)`, induced by
the shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` on the cokernels; it is characterized by
`TopCat.tensorHom_singularChainComplexπ_shuffleRel`. -/
def shuffleRel :
    (TopPair.ofSubset B).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplex (R ⊗ S) :=
  have hS := shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S
  have := hS.epi_g
  hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ (shuffle_cokernel_condition X Y B R S))

/-- The relative shuffle map is induced by the shuffle map: on `C(X; R) ⊗ C(Y; S)` it is the
shuffle map followed by the projection to the relative chains of `(X × Y, fst⁻¹(B))`. -/
@[reassoc (attr := simp)]
theorem tensorHom_singularChainComplexπ_shuffleRel :
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
theorem shuffleRel_naturality {X' Y' : TopCat.{u}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y') :
    (TopPair.singularChainComplexMap (TopPair.ofSubsetMap f hf) R ⊗ₘ
        SSet.chainComplexMap (toSSet.map g) S) ≫ shuffleRel X' Y' B' R S =
      shuffleRel X Y B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (fun _ hx ↦ hf hx)) (R ⊗ S) := by
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
    (tensorHom_comp_tensorHom _ _ _ _).trans <| (congrArg₂ (· ⊗ₘ ·)
      hπ.symm ((Category.id_comp _).trans (Category.comp_id _).symm)).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm
  have h₂ := TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (B := fst X Y ⁻¹' B) (B' := fst X' Y' ⁻¹' B') (f ⊗ₘ g)
      (fun _ hx ↦ hf hx)) (R ⊗ S)
  have hfst := TopPair.ofSubsetMap_fst (B := fst X Y ⁻¹' B) (B' := fst X' Y' ⁻¹' B') (f ⊗ₘ g)
    (fun _ hx ↦ hf hx)
  calc _ = (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ≫
        ((TopPair.ofSubset B').singularChainComplexπ R ⊗ₘ
          𝟙 ((toSSet.obj Y').chainComplex S)) ≫ shuffleRel X' Y' B' R S :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _))
    _ = shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S) :=
        (congrArg (_ ≫ ·) (tensorHom_singularChainComplexπ_shuffleRel X' Y' B' R S)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
            (shuffle_naturality f g R S)).trans (Category.assoc _ _ _)))
    _ = _ := (congrArg (fun φ ↦ shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map φ) (R ⊗ S) ≫
        (TopPair.ofSubset (fst X' Y' ⁻¹' B')).singularChainComplexπ (R ⊗ S)) hfst.symm).trans <|
      (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (tensorHom_singularChainComplexπ_shuffleRel X Y B R S).symm).trans
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
  comm₁₂ := ((tensorHom_chainComplexMap_shuffle X Y B R S).trans
    (Category.assoc _ _ _).symm).symm
  comm₂₃ := (tensorHom_singularChainComplexπ_shuffleRel X Y B R S).symm

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
instance quasiIso_shuffleRel : QuasiIso (shuffleRel X Y B R S) := by
  have h₁ : QuasiIso (shuffle (TopPair.ofSubset B).snd Y R S) := by
    rw [← eilenbergZilberHomotopyEquiv_inv]
    infer_instance
  have h₂ : QuasiIso (shuffle X Y R S) := by
    rw [← eilenbergZilberHomotopyEquiv_inv]
    infer_instance
  have h₃ : QuasiIso (SSet.chainComplexMap (toSSet.map (prodPreimageFstIso X Y B).hom) (R ⊗ S)) :=
    inferInstance
  exact HomologySequence.quasiIso_τ₃ (shuffleShortComplexMap X Y B R S)
    (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y B R S)
    ((TopPair.ofSubset (fst X Y ⁻¹' B)).shortExact_singularChainComplexShortComplex (R ⊗ S))
    (quasiIso_comp (hφ := h₁) (hφ' := h₃) _ _) h₂

/-- **The relative cross product** `Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` for
`p + q = n`: the cross product of the chain complexes `C(X, B; R)` and `C(Y; S)` followed by the
map induced by the relative shuffle map. -/
def singularHomologyCrossRel (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset B).singularHomology R p ⊗ ((singularHomologyFunctor _ q).obj S).obj Y ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyCross ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
    p q n h ≫ homologyMap (shuffleRel X Y B R S) n

/-- The relative cross product is the cross product of the chain complexes followed by the map
induced by the relative shuffle map. -/
theorem singularHomologyCrossRel_def (p q n : ℕ) (h : p + q = n) :
    singularHomologyCrossRel X Y B R S p q n h =
      homologyCross ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
        p q n h ≫ homologyMap (shuffleRel X Y B R S) n :=
  (rfl)

/-- **Naturality of the relative cross product** in maps of pairs `(X, B) ⟶ (X', B')` and in maps
`Y ⟶ Y'`: `f_* a × g_* b = (f × g)_* (a × b)`. -/
@[reassoc]
theorem singularHomologyCrossRel_naturality {X' Y' : TopCat.{u}} {B' : Set X'} (f : X ⟶ X')
    (hf : Set.MapsTo f B B') (g : Y ⟶ Y') (p q n : ℕ) (h : p + q = n) :
    (TopPair.singularHomologyMap (TopPair.ofSubsetMap f hf) R p ⊗ₘ
        ((singularHomologyFunctor _ q).obj S).map g) ≫
          singularHomologyCrossRel X' Y' B' R S p q n h =
      singularHomologyCrossRel X Y B R S p q n h ≫ TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (f ⊗ₘ g) (fun _ hx ↦ hf hx)) (R ⊗ S) n :=
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
theorem singularHomologyCross_comp_singularHomologyπ (p q n : ℕ) (h : p + q = n) :
    singularHomologyCross X Y R S p q n h ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomologyπ (R ⊗ S) n =
      ((TopPair.ofSubset B).singularHomologyπ R p ▷ ((singularHomologyFunctor _ q).obj S).obj Y) ≫
        singularHomologyCrossRel X Y B R S p q n h := by
  -- Naturality of the algebraic cross product along `π ⊗ 𝟙`, and the defining property of the
  -- relative shuffle map.
  have hn := homologyCross_naturality ((TopPair.ofSubset B).singularChainComplexπ R)
    (𝟙 ((toSSet.obj Y).chainComplex S)) p q n h
  rw [homologyMap_id, tensorHom_id] at hn
  refine (congrArg (· ≫ _) (singularHomologyCross_def X Y R S p q n h)).trans ?_
  exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (homologyMap_comp _ _ n).symm).trans <|
    (congrArg (fun φ ↦ _ ≫ homologyMap φ n)
      (tensorHom_singularChainComplexπ_shuffleRel X Y B R S).symm).trans <|
    (congrArg (_ ≫ ·) (homologyMap_comp _ _ n)).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ homologyMap (shuffleRel X Y B R S) n) hn.symm).trans (Category.assoc _ _ _)

/-- **The relative Künneth map**
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)`: the algebraic Künneth map of
the chain complexes `C(X, B; R)` and `C(Y; S)` followed by the map induced by the relative shuffle
map. -/
def singularHomologyKunnethRel (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) n ⟶
      (TopPair.ofSubset (fst X Y ⁻¹' B)).singularHomology (R ⊗ S) n :=
  homologyKunneth ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
    n ≫ homologyMap (shuffleRel X Y B R S) n

/-- The relative Künneth map is the algebraic Künneth map followed by the map induced by the
relative shuffle map. -/
theorem singularHomologyKunnethRel_def (n : ℕ) :
    singularHomologyKunnethRel X Y B R S n =
      homologyKunneth ((TopPair.ofSubset B).singularChainComplex R)
        ((toSSet.obj Y).chainComplex S) n ≫ homologyMap (shuffleRel X Y B R S) n :=
  (rfl)

/-- The relative Künneth map restricts to the relative cross product on each summand. -/
@[reassoc (attr := simp)]
theorem ι_singularHomologyKunnethRel (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
        (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) p q n h ≫
      singularHomologyKunnethRel X Y B R S n = singularHomologyCrossRel X Y B R S p q n h :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ homologyMap (shuffleRel X Y B R S) n) (ι_homologyKunneth _ _ n p q h))

/-- **The relative Künneth theorem**: if the cycles of `C(X, B; R)` and `C(Y; S)` split off their
terms and their homology splits off their cycles, the relative Künneth map
`⨁_{p + q = n} Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B); R ⊗ S)` is an isomorphism. This
holds for all coefficient modules over a commutative semisimple ring, for instance a field. -/
instance isIso_singularHomologyKunnethRel
    [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (n : ℕ) :
    IsIso (singularHomologyKunnethRel X Y B R S n) := by
  exact IsIso.comp_isIso'
    (isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi
      ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S) n)
    ((quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance)

/-- Under the hypotheses of the relative Künneth theorem, for instance over a commutative
semisimple ring, each relative cross product `Hₚ(X, B; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y, fst⁻¹(B))` is a
monomorphism: it is the inclusion of a summand followed by the relative Künneth isomorphism. -/
instance mono_singularHomologyCrossRel
    [∀ p, IsSplitMono (((TopPair.ofSubset B).singularChainComplex R).iCycles p)]
    [∀ p, IsSplitEpi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex S).iCycles q)]
    [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex S).homologyπ q)] (p q n : ℕ) (h : p + q = n) :
    Mono (singularHomologyCrossRel X Y B R S p q n h) := by
  -- The summand inclusion is the colimit inclusion of a coproduct, a monomorphism.
  have : Mono (GradedObject.Monoidal.ιTensorObj
      (fun p ↦ (TopPair.ofSubset B).singularHomology R p)
      (fun q ↦ ((singularHomologyFunctor _ q).obj S).obj Y) p q n h) :=
    by
      unfold GradedObject.Monoidal.ιTensorObj GradedObject.ιMapBifunctorMapObj GradedObject.ιMapObj
      exact CategoryTheory.Limits.MonoCoprod.mono_ι _ _
  exact ι_singularHomologyKunnethRel X Y B R S p q n h ▸ mono_comp _ _

end TopCat
