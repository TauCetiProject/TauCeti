/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Naturality
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.CrossProduct

/-!
# The Künneth spectral sequence for singular homology

Let `X` and `Y` be topological spaces and `R` a commutative ring, and let `C(X; R)` and `C(Y; R)`
be their singular chain complexes with coefficients in `R`, the tensor unit `𝟙_ (ModuleCat R)`.
The **Künneth spectral sequence** `TopCat.singularKunnethSpectralSequence X Y R` is the algebraic
Künneth spectral sequence `HomologicalComplex.kunnethSpectralSequence` of `C(X; R)` and `C(Y; R)`:
the spectral sequence of the column filtration of the Künneth bicomplex, whose column `p` is
`C(X; R) ⊗ Q.X p` for the Cartan–Eilenberg resolution `Q` of `C(Y; R)`. It is a first-quadrant
spectral sequence

`E²_{p,q} = ⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R)) ⟹ H_{p+q}(X × Y; R)`.

* **Second page.** The object of the second page (numbered `3`, see below) at column `p` and
  degree `q` is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`
  (`TopCat.singularKunnethSpectralSequenceSecondPageXIso`), by
  `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`. Outside the first quadrant every
  page vanishes (`HomologicalComplex₂.isZero_rowFiltrationSpectralSequence_page_X`, applied to
  the flipped bicomplex `(TopCat.singularKunnethBicomplex X Y R).flip`).
* **Abutment.** The abutment in total degree `n` is `Hₙ(X × Y; R)`
  (`TopCat.singularKunnethAbutmentIso`). By `HomologicalComplex₂.columnFiltrationAbutmentIso`,
  which accounts for the flip of the bicomplex, it is the homology of the total complex of the
  Künneth bicomplex. The singular chain modules are free, hence flat
  (`SSet.flat_chainComplex_X`), so the augmentation of this total complex to
  `C(X; R) ⊗ C(Y; R)` is a quasi-isomorphism
  (`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). The simplicial cross product
  `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R)` (`TauCeti.singularCrossProduct`), the shuffle map followed
  by the coefficient unitor `R ⊗ R ≅ R`, is a quasi-isomorphism by the Eilenberg–Zilber theorem
  (`TauCeti.quasiIso_singularCrossProduct`). Together they give
  `TopCat.singularKunnethTotalHomologyIso`.
* **Convergence.** Write `S` for `TopCat.singularKunnethSpectralObject X Y R`. The abutment
  `Hₙ(X × Y; R)` carries the increasing filtration whose `p`th piece `F_p Hₙ(X × Y; R)` is
  `S.abutmentFiltration p (-n)`: the image of the homology of the part of the total complex coming
  from the columns strictly below `p`. It embeds into `Hₙ(X × Y; R)` by the monomorphism
  `TopCat.singularKunnethFiltrationι`, compatibly with the inclusions
  `S.abutmentFiltrationMap p (-n)` (`TopCat.abutmentFiltrationMap_singularKunnethFiltrationι`).
  The filtration is finite: `F_p` vanishes for `p ≤ 0`
  (`HomologicalComplex₂.isZero_rowFiltration_abutmentFiltration`) and is everything for `n < p`
  (`TopCat.isIso_singularKunnethFiltrationι`). The object at column `p` and degree `q`
  stabilizes from the page `r` with `p + 2 ≤ r` and `q + 2 < r` on, to the graded piece
  `F_{p+1} H_{p+q} / F_p H_{p+q}`: with `B := TopCat.singularKunnethBicomplex X Y R`, the
  composite

  ```
  B.flip.rowFiltrationSpectralSequencePageXIsoEInfty r hr (-(q : ℤ) - 2 * p, p)
      (-((p + q : ℕ) : ℤ)) hn h₀ h₃ ≪≫ S.EInftyIsoCokernel p (-((p + q : ℕ) : ℤ))
  ```

  where `hr`, `hn`, `h₀` and `h₃` are the arithmetic hypotheses `2 ≤ r`,
  `-(p + q) = (-q - 2p) + p`, `p + 2 ≤ r` and `2 < (-q - 2p) + 2p + r`, identifies the page-`r`
  object at `(-q - 2p, p)` with
  `cokernel (S.abutmentFiltrationMap p (-(p + q)))`, its `hom` being the composite of the two
  `hom`s (`Iso.trans_hom`, `HomologicalComplex₂.rowFiltrationSpectralSequencePageXIsoEInfty_hom`).

* **Naturality in `X`.** A map `g : X ⟶ X'` induces a morphism of spectral sequences
  `TopCat.singularKunnethSpectralSequenceMap Y R g`, functorially in `g`, through the morphism
  `g_* ▷ Q.X p` of Künneth bicomplexes (`HomologicalComplex.kunnethBicomplexMapLeft`). On the
  abutment it is `(g × 𝟙)_* : Hₙ(X × Y; R) ⟶ Hₙ(X' × Y; R)`
  (`TopCat.singularKunnethAbutmentIso_naturality`).

Naturality in `Y`, which needs a comparison of Cartan–Eilenberg resolutions, the identification
of the second page naturality with the map induced on `Tor`, the edge maps and the collapse
corollaries are not treated here.

## Indexing

Pages are numbered as in `HomologicalComplex₂.columnFiltrationSpectralSequence`, following
Mathlib's cohomological convention `coreE₂Cohomological`: the first page (`E¹`) is `page 2` and
the second page (`E²`) is `page 3`, and the object at column `p` and degree `q` sits at
`(-q - 2p, p)`. The abutment in chain degree `n` sits in cohomological degree `-n`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 5.6.4 (the Künneth spectral sequence) and Application 5.6.5.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.20.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe u

namespace TopCat

variable (X Y : TopCat.{u}) (R : Type u) [CommRing R]

/-- The Künneth bicomplex `HomologicalComplex.kunnethBicomplex` of the singular chain complexes
`C(X; R)` and `C(Y; R)`: its column `p` is `C(X; R) ⊗ Q.X p` for the Cartan–Eilenberg resolution
`Q` of `C(Y; R)`. -/
abbrev singularKunnethBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  kunnethBicomplex ((TauCeti.singularChains R).obj X) ((TauCeti.singularChains R).obj Y)

/-- **The Künneth spectral sequence for singular homology** of `X` and `Y` with coefficients in
the commutative ring `R`: the algebraic Künneth spectral sequence
`HomologicalComplex.kunnethSpectralSequence` of the singular chain complexes `C(X; R)` and
`C(Y; R)`. Its second page is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`
(`TopCat.singularKunnethSpectralSequenceSecondPageXIso`) and it converges to `H_{p+q}(X × Y; R)`
(`TopCat.singularKunnethAbutmentIso`). -/
abbrev singularKunnethSpectralSequence :=
  kunnethSpectralSequence ((TauCeti.singularChains R).obj X) ((TauCeti.singularChains R).obj Y)

/-- **The second page of the singular Künneth spectral sequence.** The object of the second page
(numbered `3`) at column `p`, degree `q` is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`: this is
`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` for the singular chain complexes,
whose homology is by definition singular homology. -/
abbrev singularKunnethSpectralSequenceSecondPageXIso (p q : ℕ) :
    ((singularKunnethSpectralSequence X Y R).page 3).X (-(q : ℤ) - 2 * p, p) ≅
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
        (fun i ↦ ((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)
        (fun j ↦ ((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y) q :=
  kunnethSpectralSequenceSecondPageXIso _ _ p q

/-- **The total homology of the singular Künneth bicomplex** is `Hₙ(X × Y; R)`. The isomorphism is
induced on degree-`n` homology by, in this order, the augmentation of the total complex to
`C(X; R) ⊗ C(Y; R)` and the simplicial cross product `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R)`
(`TopCat.singularKunnethTotalHomologyIso_hom`). -/
def singularKunnethTotalHomologyIso (n : ℕ) :
    ((singularKunnethBicomplex X Y R).total (ComplexShape.down ℕ)).homology n ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  -- the singular chain modules, with coefficients the flat module `R`, are flat
  have (Z : TopCat.{u}) (i : ℕ) : Module.Flat R (((TauCeti.singularChains R).obj Z).X i) :=
    SSet.flat_chainComplex_X (toSSet.obj Z) (ModuleCat.of R R) i
  have := quasiIso_kunnethBicomplexAugmentation ((TauCeti.singularChains R).obj X)
    ((TauCeti.singularChains R).obj Y)
  -- the homology of `C(X × Y; R)` is by definition `Hₙ(X × Y; R)`
  isoOfQuasiIsoAt (kunnethBicomplexAugmentation ((TauCeti.singularChains R).obj X)
    ((TauCeti.singularChains R).obj Y) ≫ TauCeti.singularCrossProduct R X Y) n

/-- The isomorphism `TopCat.singularKunnethTotalHomologyIso` is induced by the augmentation of the
total complex, followed by the simplicial cross product. -/
lemma singularKunnethTotalHomologyIso_hom (n : ℕ) :
    (singularKunnethTotalHomologyIso X Y R n).hom =
      homologyMap (kunnethBicomplexAugmentation
          ((TauCeti.singularChains R).obj X) ((TauCeti.singularChains R).obj Y)) n ≫
        homologyMap (TauCeti.singularCrossProduct R X Y) n := by
  rw [singularKunnethTotalHomologyIso, isoOfQuasiIsoAt_hom, homologyMap_comp]

/-- The spectral object of the filtration of the total complex of the flipped Künneth bicomplex of
`C(X; R)` and `C(Y; R)` by its rows, whose spectral sequence is
`TopCat.singularKunnethSpectralSequence X Y R`. Its abutment is `H(X × Y; R)`
(`TopCat.singularKunnethAbutmentIso`). -/
abbrev singularKunnethSpectralObject :=
  (singularKunnethBicomplex X Y R).flip.rowFiltrationSpectralObject

/-- **The abutment of the singular Künneth spectral sequence.** The abutment in total degree `n`
(cohomological degree `-n`) is `Hₙ(X × Y; R)`. -/
def singularKunnethAbutmentIso (n : ℕ) :
    (singularKunnethSpectralObject X Y R).abutment (-n) ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  (singularKunnethBicomplex X Y R).columnFiltrationAbutmentIso n ≪≫
    singularKunnethTotalHomologyIso X Y R n

/-- The identification `TopCat.singularKunnethAbutmentIso` is that of the abutment of the column
filtration with the homology of the total complex, followed by
`TopCat.singularKunnethTotalHomologyIso`. -/
lemma singularKunnethAbutmentIso_eq (n : ℕ) :
    singularKunnethAbutmentIso X Y R n =
      (singularKunnethBicomplex X Y R).columnFiltrationAbutmentIso n ≪≫
        singularKunnethTotalHomologyIso X Y R n :=
  (rfl)

/-! ### Convergence -/

/-- The embedding into `Hₙ(X × Y; R)` of the `p`th piece `F_p Hₙ(X × Y; R)` of the filtration of
the abutment, the image of the homology of the part of the total complex coming from the columns
strictly below `p`. -/
def singularKunnethFiltrationι (p : ℤ) (n : ℕ) :
    (singularKunnethSpectralObject X Y R).abutmentFiltration p (-n) ⟶
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  (singularKunnethSpectralObject X Y R).abutmentFiltrationι p (-n) ≫
    (singularKunnethAbutmentIso X Y R n).hom

/-- The embedding `TopCat.singularKunnethFiltrationι` is that of the filtration of the abutment,
followed by `TopCat.singularKunnethAbutmentIso`. -/
lemma singularKunnethFiltrationι_eq (p : ℤ) (n : ℕ) :
    singularKunnethFiltrationι X Y R p n =
      (singularKunnethSpectralObject X Y R).abutmentFiltrationι p (-n) ≫
        (singularKunnethAbutmentIso X Y R n).hom :=
  (rfl)

/-- The embedding of a filtration piece into `Hₙ(X × Y; R)` is a monomorphism. -/
instance (p : ℤ) (n : ℕ) : Mono (singularKunnethFiltrationι X Y R p n) := by
  rw [singularKunnethFiltrationι_eq]
  infer_instance

/-- The filtration of `Hₙ(X × Y; R)` is increasing: the embeddings of the filtration pieces are
compatible with the inclusions `F_p ⟶ F_{p+1}` of the filtration of the abutment. -/
@[reassoc (attr := simp)]
lemma abutmentFiltrationMap_singularKunnethFiltrationι (p : ℤ) (n : ℕ) :
    (singularKunnethSpectralObject X Y R).abutmentFiltrationMap p (-n) ≫
        singularKunnethFiltrationι X Y R (p + 1) n =
      singularKunnethFiltrationι X Y R p n := by
  simp only [singularKunnethFiltrationι_eq,
    Abelian.SpectralObject.abutmentFiltrationMap_ι_assoc]

/-- The filtration of `Hₙ(X × Y; R)` is exhaustive: its `p`th piece is everything for `n < p`. -/
lemma isIso_singularKunnethFiltrationι (p : ℤ) (n : ℕ) (h : n < p) :
    IsIso (singularKunnethFiltrationι X Y R p n) := by
  have := (singularKunnethBicomplex X Y R).flip.isIso_rowFiltration_abutmentFiltrationι p (-n)
    (by omega)
  rw [singularKunnethFiltrationι_eq]
  infer_instance

/-! ### Naturality in the first space -/

variable {X} {X' X'' : TopCat.{u}} (g : X ⟶ X') (g' : X' ⟶ X'')

/-- The morphism of singular Künneth bicomplexes induced by a map `g : X ⟶ X'`: on column `p` it
is `g_* ▷ Q.X p`, for the Cartan–Eilenberg resolution `Q` of `C(Y; R)`. -/
abbrev singularKunnethBicomplexMap :
    singularKunnethBicomplex X Y R ⟶ singularKunnethBicomplex X' Y R :=
  kunnethBicomplexMapLeft ((TauCeti.singularChains R).map g) ((TauCeti.singularChains R).obj Y)

/-- The morphism of the spectral objects of the singular Künneth spectral sequences induced by a
map `g : X ⟶ X'`. -/
abbrev singularKunnethSpectralObjectMap :
    singularKunnethSpectralObject X Y R ⟶ singularKunnethSpectralObject X' Y R :=
  HomologicalComplex₂.rowFiltrationSpectralObjectMap
    ((HomologicalComplex₂.flipFunctor _ _ _).map (singularKunnethBicomplexMap Y R g))

/-- **Naturality of the singular Künneth spectral sequence in the first space**: the morphism of
spectral sequences induced by a map `g : X ⟶ X'`. It is compatible with identities and
composition (`TopCat.singularKunnethSpectralSequenceMap_id`,
`TopCat.singularKunnethSpectralSequenceMap_comp`) and, on the abutment, it is the map
`(g × 𝟙)_* : Hₙ(X × Y; R) ⟶ Hₙ(X' × Y; R)` (`TopCat.singularKunnethAbutmentIso_naturality`). -/
abbrev singularKunnethSpectralSequenceMap :
    singularKunnethSpectralSequence X Y R ⟶ singularKunnethSpectralSequence X' Y R :=
  kunnethSpectralSequenceMapLeft ((TauCeti.singularChains R).map g)
    ((TauCeti.singularChains R).obj Y)

@[simp]
lemma singularKunnethBicomplexMap_id : singularKunnethBicomplexMap Y R (𝟙 X) = 𝟙 _ := by
  rw [singularKunnethBicomplexMap, CategoryTheory.Functor.map_id, kunnethBicomplexMapLeft_id]

@[simp]
lemma singularKunnethBicomplexMap_comp :
    singularKunnethBicomplexMap Y R (g ≫ g') =
      singularKunnethBicomplexMap Y R g ≫ singularKunnethBicomplexMap Y R g' := by
  rw [singularKunnethBicomplexMap, CategoryTheory.Functor.map_comp, kunnethBicomplexMapLeft_comp]

@[simp]
lemma singularKunnethSpectralObjectMap_id :
    singularKunnethSpectralObjectMap Y R (𝟙 X) = 𝟙 _ := by
  rw [singularKunnethSpectralObjectMap, singularKunnethBicomplexMap_id,
    CategoryTheory.Functor.map_id]
  -- the identity of `(flipFunctor _ _ _).obj B` is that of `B.flip` only after unfolding
  -- `flipFunctor`
  exact HomologicalComplex₂.rowFiltrationSpectralObjectMap_id

@[simp]
lemma singularKunnethSpectralObjectMap_comp :
    singularKunnethSpectralObjectMap Y R (g ≫ g') =
      singularKunnethSpectralObjectMap Y R g ≫ singularKunnethSpectralObjectMap Y R g' := by
  rw [singularKunnethSpectralObjectMap, singularKunnethBicomplexMap_comp,
    CategoryTheory.Functor.map_comp, HomologicalComplex₂.rowFiltrationSpectralObjectMap_comp]

@[simp]
lemma singularKunnethSpectralSequenceMap_id :
    singularKunnethSpectralSequenceMap Y R (𝟙 X) = 𝟙 _ := by
  rw [singularKunnethSpectralSequenceMap, CategoryTheory.Functor.map_id,
    kunnethSpectralSequenceMapLeft_id]

@[simp]
lemma singularKunnethSpectralSequenceMap_comp :
    singularKunnethSpectralSequenceMap Y R (g ≫ g') =
      singularKunnethSpectralSequenceMap Y R g ≫ singularKunnethSpectralSequenceMap Y R g' := by
  rw [singularKunnethSpectralSequenceMap, CategoryTheory.Functor.map_comp,
    kunnethSpectralSequenceMapLeft_comp]

/-- The comparison `TopCat.singularKunnethTotalHomologyIso` of the total homology of the singular
Künneth bicomplex with `Hₙ(X × Y; R)` is natural in `X`. -/
@[reassoc]
lemma singularKunnethTotalHomologyIso_naturality (n : ℕ) :
    homologyMap (HomologicalComplex₂.total.map (singularKunnethBicomplexMap Y R g)
        (ComplexShape.down ℕ)) n ≫ (singularKunnethTotalHomologyIso X' Y R n).hom =
      (singularKunnethTotalHomologyIso X Y R n).hom ≫
        ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).map (g ▷ Y) := by
  -- the cross product is natural in the first space
  have h := TauCeti.singularCrossProduct_naturality R g (𝟙 Y)
  rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
  have h' : HomologicalComplex₂.total.map (singularKunnethBicomplexMap Y R g)
        (ComplexShape.down ℕ) ≫ kunnethBicomplexAugmentation ((TauCeti.singularChains R).obj X')
          ((TauCeti.singularChains R).obj Y) ≫ TauCeti.singularCrossProduct R X' Y =
      (kunnethBicomplexAugmentation ((TauCeti.singularChains R).obj X)
          ((TauCeti.singularChains R).obj Y) ≫ TauCeti.singularCrossProduct R X Y) ≫
        (TauCeti.singularChains R).map (g ▷ Y) := by
    rw [total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation_assoc, h, Category.assoc]
  rw [singularKunnethTotalHomologyIso, singularKunnethTotalHomologyIso, isoOfQuasiIsoAt_hom,
    isoOfQuasiIsoAt_hom]
  -- the map induced on singular homology is by definition that induced on the singular chains,
  -- so the two sides are the maps induced on homology by the two sides of `h'`
  exact (homologyMap_comp _ _ n).symm.trans
    ((congrArg (homologyMap · n) h').trans (homologyMap_comp _ _ n))

/-- **Naturality on the abutment.** Through `TopCat.singularKunnethAbutmentIso`, the morphism of
spectral objects induced by `g : X ⟶ X'` is, on the abutment in degree `n`, the map
`(g × 𝟙)_* : Hₙ(X × Y; R) ⟶ Hₙ(X' × Y; R)`. -/
@[reassoc]
lemma singularKunnethAbutmentIso_naturality (n : ℕ) :
    ((singularKunnethSpectralObjectMap Y R g).hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (singularKunnethAbutmentIso X' Y R n).hom =
      (singularKunnethAbutmentIso X Y R n).hom ≫
        ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).map (g ▷ Y) := by
  rw [singularKunnethAbutmentIso_eq, singularKunnethAbutmentIso_eq, Iso.trans_hom, Iso.trans_hom,
    HomologicalComplex₂.columnFiltrationSpectralObjectMap_abutment_naturality_assoc,
    singularKunnethTotalHomologyIso_naturality, Category.assoc]

end TopCat
