/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber

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
  (`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). The shuffle map
  `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R ⊗ R)` is the inverse of the Eilenberg–Zilber homotopy
  equivalence (`TopCat.eilenbergZilberHomotopyEquiv`), hence a quasi-isomorphism
  (`TopCat.quasiIso_shuffle`), and the unitor `R ⊗ R ≅ R` identifies the coefficients
  (`TopCat.singularKunnethTotalHomologyIso`).
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

Naturality in `X` and `Y`, the edge maps and the collapse corollaries are not treated here.

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
  kunnethBicomplex ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
    ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))

/-- **The Künneth spectral sequence for singular homology** of `X` and `Y` with coefficients in
the commutative ring `R`: the algebraic Künneth spectral sequence
`HomologicalComplex.kunnethSpectralSequence` of the singular chain complexes `C(X; R)` and
`C(Y; R)`. Its second page is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`
(`TopCat.singularKunnethSpectralSequenceSecondPageXIso`) and it converges to `H_{p+q}(X × Y; R)`
(`TopCat.singularKunnethAbutmentIso`). -/
abbrev singularKunnethSpectralSequence :=
  kunnethSpectralSequence ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
    ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))

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
`C(X; R) ⊗ C(Y; R)`, the shuffle map `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R ⊗ R)` and the coefficient
unitor `R ⊗ R ≅ R` (`TopCat.singularKunnethTotalHomologyIso_hom`). -/
def singularKunnethTotalHomologyIso (n : ℕ) :
    ((singularKunnethBicomplex X Y R).total (ComplexShape.down ℕ)).homology n ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  -- the unit `𝟙_ (ModuleCat R)` is `R`, so the singular chain modules are flat
  have : Module.Flat R (𝟙_ (ModuleCat.{u} R)) := inferInstanceAs (Module.Flat R R)
  have := quasiIso_kunnethBicomplexAugmentation
    ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
    ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))
  -- the homology of `C(X × Y; R)` is by definition `Hₙ(X × Y; R)`; the ascription keeps the
  -- composite well typed up to reducible unfolding, so that `Iso.trans_hom` applies to it
  (isoOfQuasiIsoAt (kunnethBicomplexAugmentation
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
      ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))) n ≪≫
    isoOfQuasiIsoAt (shuffle X Y (𝟙_ (ModuleCat.{u} R)) (𝟙_ _)) n ≪≫
    asIso (homologyMap (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{u} R))).hom).app
      (toSSet.obj (X ⊗ Y))) n) :
      _ ≅ (((SSet.chainComplexFunctor _).obj (𝟙_ _)).obj (toSSet.obj (X ⊗ Y))).homology n)

/-- The isomorphism `TopCat.singularKunnethTotalHomologyIso` is induced by the augmentation of the
total complex, followed by the shuffle map and the unitor. -/
lemma singularKunnethTotalHomologyIso_hom (n : ℕ) :
    (singularKunnethTotalHomologyIso X Y R n).hom =
      homologyMap (kunnethBicomplexAugmentation
          ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
          ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))) n ≫
        homologyMap (shuffle X Y (𝟙_ (ModuleCat.{u} R)) (𝟙_ _)) n ≫
        homologyMap (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{u} R))).hom).app
          (toSSet.obj (X ⊗ Y))) n := by
  simp only [singularKunnethTotalHomologyIso, Iso.trans_hom, isoOfQuasiIsoAt_hom, asIso_hom]
  -- the two sides agree syntactically except for the proofs of the `Prop`-valued instance
  -- arguments (`HasHomology`, `HasCoproducts`), which simp does not identify
  with_reducible rfl

/-- The spectral object of the filtration of the total complex of the flipped Künneth bicomplex of
`C(X; R)` and `C(Y; R)` by its rows, whose spectral sequence is
`TopCat.singularKunnethSpectralSequence X Y R`. Its abutment is `H(X × Y; R)`
(`TopCat.singularKunnethAbutmentIso`). -/
abbrev singularKunnethSpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor
    (singularKunnethBicomplex X Y R).flip.rowFiltration
    (singularKunnethBicomplex X Y R).flip.monotone_rowFiltration)

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

end TopCat
