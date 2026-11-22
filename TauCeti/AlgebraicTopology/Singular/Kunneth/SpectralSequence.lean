/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# The Künneth spectral sequence for singular homology

Let `X` and `Y` be topological spaces and `R` a commutative ring, and let `C(X; R)` and `C(Y; R)`
be their singular chain complexes with coefficients in `R`, the tensor unit `𝟙_ (ModuleCat R)`.
The **Künneth spectral sequence** `TopCat.singularKunnethSpectralSequence R X Y` is the algebraic
Künneth spectral sequence `HomologicalComplex.kunnethSpectralSequence` of `C(X; R)` and `C(Y; R)`:
the spectral sequence of the column filtration of the Künneth bicomplex, whose column `p` is
`C(X; R) ⊗ Q.X p` for the Cartan–Eilenberg resolution `Q` of `C(Y; R)`. It is a first-quadrant
spectral sequence

`E²_{p,q} = ⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R)) ⟹ H_{p+q}(X × Y; R)`.

* **Second page.** The object of the second page (numbered `3`, see below) at column `p` and
  degree `q` is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`
  (`TopCat.singularKunnethSpectralSequenceSecondPageXIso`), by
  `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso`.
* **Abutment.** The abutment in total degree `n` is `Hₙ(X × Y; R)`
  (`TopCat.singularKunnethAbutmentIso`). By `HomologicalComplex₂.columnFiltrationAbutmentIso`,
  which accounts for the flip of the bicomplex, it is the homology of the total complex of the
  Künneth bicomplex. The singular chain modules are free, hence flat, so the augmentation of this
  total complex to `C(X; R) ⊗ C(Y; R)` is a quasi-isomorphism
  (`HomologicalComplex.quasiIso_kunnethBicomplexAugmentation`). The shuffle map
  `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R ⊗ R)` is a quasi-isomorphism by the Eilenberg–Zilber theorem
  (`TopCat.quasiIso_shuffle`), and the unitor `R ⊗ R ≅ R` identifies the coefficients.
* **Convergence.** The abutment `Hₙ(X × Y; R)` carries the increasing filtration by the pieces
  `TopCat.singularKunnethFiltration R X Y p n`, embedded by the monomorphisms
  `TopCat.singularKunnethFiltrationι` compatibly with the inclusions
  `TopCat.singularKunnethFiltrationMap` (`TopCat.singularKunnethFiltrationMap_ι`). It is finite:
  it vanishes for `p ≤ 0` (`TopCat.isZero_singularKunnethFiltration`) and is everything for
  `n < p` (`TopCat.isIso_singularKunnethFiltrationι`). The object at column `p` and degree `q`
  stabilizes from the page `r` with `p + 2 ≤ r` and `q + 2 < r` on, to the graded piece
  `F_{p+1} H_{p+q} / F_p H_{p+q}` (`TopCat.singularKunnethSpectralSequencePageXIsoGraded`).

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

/-- The simplicial chain modules `Cₙ(X; R) = ⨁ R` with coefficients in the tensor unit `R` of
`ModuleCat R` are flat, being projective (`SSet.projective_chainComplex_X`). -/
lemma SSet.flat_chainComplex_X_tensorUnit (R : Type u) [CommRing R] (X : SSet.{u}) (n : ℕ) :
    Module.Flat R ((X.chainComplex (𝟙_ (ModuleCat.{u} R))).X n) :=
  -- the projectivity instance for the unit is found directly only as a local instance, see
  -- `ModuleCat.projective_tensorUnit`
  have := ModuleCat.projective_tensorUnit R
  inferInstance

namespace TopCat

variable (R : Type u) [CommRing R] (X Y : TopCat.{u})

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
(`TopCat.singularKunnethAbutmentIso`, `TopCat.singularKunnethSpectralSequencePageXIsoGraded`). -/
abbrev singularKunnethSpectralSequence :=
  kunnethSpectralSequence ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{u} R)))
    ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat.{u} R)))

/-- **The second page of the singular Künneth spectral sequence.** The object of the second page
(numbered `3`) at column `p`, degree `q` is `⨁_{i + j = q} Torₚ(Hᵢ(X; R), Hⱼ(Y; R))`. -/
def singularKunnethSpectralSequenceSecondPageXIso (p q : ℕ) :
    ((singularKunnethSpectralSequence R X Y).page 3).X (-(q : ℤ) - 2 * p, p) ≅
      GradedObject.mapBifunctorMapObj (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
        (fun i ↦ ((singularHomologyFunctor _ i).obj (𝟙_ (ModuleCat.{u} R))).obj X)
        (fun j ↦ ((singularHomologyFunctor _ j).obj (𝟙_ (ModuleCat.{u} R))).obj Y) q :=
  -- the singular homology `Hᵢ(X; R)` is by definition the homology of `C(X; R)`
  kunnethSpectralSequenceSecondPageXIso _ _ p q

/-- The identification of the second page of the singular Künneth spectral sequence is that of
the algebraic Künneth spectral sequence of the singular chain complexes. -/
lemma singularKunnethSpectralSequenceSecondPageXIso_eq (p q : ℕ) :
    singularKunnethSpectralSequenceSecondPageXIso R X Y p q =
      kunnethSpectralSequenceSecondPageXIso _ _ p q :=
  (rfl)

/-- The homology of the total complex of the Künneth bicomplex of `C(X; R)` and `C(Y; R)` in
degree `n` is `Hₙ(X × Y; R)`: the augmentation to `C(X; R) ⊗ C(Y; R)` is a quasi-isomorphism since
the singular chain modules are flat, the shuffle map `C(X; R) ⊗ C(Y; R) ⟶ C(X × Y; R ⊗ R)` is a
quasi-isomorphism by the Eilenberg–Zilber theorem, and the unitor identifies `R ⊗ R` with `R`. -/
def singularKunnethTotalHomologyIso (n : ℕ) :
    ((singularKunnethBicomplex R X Y).total (ComplexShape.down ℕ)).homology n ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  have := SSet.flat_chainComplex_X_tensorUnit R (toSSet.obj X)
  have := quasiIso_kunnethBicomplexAugmentation ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat R)))
    ((toSSet.obj Y).chainComplex (𝟙_ (ModuleCat R)))
  -- the homology of `C(X × Y; R)` is by definition `Hₙ(X × Y; R)`; the ascription keeps the
  -- composite well typed up to reducible unfolding, so that `Iso.trans_hom` applies to it
  (isoOfQuasiIsoAt (kunnethBicomplexAugmentation _ _) n ≪≫
    isoOfQuasiIsoAt (shuffle X Y _ _) n ≪≫
    homologyMapIso (((SSet.chainComplexFunctor _).mapIso (λ_ (𝟙_ (ModuleCat.{u} R)))).app
      (toSSet.obj (X ⊗ Y))) n : _ ≅ ((toSSet.obj (X ⊗ Y)).chainComplex (𝟙_ _)).homology n)

/-- The identification `TopCat.singularKunnethTotalHomologyIso` is induced by the augmentation of
the total complex, followed by the shuffle map and the unitor. -/
lemma singularKunnethTotalHomologyIso_hom (n : ℕ) :
    (singularKunnethTotalHomologyIso R X Y n).hom =
      homologyMap (kunnethBicomplexAugmentation _ _) n ≫ homologyMap (shuffle X Y _ _) n ≫
        homologyMap (((SSet.chainComplexFunctor _).map (λ_ (𝟙_ (ModuleCat.{u} R))).hom).app
          (toSSet.obj (X ⊗ Y))) n := by
  rw [singularKunnethTotalHomologyIso, Iso.trans_hom, Iso.trans_hom, isoOfQuasiIsoAt_hom,
    isoOfQuasiIsoAt_hom, homologyMapIso_hom, Iso.app_hom, Functor.mapIso_hom]

/-- The spectral object of the filtration of the total complex of the flipped Künneth bicomplex of
`C(X; R)` and `C(Y; R)` by its rows, whose spectral sequence is
`TopCat.singularKunnethSpectralSequence R X Y`. Its abutment is `H(X × Y; R)`
(`TopCat.singularKunnethAbutmentIso`). -/
abbrev singularKunnethSpectralObject :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor
    (singularKunnethBicomplex R X Y).flip.rowFiltration
    (singularKunnethBicomplex R X Y).flip.monotone_rowFiltration)

/-- **The abutment of the singular Künneth spectral sequence.** The abutment in total degree `n`
(cohomological degree `-n`) is `Hₙ(X × Y; R)`. -/
def singularKunnethAbutmentIso (n : ℕ) :
    (singularKunnethSpectralObject R X Y).abutment (-n) ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  (singularKunnethBicomplex R X Y).columnFiltrationAbutmentIso n ≪≫
    singularKunnethTotalHomologyIso R X Y n

/-- The identification `TopCat.singularKunnethAbutmentIso` is that of the abutment of the column
filtration with the homology of the total complex, followed by
`TopCat.singularKunnethTotalHomologyIso`. -/
lemma singularKunnethAbutmentIso_eq (n : ℕ) :
    singularKunnethAbutmentIso R X Y n =
      (singularKunnethBicomplex R X Y).columnFiltrationAbutmentIso n ≪≫
        singularKunnethTotalHomologyIso R X Y n :=
  (rfl)

/-! ### Convergence -/

/-- The `p`th piece `F_p Hₙ(X × Y; R)` of the filtration of the abutment of the singular Künneth
spectral sequence in total degree `n`. It embeds into `Hₙ(X × Y; R)` by
`TopCat.singularKunnethFiltrationι`. -/
abbrev singularKunnethFiltration (p : ℤ) (n : ℕ) : ModuleCat.{u} R :=
  (singularKunnethSpectralObject R X Y).abutmentFiltration p (-n)

/-- The embedding of the `p`th piece of the filtration into `Hₙ(X × Y; R)`. -/
def singularKunnethFiltrationι (p : ℤ) (n : ℕ) :
    singularKunnethFiltration R X Y p n ⟶
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{u} R))).obj (X ⊗ Y) :=
  (singularKunnethSpectralObject R X Y).abutmentFiltrationι p (-n) ≫
    (singularKunnethAbutmentIso R X Y n).hom

/-- The embedding `TopCat.singularKunnethFiltrationι` is that of the filtration of the abutment,
followed by `TopCat.singularKunnethAbutmentIso`. -/
lemma singularKunnethFiltrationι_eq (p : ℤ) (n : ℕ) :
    singularKunnethFiltrationι R X Y p n =
      (singularKunnethSpectralObject R X Y).abutmentFiltrationι p (-n) ≫
        (singularKunnethAbutmentIso R X Y n).hom :=
  (rfl)

/-- The embedding of a filtration piece into `Hₙ(X × Y; R)` is a monomorphism. -/
instance (p : ℤ) (n : ℕ) : Mono (singularKunnethFiltrationι R X Y p n) := by
  rw [singularKunnethFiltrationι_eq]
  infer_instance

/-- The inclusion `F_p Hₙ(X × Y; R) ⟶ F_{p+1} Hₙ(X × Y; R)` of the filtration pieces. -/
def singularKunnethFiltrationMap (p : ℤ) (n : ℕ) :
    singularKunnethFiltration R X Y p n ⟶ singularKunnethFiltration R X Y (p + 1) n :=
  (singularKunnethSpectralObject R X Y).abutmentFiltrationMap p (-n)

/-- The inclusion `TopCat.singularKunnethFiltrationMap` is that of the filtration of the
abutment. -/
lemma singularKunnethFiltrationMap_eq (p : ℤ) (n : ℕ) :
    singularKunnethFiltrationMap R X Y p n =
      (singularKunnethSpectralObject R X Y).abutmentFiltrationMap p (-n) :=
  (rfl)

/-- The inclusion of consecutive filtration pieces is a monomorphism. -/
instance (p : ℤ) (n : ℕ) : Mono (singularKunnethFiltrationMap R X Y p n) := by
  rw [singularKunnethFiltrationMap_eq]
  infer_instance

/-- The filtration of `Hₙ(X × Y; R)` is increasing: the embeddings of the filtration pieces are
compatible with the inclusions `TopCat.singularKunnethFiltrationMap`. -/
@[reassoc (attr := simp)]
lemma singularKunnethFiltrationMap_ι (p : ℤ) (n : ℕ) :
    singularKunnethFiltrationMap R X Y p n ≫ singularKunnethFiltrationι R X Y (p + 1) n =
      singularKunnethFiltrationι R X Y p n := by
  rw [singularKunnethFiltrationMap_eq, singularKunnethFiltrationι_eq,
    singularKunnethFiltrationι_eq, Abelian.SpectralObject.abutmentFiltrationMap_ι_assoc]

/-- The filtration of `Hₙ(X × Y; R)` vanishes in the columns `p ≤ 0`. -/
lemma isZero_singularKunnethFiltration (p : ℤ) (hp : p ≤ 0) (n : ℕ) :
    IsZero (singularKunnethFiltration R X Y p n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _
    ((singularKunnethBicomplex R X Y).flip.rowFiltration_eq_bot p hp) _

/-- The filtration of `Hₙ(X × Y; R)` is exhaustive: its `p`th piece is everything for `n < p`. -/
lemma isIso_singularKunnethFiltrationι (p : ℤ) (n : ℕ) (h : n < p) :
    IsIso (singularKunnethFiltrationι R X Y p n) := by
  have := (singularKunnethBicomplex R X Y).flip.isIso_rowFiltration_abutmentFiltrationι p (-n)
    (by omega)
  rw [singularKunnethFiltrationι_eq]
  infer_instance

/-- **Convergence of the singular Künneth spectral sequence.** On every page `r` with `p + 2 ≤ r`
and `q + 2 < r`, the object at column `p`, degree `q` is the graded piece
`F_{p+1} H_{p+q}(X × Y; R) / F_p H_{p+q}(X × Y; R)` of the filtration of `H_{p+q}(X × Y; R)`. In
particular the object at a fixed position stabilizes after finitely many pages. -/
def singularKunnethSpectralSequencePageXIsoGraded (r : ℤ) (p q : ℕ) (h₀ : (p : ℤ) + 2 ≤ r)
    (h₃ : (q : ℤ) + 2 < r) :
    ((singularKunnethSpectralSequence R X Y).page r).X (-(q : ℤ) - 2 * p, p) ≅
      cokernel (singularKunnethFiltrationMap R X Y p (p + q)) :=
  (singularKunnethBicomplex R X Y).flip.rowFiltrationSpectralSequencePageXIsoEInfty r (by omega)
      _ h₀ (by dsimp; omega) ≪≫
    -- the total degree `-(q : ℤ) - 2 * p + p` is `-(p + q)`
    eqToIso (congrArg ((singularKunnethSpectralObject R X Y).EInfty p) (by push_cast; ring)) ≪≫
    (singularKunnethSpectralObject R X Y).EInftyIsoCokernel _ _

end TopCat
