/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.DifferentialTransport
public import TauCeti.CategoryTheory.Abelian.Injective.Resolution
public import TauCeti.CategoryTheory.Sites.Over.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.SecondPage
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Over

/-!
# The Čech-to-cohomology spectral sequence of a covering of an object

Let `(C, J)` be a site, `V : C`, and `f i : u i ⟶ V` a family of morphisms generating a covering
sieve of `V`, and let `F` be an abelian sheaf on `C` with an injective resolution `R`. On the
localized site `J.over V`, whose terminal object is `Over.mk (𝟙 V)`, the objects `Over.mk (f i)`
cover the site (`CategoryTheory.GrothendieckTopology.coversTop_over_mk_iff`), and the restriction
of `R` is an injective resolution of the restriction of `F`. The Čech-to-cohomology spectral
sequence of `TauCeti.CategoryTheory.cechToCohomologySpectralSequence` for this covering of a site is
therefore the Čech-to-cohomology spectral sequence of the covering `f` of `V`
(`TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequence`).

Restriction to `J.over V` and its left adjoint are exact. This file states the spectral sequence
in terms of the cohomology of `F` on `C`, through the comparison
`CategoryTheory.GrothendieckTopology.cohomologyPresheafFunctorOverIso` of the cohomology presheaf of
the restricted sheaf with the restriction of the cohomology presheaf `W ↦ Hᵏ(W, F)`:

* its object at `(-k - 2p, p)` on the first page (numbered `2`) is the opposite of the group
  `Čᵖ(U, Hᵏ(F))` of Čech cochains of degree `p` of the presheaf `Hᵏ(-, F)` restricted to `Over V`,
  that is, of the product of the groups `Hᵏ(u (a 0) ×_V ⋯ ×_V u (a p), F)`
  (`TauCeti.CategoryTheory.cechToCohomologyOverFirstPageXIso`);
* the differential of the first page is, up to the sign `(-1)^k`, the Čech differential of that
  presheaf (`TauCeti.CategoryTheory.cechToCohomologyOverSpectralSequence_page_two_d`), so that the
  objects of the second page are the Čech cohomology groups `Hᵖ(U, Hᵏ(F))`
  (`TauCeti.CategoryTheory.cechToCohomologyOverSecondPageXIso`);
* its abutment in degree `-n` is the opposite of `Hⁿ(V, F)`
  (`TauCeti.CategoryTheory.cechToCohomologyOverAbutmentIso`).

As for a covering of a site, the spectral sequence is formed in the opposite category of abelian
groups, and each of its objects is the opposite of the expected group.

## References

* The reduction to the localized site `J.over V` and the comparison of its cohomology with the
  cohomology on `C` follow the
  [lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/877ee6253118ae038b46aca137f48841db354fe9)
  of the Leray and Čech spectral sequences.

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech
  cohomology and cohomology, Lemma 21.10.6 (tag 03AZ) for the spectral sequence.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {V : C}
  [HasFiniteProducts (Over V)] [HasSheafify J AddCommGrpCat.{v}]
  [HasSheafify (J.over V) AddCommGrpCat.{v}]
  {ι : Type v} {u : ι → C} (f : ∀ i, u i ⟶ V) {F : Sheaf J AddCommGrpCat.{v}}
  (R : InjectiveResolution F)

/-- **The Čech-to-cohomology spectral sequence of a covering of an object.** For a family of
morphisms `f i : u i ⟶ V` and an injective resolution `R` of an abelian sheaf `F`, it is the
Čech-to-cohomology spectral sequence of the objects `Over.mk (f i)` of the localized site
`J.over V`, built from the restriction of `R`. Its first page is the group of Čech cochains of the
presheaf `Hᵏ(-, F)` restricted to `Over V` (`cechToCohomologyOverFirstPageXIso`), and when `f`
generates a covering sieve of `V` it converges to `Hⁿ(V, F)` (`cechToCohomologyOverAbutmentIso`). -/
abbrev cechToCohomologyOverSpectralSequence :=
  cechToCohomologySpectralSequence (fun i ↦ Over.mk (f i))
    ((J.overPullback AddCommGrpCat.{v} V).mapInjectiveResolution R)

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf (J.over V) AddCommGrpCat.{v})]

/-- **The abutment of the Čech-to-cohomology spectral sequence of a covering.** If the morphisms
`f i : u i ⟶ V` generate a covering sieve of `V`, the abutment in degree `-n` of the
Čech-to-cohomology spectral sequence of `f` is the opposite of the sheaf cohomology `Hⁿ(V, F)`. -/
def cechToCohomologyOverAbutmentIso (hf : Sieve.ofArrows u f ∈ J V) (n : ℕ) :
    (presheafCechDoubleComplexSpectralObject (fun i ↦ Over.mk (f i))
      ((J.overPullback AddCommGrpCat.{v} V).mapInjectiveResolution R).presheafComplex).abutment
        (-n) ≅ op (F.H' n V) :=
  cechToCohomologyAbutmentIso (fun i ↦ Over.mk (f i)) Over.mkIdTerminal
    ((J.coversTop_over_mk_iff f).2 hf) _ n ≪≫ (F.cohomologyPresheafObjIsoOverH n V).op

/-- The identification of the abutment is that of the covering of the localized site, followed by
the comparison of the cohomology at `V` with that of the restricted sheaf. -/
lemma cechToCohomologyOverAbutmentIso_hom (hf : Sieve.ofArrows u f ∈ J V) (n : ℕ) :
    (cechToCohomologyOverAbutmentIso f R hf n).hom =
      (cechToCohomologyAbutmentIso (fun i ↦ Over.mk (f i)) Over.mkIdTerminal
        ((J.coversTop_over_mk_iff f).2 hf) _ n).hom ≫
          (F.cohomologyPresheafObjIsoOverH n V).hom.op :=
  (rfl)

/-- **The first page of the Čech-to-cohomology spectral sequence of a covering.** Its object at
`(-k - 2p, p)` (the first page being numbered `2`) is the opposite of the group `Čᵖ(U, Hᵏ(F))` of
Čech cochains of degree `p`, for the family `Over.mk (f i)`, of the cohomology presheaf
`W ↦ Hᵏ(W, F)` restricted to `Over V`: the product, over `a : Fin (p + 1) → ι`, of the groups
`Hᵏ(u (a 0) ×_V ⋯ ×_V u (a p), F)`. -/
def cechToCohomologyOverFirstPageXIso (p k : ℕ) :
    ((cechToCohomologyOverSpectralSequence f R).page 2).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor (fun i ↦ Over.mk (f i))).obj
        ((Over.forget V).op ⋙ F.cohomologyPresheaf k)).X p) :=
  cechToCohomologyFirstPageXIso (fun i ↦ Over.mk (f i)) _ p k ≪≫
    ((cechComplexFunctor (fun i ↦ Over.mk (f i)) ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℕ) p).mapIso
        ((J.cohomologyPresheafFunctorOverIso V k).app F)).op

/-- The identification of the first page is that of the covering of the localized site, followed
by the comparison of the cohomology presheaf of the restricted sheaf with the restriction of the
cohomology presheaf. -/
lemma cechToCohomologyOverFirstPageXIso_hom (p k : ℕ) :
    (cechToCohomologyOverFirstPageXIso f R p k).hom =
      (cechToCohomologyFirstPageXIso (fun i ↦ Over.mk (f i))
        ((J.overPullback AddCommGrpCat.{v} V).mapInjectiveResolution R) p k).hom ≫
        (((cechComplexFunctor (fun i ↦ Over.mk (f i))).map
          ((J.cohomologyPresheafFunctorOverIso V k).hom.app F)).f p).op :=
  (rfl)

/-- **The second page of the Čech-to-cohomology spectral sequence of a covering.** Its object at
`(-k - 2p, p)` (the first page being numbered `2`) is the opposite of the Čech cohomology group
`Hᵖ(Č(U, Hᵏ(F)))`, computed from the restriction to `Over V` of the ambient cohomology presheaf. -/
def cechToCohomologyOverSecondPageXIso (p k : ℕ) :
    ((cechToCohomologyOverSpectralSequence f R).page 3).X (-(k : ℤ) - 2 * p, p) ≅
      op (((cechComplexFunctor (fun i ↦ Over.mk (f i))).obj
        ((Over.forget V).op ⋙ F.cohomologyPresheaf k)).homology p) :=
  cechToCohomologySecondPageXIso (fun i ↦ Over.mk (f i)) _ p k ≪≫
    ((cechComplexFunctor (fun i ↦ Over.mk (f i)) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p).mapIso
        ((J.cohomologyPresheafFunctorOverIso V k).app F)).op

/-- The second-page comparison is the slice comparison followed by the homology comparison
induced by restriction of the ambient cohomology presheaf. -/
lemma cechToCohomologyOverSecondPageXIso_hom (p k : ℕ) :
    (cechToCohomologyOverSecondPageXIso f R p k).hom =
      (cechToCohomologySecondPageXIso (fun i ↦ Over.mk (f i))
        ((J.overPullback AddCommGrpCat.{v} V).mapInjectiveResolution R) p k).hom ≫
        (HomologicalComplex.homologyMap
          ((cechComplexFunctor (fun i ↦ Over.mk (f i))).map
            ((J.cohomologyPresheafFunctorOverIso V k).hom.app F)) p).op :=
  (rfl)

/-- **The first differential of the Čech-to-cohomology spectral sequence of a covering.** Under
the identifications `cechToCohomologyOverFirstPageXIso` of the first page with the Čech cochains of
the presheaf `Hᵏ(-, F)` restricted to `Over V`, the differential from `(-k - 2(p + 1), p + 1)` to
`(-k - 2p, p)` is `(-1)^k` times the opposite of the Čech differential
`Čᵖ(U, Hᵏ(F)) ⟶ Čᵖ⁺¹(U, Hᵏ(F))`. Hence the objects of the second page are the Čech cohomology
groups `Hᵖ(U, Hᵏ(F))` of the covering. -/
theorem cechToCohomologyOverSpectralSequence_page_two_d (p k : ℕ) :
    (cechToCohomologyOverFirstPageXIso f R (p + 1) k).inv ≫
      ((cechToCohomologyOverSpectralSequence f R).page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (cechToCohomologyOverFirstPageXIso f R p k).hom =
    ((-1 : ℤ) ^ k) • (((cechComplexFunctor (fun i ↦ Over.mk (f i))).obj
      ((Over.forget V).op ⋙ F.cohomologyPresheaf k)).d p (p + 1)).op := by
  exact HomologicalComplex.transport_op_d
    ((cechComplexFunctor (fun i ↦ Over.mk (f i))).mapIso
      ((J.cohomologyPresheafFunctorOverIso V k).app F)) p (p + 1)
    (cechToCohomologyFirstPageXIso (fun i ↦ Over.mk (f i)) _ (p + 1) k)
    (cechToCohomologyFirstPageXIso (fun i ↦ Over.mk (f i)) _ p k) _ _
    (cechToCohomologySpectralSequence_page_two_d (fun i ↦ Over.mk (f i)) _ p k)

end TauCeti.CategoryTheory
