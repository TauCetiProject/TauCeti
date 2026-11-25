/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.OverBaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat
public import TauCeti.CategoryTheory.EffectiveEpi.GrpObj

/-!
# Effective fpqc descent of group schemes

Let `p : S' ⟶ S` be a surjective, flat and quasi-compact morphism of schemes. Combining effective
fpqc descent of schemes
(`TauCeti.DescentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact`,
`TauCeti.DescentDatum.exists_finiteLocallyFree_baseChange_hom_isIso`, and
`TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_mem`) with descent of group-object
structures along effective epimorphic pullbacks (`TauCeti.DescentDatum.Hom.descendGrpObj`,
`TauCeti.DescentDatum.Hom.isCommMonObj_descendGrpObj`), this file establishes effective fpqc
descent for:

* group schemes affine over the cover
  (`exists_grp_isAffineHom_baseChange_hom_isIso_of_quasiCompact`);
* finite locally free commutative group schemes
  (`exists_finiteFlatCommGroupScheme_baseChange_hom_isIso`), preserving the rank function along `p`
  and with canonical uniqueness up to group-scheme isomorphism
  (`TauCeti.DescentDatum.Hom.descendGrpIso`);
* group schemes affine over the base change `G₀ ×_S S'` of an arbitrary group scheme `G₀` over `S`
  (`Hom.exists_grp_baseChange_hom_isIso_of_mem`) and finite locally free homomorphisms into
  `G₀ ×_S S'` (`Hom.exists_grp_finiteLocallyFree_baseChange_hom_isIso`); for closed subgroup
  immersions without an explicit `IsMon` assumption, see
  `TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Descent`.

## Main results

* `TauCeti.DescentDatum.exists_grp_isAffineHom_baseChange_hom_isIso_of_quasiCompact`: effective
  fpqc descent for group schemes affine over `S'`.
* `TauCeti.DescentDatum.exists_finiteFlatCommGroupScheme_baseChange_hom_isIso`: effective fpqc
  descent for `FiniteFlatCommGroupScheme`, retaining `Scheme.Hom.finrank`.
* `TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChangeIsoOfDescent`: the comparison
  isomorphism `G₀.baseChange p ≅ G` induced by a group-homomorphism isomorphism of descent data
  (with uniqueness of the descended `FiniteFlatCommGroupScheme` given by
  `FiniteFlatCommGroupScheme.isoMk (f.descendGrpIso g)`).
* `TauCeti.DescentDatum.Hom.exists_grp_baseChange_hom_isIso_of_mem` and
  `TauCeti.DescentDatum.Hom.exists_grp_finiteLocallyFree_baseChange_hom_isIso`: effective fpqc
  descent of group schemes affine over a descended group scheme `G₀`, preserving morphism
  properties and finite-flat rank.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 and Corollaire 2.2.
* [The Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245).
-/

public section

open CategoryTheory Limits AlgebraicGeometry MorphismProperty
open scoped CategoryTheory.Obj

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [Surjective p] [Flat p] [QuasiCompact p]

/-- **Effective fpqc descent of group schemes affine over the cover.** Let `p : S' ⟶ S` be
surjective, flat and quasi-compact, and let `D` be a monoid-compatible descent datum relative to
`p` on a group scheme `G` affine over `S'`. Then `D` is isomorphic, via a group-homomorphism
morphism of descent data, to the canonical descent datum on the base change of a group scheme `G₀`
affine over `S`. When `G` is commutative, `G₀` is also commutative by
`TauCeti.DescentDatum.Hom.isCommMonObj_of_mono`. -/
theorem exists_grp_isAffineHom_baseChange_hom_isIso_of_quasiCompact
    {G : Over S'} [GrpObj G] [IsAffineHom G.hom] (D : DescentDatum p G) [D.IsMon] :
    ∃ G₀ : Grp (Over S), IsAffineHom G₀.X.hom ∧
      ∃ f : Hom (baseChange p G₀.X) D, IsIso f.hom ∧ IsMonHom f.hom := by
  obtain ⟨X₀, haff, f, hf⟩ := D.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  let : GrpObj X₀ := f.descendGrpObj
  have : IsMonHom f.hom := f.isMonHom_hom_descendGrpObj
  exact ⟨Grp.mk X₀, haff, f, hf, inferInstance⟩

/-- **Effective fpqc descent of finite locally free commutative group schemes.** Let `p : S' ⟶ S`
be surjective, flat and quasi-compact, and let `D` be a monoid-compatible descent datum relative
to `p` on a finite locally free commutative group scheme `G` over `S'`. Then there exist a finite
locally free commutative group scheme `G₀` over `S` and an isomorphism `f` of descent data from
`baseChange p G₀.toOver` to `D` whose underlying morphism over `S'` is a group homomorphism, and
the rank of `G` over `S'` is the rank of `G₀` pulled back along `p`. Uniqueness up to canonical
isomorphism `G₀ ≅ H₀` is supplied by `FiniteFlatCommGroupScheme.isoMk (f.descendGrpIso g)`. -/
theorem exists_finiteFlatCommGroupScheme_baseChange_hom_isIso
    (G : TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S')
    (D : DescentDatum p G.toOver) [D.IsMon] :
    ∃ G₀ : TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme S,
      ∃ f : Hom (baseChange p G₀.toOver) D,
        IsIso f.hom ∧ IsMonHom f.hom ∧
          G.structureMap.finrank = G₀.structureMap.finrank ∘ p := by
  have : IsFinite G.toOver.hom := G.finite
  have : Flat G.toOver.hom := G.flat
  have : LocallyOfFinitePresentation G.toOver.hom := G.locallyOfFinitePresentation
  obtain ⟨X₀, hfin, hflat, hlfp, f, hf, hrank⟩ :=
    D.exists_finiteLocallyFree_baseChange_hom_isIso
  let f' : Hom (baseChange p (Over.mk X₀.hom)) D := f
  have : IsIso f'.hom := hf
  let grp₀ : GrpObj (Over.mk X₀.hom) := f'.descendGrpObj
  have comm₀ : IsCommMonObj (Over.mk X₀.hom) := f'.isCommMonObj_descendGrpObj
  have hmon : IsMonHom f'.hom := f'.isMonHom_hom_descendGrpObj
  exact ⟨{ carrier := X₀.left
           structureMap := X₀.hom
           grp := grp₀
           comm := comm₀
           finite := hfin
           flat := hflat
           locallyOfFinitePresentation := hlfp },
    f', hf, hmon, hrank⟩

/-- **Effective fpqc descent of group schemes affine over a descended group scheme.** Let
`p : S' ⟶ S` be surjective, flat and quasi-compact, let `G₀` be a group scheme over `S`, let `D`
be a monoid-compatible descent datum on a group scheme `Z` over `S'`, and let
`f : Hom D (baseChange p G₀.X)` be an affine morphism of descent data whose underlying morphism in
`Over S'` is a group homomorphism. Then there exist a group scheme `K₀` over `S`, a homomorphism
`i₀ : K₀ ⟶ G₀` of group schemes over `S`, and an isomorphism `g : Hom (baseChange p K₀.X) D` of
descent data whose underlying morphism is a group homomorphism, intertwining `f` with the base
change of `i₀`, such that `i₀` inherits every property `P` of `f` satisfying fpqc descent. -/
theorem Hom.exists_grp_baseChange_hom_isIso_of_mem
    {G₀ : Grp (Over S)} {Z : Over S'} [GrpObj Z] {D : DescentDatum p Z} [D.IsMon]
    {P : MorphismProperty Scheme.{u}} [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (f : Hom D (baseChange p G₀.X)) [IsMonHom f.hom] [IsAffineHom f.hom.left]
    (hf : P f.hom.left) :
    ∃ (K₀ : Grp (Over S)) (i₀ : K₀ ⟶ G₀) (g : Hom (baseChange p K₀.X) D),
      IsIso g.hom ∧ IsMonHom g.hom ∧ f.comp g = baseChangeHom p i₀.hom.hom ∧
        P i₀.hom.hom.left := by
  obtain ⟨W, g, hg, hcomp, hP⟩ := f.exists_baseChange_hom_isIso_of_mem (P := P) hf
  let : GrpObj (Over.mk (W.hom ≫ G₀.X.hom)) := g.descendGrpObj
  have : IsMonHom g.hom := g.isMonHom_hom_descendGrpObj
  let wHom : Over.mk (W.hom ≫ G₀.X.hom) ⟶ G₀.X := Over.homMk W.hom rfl
  have : IsMonHom wHom := f.isMonHom_of_comp_eq_baseChangeHom g hcomp
  exact ⟨Grp.mk (Over.mk (W.hom ≫ G₀.X.hom)), Grp.homMk wHom, g, hg, inferInstance, hcomp, hP⟩

/-- **Effective fpqc descent of finite locally free homomorphisms into a descended group scheme.**
Let `p : S' ⟶ S` be surjective, flat and quasi-compact, let `G₀` be a group scheme over `S`, let
`D` be a monoid-compatible descent datum on a group scheme `Z` over `S'`, and let
`f : Hom D (baseChange p G₀.X)` be a finite locally free morphism whose underlying morphism in
`Over S'` is a group homomorphism. Then `(Z, f)` descends to a finite locally free homomorphism
`i₀ : K₀ ⟶ G₀` of group schemes over `S`, and the rank of `f` is the rank of `i₀` pulled back
along `G₀ ×_S S' ⟶ G₀`. -/
theorem Hom.exists_grp_finiteLocallyFree_baseChange_hom_isIso
    {G₀ : Grp (Over S)} {Z : Over S'} [GrpObj Z] {D : DescentDatum p Z} [D.IsMon]
    (f : Hom D (baseChange p G₀.X)) [IsMonHom f.hom] [IsFinite f.hom.left] [Flat f.hom.left]
    [LocallyOfFinitePresentation f.hom.left] :
    ∃ (K₀ : Grp (Over S)) (i₀ : K₀ ⟶ G₀) (g : Hom (baseChange p K₀.X) D),
      IsIso g.hom ∧ IsMonHom g.hom ∧ f.comp g = baseChangeHom p i₀.hom.hom ∧
        IsFinite i₀.hom.hom.left ∧ Flat i₀.hom.hom.left ∧
          LocallyOfFinitePresentation i₀.hom.hom.left ∧
            f.hom.left.finrank = i₀.hom.hom.left.finrank ∘ pullback.fst G₀.X.hom p := by
  obtain ⟨W, g, hg, hcomp, hfin, hflat, hlfp, hrank⟩ :=
    f.exists_finiteLocallyFree_baseChange_hom_isIso
  let : GrpObj (Over.mk (W.hom ≫ G₀.X.hom)) := g.descendGrpObj
  have : IsMonHom g.hom := g.isMonHom_hom_descendGrpObj
  let wHom : Over.mk (W.hom ≫ G₀.X.hom) ⟶ G₀.X := Over.homMk W.hom rfl
  have : IsMonHom wHom := f.isMonHom_of_comp_eq_baseChangeHom g hcomp
  exact ⟨Grp.mk (Over.mk (W.hom ≫ G₀.X.hom)), Grp.homMk wHom, g, hg, inferInstance,
    hcomp, hfin, hflat, hlfp, hrank⟩

end TauCeti.DescentDatum

namespace TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S}

/-- An isomorphism `f : Hom (baseChange p G₀.toOver) D` of descent data whose underlying morphism
over `S'` is a group isomorphism induces an isomorphism `G₀.baseChange p ≅ G` of finite locally
free commutative group schemes over `S'`. -/
noncomputable def baseChangeIsoOfDescent (G₀ : FiniteFlatCommGroupScheme S)
    (G : FiniteFlatCommGroupScheme S') (D : DescentDatum p G.toOver)
    (f : DescentDatum.Hom (DescentDatum.baseChange p G₀.toOver) D)
    [IsIso f.hom] [IsMonHom f.hom] :
    G₀.baseChange p ≅ G :=
  let e := asIso f.hom
  isoMk <| eqToIso (G₀.grpMk_baseChange p) ≪≫
    Grp.mkIso (G := (Over.pullback p).mapGrp.obj (Grp.mk G₀.toOver)) (H := Grp.mk G.toOver)
      e (IsMonHom.one_hom f.hom) (IsMonHom.mul_hom f.hom)

/-- The underlying morphism in `Over S'` of `G₀.baseChangeIsoOfDescent G D f` is `f.hom`, read
through `G₀.grpMk_baseChange p`. -/
@[simp]
theorem baseChangeIsoOfDescent_hom_hom_hom_hom (G₀ : FiniteFlatCommGroupScheme S)
    (G : FiniteFlatCommGroupScheme S') (D : DescentDatum p G.toOver)
    (f : DescentDatum.Hom (DescentDatum.baseChange p G₀.toOver) D)
    [IsIso f.hom] [IsMonHom f.hom] :
    (G₀.baseChangeIsoOfDescent G D f).hom.hom.hom.hom =
      eqToHom (congrArg (fun H : Grp (Over S') ↦ H.X) (G₀.grpMk_baseChange p)) ≫ f.hom := by
  simp only [baseChangeIsoOfDescent, isoMk_hom, homMk_hom, Iso.trans_hom, Grp.comp',
    Mon.comp_hom', eqToIso.hom]
  exact congrArg (· ≫ f.hom) (eqToHom_map (Grp.forget (Over S')) (G₀.grpMk_baseChange p))

end TauCeti.AlgebraicGeometry.FiniteFlatCommGroupScheme
