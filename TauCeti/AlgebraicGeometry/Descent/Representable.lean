/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.AlgebraicGeometry.Descent.Fpqc
public import TauCeti.CategoryTheory.Adjunction.Representable
public import TauCeti.CategoryTheory.EffectiveEpi.Representable
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Fppf sheaves which are representable by affine schemes after a base change

Let `p : S' ⟶ S` be a surjective, flat, quasi-compact morphism of schemes, locally of finite
presentation. This file shows that a sheaf `F` on the big fppf site of `S` whose restriction to
schemes over `S'` is represented by a scheme affine over `S'` is itself represented by a scheme
affine over `S` (`AlgebraicGeometry.Scheme.Hom.exists_isAffineHom_nonempty_representableBy`). The
representation of the restriction induces a descent datum on the scheme over `S'`
(`CategoryTheory.Functor.RepresentableBy.descentDatum`), which is effective by fpqc descent of
schemes affine over the cover
(`TauCeti.DescentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact`), and the
descended scheme represents `F` (`CategoryTheory.Functor.RepresentableBy.descend`).

The main application is to torsors. Let `𝒢` be a sheaf of groups on the big fppf site of `S`
whose underlying sheaf of sets is represented by a scheme `G` affine over `S`, for instance the
sheaf of points of an affine group scheme. A `𝒢`-torsor `P` with a section over `S'` is
isomorphic over `S'` to `𝒢`, through the action on that section, so its restriction is
represented by the base change of `G` to `S'`. Hence `P` is represented by a scheme affine over
`S` (`CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_representableBy`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isAffineHom_nonempty_representableBy`: an fppf sheaf which
  is represented by a scheme affine over `S'` after base change along `p` is represented by a
  scheme affine over `S`.
* `CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_representableBy`: a torsor under a
  sheaf of groups represented by a scheme affine over `S`, with a section over `S'`, is
  represented by a scheme affine over `S`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* J. S. Milne, *Étale cohomology*, Chapter III, Theorem 4.3.
* B. Poonen, *Rational points on varieties*, Theorem 6.5.10 (i), for the representability of
  torsors under an fppf group scheme affine over the base.
-/

public section

open CategoryTheory Limits Opposite TauCeti

universe w u

namespace AlgebraicGeometry.Scheme.Hom

variable {S S' : Scheme.{u}} (p : S' ⟶ S)

/-- **Fppf sheaves locally representable by affine schemes are representable.** Let
`p : S' ⟶ S` be surjective, flat, quasi-compact and locally of finite presentation, and let `F`
be a sheaf on the big fppf site of `S`. If the restriction of `F` to schemes over `S'` is
represented by a scheme affine over `S'`, then `F` is represented by a scheme affine over `S`. -/
theorem exists_isAffineHom_nonempty_representableBy [Surjective p] [Flat p] [QuasiCompact p]
    [LocallyOfFinitePresentation p] (F : Sheaf (fppfTopology.over S) (Type w)) {X : Over S'}
    [IsAffineHom X.hom] (e : ((Over.map p).op ⋙ F.obj).RepresentableBy X) :
    ∃ X₀ : Over S, IsAffineHom X₀.hom ∧ Nonempty (F.obj.RepresentableBy X₀) := by
  obtain ⟨X₀, hX₀, f, hf⟩ :=
    e.descentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  have hF (T : Over S) :
      Presieve.IsSheafFor F.obj (.singleton ((Over.mapPullbackAdj p).counit.app T)) :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property).isSheafFor _
      (p.generate_singleton_counit_mem_fppfTopology_over T)
  exact ⟨X₀, hX₀, ⟨e.descend hF f⟩⟩

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.Sheaf.Torsor

open AlgebraicGeometry

variable {S S' : Scheme.{u}} {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{w}}

/-- **Torsors under an affine group are representable.** Let `𝒢` be a sheaf of groups on the big
fppf site of `S` whose underlying sheaf of sets is represented by a scheme `G` affine over `S`,
and let `P` be a `𝒢`-torsor with a section over `S'`, for a surjective, flat, quasi-compact
morphism `p : S' ⟶ S` locally of finite presentation. Then `P` is represented by a scheme affine
over `S`. -/
theorem exists_isAffineHom_nonempty_representableBy (P : Torsor 𝒢) {G : Over S}
    [IsAffineHom G.hom] (eG : (𝒢.obj ⋙ forget GrpCat).RepresentableBy G) (p : S' ⟶ S)
    [Surjective p] [Flat p] [QuasiCompact p] [LocallyOfFinitePresentation p]
    (ξ : P.sheaf.obj.obj (op (Over.mk p))) :
    ∃ X₀ : Over S, IsAffineHom X₀.hom ∧ Nonempty (P.sheaf.obj.RepresentableBy X₀) := by
  -- The section `ξ`, restricted to every scheme over `S'`.
  let s (T : Over S') : P.sheaf.obj.obj (op ((Over.map p).obj T)) :=
    P.sheaf.obj.map (Over.homMk T.hom : (Over.map p).obj T ⟶ Over.mk p).op ξ
  have hs ⦃T T' : Over S'⦄ (f : T ⟶ T') : P.sheaf.obj.map ((Over.map p).map f).op (s T') = s T := by
    simp only [s, ← Functor.map_comp_apply, ← op_comp]
    congr 3
    ext
    simp
  have : IsAffineHom ((Over.pullback p).obj G).hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  exact p.exists_isAffineHom_nonempty_representableBy P.sheaf
    (((Over.mapPullbackAdj p).representableByComp eG).ofIso (P.isoOfSection (Over.map p) s hs))

end CategoryTheory.Sheaf.Torsor
