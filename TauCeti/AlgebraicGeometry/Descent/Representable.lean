/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.AlgebraicGeometry.Descent.Fpqc
public import TauCeti.AlgebraicGeometry.Sites.Big.Representability
public import TauCeti.CategoryTheory.Adjunction.Representable
public import TauCeti.CategoryTheory.EffectiveEpi.Representable
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor

/-!
# Representability of fppf sheaves and of torsors under affine groups

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
represented by the base change of `G` to `S'`, and `P` is represented by a scheme affine over `S`.
Every `𝒢`-torsor has such sections locally on `S`: every point of `S` has an open neighbourhood
`W` with a surjective, flat, quasi-compact morphism `p : V ⟶ W` of finite presentation, from an
affine scheme `V`, over which `P` has a section. Indeed, `P` has a section over a morphism
`f : Y ⟶ S`, flat and locally of finite presentation, through that point; take for `V` an affine
open of `Y` over an affine open of `S`, and for `W` its image, which is open since `f` is flat
and locally of finite presentation. The representing schemes over these neighbourhoods glue
(`AlgebraicGeometry.Scheme.OpenCover.exists_hom_mem_nonempty_representableBy`), so that every
`𝒢`-torsor is represented by a scheme affine over `S`
(`CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_representableBy`), with no Noetherian
or other hypothesis on `S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isAffineHom_nonempty_representableBy`: an fppf sheaf which
  is represented by a scheme affine over `S'` after base change along `p` is represented by a
  scheme affine over `S`.
* `CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_representableBy`: every torsor under a
  sheaf of groups represented by a scheme affine over `S` is represented by a scheme affine
  over `S`.

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

/-- Let `ι : W ⟶ S` be a morphism, for instance the inclusion of an open subscheme, and let `P` be
a `𝒢`-torsor with a section over `p ≫ ι`, for a surjective, flat, quasi-compact morphism
`p : S' ⟶ W` locally of finite presentation. Then the restriction of `P` to schemes over `W` is
represented by a scheme affine over `W`. This is the local step of
`exists_isAffineHom_nonempty_representableBy`, which shows that no section is needed. -/
private theorem exists_isAffineHom_nonempty_representableBy_overMap (P : Torsor 𝒢) {G : Over S}
    [IsAffineHom G.hom] (eG : (𝒢.obj ⋙ forget GrpCat).RepresentableBy G) {W : Scheme.{u}}
    (ι : W ⟶ S) (p : S' ⟶ W) [Surjective p] [Flat p] [QuasiCompact p]
    [LocallyOfFinitePresentation p] (ξ : P.sheaf.obj.obj (op (Over.mk (p ≫ ι)))) :
    ∃ X₀ : Over W, IsAffineHom X₀.hom ∧
      Nonempty (((Over.map ι).op ⋙ P.sheaf.obj).RepresentableBy X₀) := by
  -- The section `ξ`, restricted to every scheme over `S'`.
  let s (T : Over S') : P.sheaf.obj.obj (op ((Over.map p ⋙ Over.map ι).obj T)) :=
    P.sheaf.obj.map
      (Over.homMk T.hom : (Over.map p ⋙ Over.map ι).obj T ⟶ Over.mk (p ≫ ι)).op ξ
  have hs ⦃T T' : Over S'⦄ (f : T ⟶ T') :
      P.sheaf.obj.map ((Over.map p ⋙ Over.map ι).map f).op (s T') = s T := by
    simp only [s, ← Functor.map_comp_apply, ← op_comp]
    congr 3
    ext
    simp
  have : IsAffineHom ((Over.pullback ι).obj G).hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have : IsAffineHom ((Over.pullback p).obj ((Over.pullback ι).obj G)).hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  exact p.exists_isAffineHom_nonempty_representableBy
    ((Scheme.fppfTopology.overMapPullback (Type w) ι).obj P.sheaf)
    (((Over.mapPullbackAdj p).representableByComp
      ((Over.mapPullbackAdj ι).representableByComp eG)).ofIso
        (P.isoOfSection (Over.map p ⋙ Over.map ι) s hs))

/-- Every point `s` of `S` lies in the image of a morphism `f : Y ⟶ S`, flat and locally of
finite presentation, over which the torsor `P` has a section. -/
private lemma exists_flat_section (P : Torsor 𝒢) (s : S) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S) (y : Y), Flat f ∧ LocallyOfFinitePresentation f ∧ f y = s ∧
      Nonempty (P.sheaf.obj.obj (op (Over.mk f))) := by
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  have h := (GrothendieckTopology.coversTop_iff_of_isTerminal _ _ Over.mkIdTerminal _).1
    P.coversTop
  rw [GrothendieckTopology.mem_over_iff] at h
  obtain ⟨R, hR, hRS⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.1 h
  obtain ⟨Y, f, hf, y, hy⟩ := (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hR.1 s
  obtain ⟨⟨T, ⟨x⟩⟩, ⟨a⟩⟩ := (Sieve.overEquiv_iff _ _).1 (hRS Y f hf)
  exact ⟨Y, f, y, (hR.2 hf).1, (hR.2 hf).2, hy,
    ⟨P.sheaf.obj.map ((Over.homMk (𝟙 Y) : Over.mk f ⟶ Over.mk (f ≫ 𝟙 S)) ≫ a).op x⟩⟩

/-- Every point `s` of `S` has an open neighbourhood `W` with a surjective, flat, quasi-compact
morphism `p : V ⟶ W` locally of finite presentation over which the torsor `P` has a section. -/
private lemma exists_open_section (P : Torsor 𝒢) (s : S) :
    ∃ (W : S.Opens) (V : Scheme.{u}) (p : V ⟶ W), s ∈ W ∧ Surjective p ∧ Flat p ∧
      QuasiCompact p ∧ LocallyOfFinitePresentation p ∧
        Nonempty (P.sheaf.obj.obj (op (Over.mk (p ≫ W.ι)))) := by
  -- For a section over `f : Y ⟶ S` through `s`, take for `V` an affine open of `Y` lying over an
  -- affine open neighbourhood `U` of `s`, and for `W ⊆ U` its image, which is open since `f` is
  -- flat and locally of finite presentation. Then `V ⟶ W` is quasi-compact, as `V ⟶ U` is.
  obtain ⟨Y, f, y, _, _, rfl, ⟨ξ⟩⟩ := exists_flat_section P s
  obtain ⟨U, hU, hyU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (f y))
  obtain ⟨V, hV, hyV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (f.mem_preimage.2 hyU)
  let W : S.Opens := ⟨f '' V, f.isOpenMap _ V.isOpen⟩
  have hVW : V ≤ f ⁻¹ᵁ W := fun v hv ↦ ⟨v, hv, rfl⟩
  have hWU : W ≤ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact hVU hv
  let p := f.resLE W V hVW
  have : IsAffine V := hV
  have : IsAffine U := hU
  have : QuasiCompact (p ≫ S.homOfLE hWU) := by
    rw [Scheme.Hom.resLE_map]
    infer_instance
  refine ⟨W, V, p, ⟨y, hyV, rfl⟩, ⟨fun w ↦ ?_⟩, inferInstance,
    QuasiCompact.of_comp p (S.homOfLE hWU), inferInstance,
    ⟨P.sheaf.obj.map
      (Over.homMk (Scheme.Opens.ι V) (by simp [p]) : Over.mk (p ≫ W.ι) ⟶ Over.mk f).op ξ⟩⟩
  -- A point of `W` is the image `f v` of a point `v` of `V`.
  obtain ⟨v, hv, hvw⟩ := w.property
  obtain ⟨v, rfl⟩ : v ∈ Set.range (Scheme.Opens.ι V) := by rwa [Scheme.Opens.range_ι]
  refine ⟨v, W.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply p W.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  exact hvw

/-- **Torsors under an affine group are representable.** Let `𝒢` be a sheaf of groups on the big
fppf site of `S` whose underlying sheaf of sets is represented by a scheme `G` affine over `S`,
for instance the sheaf of points of a group scheme affine over `S`. Then every `𝒢`-torsor `P` is
represented by a scheme affine over `S` (Poonen, Theorem 6.5.10 (i), here without Noetherian
hypotheses on `S` and without flatness of `G`). -/
theorem exists_isAffineHom_nonempty_representableBy (P : Torsor 𝒢) {G : Over S}
    [IsAffineHom G.hom] (eG : (𝒢.obj ⋙ forget GrpCat).RepresentableBy G) :
    ∃ X₀ : Over S, IsAffineHom X₀.hom ∧ Nonempty (P.sheaf.obj.RepresentableBy X₀) := by
  -- Around every point of `S`, `P` has a section over a single surjective, flat, quasi-compact
  -- morphism of finite presentation to an open neighbourhood `W`, so its restriction to schemes
  -- over `W` is represented by a scheme affine over `W`; these schemes glue.
  choose W V p hW _ _ _ _ ξ using exists_open_section P
  choose Y hY e using fun s ↦
    P.exists_isAffineHom_nonempty_representableBy_overMap eG (W s).ι (p s) (ξ s).some
  have hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) P.sheaf.obj :=
    Presieve.isSheaf_of_le _ (GrothendieckTopology.over_mono
      (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage) S)
      ((isSheaf_iff_isSheaf_of_type _ _).1 P.sheaf.property)
  have : IsZariskiLocalAtTarget @IsAffineHom.{u} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyIsAffineHomIsAffine
  exact Scheme.OpenCover.exists_hom_mem_nonempty_representableBy
    (S.openCoverOfIsOpenCover W
      (top_le_iff.1 fun s _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨s, hW s⟩))
    hF (fun s ↦ (e s).some) @IsAffineHom hY

end CategoryTheory.Sheaf.Torsor
