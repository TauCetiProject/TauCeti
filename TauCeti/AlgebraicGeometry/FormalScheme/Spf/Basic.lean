/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.IdealIndependence

/-!
# The formal spectrum as a locally ringed space

Let `A` be an adic ring of finite ideal type. The structure sheaf `O_{Spf A}` of the formal
spectrum (`TauCeti.FormalScheme.Spf.structureSheaf`) has sections the completed localisation
`A_{f}` over each basic open set `D(f)`, and these sets form a basis of the topology. Hence the
stalk of `O_{Spf A}` at an open prime `p` is the colimit `colim_{f ∉ p} A_{f}` of the completed
localisations along the restriction maps (EGA I, Ch. I, 10.1.5–10.1.6), which is a local ring
with residue field `Frac(A ⧸ p)`
(`TauCeti.FormalScheme.Spf.completedNeighbourhoodColimit_isLocalRing`, EGA I, Ch. 0, 7.6.17).
So `Spf A`, with this structure sheaf, is a locally ringed space.

The comparison of the stalk with the colimit holds because the basic open neighbourhoods `D(f)`
of `p` are cofinal among all open neighbourhoods of `p`. Locality of the stalks holds for the
structure sheaf built from every ideal of definition, by the comparison
`TauCeti.FormalScheme.Spf.structureSheafIso` with the structure sheaf built from a finitely
generated one.

## Main definitions

* `TauCeti.FormalScheme.Spf.completedNeighbourhoodCocone`: the germs at `p` of the sections over
  the basic open sets `D(f)`, read as a cocone on the diagram of completed localisations `A_{f}`.
* `TauCeti.FormalScheme.Spf.completedNeighbourhoodColimitIso`: the stalk of `O_{Spf A}` at `p` is
  the colimit `colim_{f ∉ p} A_{f}`.
* `TauCeti.FormalScheme.Spf`: the formal spectrum of an adic ring of finite ideal type, as a
  locally ringed space.
* `TauCeti.FormalScheme.Spf.stalkResidueFieldEquiv`: the residue field of `Spf A` at `p` is
  `Frac(A ⧸ p)`.

## Main results

* `TauCeti.FormalScheme.Spf.completedNeighbourhoodIsColimit`: the germ cocone is a colimit cocone.
* `TauCeti.FormalScheme.Spf.completedNeighbourhoodColimitIso_germ`: the comparison of the colimit
  with the stalk restricts on `A_{f}` to the germ at `p` of the sections over `D(f)`.
* `TauCeti.FormalScheme.Spf.stalk_isLocalRing`: the stalks of the structure sheaf of `Spf A` are
  local rings.
* `TauCeti.FormalScheme.Spf.stalkResidueFieldEquiv_residue_germ`: the residue field
  isomorphism sends the residue class of `a ∈ A` to the image of `a` in `Frac(A ⧸ p)`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.17, and
  Ch. I, §10.1 (10.1.2, 10.1.5, 10.1.6).
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme

namespace Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  {I : Ideal A} (p : carrier A)

/-- The basic open neighbourhoods `D(f)` of `p`, as open neighbourhoods of `p`. -/
private def basicOpenNhds :
    BasicNeighbourhood p ⥤ (OpenNhds (X := TopCat.of (carrier A)) p)ᵒᵖ where
  obj f := op ⟨basicOpen f.elem, mem_basicOpen.mpr f.notMem⟩
  map h := (homOfLE h.le).op

/-- The basic open neighbourhoods of `p` are cofinal among all open neighbourhoods of `p`. -/
private instance final_basicOpenNhds : (basicOpenNhds p).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun U ↦ ?_)
    fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    (Opens.isBasis_iff_nbhd.mp isBasis_basicOpen) (unop U).2
  exact ⟨⟨f, mem_basicOpen.mp hpf⟩, ⟨(homOfLE hfU).op⟩⟩

variable (hI : IsAdic I) (hIfg : I.FG)

/-- The sections of `O_{Spf A}` over the basic open neighbourhoods of `p` form the diagram of
completed localisations at `p`. -/
private noncomputable def completedNeighbourhoodDiagramIso :
    basicOpenNhds p ⋙ (OpenNhds.inclusion _).op ⋙ (structureSheaf hI).obj ≅
      completedNeighbourhoodDiagram p :=
  NatIso.ofComponents (fun f ↦ basicOpenSectionsIso hI hIfg f.elem) fun h ↦
    map_comp_basicOpenSectionsIso_hom hI hIfg h.le

/-- The germs at `p` of the sections of `O_{Spf A}` over the basic open sets `D(f)` containing
`p`, read through the identifications of these sections with the completed localisations `A_{f}`,
form a cocone on the diagram `f ↦ A_{f}` with vertex the stalk of `O_{Spf A}` at `p`. -/
noncomputable def completedNeighbourhoodCocone : Cocone (completedNeighbourhoodDiagram p) where
  pt := TopCat.Presheaf.stalk (C := CommRingCat) (structureSheaf hI).obj p
  ι.app f := (basicOpenSectionsIso hI hIfg f.elem).inv ≫
    TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj (basicOpen f.elem) p
      (mem_basicOpen.mpr f.notMem)
  ι.naturality {f g} h := by
    have key := map_comp_basicOpenSectionsIso_hom hI hIfg h.le
    rw [← Iso.inv_comp_eq] at key
    -- unfold the diagram so that its objects are syntactically the rings `A_{f}` of `key`
    dsimp only [completedNeighbourhoodDiagram, Functor.const_obj_map]
    simp only [AlgHom.toRingHom_eq_coe, ← key, Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg _ ((TopCat.Presheaf.germ_res _ _ _ _).trans (Category.comp_id _).symm)

/-- The vertex of the germ cocone is the stalk of `O_{Spf A}` at `p`. -/
@[simp]
theorem completedNeighbourhoodCocone_pt :
    (completedNeighbourhoodCocone p hI hIfg).pt =
      TopCat.Presheaf.stalk (C := CommRingCat) (structureSheaf hI).obj p :=
  (rfl)

/-- The leg of the germ cocone at `A_{f}` is the germ at `p` of the corresponding section over
`D(f)`. -/
theorem completedNeighbourhoodCocone_ι_app (f : BasicNeighbourhood p) :
    (completedNeighbourhoodCocone p hI hIfg).ι.app f ≫
        eqToHom (completedNeighbourhoodCocone_pt p hI hIfg) =
      (basicOpenSectionsIso hI hIfg f.elem).inv ≫
        TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj (basicOpen f.elem) p
          (mem_basicOpen.mpr f.notMem) :=
  (Category.comp_id _)

/-- The stalk of `O_{Spf A}` at `p` is the colimit of the completed localisations `A_{f}` over the
basic open neighbourhoods `D(f)` of `p` (EGA I, Ch. I, 10.1.6). -/
noncomputable def completedNeighbourhoodIsColimit :
    IsColimit (completedNeighbourhoodCocone p hI hIfg) :=
  -- the germ cocone is the colimit cocone of the stalk, restricted along the cofinal basic
  -- neighbourhoods and transported along the identifications of sections with the `A_{f}`
  ((IsColimit.precomposeInvEquiv (completedNeighbourhoodDiagramIso p hI hIfg) _).symm <|
    (Functor.Final.isColimitWhiskerEquiv (basicOpenNhds p) _).symm
      (colimit.isColimit _)).ofIsoColimit (Cocone.ext (Iso.refl _))

/-- The colimit `colim_{f ∉ p} A_{f}` of the completed localisations of `A` over the basic open
neighbourhoods of `p` is isomorphic to the stalk of `O_{Spf A}` at `p`. -/
noncomputable def completedNeighbourhoodColimitIso :
    colimit (completedNeighbourhoodDiagram p) ≅
      TopCat.Presheaf.stalk (C := CommRingCat) (structureSheaf hI).obj p :=
  (colimit.isColimit _).coconePointUniqueUpToIso (completedNeighbourhoodIsColimit p hI hIfg)

/-- On the completed localisation `A_{f}`, the comparison of the colimit with the stalk is the
germ at `p` of the corresponding section over `D(f)`. -/
@[reassoc (attr := simp)]
theorem completedNeighbourhoodColimitIso_germ (f : BasicNeighbourhood p) :
    colimit.ι (completedNeighbourhoodDiagram p) f ≫
        (completedNeighbourhoodColimitIso p hI hIfg).hom =
      (basicOpenSectionsIso hI hIfg f.elem).inv ≫
        TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj (basicOpen f.elem) p
          (mem_basicOpen.mpr f.notMem) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (completedNeighbourhoodIsColimit p hI hIfg) f

/-- The stalks of the structure sheaf of `Spf A`, built from any ideal of definition, are local
rings (EGA I, Ch. I, 10.1.6). -/
theorem stalk_isLocalRing :
    IsLocalRing (TopCat.Presheaf.stalk (C := CommRingCat) (structureSheaf hI).obj p) := by
  obtain ⟨hI₀fg, hI₀, -⟩ := IsAdicRing.ideal_spec (A := A)
  -- the stalk of the structure sheaf built from the chosen ideal is the colimit of the `A_{f}`
  let e := completedNeighbourhoodColimitIso p hI₀ hI₀fg ≪≫
    (TopCat.Presheaf.stalkFunctor CommRingCat (X := TopCat.of (carrier A)) p).mapIso
      ((sheafToPresheaf _ _).mapIso (structureSheafIso hI₀ hI))
  have := isLocalHom_of_iso e.symm
  exact e.inv.hom.domain_isLocalRing

end Spf

/-- The **formal spectrum** `Spf A` of an adic ring `A` of finite ideal type, as a locally ringed
space (EGA I, Ch. I, 10.1.2): its points are the open prime ideals of `A`, and its structure sheaf
is `lim_n O_{Spec (A ⧸ I ^ (n + 1))}` for the chosen ideal of definition `I`.

The body is exposed so that the underlying space and the structure sheaf are definitionally
`TauCeti.FormalScheme.Spf.carrier A` and `TauCeti.FormalScheme.Spf.structureSheaf`, whose API then
applies to `Spf A` directly. -/
@[expose] noncomputable def Spf (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] : LocallyRingedSpace.{u} where
  carrier := TopCat.of (Spf.carrier A)
  presheaf := (Spf.structureSheaf (IsAdicRing.ideal_spec A).2.1).obj
  IsSheaf := (Spf.structureSheaf (IsAdicRing.ideal_spec A).2.1).property
  isLocalRing x := TauCeti.FormalScheme.Spf.stalk_isLocalRing x _

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- The points of `Spf A` are the open prime ideals of `A`. -/
theorem Spf_carrier : (Spf A).carrier = TopCat.of (Spf.carrier A) :=
  (rfl)

/-- The structure sheaf of `Spf A` is the limit of the structure sheaves of the thickenings
`Spec (A ⧸ I ^ (n + 1))`, for the chosen ideal of definition `I`. -/
theorem Spf_presheaf :
    (Spf A).presheaf = (Spf.structureSheaf (IsAdicRing.ideal_spec A).2.1).obj :=
  (rfl)

namespace Spf

variable {A}

/-- The residue field of `Spf A` at an open prime `p` is the fraction field of `A ⧸ p`
(EGA I, Ch. I, 10.1.6). -/
noncomputable def stalkResidueFieldEquiv (p : carrier A) :
    (Spf A).residueField p ≃+* FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal) :=
  let e : colimit (completedNeighbourhoodDiagram p) ≅ (Spf A).presheaf.stalk p :=
    completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
  haveI := (Spf A).isLocalRing p
  (IsLocalRing.ResidueField.mapEquiv e.commRingCatIsoToRingEquiv).symm.trans (stalkResidueIso p)

/-- The residue field isomorphism sends the residue class of the germ at `p` of the section
over `D(f)` corresponding to `a ∈ A` to the image of `a` in `Frac(A ⧸ p)`. -/
@[simp]
theorem stalkResidueFieldEquiv_residue_germ {p : carrier A} (f : BasicNeighbourhood p) (a : A) :
    stalkResidueFieldEquiv p ((Spf A).residue p
      ((Spf A).presheaf.germ (basicOpen f.elem) p (mem_basicOpen.mpr f.notMem)
        ((basicOpenSectionsIso (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1 f.elem).inv
          (algebraMap A (AdicRing.CompletedAway A f.elem) a)))) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
  let e := completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec A).1
  -- the comparison of the colimit with the stalk is the germ on `A_{f}`
  have h := (RingEquiv.symm_apply_eq e.commRingCatIsoToRingEquiv).mpr (ConcreteCategory.congr_hom
    (completedNeighbourhoodColimitIso_germ p _ _ f)
      (algebraMap A (AdicRing.CompletedAway A f.elem) a)).symm
  -- `stalkResidueFieldEquiv` pulls the residue class back along `e` and applies
  -- `stalkResidueIso`, so the residue class of the germ is that of `a` in the colimit
  exact (congrArg (fun x ↦ stalkResidueIso p (IsLocalRing.residue _ x)) h).trans
    (stalkResidueIso_coeff p f a)

end Spf

end TauCeti.FormalScheme
