/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# Colimits of spectral sequences

Let `C` be an abelian category in which colimits of shape `J` exist and are exact. Then a diagram
`F : J ⥤ SpectralSequence C c r₀` of spectral sequences has a colimit, computed page by page: the
`r`th page of the colimit is the colimit of the `r`th pages, and, since homology commutes with
exact colimits, the homology of this colimit page is the colimit of the homologies of the pages,
which is the colimit of the next pages. In particular every page functor preserves colimits of
shape `J`; for a filtered diagram in a category of modules, the `E²` page of the colimit is the
colimit of the `E²` pages.

This is how a spectral sequence is assembled from a direct system of spectral sequences, as for
the spectral sequence of symplectic homology with DG coefficients, the colimit over admissible
Hamiltonians of the spectral sequences of the Floer complexes (Barraud–Damian–Humilière–Oancea,
Theorem 3.49).

Conversely, a cocone of spectral sequences is a colimit as soon as its cocones of pages are
(`CategoryTheory.SpectralSequence.isColimitOfPage`), and, when colimits of shape `J` are exact, as
soon as its cocone of initial pages is: the later pages are then colimits as well
(`CategoryTheory.SpectralSequence.isColimitPageOfLE`). So the initial page functor reflects
colimits of shape `J`.

## Main results

* `CategoryTheory.SpectralSequence.isColimitOfPage`: a cocone of spectral sequences whose cocones
  of pages are colimits is a colimit.
* `CategoryTheory.SpectralSequence.hasColimitsOfShape`: when colimits of shape `J` in `C` exist and
  are exact, spectral sequences in `C` have colimits of shape `J`, computed page by page.
* `CategoryTheory.SpectralSequence.preservesColimitsOfShape_pageFunctor`: every page functor
  preserves them.
* `CategoryTheory.SpectralSequence.isColimitPageOfLE`: if the cocone of `r`th pages of a cocone
  of spectral sequences is a colimit, so is its cocone of `r'`th pages for every `r ≤ r'`.
* `CategoryTheory.SpectralSequence.reflectsColimitsOfShape_pageFunctor`: the functor of the initial
  page reflects colimits of shape `J`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 3.49.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 2.6.15 (filtered colimits of modules are exact).
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits

variable {C : Type*} [Category* C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {J : Type*} [Category* J] {F : J ⥤ SpectralSequence C c r₀}

section IsColimit

variable [HasColimitsOfShape J C]

/-- Morphisms of pages from the cocone point of `s` to that of `t`, compatible with the legs,
commute with the identifications of the homology of a page with the next page, provided the
cocone of `r'`th pages of `s` is a colimit: after each leg of `s`, both sides become the
identification for `F.obj j` followed by the leg of `t`. -/
private lemma comm_of_isColimit {s t : Cocone F}
    (D : ∀ (r : ℤ) (hr : r₀ ≤ r), s.pt.page r hr ⟶ t.pt.page r hr)
    (hD : ∀ j (r : ℤ) (hr : r₀ ≤ r), (s.ι.app j).hom r hr ≫ D r hr = (t.ι.app j).hom r hr)
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (hs : IsColimit ((pageFunctor C c r₀ r' (by lia)).mapCocone s)) :
    HomologicalComplex.homologyMap (D r hr) pq ≫ (t.pt.iso r r' pq).hom =
      (s.pt.iso r r' pq).hom ≫ (D r' (by lia)).f pq := by
  rw [← cancel_epi (s.pt.iso r r' pq).inv, Iso.inv_hom_id_assoc]
  -- The legs of the evaluated cocone are the components of the legs of `s` up to unfolding
  -- `Functor.mapCocone`; the ascription states the goal with them so that `hD` applies.
  refine (isColimitOfPreserves (HomologicalComplex.eval C (c r') pq) hs).hom_ext
    (fun j ↦ (?_ : ((s.ι.app j).hom r' (by lia)).f pq ≫ _ = ((s.ι.app j).hom r' (by lia)).f pq ≫ _))
  -- After precomposing with `((F.obj j).iso r r' pq).hom`, `Hom.comm` for the legs of `s` and of
  -- `t` reduces both sides to the leg of `t`. The legs have
  -- codomain `((Functor.const J).obj _).obj j`; naming the cocone points as `E'` lets the rewrites
  -- match their identifications `s.pt.iso` and `t.pt.iso`.
  rw [← cancel_epi ((F.obj j).iso r r' pq).hom,
    ← Hom.comm_assoc (E' := s.pt) (s.ι.app j) r r' pq hrr' hr, Iso.hom_inv_id_assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, hD,
    Hom.comm (E' := t.pt) (t.ι.app j) r r' pq hrr' hr]
  simp [← HomologicalComplex.comp_f, hD]

/-- **A cocone of spectral sequences is a colimit if its cocones of pages are.** The descended
morphism is the descended morphism of pages on every page. -/
noncomputable def isColimitOfPage (s : Cocone F)
    (hs : ∀ (r : ℤ) (hr : r₀ ≤ r), IsColimit ((pageFunctor C c r₀ r hr).mapCocone s)) :
    IsColimit s where
  desc t :=
    { hom r hr := (hs r hr).desc ((pageFunctor C c r₀ r hr).mapCocone t)
      comm r r' pq hrr' hr :=
        comm_of_isColimit (fun r hr ↦ (hs r hr).desc ((pageFunctor C c r₀ r hr).mapCocone t))
          (fun j r hr ↦ (hs r hr).fac ((pageFunctor C c r₀ r hr).mapCocone t) j) r r' pq hrr' hr
          (hs r' (by lia)) }
  fac t j := by
    ext r hr : 1
    exact (hs r hr).fac ((pageFunctor C c r₀ r hr).mapCocone t) j
  uniq t m hm := by
    ext r hr : 1
    exact (hs r hr).uniq ((pageFunctor C c r₀ r hr).mapCocone t) (m.hom r) fun j ↦
      (comp_hom (s.ι.app j) m r hr).symm.trans (congrArg (fun f ↦ f.hom r hr) (hm j))

end IsColimit

section Exact

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- The cocone of `r'`th pages of a cocone `s` of spectral sequences is a colimit if its cocone
of `r`th pages is, for `r + 1 = r'`: in each position, the homology of the colimit page is the
colimit of the homologies, since homology commutes with exact colimits, and it is identified with
the next page, compatibly with the legs. -/
private noncomputable def isColimitPageOfSucc (s : Cocone F) (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (hs : IsColimit ((pageFunctor C c r₀ r hr).mapCocone s)) :
    IsColimit ((pageFunctor C c r₀ r' (by lia)).mapCocone s) :=
  HomologicalComplex.isColimitOfEval _ _ fun pq ↦
    (IsColimit.equivOfNatIsoOfIso
        (Functor.isoWhiskerLeft F (pageHomologyNatIso C c r₀ r r' pq hrr' hr))
        ((HomologicalComplex.homologyFunctor C (c r) pq).mapCocone
          ((pageFunctor C c r₀ r hr).mapCocone s))
        ((HomologicalComplex.eval C (c r') pq).mapCocone
          ((pageFunctor C c r₀ r' (by lia)).mapCocone s))
        -- The components of `pageHomologyNatIso` are the isomorphisms `(F.obj j).iso`, by
        -- `NatIso.ofComponents`, and the legs are those of `s` evaluated at `pq`, so the
        -- compatibility is `Hom.comm` for the leg at `j`.
        (Cocone.ext (s.pt.iso r r' pq) fun j ↦ (Category.assoc _ _ _).trans
          ((Iso.inv_comp_eq _).2 ((s.ι.app j).comm r r' pq hrr' hr))))
      (isColimitOfPreserves (HomologicalComplex.homologyFunctor C (c r) pq) hs)

/-- **Later pages of a colimit.** When colimits of shape `J` are exact, if the cocone of `r`th
pages of a cocone of spectral sequences is a colimit, then so is its cocone of `r'`th pages for
every `r' ≥ r`. -/
noncomputable def isColimitPageOfLE (s : Cocone F) (r : ℤ) (hr : r₀ ≤ r)
    (hs : IsColimit ((pageFunctor C c r₀ r hr).mapCocone s)) (r' : ℤ) (hrr' : r ≤ r') :
    IsColimit ((pageFunctor C c r₀ r' (hr.trans hrr')).mapCocone s) := by
  induction r', hrr' using Int.leInduction with
  | base => exact hs
  | succ r' hrr' ih => exact isColimitPageOfSucc s r' (r' + 1) rfl (hr.trans hrr') ih

/-- When colimits of shape `J` are exact, the functor sending a spectral sequence to its initial
page reflects colimits of shape `J`: a cocone of spectral sequences whose cocone of initial pages
is a colimit is a colimit. -/
instance reflectsColimitsOfShape_pageFunctor :
    ReflectsColimitsOfShape J (pageFunctor C c r₀ r₀) where
  reflectsColimit {_} := ⟨fun {s} hs ↦ ⟨isColimitOfPage s fun r hr ↦
    isColimitPageOfLE s r₀ le_rfl hs r hr⟩⟩

/-- The identification of the homology of the colimit of the `r`th pages of a diagram of spectral
sequences with the colimit of the `r'`th pages, for `r + 1 = r'`: both are colimits of the
pointwise homology of the `r`th pages, since homology commutes with exact colimits. -/
private noncomputable def colimitPageHomologyIso (F : J ⥤ SpectralSequence C c r₀) (r r' : ℤ)
    (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) :
    (colimit (F ⋙ pageFunctor C c r₀ r)).homology pq ≅
      (colimit (F ⋙ pageFunctor C c r₀ r' (by lia))).X pq :=
  IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves (HomologicalComplex.homologyFunctor C (c r) pq)
      (colimit.isColimit (F ⋙ pageFunctor C c r₀ r hr)))
    (isColimitOfPreserves (HomologicalComplex.eval C (c r') pq)
      (colimit.isColimit (F ⋙ pageFunctor C c r₀ r' (by lia))))
    (Functor.isoWhiskerLeft F (pageHomologyNatIso C c r₀ r r' pq hrr' hr))

/-- The legs of the colimit of the `r`th pages and of the `r'`th pages are compatible with
`colimitPageHomologyIso` and the identifications for the `F.obj j`. The statement is that of
`IsColimit.comp_coconePointsIsoOfNatIso_hom` with the components of `pageHomologyNatIso`
and the legs of the evaluated colimit cocones unfolded. -/
private lemma homologyMap_ι_colimitPageHomologyIso_hom (F : J ⥤ SpectralSequence C c r₀)
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (j : J) :
    HomologicalComplex.homologyMap (colimit.ι (F ⋙ pageFunctor C c r₀ r) j) pq ≫
        (colimitPageHomologyIso F r r' pq hrr' hr).hom =
      ((F.obj j).iso r r' pq).hom ≫ (colimit.ι (F ⋙ pageFunctor C c r₀ r' (by lia)) j).f pq :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (HomologicalComplex.homologyFunctor C (c r) pq)
      (colimit.isColimit (F ⋙ pageFunctor C c r₀ r hr)))
    (isColimitOfPreserves (HomologicalComplex.eval C (c r') pq)
      (colimit.isColimit (F ⋙ pageFunctor C c r₀ r' (by lia))))
    (Functor.isoWhiskerLeft F (pageHomologyNatIso C c r₀ r r' pq hrr' hr)) j

variable (F) in
/-- The pagewise colimit of a diagram `F` of spectral sequences, when colimits of shape `J`
are exact: its `r`th page is the colimit of the `r`th pages of the spectral sequences `F.obj j`,
and its legs are the colimit inclusions of pages. -/
private noncomputable def colimitCocone : Cocone F where
  pt :=
    { page r hr := colimit (F ⋙ pageFunctor C c r₀ r hr)
      iso r r' pq hrr' hr := colimitPageHomologyIso F r r' pq hrr' hr }
  ι :=
    { app j :=
        { hom r hr := colimit.ι (F ⋙ pageFunctor C c r₀ r hr) j
          comm r r' pq hrr' hr := homologyMap_ι_colimitPageHomologyIso_hom F r r' pq hrr' hr j }
      naturality j j' f := by
        ext r hr : 1
        simp only [Functor.const_obj_obj, Functor.const_obj_map, comp_hom,
          Category.comp_id]
        exact colimit.w (F ⋙ pageFunctor C c r₀ r hr) f }

variable (F) in
/-- The pagewise colimit cocone of a diagram of spectral sequences is a colimit cocone. -/
private noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfPage _ fun r hr ↦ colimit.isColimit (F ⋙ pageFunctor C c r₀ r hr)

/-- When colimits of shape `J` in `C` exist and are exact, so do colimits of shape `J` of spectral
sequences in `C`. -/
instance hasColimitsOfShape : HasColimitsOfShape J (SpectralSequence C c r₀) where
  has_colimit F := ⟨⟨⟨colimitCocone F, isColimitColimitCocone F⟩⟩⟩

/-- When colimits of shape `J` are exact, every page of a colimit of spectral sequences is the
colimit of the pages. -/
instance preservesColimitsOfShape_pageFunctor (r : ℤ) (hr : r₀ ≤ r) :
    PreservesColimitsOfShape J (pageFunctor C c r₀ r hr) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone
    (isColimitColimitCocone F) (colimit.isColimit (F ⋙ pageFunctor C c r₀ r hr))

end Exact

end CategoryTheory.SpectralSequence
