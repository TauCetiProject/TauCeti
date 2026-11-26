/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.SubquotientPresentation
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.CategoryTheory.Subobject.Basic

/-!
# The cycle and boundary towers of a spectral sequence

Each page of a spectral sequence `E` is the homology of the previous one, so the object at a
position `pq` on the page `r` is a subquotient `Z_r(pq) / B_r(pq)` of the object at `pq` on the
first page `r₀`. This file constructs these subquotient presentations by recursion over the
pages (`CategoryTheory.SpectralSequence.pagePresentation`). On the first page the presentation is
the identity one, by `⊥ ≤ ⊤`. From the page `r` to the page `r + 1`, the presentation of the
homology of the page `r` at `pq`, by the image of the entering differential and the kernel of the
leaving one, is pulled back along the presentation of the page `r`, and then transported along
the isomorphism `E.iso r (r + 1) pq` from that homology to the page `r + 1`.

The larger subobjects form the decreasing *cycle tower* `Z_r(pq)`
(`CategoryTheory.SpectralSequence.cyclesSubobject`) and the smaller ones the increasing *boundary
tower* `B_r(pq)` (`CategoryTheory.SpectralSequence.boundariesSubobject`) of subobjects of
`(E.page r₀).X pq`, with `B_r ≤ B_{r+1} ≤ Z_{r+1} ≤ Z_r`. The cycle tower stays the same from
`r` to `r + 1` exactly when the differential leaving `pq` on the page `r` vanishes, and the
boundary tower stays the same exactly when the differential entering `pq` vanishes. The object at
`pq` on the page `r` is zero exactly when `B_r(pq) = Z_r(pq)`.

The towers are natural: a morphism `f : E ⟶ E'` of spectral sequences maps the presentation of
each page of `E` to that of `E'` through its first-page component, over its component on that page
(`CategoryTheory.SpectralSequence.pagePresentation_mapsTo`). So the first-page component maps
`Z_r(E, pq)` into `Z_r(E', pq)` and `B_r(E, pq)` into `B_r(E', pq)`, and an isomorphism of spectral
sequences identifies the towers.

This file also provides rebasing (`CategoryTheory.SpectralSequence.fromPage`), stabilisation and
regularity predicates (`StabilisesAt`, `IsRegularAt`, `IsCoregularAt`, `DegeneratesAt`)
characterised by eventual constancy of the towers, and coherent stabilisation isomorphisms
(`CategoryTheory.SpectralSequence.pageXIsoOfStabilises`).

## Main definitions

* `CategoryTheory.SpectralSequence.fromPage`, `fromPageFunctor`: rebasing to a later page.
* `CategoryTheory.SpectralSequence.pagePresentation`: the presentation of `(E.page r).X pq` inside
  `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.cyclesSubobject`,
  `CategoryTheory.SpectralSequence.boundariesSubobject`: the cycle and boundary towers `Z_r(pq)`
  and `B_r(pq)`.
* `CategoryTheory.SpectralSequence.StabilisesAt`, `IsRegularAt`, `IsCoregularAt`, `DegeneratesAt`,
  and `pageXIsoOfStabilises`: stabilisation and degeneration criteria.

## Main results

* `CategoryTheory.SpectralSequence.pagePresentation_self`,
  `CategoryTheory.SpectralSequence.pagePresentation_add_one`: the recursion defining the
  presentations.
* `CategoryTheory.SpectralSequence.cyclesSubobject_add_one`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_add_one`: `Z_{r+1}` and `B_{r+1}` are the
  preimages of the kernel of the leaving differential and of the image of the entering one.
* `CategoryTheory.SpectralSequence.cyclesSubobject_anti`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_mono`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_le_cyclesSubobject`: the cycle tower
  decreases, the boundary tower increases, and every boundary subobject lies below every cycle
  subobject.
* `CategoryTheory.SpectralSequence.cyclesSubobject_add_one_eq_iff`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_add_one_eq_iff`: a tower stays the same
  from one page to the next exactly when the corresponding differential vanishes.
* `CategoryTheory.SpectralSequence.isZero_page_X_iff`: the object at `pq` on the page `r` is zero
  exactly when `B_r(pq) = Z_r(pq)`.
* `CategoryTheory.SpectralSequence.pagePresentation_mapsTo`,
  `CategoryTheory.SpectralSequence.cyclesSubobject_le_pullback`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_le_pullback`: naturality of the
  presentations and the towers in morphisms of spectral sequences.
* `CategoryTheory.SpectralSequence.pullback_cyclesSubobject_of_iso`,
  `CategoryTheory.SpectralSequence.pullback_boundariesSubobject_of_iso`: isomorphic spectral
  sequences have towers corresponding under the first-page isomorphism.

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N), the construction after
  Definition 20.1, and [Tag 0BDV](https://stacks.math.columbia.edu/tag/0BDV) (Lemma 12.24.8).
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Lemma 2.2.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits Subobject TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section FromPage

variable (E : SpectralSequence C c r₀)

/-- Rebase a spectral sequence `E` starting at page `r₀` to start at a later page `s ≥ r₀`. -/
abbrev fromPage (s : ℤ) (hs : r₀ ≤ s := by lia) : SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

@[simp]
lemma fromPage_page (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.fromPage s hs).page r hr = E.page r (hs.trans hr) := rfl

@[simp]
lemma fromPage_iso (s : ℤ) (hs : r₀ ≤ s) (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : s ≤ r) :
    (E.fromPage s hs).iso r r' pq hrr' hr = E.iso r r' pq hrr' (hs.trans hr) := rfl

/-- Restrict a morphism of spectral sequences to start at a later page `s ≥ r₀`. -/
def Hom.fromPage {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ)
    (hs : r₀ ≤ s := by lia) : E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
lemma Hom.fromPage_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) : (f.fromPage s hs).hom r hr = f.hom r (hs.trans hr) := (rfl)

/-- Rebasing spectral sequences from page `r₀` to page `s ≥ r₀`, as a functor. -/
@[expose, simps]
def fromPageFunctor (C : Type u) [Category.{v} C] [Abelian C] {κ : Type*}
    (c : ℤ → ComplexShape κ) (r₀ s : ℤ) (hs : r₀ ≤ s := by lia) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := f.fromPage s hs

lemma fromPage_fromPage (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).fromPage t hst = E.fromPage t (hs.trans hst) := rfl

end FromPage

section Tower

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- The presentation of the object at `pq` on the page `r` as a subquotient of the object at `pq`
on the first page `r₀`. On the first page it is the identity presentation; the presentation on the
page `r + 1` presents the homology of the page `r` at `pq` inside the presentation on the page
`r`, and transports it along `E.iso r (r + 1) pq`. -/
noncomputable def pagePresentation (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SubquotientPresentation ((E.page r₀).X pq) ((E.page r).X pq) :=
  Int.leInduction
    (motive := fun r hr ↦ SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq))
    (SubquotientPresentation.refl _)
    (fun s hs P ↦ (P.trans ((E.page s).sc pq).homologyPresentation).mapIso (E.iso s (s + 1) pq))
    r hr

/-- On the first page, the presentation is the identity presentation. -/
@[simp]
lemma pagePresentation_self : E.pagePresentation pq r₀ le_rfl = SubquotientPresentation.refl _ :=
  Int.leInduction_base _ _

/-- The presentation on the page `r + 1` is the presentation of the homology of the page `r` at
`pq`, taken inside the presentation on the page `r`, and transported along `E.iso r (r + 1) pq`.
-/
lemma pagePresentation_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) =
      ((E.pagePresentation pq r hr).trans ((E.page r).sc pq).homologyPresentation).mapIso
        (E.iso r (r + 1) pq) :=
  Int.leInduction_add_one _ _ r hr

/-- The cycle tower `Z_r(pq)`: the subobject of the object at `pq` on the first page whose
quotient by the boundary subobject `B_r(pq)` is the object at `pq` on the page `r`. It consists of
the elements that survive to the page `r`. -/
noncomputable def cyclesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).Z

/-- The boundary tower `B_r(pq)`: the subobject of the object at `pq` on the first page that is
divided out in the object at `pq` on the page `r`. It consists of the elements that are boundaries
by the page `r`. -/
noncomputable def boundariesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).B

@[simp]
lemma pagePresentation_Z (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).Z = E.cyclesSubobject pq r :=
  (rfl)

@[simp]
lemma pagePresentation_B (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).B = E.boundariesSubobject pq r :=
  (rfl)

/-- On the first page every element is a cycle. -/
@[simp]
lemma cyclesSubobject_self : E.cyclesSubobject pq r₀ le_rfl = ⊤ := by
  rw [cyclesSubobject, pagePresentation_self, SubquotientPresentation.refl_Z]

/-- On the first page only zero is a boundary. -/
@[simp]
lemma boundariesSubobject_self : E.boundariesSubobject pq r₀ le_rfl = ⊥ := by
  rw [boundariesSubobject, pagePresentation_self, SubquotientPresentation.refl_B]

/-- The cycles of the page `r + 1` are the preimage, under the presentation of the page `r`, of
the kernel of the differential of the page `r` leaving `pq`. -/
lemma cyclesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r).dFrom pq)) := by
  rw [cyclesSubobject, pagePresentation_add_one _ _ r hr, SubquotientPresentation.mapIso_Z,
    SubquotientPresentation.trans_Z, ShortComplex.homologyPresentation_Z,
    HomologicalComplex.shortComplexFunctor_obj_g]

/-- The boundaries of the page `r + 1` are the preimage, under the presentation of the page `r`,
of the image of the differential of the page `r` entering `pq`. -/
lemma boundariesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r).dTo pq)) := by
  rw [boundariesSubobject, pagePresentation_add_one _ _ r hr, SubquotientPresentation.mapIso_B,
    SubquotientPresentation.trans_B, ShortComplex.homologyPresentation_B,
    HomologicalComplex.shortComplexFunctor_obj_f]

/-- On each page, every boundary is a cycle. -/
lemma boundariesSubobject_le_cyclesSubobject_self (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r ≤ E.cyclesSubobject pq r :=
  (E.pagePresentation pq r hr).le

/-- The cycles of the page `r + 1` are cycles of the page `r`. -/
lemma cyclesSubobject_add_one_le (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r := by
  rw [cyclesSubobject_add_one]
  exact (E.pagePresentation pq r hr).preimage_le_Z _

/-- The boundaries of the page `r` are boundaries of the page `r + 1`. -/
lemma boundariesSubobject_le_boundariesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
  rw [boundariesSubobject_add_one]
  exact (E.pagePresentation pq r hr).B_le_preimage _

/-- The cycle tower is decreasing. -/
lemma cyclesSubobject_anti {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.cyclesSubobject pq r' (hr.trans hrr') ≤ E.cyclesSubobject pq r := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih => exact (E.cyclesSubobject_add_one_le pq s (hr.trans hrs)).trans ih

/-- The boundary tower is increasing. -/
lemma boundariesSubobject_mono {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.boundariesSubobject pq r ≤ E.boundariesSubobject pq r' (hr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih =>
    exact ih.trans (E.boundariesSubobject_le_boundariesSubobject_add_one pq s (hr.trans hrs))

/-- Every boundary subobject lies below every cycle subobject: `B_r(pq) ≤ Z_{r'}(pq)` for all
pages `r` and `r'`. -/
lemma boundariesSubobject_le_cyclesSubobject (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r₀ ≤ r') :
    E.boundariesSubobject pq r ≤ E.cyclesSubobject pq r' := by
  rcases le_total r r' with h | h
  · exact (E.boundariesSubobject_mono pq hr h).trans
      (E.boundariesSubobject_le_cyclesSubobject_self pq r' hr')
  · exact (E.boundariesSubobject_le_cyclesSubobject_self pq r hr).trans
      (E.cyclesSubobject_anti pq hr' h)

/-- The cycles do not change from the page `r` to the page `r + 1` exactly when the differential
of the page `r` leaving `pq` vanishes. -/
lemma cyclesSubobject_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r ↔
      (E.page r).dFrom pq = 0 := by
  rw [E.cyclesSubobject_add_one pq r hr, ← E.pagePresentation_Z pq r hr,
    ← SubquotientPresentation.preimage_top, SubquotientPresentation.preimage_inj]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, kernelSubobject_zero]⟩
  rw [← Category.id_comp ((E.page r).dFrom pq), ← kernelSubobject_factors_iff, h]
  exact top_factors _

/-- The boundaries do not change from the page `r` to the page `r + 1` exactly when the
differential of the page `r` entering `pq` vanishes. -/
lemma boundariesSubobject_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r ↔
      (E.page r).dTo pq = 0 := by
  rw [E.boundariesSubobject_add_one pq r hr, ← E.pagePresentation_B pq r hr,
    ← SubquotientPresentation.preimage_bot, SubquotientPresentation.preimage_inj]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, imageSubobject_zero]⟩
  rw [← bot_factors_iff_zero, ← h]
  simpa using imageSubobject_factors_comp_self ((E.page r).dTo pq) (𝟙 _)

/-- The object at `pq` on the page `r` is zero exactly when its boundary and cycle subobjects
agree. -/
lemma isZero_page_X_iff (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) ↔ E.boundariesSubobject pq r = E.cyclesSubobject pq r :=
  (E.pagePresentation pq r hr).isZero_iff_B_eq_Z

/-- Rebasing compatibility for `pagePresentation`. -/
lemma pagePresentation_eq_comp_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).trans ((E.fromPage s hs).pagePresentation pq r hsr) := by
  induction r, hsr using Int.leInduction with
  | base => rw [pagePresentation_self, SubquotientPresentation.trans_refl]
  | succ r hsr ih =>
    rw [pagePresentation_add_one E pq r (hs.trans hsr),
      pagePresentation_add_one (E.fromPage s hs) pq r hsr, ih, SubquotientPresentation.trans_assoc,
      SubquotientPresentation.trans_mapIso]

/-- Rebasing compatibility for cycles. -/
lemma cyclesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesSubobject pq r hsr) :=
  congrArg SubquotientPresentation.Z (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

/-- Rebasing compatibility for boundaries. -/
lemma boundariesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSubobject pq r hsr) :=
  congrArg SubquotientPresentation.B (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

end Tower

section Naturality

variable {E} {E' : SpectralSequence C c r₀}

/-- **Naturality of the presentations.** A morphism `f : E ⟶ E'` maps the presentation of the page
`r` of `E` at `pq` to that of `E'`, through its first-page component and over its page-`r`
component. -/
lemma pagePresentation_mapsTo (pq : κ) (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).MapsTo (E'.pagePresentation pq r hr) ((f.hom r₀).f pq)
      ((f.hom r).f pq) := by
  induction r, hr using Int.leInduction with
  | base =>
    rw [pagePresentation_self, pagePresentation_self]
    exact SubquotientPresentation.mapsTo_refl _
  | succ s hs ih =>
    rw [pagePresentation_add_one, pagePresentation_add_one]
    exact (ih.trans (ShortComplex.homologyPresentation_mapsTo _
      ((HomologicalComplex.shortComplexFunctor C (c s) pq).map (f.hom s)))).mapIso
        (f.comm s (s + 1) pq)

/-- A morphism of spectral sequences maps the cycles of each page into the cycles of that page. -/
lemma cyclesSubobject_le_pullback (pq : κ) (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesSubobject pq r) :=
  (pagePresentation_mapsTo pq f r hr).Z_le_pullback

/-- A morphism of spectral sequences maps the boundaries of each page into the boundaries of that
page. -/
lemma boundariesSubobject_le_pullback (pq : κ) (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundariesSubobject pq r) :=
  (pagePresentation_mapsTo pq f r hr).B_le_pullback

/-- Naturality of the cycle tower: `f : E ⟶ E'` maps `Z_r(E, pq)` into `Z_r(E', pq)`. -/
lemma Hom.exists_cyclesSubobject_le (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) ≤
      E'.cyclesSubobject pq r hr :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mpr (cyclesSubobject_le_pullback pq f r hr)

/-- Naturality of the boundary tower: `f : E ⟶ E'` maps `B_r(E, pq)` into `B_r(E', pq)`. -/
lemma Hom.exists_boundariesSubobject_le (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mpr (boundariesSubobject_le_pullback pq f r hr)

/-- The morphism induced by `(f.hom r₀).f pq` on `pagePresentation` is `(f.hom r).f pq`. -/
lemma Hom.mapInduced_pagePresentation (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr) ((f.hom r₀).f pq)
        (by rw [pagePresentation_Z]; exact f.exists_cyclesSubobject_le pq r hr)
        (by rw [pagePresentation_B]; exact f.exists_boundariesSubobject_le pq r hr) =
      (f.hom r hr).f pq :=
  (pagePresentation_mapsTo pq f r hr).mapInduced_eq _ _

/-- Under an isomorphism of spectral sequences, the cycles of `E` are the pullback of the cycles
of `E'` along the first-page component. -/
lemma pullback_cyclesSubobject_of_iso (pq : κ) (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.cyclesSubobject pq r) =
      E.cyclesSubobject pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (cyclesSubobject_le_pullback pq e.hom r hr) (cyclesSubobject_le_pullback pq e.inv r hr)

/-- Under an isomorphism of spectral sequences, the boundaries of `E` are the pullback of the
boundaries of `E'` along the first-page component. -/
lemma pullback_boundariesSubobject_of_iso (pq : κ) (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.boundariesSubobject pq r) =
      E.boundariesSubobject pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (boundariesSubobject_le_pullback pq e.hom r hr) (boundariesSubobject_le_pullback pq e.inv r hr)

/-- An isomorphism `e : E ≅ E'` carries `Z_r(E, pq)` onto `Z_r(E', pq)`. -/
lemma exists_cyclesSubobject_eq_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr := by
  rw [← pullback_cyclesSubobject_of_iso pq e r hr, Subobject.exists_pullback_eq_self_of_epi]

/-- An isomorphism `e : E ≅ E'` carries `B_r(E, pq)` onto `B_r(E', pq)`. -/
lemma exists_boundariesSubobject_eq_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr := by
  rw [← pullback_boundariesSubobject_of_iso pq e r hr, Subobject.exists_pullback_eq_self_of_epi]

end Naturality

section Stabilisation

section

variable (E : SpectralSequence C c r₀)

/-- `E` *stabilises at `pq` from page `s`* if on every page `r ≥ s`, both the differential leaving
`pq` and the differential entering `pq` vanish. -/
def StabilisesAt (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) : Prop :=
  ∀ (r : ℤ) (hsr : s ≤ r),
    (E.page r (hs.trans hsr)).dFrom pq = 0 ∧ (E.page r (hs.trans hsr)).dTo pq = 0

/-- `E` is *regular at `pq`* if the differentials leaving `pq` vanish from some page onward. -/
def IsRegularAt (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0

/-- `E` is *coregular at `pq`* if the differentials entering `pq` vanish from some page onward. -/
def IsCoregularAt (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0

/-- `E` *degenerates at page `s`* if every differential on every page `r ≥ s` vanishes. -/
def DegeneratesAt (s : ℤ) (hs : r₀ ≤ s := by lia) : Prop :=
  ∀ (r : ℤ) (hsr : s ≤ r) (i j : κ), (E.page r (hs.trans hsr)).d i j = 0

lemma stabilisesAt_iff (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dFrom pq = 0 ∧ (E.page r (hs.trans hsr)).dTo pq = 0 :=
  Iff.rfl

lemma isRegularAt_iff (pq : κ) :
    E.IsRegularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dFrom pq = 0 :=
  Iff.rfl

lemma isCoregularAt_iff (pq : κ) :
    E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dTo pq = 0 :=
  Iff.rfl

lemma degeneratesAt_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r) (i j : κ),
      (E.page r (hs.trans hsr)).d i j = 0 :=
  Iff.rfl

end

section

variable {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs)
include h

lemma StabilisesAt.dFrom_eq_zero {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dFrom pq = 0 := (h r hsr).1

lemma StabilisesAt.dTo_eq_zero {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dTo pq = 0 := (h r hsr).2

lemma StabilisesAt.d_out {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq pq' = 0 :=
  ((E.page r (hs.trans hsr)).dFrom_eq_zero_iff pq).mp (h.dFrom_eq_zero hsr) pq'

lemma StabilisesAt.d_in {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq' pq = 0 :=
  ((E.page r (hs.trans hsr)).dTo_eq_zero_iff pq).mp (h.dTo_eq_zero hsr) pq'

/-- Stabilisation from page `s` persists to every later page `s' ≥ s`. -/
lemma StabilisesAt.of_le {s' : ℤ} (hss' : s ≤ s') : E.StabilisesAt pq s' (hs.trans hss') :=
  fun r hs'r ↦ h r (hss'.trans hs'r)

lemma StabilisesAt.isRegularAt : E.IsRegularAt pq := ⟨s, hs, fun r hsr ↦ (h r hsr).1⟩

lemma StabilisesAt.isCoregularAt : E.IsCoregularAt pq := ⟨s, hs, fun r hsr ↦ (h r hsr).2⟩

end

lemma DegeneratesAt.d_eq_zero {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) {r : ℤ} (hsr : s ≤ r) (i j : κ) :
    (E.page r (hs.trans hsr)).d i j = 0 :=
  hd r hsr i j

/-- Degeneration at page `s` persists to every later page `s' ≥ s`. -/
lemma DegeneratesAt.of_le {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) {s' : ℤ} (hss' : s ≤ s') : E.DegeneratesAt s' (hs.trans hss') :=
  fun r hs'r i j ↦ hd r (hss'.trans hs'r) i j

/-- Degeneration at page `s` implies stabilisation at every position from page `s`. -/
lemma DegeneratesAt.stabilisesAt {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) (pq : κ) : E.StabilisesAt pq s hs :=
  fun r hsr ↦ ⟨hd r hsr pq _, hd r hsr _ pq⟩

section

variable (E : SpectralSequence C c r₀) (pq : κ)

lemma stabilisesAt_iff_forall_d_eq_zero (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r) (pq' : κ),
      (E.page r (hs.trans hsr)).d pq pq' = 0 ∧ (E.page r (hs.trans hsr)).d pq' pq = 0 :=
  ⟨fun h _ hsr pq' ↦ ⟨h.d_out hsr pq', h.d_in hsr pq'⟩,
   fun h r hsr ↦
     ⟨((E.page r (hs.trans hsr)).dFrom_eq_zero_iff pq).mpr (fun pq' ↦ (h r hsr pq').1),
      ((E.page r (hs.trans hsr)).dTo_eq_zero_iff pq).mpr (fun pq' ↦ (h r hsr pq').2)⟩⟩

/-- `E` is both regular and coregular at `pq` iff it stabilises at `pq` from some page. -/
lemma isRegularAt_and_isCoregularAt_iff_exists_stabilisesAt :
    E.IsRegularAt pq ∧ E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), E.StabilisesAt pq s hs :=
  ⟨fun ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, _, h₂⟩⟩ ↦ ⟨max s₁ s₂, hs₁.trans (le_max_left s₁ s₂), fun r hr ↦
      ⟨h₁ r ((le_max_left s₁ s₂).trans hr), h₂ r ((le_max_right s₁ s₂).trans hr)⟩⟩,
   fun ⟨_, _, h⟩ ↦ ⟨h.isRegularAt, h.isCoregularAt⟩⟩

/-- `E` degenerates at page `s` iff it stabilises at every position from page `s`. -/
lemma degeneratesAt_iff_forall_stabilisesAt (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ ∀ pq : κ, E.StabilisesAt pq s hs :=
  ⟨fun h pq ↦ h.stabilisesAt pq, fun h _ hsr i j ↦ (h i).d_out hsr j⟩

/-- If differentials leaving `pq` vanish from page `s` onward, `Z_r(pq) = Z_s(pq)` for `r ≥ s`. -/
lemma cyclesSubobject_eq_of_forall_dFrom_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih => rw [(E.cyclesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- If differentials entering `pq` vanish from page `s` onward, `B_r(pq) = B_s(pq)` for `r ≥ s`. -/
lemma boundariesSubobject_eq_of_forall_dTo_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih =>
    rw [(E.boundariesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- `E` is regular at `pq` if and only if the cycle tower `r ↦ Z_r(pq)` is eventually constant. -/
lemma isRegularAt_iff_eventually_const_cyclesSubobject :
    E.IsRegularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs h⟩,
   fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun r hsr ↦ (E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp
      (by rw [h (r + 1) (Int.le_add_one hsr), h r hsr])⟩⟩

/-- `E` is coregular at `pq` iff the boundary tower `r ↦ B_r(pq)` is eventually constant. -/
lemma isCoregularAt_iff_eventually_const_boundariesSubobject :
    E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs h⟩,
   fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun r hsr ↦
      (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp
        (by rw [h (r + 1) (Int.le_add_one hsr), h r hsr])⟩⟩

/-- `E` stabilises at `pq` from page `s` iff `Z_r(pq)` and `B_r(pq)` are constant for `r ≥ s`. -/
lemma stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r),
      E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs ∧
        E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ⟨fun h r hsr ↦
      ⟨E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs (fun _ ↦ h.dFrom_eq_zero) r hsr,
       E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs (fun _ ↦ h.dTo_eq_zero) r hsr⟩,
   fun h r hsr ↦ ⟨(E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp
        (by rw [(h (r + 1) (Int.le_add_one hsr)).1, (h r hsr).1]),
      (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp
        (by rw [(h (r + 1) (Int.le_add_one hsr)).2, (h r hsr).2])⟩⟩

lemma stabilisesAt_fromPage_iff (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).StabilisesAt pq t hst ↔ E.StabilisesAt pq t (hs.trans hst) := Iff.rfl

lemma isRegularAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsRegularAt pq ↔ E.IsRegularAt pq :=
  ⟨fun ⟨t, hst, h⟩ ↦ ⟨t, hs.trans hst, h⟩,
   fun ⟨t, _, h⟩ ↦ ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩⟩

lemma isCoregularAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsCoregularAt pq ↔ E.IsCoregularAt pq :=
  ⟨fun ⟨t, hst, h⟩ ↦ ⟨t, hs.trans hst, h⟩,
   fun ⟨t, _, h⟩ ↦ ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩⟩

lemma degeneratesAt_fromPage_iff (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).DegeneratesAt t hst ↔ E.DegeneratesAt t (hs.trans hst) := Iff.rfl

/-- When `E` stabilises at `pq` from page `s`, the canonical iso `(E.page s).X pq ≅ (E.page r).X pq`
for `r ≥ s`. -/
noncomputable def pageXIsoOfStabilises (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (r : ℤ)
    (hsr : s ≤ r) : (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq :=
  Int.leInduction (motive := fun r hsr ↦ (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq)
    (Iso.refl _)
    (fun t hst e ↦ e ≪≫
      (E.page t (hs.trans hst)).XIsoHomologyOfDEqZero pq
        (h.dTo_eq_zero hst) (h.dFrom_eq_zero hst) ≪≫
      E.iso t (t + 1) pq rfl (hs.trans hst)) r hsr

@[simp]
lemma pageXIsoOfStabilises_self (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.pageXIsoOfStabilises pq s hs h s le_rfl = Iso.refl _ := Int.leInduction_base _ _

lemma pageXIsoOfStabilises_add_one (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (t : ℤ)
    (hst : s ≤ t) :
    E.pageXIsoOfStabilises pq s hs h (t + 1) (Int.le_add_one hst) =
      E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        (E.page t (hs.trans hst)).XIsoHomologyOfDEqZero pq
          (h.dTo_eq_zero hst) (h.dFrom_eq_zero hst) ≪≫
        E.iso t (t + 1) pq rfl (hs.trans hst) := Int.leInduction_add_one _ _ t hst

/-- When `E` stabilises at `pq` from page `s`, `pagePresentation` on page `r ≥ s` is the
page-`s` presentation transported along `pageXIsoOfStabilises`. -/
lemma pagePresentation_eq_mapIso_pageXIsoOfStabilises (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h r hsr) := by
  induction r, hsr using Int.leInduction with
  | base => rw [pageXIsoOfStabilises_self, SubquotientPresentation.mapIso_refl]
  | succ t hst ih =>
    rw [pagePresentation_add_one E pq t (hs.trans hst), ih,
      pageXIsoOfStabilises_add_one E pq s hs h t hst,
      ShortComplex.homologyPresentation_eq_refl_mapIso _ (h.dTo_eq_zero hst) (h.dFrom_eq_zero hst),
      ← HomologicalComplex.XIsoHomologyOfDEqZero_eq_shortComplex,
      SubquotientPresentation.trans_mapIso]
    have htr : ((E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h t hst)).trans
        (SubquotientPresentation.refl (((E.page t (hs.trans hst)).sc pq).X₂)) =
      (E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h t hst) :=
      SubquotientPresentation.trans_refl _
    rw [htr, SubquotientPresentation.mapIso_trans, SubquotientPresentation.mapIso_trans]

/-- Composition compatibility of `pageXIsoOfStabilises` for `s ≤ t ≤ r`. -/
lemma pageXIsoOfStabilises_trans {s t r : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs)
    (hst : s ≤ t) (htr : t ≤ r) :
    E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        E.pageXIsoOfStabilises pq t (hs.trans hst) (h.of_le hst) r htr =
      E.pageXIsoOfStabilises pq s hs h r (hst.trans htr) := by
  induction r, htr using Int.leInduction with
  | base => rw [pageXIsoOfStabilises_self, Iso.trans_refl]
  | succ u htu ih =>
    rw [pageXIsoOfStabilises_add_one E pq t (hs.trans hst) (h.of_le hst) u htu,
      pageXIsoOfStabilises_add_one E pq s hs h u (hst.trans htu), ← Iso.trans_assoc, ih]

lemma pageXIsoOfStabilises_fromPage {s t r : ℤ} (hs : r₀ ≤ s) (hst : s ≤ t)
    (h : E.StabilisesAt pq t (hs.trans hst)) (htr : t ≤ r) :
    (E.fromPage s hs).pageXIsoOfStabilises pq t hst
        ((E.stabilisesAt_fromPage_iff pq s t hs hst).mpr h) r htr =
      E.pageXIsoOfStabilises pq t (hs.trans hst) h r htr := by
  induction r, htr using Int.leInduction with
  | base => rw [pageXIsoOfStabilises_self, pageXIsoOfStabilises_self]
  | succ u htu ih =>
    rw [pageXIsoOfStabilises_add_one (E.fromPage s hs) pq t hst
        ((E.stabilisesAt_fromPage_iff pq s t hs hst).mpr h) u htu,
      pageXIsoOfStabilises_add_one E pq t (hs.trans hst) h u htu, ih]

end

section

variable {E E' : SpectralSequence C c r₀}

lemma StabilisesAt.cyclesSubobject_eq {pq : κ} {s : ℤ} {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs)
    (r : ℤ) (hsr : s ≤ r) : E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).1

lemma StabilisesAt.boundariesSubobject_eq {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).2

lemma DegeneratesAt.cyclesSubobject_eq_top (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : E.cyclesSubobject pq r hr = ⊤ := by
  rw [(h.stabilisesAt pq).cyclesSubobject_eq r hr, cyclesSubobject_self]

lemma DegeneratesAt.boundariesSubobject_eq_bot (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : E.boundariesSubobject pq r hr = ⊥ := by
  rw [(h.stabilisesAt pq).boundariesSubobject_eq r hr, boundariesSubobject_self]

/-- Naturality of `pageXIsoOfStabilises` with respect to morphisms of spectral sequences. -/
@[reassoc]
lemma Hom.pageXIsoOfStabilises_naturality (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (h' : E'.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    (f.hom s hs).f pq ≫ (E'.pageXIsoOfStabilises pq s hs h' r hsr).hom =
      (E.pageXIsoOfStabilises pq s hs h r hsr).hom ≫ (f.hom r (hs.trans hsr)).f pq := by
  induction r, hsr using Int.leInduction with
  | base => simp
  | succ t hst ih =>
    rw [pageXIsoOfStabilises_add_one E' pq s hs h' t hst,
      pageXIsoOfStabilises_add_one E pq s hs h t hst]
    simp only [Iso.trans_hom, Category.assoc]
    rw [reassoc_of% ih, HomologicalComplex.XIsoHomologyOfDEqZero_hom_naturality_assoc,
      f.comm t (t + 1) pq rfl (hs.trans hst)]

variable (e : E ≅ E')
include e

/-- Isomorphic spectral sequences have the same vanishing differentials on every page. -/
lemma page_d_eq_zero_iff_of_iso (r : ℤ) (hr : r₀ ≤ r) (i j : κ) :
    (E.page r hr).d i j = 0 ↔ (E'.page r hr).d i j = 0 := by
  have hcomm := (e.hom.hom r hr).comm i j
  exact ⟨fun h ↦ (cancel_epi ((e.hom.hom r hr).f i)).mp (by rw [comp_zero, hcomm, h, zero_comp]),
    fun h ↦ (cancel_mono ((e.hom.hom r hr).f j)).mp (by rw [zero_comp, ← hcomm, h, comp_zero])⟩

/-- Isomorphic spectral sequences stabilise at the same positions and pages. -/
lemma stabilisesAt_iff_of_iso (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ E'.StabilisesAt pq s hs := by
  simp only [StabilisesAt, HomologicalComplex.dFrom, HomologicalComplex.dTo,
    page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are regular at the same positions. -/
lemma isRegularAt_iff_of_iso (pq : κ) : E.IsRegularAt pq ↔ E'.IsRegularAt pq := by
  simp only [IsRegularAt, HomologicalComplex.dFrom, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are coregular at the same positions. -/
lemma isCoregularAt_iff_of_iso (pq : κ) : E.IsCoregularAt pq ↔ E'.IsCoregularAt pq := by
  simp only [IsCoregularAt, HomologicalComplex.dTo, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences degenerate at the same pages. -/
lemma degeneratesAt_iff_of_iso (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ E'.DegeneratesAt s hs := by
  simp only [DegeneratesAt, page_d_eq_zero_iff_of_iso e]

end

end Stabilisation

end CategoryTheory.SpectralSequence
