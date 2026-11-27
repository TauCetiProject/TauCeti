/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.SubquotientPresentation

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

The presentations and towers are compatible with rebasing to a later page `s ≥ r₀`
(`CategoryTheory.SpectralSequence.fromPage`): composing the page-`s` presentation of `E` with the
page-`r` presentation of `E.fromPage s hs` yields the page-`r` presentation of `E`
(`CategoryTheory.SpectralSequence.pagePresentation_trans_fromPage`), so the rebased cycle and
boundary subobjects at page `r ≥ s` are the images of `Z_r(pq)` and `B_r(pq)` under the page-`s`
presentation (`CategoryTheory.SpectralSequence.fromPage_cyclesSubobject_eq_image`,
`CategoryTheory.SpectralSequence.fromPage_boundariesSubobject_eq_image`).

## Main definitions

* `CategoryTheory.SpectralSequence.pagePresentation`: the presentation of `(E.page r).X pq` inside
  `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.cyclesSubobject`,
  `CategoryTheory.SpectralSequence.boundariesSubobject`: the cycle and boundary towers `Z_r(pq)`
  and `B_r(pq)`.

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
* `CategoryTheory.SpectralSequence.pagePresentation_trans_fromPage`,
  `CategoryTheory.SpectralSequence.preimage_fromPage_cyclesSubobject`,
  `CategoryTheory.SpectralSequence.preimage_fromPage_boundariesSubobject`,
  `CategoryTheory.SpectralSequence.fromPage_cyclesSubobject_eq_image`,
  `CategoryTheory.SpectralSequence.fromPage_boundariesSubobject_eq_image`,
  `CategoryTheory.SpectralSequence.orderIso_fromPage_cyclesSubobject`,
  `CategoryTheory.SpectralSequence.orderIso_fromPage_boundariesSubobject`: compatibility of the
  presentations and towers with rebasing.

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N), the construction after
  Definition 20.1.
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Lemma 2.2.
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits Subobject TauCeti

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence C c r₀) (pq : κ)

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

section Naturality

variable {E} {E' : SpectralSequence C c r₀}

/-- **Naturality of the presentations.** A morphism `f : E ⟶ E'` maps the presentation of the page
`r` of `E` at `pq` to that of `E'`, through its first-page component and over its page-`r`
component. -/
lemma pagePresentation_mapsTo (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
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
lemma cyclesSubobject_le_pullback (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesSubobject pq r) :=
  (pagePresentation_mapsTo pq f r hr).Z_le_pullback

/-- A morphism of spectral sequences maps the boundaries of each page into the boundaries of that
page. -/
lemma boundariesSubobject_le_pullback (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundariesSubobject pq r) :=
  (pagePresentation_mapsTo pq f r hr).B_le_pullback

/-- Under an isomorphism of spectral sequences, the cycles of `E` are the pullback of the cycles
of `E'` along the first-page component. -/
lemma pullback_cyclesSubobject_of_iso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.cyclesSubobject pq r) =
      E.cyclesSubobject pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (cyclesSubobject_le_pullback pq e.hom r hr) (cyclesSubobject_le_pullback pq e.inv r hr)

/-- Under an isomorphism of spectral sequences, the boundaries of `E` are the pullback of the
boundaries of `E'` along the first-page component. -/
lemma pullback_boundariesSubobject_of_iso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.boundariesSubobject pq r) =
      E.boundariesSubobject pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (boundariesSubobject_le_pullback pq e.hom r hr) (boundariesSubobject_le_pullback pq e.inv r hr)

end Naturality

section Rebase

/-- **Rebasing the presentations.** Composing the presentation of the page `s` of `E` with the
presentation of the page `r ≥ s` of `E` rebased at `s` gives the presentation of the page `r` of
`E`. -/
lemma pagePresentation_trans_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).trans ((E.fromPage s hs).pagePresentation pq r hsr) =
      E.pagePresentation pq r (hs.trans hsr) := by
  induction r, hsr using Int.leInduction with
  | base =>
    rw [pagePresentation_self, SubquotientPresentation.trans_refl]
  | succ k hk ih =>
    rw [pagePresentation_add_one _ _ k hk, SubquotientPresentation.trans_mapIso,
      ← SubquotientPresentation.trans_assoc, ih, pagePresentation_add_one _ _ k (hs.trans hk)]

/-- The preimage under the page-`s` presentation of the rebased cycles at page `r ≥ s` is
`Z_r(pq)`. -/
lemma preimage_fromPage_cyclesSubobject (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesSubobject pq r hsr) =
      E.cyclesSubobject pq r (hs.trans hsr) := by
  rw [← (E.fromPage s hs).pagePresentation_Z pq r hsr, ← E.pagePresentation_Z pq r (hs.trans hsr),
    ← SubquotientPresentation.trans_Z (E.pagePresentation pq s hs),
    E.pagePresentation_trans_fromPage pq s hs r hsr]

/-- The preimage under the page-`s` presentation of the rebased boundaries at page `r ≥ s` is
`B_r(pq)`. -/
lemma preimage_fromPage_boundariesSubobject (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSubobject pq r hsr) =
      E.boundariesSubobject pq r (hs.trans hsr) := by
  rw [← (E.fromPage s hs).pagePresentation_B pq r hsr, ← E.pagePresentation_B pq r (hs.trans hsr),
    ← SubquotientPresentation.trans_B (E.pagePresentation pq s hs),
    E.pagePresentation_trans_fromPage pq s hs r hsr]

/-- Seen in `(E.page s).X pq`, the rebased cycles at page `r ≥ s` are the image of `Z_r(pq)` under
the page-`s` presentation. -/
lemma fromPage_cyclesSubobject_eq_image (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.fromPage s hs).cyclesSubobject pq r hsr =
      (E.pagePresentation pq s hs).image (E.cyclesSubobject pq r (hs.trans hsr)) := by
  rw [← E.preimage_fromPage_cyclesSubobject pq s hs r hsr, SubquotientPresentation.image_preimage]

/-- Seen in `(E.page s).X pq`, the rebased boundaries at page `r ≥ s` are the image of `B_r(pq)`
under the page-`s` presentation. -/
lemma fromPage_boundariesSubobject_eq_image (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.fromPage s hs).boundariesSubobject pq r hsr =
      (E.pagePresentation pq s hs).image (E.boundariesSubobject pq r (hs.trans hsr)) := by
  rw [← E.preimage_fromPage_boundariesSubobject pq s hs r hsr,
    SubquotientPresentation.image_preimage]

/-- Under the order isomorphism of the page-`s` presentation, the rebased cycles at page `r ≥ s`
correspond to `Z_r(pq)` in `[B_s(pq), Z_s(pq)]`. -/
lemma orderIso_fromPage_cyclesSubobject (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).orderIso ((E.fromPage s hs).cyclesSubobject pq r hsr) =
      ⟨E.cyclesSubobject pq r (hs.trans hsr),
        (E.pagePresentation_B pq s hs).symm ▸
          E.boundariesSubobject_le_cyclesSubobject pq s r hs (hs.trans hsr),
        (E.pagePresentation_Z pq s hs).symm ▸ E.cyclesSubobject_anti pq hs hsr⟩ :=
  Subtype.ext ((SubquotientPresentation.coe_orderIso_apply _ _).trans
    (E.preimage_fromPage_cyclesSubobject pq s hs r hsr))

/-- Under the order isomorphism of the page-`s` presentation, the rebased boundaries at page `r ≥ s`
correspond to `B_r(pq)` in `[B_s(pq), Z_s(pq)]`. -/
lemma orderIso_fromPage_boundariesSubobject (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).orderIso ((E.fromPage s hs).boundariesSubobject pq r hsr) =
      ⟨E.boundariesSubobject pq r (hs.trans hsr),
        (E.pagePresentation_B pq s hs).symm ▸ E.boundariesSubobject_mono pq hs hsr,
        (E.pagePresentation_Z pq s hs).symm ▸
          E.boundariesSubobject_le_cyclesSubobject pq r s (hs.trans hsr) hs⟩ :=
  Subtype.ext ((SubquotientPresentation.coe_orderIso_apply _ _).trans
    (E.preimage_fromPage_boundariesSubobject pq s hs r hsr))

end Rebase

end CategoryTheory.SpectralSequence
