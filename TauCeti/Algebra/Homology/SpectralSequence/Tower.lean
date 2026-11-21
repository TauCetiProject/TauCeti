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
(`CategoryTheory.SpectralSequence.cycles`) and the smaller ones the increasing *boundary tower*
`B_r(pq)` (`CategoryTheory.SpectralSequence.boundaries`) of subobjects of `(E.page r₀).X pq`, with
`B_r ≤ B_{r+1} ≤ Z_{r+1} ≤ Z_r`. The cycle tower stays the same from `r` to `r + 1` exactly when
the differential leaving `pq` on the page `r` vanishes, and the boundary tower stays the same
exactly when the differential entering `pq` vanishes. The object at `pq` on the page `r` is zero
exactly when `B_r(pq) = Z_r(pq)`.

The towers are natural: a morphism `f : E ⟶ E'` of spectral sequences maps the presentation of
each page of `E` to that of `E'` through its first-page component, over its component on that page
(`CategoryTheory.SpectralSequence.pagePresentation_mapsTo`). So the first-page component maps
`Z_r(E, pq)` into `Z_r(E', pq)` and `B_r(E, pq)` into `B_r(E', pq)`, and an isomorphism of spectral
sequences identifies the towers.

## Main definitions

* `CategoryTheory.SpectralSequence.pagePresentation`: the presentation of `(E.page r).X pq` inside
  `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.cycles`, `CategoryTheory.SpectralSequence.boundaries`: the
  cycle and boundary towers `Z_r(pq)` and `B_r(pq)`.

## Main results

* `CategoryTheory.SpectralSequence.pagePresentation_self`,
  `CategoryTheory.SpectralSequence.pagePresentation_add_one`: the recursion defining the
  presentations.
* `CategoryTheory.SpectralSequence.cycles_add_one`,
  `CategoryTheory.SpectralSequence.boundaries_add_one`: `Z_{r+1}` and `B_{r+1}` are the preimages
  of the kernel of the leaving differential and of the image of the entering one.
* `CategoryTheory.SpectralSequence.cycles_anti`,
  `CategoryTheory.SpectralSequence.boundaries_mono`,
  `CategoryTheory.SpectralSequence.boundaries_le_cycles`: the cycle tower decreases, the boundary
  tower increases, and every boundary subobject lies below every cycle subobject.
* `CategoryTheory.SpectralSequence.cycles_add_one_eq_iff`,
  `CategoryTheory.SpectralSequence.boundaries_add_one_eq_iff`: a tower stays the same from one
  page to the next exactly when the corresponding differential vanishes.
* `CategoryTheory.SpectralSequence.isZero_page_X_iff`: the object at `pq` on the page `r` is zero
  exactly when `B_r(pq) = Z_r(pq)`.
* `CategoryTheory.SpectralSequence.pagePresentation_mapsTo`,
  `CategoryTheory.SpectralSequence.cycles_le_pullback`,
  `CategoryTheory.SpectralSequence.boundaries_le_pullback`: naturality of the presentations and the
  towers in morphisms of spectral sequences.
* `CategoryTheory.SpectralSequence.pullback_cycles_of_iso`,
  `CategoryTheory.SpectralSequence.pullback_boundaries_of_iso`: isomorphic spectral sequences have
  towers corresponding under the first-page isomorphism.

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
noncomputable def cycles (r : ℤ) (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).Z

/-- The boundary tower `B_r(pq)`: the subobject of the object at `pq` on the first page that is
divided out in the object at `pq` on the page `r`. It consists of the elements that are boundaries
by the page `r`. -/
noncomputable def boundaries (r : ℤ) (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).B

@[simp]
lemma pagePresentation_Z (r : ℤ) (hr : r₀ ≤ r) : (E.pagePresentation pq r hr).Z = E.cycles pq r :=
  (rfl)

@[simp]
lemma pagePresentation_B (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).B = E.boundaries pq r :=
  (rfl)

/-- On the first page every element is a cycle. -/
@[simp]
lemma cycles_self : E.cycles pq r₀ le_rfl = ⊤ := by
  rw [cycles, pagePresentation_self, SubquotientPresentation.refl_Z]

/-- On the first page only zero is a boundary. -/
@[simp]
lemma boundaries_self : E.boundaries pq r₀ le_rfl = ⊥ := by
  rw [boundaries, pagePresentation_self, SubquotientPresentation.refl_B]

/-- The cycles of the page `r + 1` are the preimage, under the presentation of the page `r`, of
the kernel of the differential of the page `r` leaving `pq`. -/
lemma cycles_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.cycles pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r).dFrom pq)) := by
  rw [cycles, pagePresentation_add_one _ _ r hr, SubquotientPresentation.mapIso_Z,
    SubquotientPresentation.trans_Z, ShortComplex.homologyPresentation_Z,
    HomologicalComplex.shortComplexFunctor_obj_g]

/-- The boundaries of the page `r + 1` are the preimage, under the presentation of the page `r`,
of the image of the differential of the page `r` entering `pq`. -/
lemma boundaries_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundaries pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r).dTo pq)) := by
  rw [boundaries, pagePresentation_add_one _ _ r hr, SubquotientPresentation.mapIso_B,
    SubquotientPresentation.trans_B, ShortComplex.homologyPresentation_B,
    HomologicalComplex.shortComplexFunctor_obj_f]

/-- On each page, every boundary is a cycle. -/
lemma boundaries_le_cycles_self (r : ℤ) (hr : r₀ ≤ r) : E.boundaries pq r ≤ E.cycles pq r :=
  (E.pagePresentation pq r hr).le

/-- The cycles of the page `r + 1` are cycles of the page `r`. -/
lemma cycles_add_one_le (r : ℤ) (hr : r₀ ≤ r) :
    E.cycles pq (r + 1) (Int.le_add_one hr) ≤ E.cycles pq r := by
  rw [cycles_add_one]
  exact (E.pagePresentation pq r hr).preimage_le_Z _

/-- The boundaries of the page `r` are boundaries of the page `r + 1`. -/
lemma boundaries_le_boundaries_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundaries pq r ≤ E.boundaries pq (r + 1) (Int.le_add_one hr) := by
  rw [boundaries_add_one]
  exact (E.pagePresentation pq r hr).B_le_preimage _

/-- The cycle tower is decreasing. -/
lemma cycles_anti {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.cycles pq r' (hr.trans hrr') ≤ E.cycles pq r := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih => exact (E.cycles_add_one_le pq s (hr.trans hrs)).trans ih

/-- The boundary tower is increasing. -/
lemma boundaries_mono {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.boundaries pq r ≤ E.boundaries pq r' (hr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih => exact ih.trans (E.boundaries_le_boundaries_add_one pq s (hr.trans hrs))

/-- Every boundary subobject lies below every cycle subobject: `B_r(pq) ≤ Z_{r'}(pq)` for all
pages `r` and `r'`. -/
lemma boundaries_le_cycles (r r' : ℤ) (hr : r₀ ≤ r) (hr' : r₀ ≤ r') :
    E.boundaries pq r ≤ E.cycles pq r' := by
  rcases le_total r r' with h | h
  · exact (E.boundaries_mono pq hr h).trans (E.boundaries_le_cycles_self pq r' hr')
  · exact (E.boundaries_le_cycles_self pq r hr).trans (E.cycles_anti pq hr' h)

/-- The cycles do not change from the page `r` to the page `r + 1` exactly when the differential
of the page `r` leaving `pq` vanishes. -/
lemma cycles_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.cycles pq (r + 1) (Int.le_add_one hr) = E.cycles pq r ↔ (E.page r).dFrom pq = 0 := by
  rw [E.cycles_add_one pq r hr, ← E.pagePresentation_Z pq r hr,
    ← SubquotientPresentation.preimage_top, SubquotientPresentation.preimage_inj]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, kernelSubobject_zero]⟩
  rw [← Category.id_comp ((E.page r).dFrom pq), ← kernelSubobject_factors_iff, h]
  exact top_factors _

/-- The boundaries do not change from the page `r` to the page `r + 1` exactly when the
differential of the page `r` entering `pq` vanishes. -/
lemma boundaries_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.boundaries pq (r + 1) (Int.le_add_one hr) = E.boundaries pq r ↔
      (E.page r).dTo pq = 0 := by
  rw [E.boundaries_add_one pq r hr, ← E.pagePresentation_B pq r hr,
    ← SubquotientPresentation.preimage_bot, SubquotientPresentation.preimage_inj]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, imageSubobject_zero]⟩
  rw [← bot_factors_iff_zero, ← h]
  simpa using imageSubobject_factors_comp_self ((E.page r).dTo pq) (𝟙 _)

/-- The object at `pq` on the page `r` is zero exactly when its boundary and cycle subobjects
agree. -/
lemma isZero_page_X_iff (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r).X pq) ↔ E.boundaries pq r = E.cycles pq r :=
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
lemma cycles_le_pullback (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.cycles pq r ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cycles pq r) :=
  (pagePresentation_mapsTo pq f r hr).Z_le_pullback

/-- A morphism of spectral sequences maps the boundaries of each page into the boundaries of that
page. -/
lemma boundaries_le_pullback (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    E.boundaries pq r ≤ (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundaries pq r) :=
  (pagePresentation_mapsTo pq f r hr).B_le_pullback

/-- Under an isomorphism of spectral sequences, the cycles of `E` are the pullback of the cycles
of `E'` along the first-page component. -/
lemma pullback_cycles_of_iso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.cycles pq r) = E.cycles pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (cycles_le_pullback pq e.hom r hr) (cycles_le_pullback pq e.inv r hr)

/-- Under an isomorphism of spectral sequences, the boundaries of `E` are the pullback of the
boundaries of `E'` along the first-page component. -/
lemma pullback_boundaries_of_iso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.pullback ((e.hom.hom r₀).f pq)).obj (E'.boundaries pq r) = E.boundaries pq r :=
  pullback_eq_of_comp_eq_id (hom_inv_id_hom_f e r₀ le_rfl pq)
    (boundaries_le_pullback pq e.hom r hr) (boundaries_le_pullback pq e.inv r hr)

end Naturality

end CategoryTheory.SpectralSequence
