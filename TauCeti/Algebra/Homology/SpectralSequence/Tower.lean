/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Subquotient
import TauCeti.CategoryTheory.Subobject.Basic

/-!
# Cycle and boundary towers, stabilisation, and degeneration of spectral sequences

Given `E : SpectralSequence C c r₀` in an abelian category `C`, iterating
`ShortComplex.homologyPresentation` along `E.iso` presents each `(E.page r).X pq` as a subquotient
`Z_r(pq) / B_r(pq)` of `(E.page r₀).X pq`:

* `pagePresentation`, `cyclesSubobject` (`Z_r`), `boundariesSubobject` (`B_r`), and `fromPage`
  (rebasing to a later page `s ≥ r₀`, compatible with `pagePresentation` via composition).
* `StabilisesAt`, `IsRegularAt`, `IsCoregularAt`, and `DegeneratesAt`, characterised by eventual
  constancy of the cycle and boundary towers.
* `pageXIsoOfStabilises`: coherent stabilisation isomorphisms `(E.page s).X pq ≅ (E.page r).X pq`
  compatible with `pagePresentation`, composition, rebasing, and morphisms.

## References

* Stacks Project, Tag 011N (Section 12.20, *Spectral sequences*) and Tag 0BDV (Lemma 12.24.8).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

open CategoryTheory Limits
open TauCeti (SubquotientPresentation)

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section FromPage

variable (E : SpectralSequence C c r₀)

/-- Rebase a spectral sequence `E` starting at page `r₀` to start at a later page `s ≥ r₀`. -/
abbrev fromPage (s : ℤ) (hs : r₀ ≤ s := by lia) : SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

@[simp]
theorem fromPage_page (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.fromPage s hs).page r hr = E.page r (hs.trans hr) := rfl

@[simp]
theorem fromPage_iso (s : ℤ) (hs : r₀ ≤ s) (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : s ≤ r) :
    (E.fromPage s hs).iso r r' pq hrr' hr = E.iso r r' pq hrr' (hs.trans hr) := rfl

/-- Restrict a morphism of spectral sequences to start at a later page `s ≥ r₀`. -/
def Hom.fromPage {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
theorem Hom.fromPage_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) : (f.fromPage s hs).hom r hr = f.hom r (hs.trans hr) := by rfl

/-- Rebasing spectral sequences from page `r₀` to page `s ≥ r₀`, as a functor. -/
@[expose, simps]
def fromPageFunctor (C : Type u) [Category.{v} C] [Abelian C] {κ : Type*}
    (c : ℤ → ComplexShape κ) (r₀ s : ℤ) (hs : r₀ ≤ s := by lia) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := f.fromPage s hs

theorem fromPage_fromPage (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).fromPage t hst = E.fromPage t (hs.trans hst) := rfl

end FromPage

section Tower

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- The canonical subquotient presentation of `(E.page r).X pq` inside `(E.page r₀).X pq`, built
by induction on `r ≥ r₀` from `SubquotientPresentation.refl` and `ShortComplex.homologyPresentation`
transported along `E.iso`. -/
noncomputable def pagePresentation (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq) :=
  Int.leInduction
    (motive := fun r hr ↦ SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq))
    (SubquotientPresentation.refl ((E.page r₀).X pq))
    (fun s hs p ↦ p.trans ((((E.page s hs).sc pq).homologyPresentation).mapIso
      (E.iso s (s + 1) pq rfl hs))) r hr

@[simp]
theorem pagePresentation_base :
    E.pagePresentation pq r₀ le_rfl = SubquotientPresentation.refl ((E.page r₀).X pq) :=
  Int.leInduction_base _ _

theorem pagePresentation_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) = (E.pagePresentation pq r hr).trans
      ((((E.page r hr).sc pq).homologyPresentation).mapIso (E.iso r (r + 1) pq rfl hr)) :=
  Int.leInduction_add_one _ _ r hr

/-- The `r`-cycle subobject `Z_r(pq) ≤ (E.page r₀).X pq` at position `pq`. -/
noncomputable abbrev cyclesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) := (E.pagePresentation pq r hr).Z

/-- The `r`-boundary subobject `B_r(pq) ≤ (E.page r₀).X pq` at position `pq`. -/
noncomputable abbrev boundariesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) := (E.pagePresentation pq r hr).B

@[simp]
theorem cyclesSubobject_base : E.cyclesSubobject pq r₀ le_rfl = ⊤ := by
  rw [cyclesSubobject, pagePresentation_base, SubquotientPresentation.refl_Z]

@[simp]
theorem boundariesSubobject_base : E.boundariesSubobject pq r₀ le_rfl = ⊥ := by
  rw [boundariesSubobject, pagePresentation_base, SubquotientPresentation.refl_B]

/-- On page `r + 1`, `Z_{r+1}(pq)` is the preimage of `kernelSubobject ((E.page r).dFrom pq)`. -/
theorem cyclesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).dFrom pq)) := by
  rw [cyclesSubobject, pagePresentation_add_one E pq r hr, SubquotientPresentation.trans_Z,
    SubquotientPresentation.mapIso_Z, SubquotientPresentation.ofIsColimit_Z]
  rfl

/-- On page `r + 1`, `B_{r+1}(pq)` is the preimage of `imageSubobject ((E.page r).dTo pq)`. -/
theorem boundariesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r hr).dTo pq)) := by
  rw [boundariesSubobject, pagePresentation_add_one E pq r hr, SubquotientPresentation.trans_B,
    SubquotientPresentation.mapIso_B, SubquotientPresentation.ofIsColimit_B]
  rfl

/-- On every page `r ≥ r₀`, boundaries lie inside cycles: `B_r(pq) ≤ Z_r(pq)`. -/
theorem boundariesSubobject_le_cyclesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r hr := (E.pagePresentation pq r hr).le

/-- The cycle tower decreases at each page: `Z_{r+1}(pq) ≤ Z_r(pq)`. -/
theorem cyclesSubobject_add_one_le (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r hr := by
  rw [cyclesSubobject_add_one E pq r hr]; exact (E.pagePresentation pq r hr).preimage_le_Z _

/-- The boundary tower increases at each page: `B_r(pq) ≤ B_{r+1}(pq)`. -/
theorem le_boundariesSubobject_add_one (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
  rw [boundariesSubobject_add_one E pq r hr]; exact (E.pagePresentation pq r hr).B_le_preimage _

/-- The cycle tower `r ↦ Z_r(pq)` is antitone. -/
theorem cyclesSubobject_anti {r₁ r₂ : ℤ} (h₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    E.cyclesSubobject pq r₂ (h₁.trans h₁₂) ≤ E.cyclesSubobject pq r₁ h₁ := by
  induction r₂, h₁₂ using Int.leInduction with
  | base => exact le_rfl
  | succ r h ih => exact (E.cyclesSubobject_add_one_le pq r (h₁.trans h)).trans ih

/-- The boundary tower `r ↦ B_r(pq)` is monotone. -/
theorem boundariesSubobject_mono {r₁ r₂ : ℤ} (h₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    E.boundariesSubobject pq r₁ h₁ ≤ E.boundariesSubobject pq r₂ (h₁.trans h₁₂) := by
  induction r₂, h₁₂ using Int.leInduction with
  | base => exact le_rfl
  | succ r h ih => exact ih.trans (E.le_boundariesSubobject_add_one pq r (h₁.trans h))

/-- Every boundary subobject `B_{r₁}(pq)` lies below every cycle subobject `Z_{r₂}(pq)`. -/
theorem boundariesSubobject_le_cyclesSubobject_of_any (r₁ r₂ : ℤ)
    (h₁ : r₀ ≤ r₁ := by lia) (h₂ : r₀ ≤ r₂ := by lia) :
    E.boundariesSubobject pq r₁ h₁ ≤ E.cyclesSubobject pq r₂ h₂ :=
  (E.boundariesSubobject_mono pq h₁ (le_max_left r₁ r₂)).trans <|
    (E.boundariesSubobject_le_cyclesSubobject pq (max r₁ r₂) (h₁.trans (le_max_left r₁ r₂))).trans
      (E.cyclesSubobject_anti pq h₂ (le_max_right r₁ r₂))

/-- The differential `dFrom pq` on page `r` vanishes iff every differential leaving `pq` does. -/
theorem page_dFrom_eq_zero_iff (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.page r hr).dFrom pq = 0 ↔ ∀ pq' : κ, (E.page r hr).d pq pq' = 0 :=
  ⟨fun h pq' ↦ by classical exact if hrel : (c r).Rel pq pq' then (c r).next_eq' hrel ▸ h
      else (E.page r hr).shape pq pq' hrel, fun h ↦ h ((c r).next pq)⟩

/-- The differential `dTo pq` on page `r` vanishes iff every differential entering `pq` does. -/
theorem page_dTo_eq_zero_iff (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.page r hr).dTo pq = 0 ↔ ∀ pq' : κ, (E.page r hr).d pq' pq = 0 :=
  ⟨fun h pq' ↦ by classical exact if hrel : (c r).Rel pq' pq then (c r).prev_eq' hrel ▸ h
      else (E.page r hr).shape pq' pq hrel, fun h ↦ h ((c r).prev pq)⟩

/-- `Z_{r+1}(pq) = Z_r(pq)` if and only if the differential of page `r` leaving `pq` vanishes. -/
theorem cyclesSubobject_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      (E.page r hr).dFrom pq = 0 := by
  rw [cyclesSubobject_add_one E pq r hr, (E.pagePresentation pq r hr).preimage_eq_Z_iff,
    kernelSubobject_eq_top_iff]

/-- `B_{r+1}(pq) = B_r(pq)` if and only if the differential of page `r` entering `pq` vanishes. -/
theorem boundariesSubobject_add_one_eq_iff (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      (E.page r hr).dTo pq = 0 := by
  rw [boundariesSubobject_add_one E pq r hr, (E.pagePresentation pq r hr).preimage_eq_B_iff,
    imageSubobject_eq_bot_iff]

/-- The object `(E.page r).X pq` vanishes if and only if `B_r(pq) = Z_r(pq)`. -/
theorem isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject (r : ℤ) (hr : r₀ ≤ r := by lia) :
    IsZero ((E.page r hr).X pq) ↔ E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).isZero_iff

/-- Rebasing compatibility for `pagePresentation`. -/
theorem pagePresentation_eq_comp_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).trans ((E.fromPage s hs).pagePresentation pq r hsr) := by
  induction r, hsr using Int.leInduction with
  | base => rw [pagePresentation_base, SubquotientPresentation.trans_refl]
  | succ r hsr ih =>
    rw [pagePresentation_add_one E pq r (hs.trans hsr),
      pagePresentation_add_one (E.fromPage s hs) pq r hsr, ih, SubquotientPresentation.trans_assoc]

/-- Rebasing compatibility for cycles. -/
theorem cyclesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesSubobject pq r hsr) :=
  congrArg SubquotientPresentation.Z (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

/-- Rebasing compatibility for boundaries. -/
theorem boundariesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSubobject pq r hsr) :=
  congrArg SubquotientPresentation.B (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

end Tower

section Naturality

variable {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)

private theorem mapInduced_pagePresentation_aux (r : ℤ) (hr : r₀ ≤ r) :
    ∃ (hZ : (Subobject.exists ((f.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) ≤
        E'.cyclesSubobject pq r hr)
      (hB : (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) ≤
        E'.boundariesSubobject pq r hr),
      (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr)
        ((f.hom r₀).f pq) hZ hB = (f.hom r hr).f pq := by
  let f₀ := (f.hom r₀).f pq
  induction r, hr using Int.leInduction with
  | base =>
    refine ⟨by simp, by rw [boundariesSubobject_base, boundariesSubobject_base,
      (Subobject.existsPullbackAdj f₀).gc.l_bot], ?_⟩
    rw [SubquotientPresentation.mapInduced_congr (E.pagePresentation_base pq)
      (E'.pagePresentation_base pq) rfl _ _ (by simp)
      (by simp only [SubquotientPresentation.refl_B, le_bot_iff]
          exact (Subobject.existsPullbackAdj _).gc.l_bot)]
    exact SubquotientPresentation.refl_mapInduced_refl f₀ _ _
  | succ r hr ih =>
    obtain ⟨hZ, hB, hmap⟩ := ih
    let p := E.pagePresentation pq r hr; let p' := E'.pagePresentation pq r hr
    let φ := (HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)
    have hZ_s : (Subobject.exists (p.mapInduced p' f₀ hZ hB)).obj
        (kernelSubobject ((E.page r hr).sc pq).g) ≤ kernelSubobject ((E'.page r hr).sc pq).g :=
      hmap.symm ▸ ShortComplex.exists_kernelSubobject_le φ
    have hB_s : (Subobject.exists (p.mapInduced p' f₀ hZ hB)).obj
        (imageSubobject ((E.page r hr).sc pq).f) ≤ imageSubobject ((E'.page r hr).sc pq).f :=
      hmap.symm ▸ ShortComplex.exists_imageSubobject_le φ
    have hZ' := (p.exists_preimage_le_preimage_iff p' f₀ hZ hB _ _).mpr hZ_s
    have hB' := (p.exists_preimage_le_preimage_iff p' f₀ hZ hB _ _).mpr hB_s
    have hhom : ((E.page r hr).sc pq).homologyPresentation.mapInduced
          ((E'.page r hr).sc pq).homologyPresentation (p.mapInduced p' f₀ hZ hB) hZ_s hB_s =
        HomologicalComplex.homologyMap (f.hom r hr) pq :=
      (SubquotientPresentation.mapInduced_congr rfl rfl hmap _ _ _ _).trans
        (ShortComplex.mapInduced_homologyPresentation φ)
    refine ⟨by rwa [cyclesSubobject_add_one, cyclesSubobject_add_one],
      by rwa [boundariesSubobject_add_one, boundariesSubobject_add_one], ?_⟩
    refine (SubquotientPresentation.mapInduced_congr (pagePresentation_add_one E pq r hr)
        (pagePresentation_add_one E' pq r hr) rfl _ _ hZ' hB').trans ?_
    refine (SubquotientPresentation.mapInduced_trans p p' _ _ f₀ hZ hB hZ_s hB_s).trans ?_
    refine (SubquotientPresentation.mapInduced_mapIso
        ((E.page r hr).sc pq).homologyPresentation
        ((E'.page r hr).sc pq).homologyPresentation
        (E.iso r (r + 1) pq rfl hr) (E'.iso r (r + 1) pq rfl hr)
        (p.mapInduced p' f₀ hZ hB) hZ_s hB_s).trans ?_
    rw [hhom, f.comm r (r + 1) pq rfl hr, Iso.inv_hom_id_assoc]

/-- Naturality of the cycle tower: `f : E ⟶ E'` maps `Z_r(E, pq)` into `Z_r(E', pq)`. -/
theorem Hom.exists_cyclesSubobject_le (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) ≤
      E'.cyclesSubobject pq r hr := (mapInduced_pagePresentation_aux f pq r hr).choose

/-- Naturality of the boundary tower: `f : E ⟶ E'` maps `B_r(E, pq)` into `B_r(E', pq)`. -/
theorem Hom.exists_boundariesSubobject_le (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  (mapInduced_pagePresentation_aux f pq r hr).choose_spec.choose

/-- Adjoint form of naturality for cycles. -/
theorem Hom.cyclesSubobject_le_pullback (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.cyclesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesSubobject pq r hr) :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mp (f.exists_cyclesSubobject_le pq r hr)

/-- Adjoint form of naturality for boundaries. -/
theorem Hom.boundariesSubobject_le_pullback (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundariesSubobject pq r hr) :=
  (Subobject.existsPullbackAdj _).gc.le_iff_le.mp (f.exists_boundariesSubobject_le pq r hr)

/-- The morphism induced by `(f.hom r₀).f pq` on `pagePresentation` is `(f.hom r).f pq`. -/
theorem Hom.mapInduced_pagePresentation (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr) ((f.hom r₀).f pq)
        (f.exists_cyclesSubobject_le pq r hr) (f.exists_boundariesSubobject_le pq r hr) =
      (f.hom r hr).f pq := (mapInduced_pagePresentation_aux f pq r hr).choose_spec.choose_spec

end Naturality

section NaturalityIso

variable {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)

private theorem exists_eq_of_iso_aux {S : Subobject ((E.page r₀).X pq)}
    {S' : Subobject ((E'.page r₀).X pq)}
    (h1 : (Subobject.exists ((e.hom.hom r₀).f pq)).obj S ≤ S')
    (h2 : (Subobject.exists ((e.inv.hom r₀).f pq)).obj S' ≤ S) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj S = S' := by
  refine le_antisymm h1 ?_
  have h := (Subobject.exists ((e.hom.hom r₀).f pq)).monotone h2
  have hid : (e.inv.hom r₀).f pq ≫ (e.hom.hom r₀).f pq = 𝟙 ((E'.page r₀).X pq) :=
    ((pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e).inv_hom_id
  rw [← Subobject.exists_comp, hid, Subobject.exists_id] at h
  exact h

/-- An isomorphism `e : E ≅ E'` carries `Z_r(E, pq)` onto `Z_r(E', pq)`. -/
theorem exists_cyclesSubobject_eq_of_iso (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr :=
  exists_eq_of_iso_aux e pq (e.hom.exists_cyclesSubobject_le pq r hr)
    (e.inv.exists_cyclesSubobject_le pq r hr)

/-- An isomorphism `e : E ≅ E'` carries `B_r(E, pq)` onto `B_r(E', pq)`. -/
theorem exists_boundariesSubobject_eq_of_iso (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr :=
  exists_eq_of_iso_aux e pq (e.hom.exists_boundariesSubobject_le pq r hr)
    (e.inv.exists_boundariesSubobject_le pq r hr)

end NaturalityIso

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

theorem stabilisesAt_iff (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dFrom pq = 0 ∧ (E.page r (hs.trans hsr)).dTo pq = 0 :=
  Iff.rfl

theorem isRegularAt_iff (pq : κ) :
    E.IsRegularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dFrom pq = 0 :=
  Iff.rfl

theorem isCoregularAt_iff (pq : κ) :
    E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      (E.page r (hs.trans hsr)).dTo pq = 0 :=
  Iff.rfl

theorem degeneratesAt_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r) (i j : κ),
      (E.page r (hs.trans hsr)).d i j = 0 :=
  Iff.rfl

end

section

variable {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs)
include h

theorem StabilisesAt.dFrom_eq_zero {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dFrom pq = 0 := (h r hsr).1

theorem StabilisesAt.dTo_eq_zero {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dTo pq = 0 := (h r hsr).2

theorem StabilisesAt.d_out {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq pq' = 0 :=
  (E.page_dFrom_eq_zero_iff pq r (hs.trans hsr)).mp (h.dFrom_eq_zero hsr) pq'

theorem StabilisesAt.d_in {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq' pq = 0 :=
  (E.page_dTo_eq_zero_iff pq r (hs.trans hsr)).mp (h.dTo_eq_zero hsr) pq'

/-- Stabilisation from page `s` persists to every later page `s' ≥ s`. -/
theorem StabilisesAt.of_le {s' : ℤ} (hss' : s ≤ s') : E.StabilisesAt pq s' (hs.trans hss') :=
  fun r hs'r ↦ h r (hss'.trans hs'r)

theorem StabilisesAt.isRegularAt : E.IsRegularAt pq := ⟨s, hs, fun r hsr ↦ (h r hsr).1⟩

theorem StabilisesAt.isCoregularAt : E.IsCoregularAt pq := ⟨s, hs, fun r hsr ↦ (h r hsr).2⟩

end

theorem DegeneratesAt.d_eq_zero {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) {r : ℤ} (hsr : s ≤ r) (i j : κ) :
    (E.page r (hs.trans hsr)).d i j = 0 :=
  hd r hsr i j

/-- Degeneration at page `s` persists to every later page `s' ≥ s`. -/
theorem DegeneratesAt.of_le {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) {s' : ℤ} (hss' : s ≤ s') : E.DegeneratesAt s' (hs.trans hss') :=
  fun r hs'r i j ↦ hd r (hss'.trans hs'r) i j

/-- Degeneration at page `s` implies stabilisation at every position from page `s`. -/
theorem DegeneratesAt.stabilisesAt {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (hd : E.DegeneratesAt s hs) (pq : κ) : E.StabilisesAt pq s hs :=
  fun r hsr ↦ ⟨hd r hsr pq _, hd r hsr _ pq⟩

section

variable (E : SpectralSequence C c r₀) (pq : κ)

theorem stabilisesAt_iff_forall_d_eq_zero (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ ∀ (r : ℤ) (hsr : s ≤ r) (pq' : κ),
      (E.page r (hs.trans hsr)).d pq pq' = 0 ∧ (E.page r (hs.trans hsr)).d pq' pq = 0 :=
  ⟨fun h _ hsr pq' ↦ ⟨h.d_out hsr pq', h.d_in hsr pq'⟩,
   fun h r hsr ↦ ⟨(E.page_dFrom_eq_zero_iff pq r (hs.trans hsr)).mpr (fun pq' ↦ (h r hsr pq').1),
     (E.page_dTo_eq_zero_iff pq r (hs.trans hsr)).mpr (fun pq' ↦ (h r hsr pq').2)⟩⟩

/-- `E` is both regular and coregular at `pq` iff it stabilises at `pq` from some page. -/
theorem isRegularAt_and_isCoregularAt_iff_exists_stabilisesAt :
    E.IsRegularAt pq ∧ E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), E.StabilisesAt pq s hs :=
  ⟨fun ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, _, h₂⟩⟩ ↦ ⟨max s₁ s₂, hs₁.trans (le_max_left s₁ s₂), fun r hr ↦
      ⟨h₁ r ((le_max_left s₁ s₂).trans hr), h₂ r ((le_max_right s₁ s₂).trans hr)⟩⟩,
   fun ⟨_, _, h⟩ ↦ ⟨h.isRegularAt, h.isCoregularAt⟩⟩

/-- `E` degenerates at page `s` iff it stabilises at every position from page `s`. -/
theorem degeneratesAt_iff_forall_stabilisesAt (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ ∀ pq : κ, E.StabilisesAt pq s hs :=
  ⟨fun h pq ↦ h.stabilisesAt pq, fun h _ hsr i j ↦ (h i).d_out hsr j⟩

/-- If differentials leaving `pq` vanish from page `s` onward, `Z_r(pq) = Z_s(pq)` for `r ≥ s`. -/
theorem cyclesSubobject_eq_of_forall_dFrom_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih => rw [(E.cyclesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- If differentials entering `pq` vanish from page `s` onward, `B_r(pq) = B_s(pq)` for `r ≥ s`. -/
theorem boundariesSubobject_eq_of_forall_dTo_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih =>
    rw [(E.boundariesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- `E` is regular at `pq` if and only if the cycle tower `r ↦ Z_r(pq)` is eventually constant. -/
theorem isRegularAt_iff_eventually_const_cyclesSubobject :
    E.IsRegularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs h⟩,
   fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun r hsr ↦ (E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp
      (by rw [h (r + 1) (Int.le_add_one hsr), h r hsr])⟩⟩

/-- `E` is coregular at `pq` iff the boundary tower `r ↦ B_r(pq)` is eventually constant. -/
theorem isCoregularAt_iff_eventually_const_boundariesSubobject :
    E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
      E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs h⟩,
   fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun r hsr ↦ (E.boundariesSubobject_add_one_eq_iff pq r _).mp
      (by rw [h (r + 1) (Int.le_add_one hsr), h r hsr])⟩⟩

/-- `E` stabilises at `pq` from page `s` iff `Z_r(pq)` and `B_r(pq)` are constant for `r ≥ s`. -/
theorem stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject (s : ℤ)
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

theorem stabilisesAt_fromPage_iff (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).StabilisesAt pq t hst ↔ E.StabilisesAt pq t (hs.trans hst) := Iff.rfl

theorem isRegularAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsRegularAt pq ↔ E.IsRegularAt pq :=
  ⟨fun ⟨t, hst, h⟩ ↦ ⟨t, hs.trans hst, h⟩,
   fun ⟨t, _, h⟩ ↦ ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩⟩

theorem isCoregularAt_fromPage_iff (s : ℤ) (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsCoregularAt pq ↔ E.IsCoregularAt pq :=
  ⟨fun ⟨t, hst, h⟩ ↦ ⟨t, hs.trans hst, h⟩,
   fun ⟨t, _, h⟩ ↦ ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩⟩

theorem degeneratesAt_fromPage_iff (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).DegeneratesAt t hst ↔ E.DegeneratesAt t (hs.trans hst) := Iff.rfl

/-- When `E` stabilises at `pq` from page `s`, the canonical iso `(E.page s).X pq ≅ (E.page r).X pq`
for `r ≥ s`. -/
noncomputable def pageXIsoOfStabilises (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (r : ℤ)
    (hsr : s ≤ r) : (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq :=
  Int.leInduction (motive := fun r hsr ↦ (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq)
    (Iso.refl _)
    (fun t hst e ↦ e ≪≫ (((E.page t (hs.trans hst)).sc pq).cyclesIsoX₂ (h.dFrom_eq_zero hst)).symm
      ≪≫ ((E.page t (hs.trans hst)).sc pq).asIsoHomologyπ (h.dTo_eq_zero hst) ≪≫
      E.iso t (t + 1) pq rfl (hs.trans hst)) r hsr

@[simp]
theorem pageXIsoOfStabilises_self (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.pageXIsoOfStabilises pq s hs h s le_rfl = Iso.refl _ := Int.leInduction_base _ _

theorem pageXIsoOfStabilises_add_one (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (t : ℤ)
    (hst : s ≤ t) :
    E.pageXIsoOfStabilises pq s hs h (t + 1) (Int.le_add_one hst) =
      E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        (((E.page t (hs.trans hst)).sc pq).cyclesIsoX₂ (h.dFrom_eq_zero hst)).symm ≪≫
        ((E.page t (hs.trans hst)).sc pq).asIsoHomologyπ (h.dTo_eq_zero hst) ≪≫
        E.iso t (t + 1) pq rfl (hs.trans hst) := Int.leInduction_add_one _ _ t hst

/-- When `E` stabilises at `pq` from page `s`, `pagePresentation` on page `r ≥ s` is the
page-`s` presentation transported along `pageXIsoOfStabilises`. -/
theorem pagePresentation_eq_mapIso_pageXIsoOfStabilises (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h r hsr) := by
  induction r, hsr using Int.leInduction with
  | base => rw [pageXIsoOfStabilises_self, SubquotientPresentation.mapIso_refl]
  | succ t hst ih =>
    rw [pagePresentation_add_one E pq t (hs.trans hst), ih,
      pageXIsoOfStabilises_add_one E pq s hs h t hst,
      ShortComplex.homologyPresentation_eq_refl_mapIso _ (h.dTo_eq_zero hst) (h.dFrom_eq_zero hst),
      SubquotientPresentation.mapIso_trans, SubquotientPresentation.trans_mapIso]
    have htr : ((E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h t hst)).trans
        (SubquotientPresentation.refl (((E.page t (hs.trans hst)).sc pq).X₂)) =
      (E.pagePresentation pq s hs).mapIso (E.pageXIsoOfStabilises pq s hs h t hst) :=
      SubquotientPresentation.trans_refl _
    rw [htr, SubquotientPresentation.mapIso_trans]
    simp only [Iso.trans_assoc]

/-- Composition compatibility of `pageXIsoOfStabilises` for `s ≤ t ≤ r`. -/
theorem pageXIsoOfStabilises_trans {s t r : ℤ} (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs)
    (hst : s ≤ t) (htr : t ≤ r) :
    E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        E.pageXIsoOfStabilises pq t (hs.trans hst) (h.of_le hst) r htr =
      E.pageXIsoOfStabilises pq s hs h r (hst.trans htr) := by
  induction r, htr using Int.leInduction with
  | base => rw [pageXIsoOfStabilises_self, Iso.trans_refl]
  | succ u htu ih =>
    rw [pageXIsoOfStabilises_add_one E pq t (hs.trans hst) (h.of_le hst) u htu,
      pageXIsoOfStabilises_add_one E pq s hs h u (hst.trans htu), ← Iso.trans_assoc, ih]

theorem pageXIsoOfStabilises_fromPage {s t r : ℤ} (hs : r₀ ≤ s) (hst : s ≤ t)
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

theorem StabilisesAt.cyclesSubobject_eq {pq : κ} {s : ℤ} {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs)
    (r : ℤ) (hsr : s ≤ r) : E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).1

theorem StabilisesAt.boundariesSubobject_eq {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).2

theorem DegeneratesAt.cyclesSubobject_eq_top (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : E.cyclesSubobject pq r hr = ⊤ := by
  rw [(h.stabilisesAt pq).cyclesSubobject_eq r hr, cyclesSubobject_base]

theorem DegeneratesAt.boundariesSubobject_eq_bot (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : E.boundariesSubobject pq r hr = ⊥ := by
  rw [(h.stabilisesAt pq).boundariesSubobject_eq r hr, boundariesSubobject_base]

/-- Naturality of `pageXIsoOfStabilises` with respect to morphisms of spectral sequences. -/
@[reassoc]
theorem Hom.pageXIsoOfStabilises_naturality (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s)
    (h : E.StabilisesAt pq s hs) (h' : E'.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    (f.hom s hs).f pq ≫ (E'.pageXIsoOfStabilises pq s hs h' r hsr).hom =
      (E.pageXIsoOfStabilises pq s hs h r hsr).hom ≫ (f.hom r (hs.trans hsr)).f pq := by
  have hmap := f.mapInduced_pagePresentation pq r (hs.trans hsr)
  rw [SubquotientPresentation.mapInduced_congr
      (E.pagePresentation_eq_mapIso_pageXIsoOfStabilises pq s hs h r hsr)
      (E'.pagePresentation_eq_mapIso_pageXIsoOfStabilises pq s hs h' r hsr) rfl _ _
      (f.exists_cyclesSubobject_le pq s hs) (f.exists_boundariesSubobject_le pq s hs),
    SubquotientPresentation.mapInduced_mapIso, f.mapInduced_pagePresentation pq s hs] at hmap
  rw [← hmap, Iso.hom_inv_id_assoc]

variable (e : E ≅ E')
include e

/-- Isomorphic spectral sequences have the same vanishing differentials on every page. -/
theorem page_d_eq_zero_iff_of_iso (r : ℤ) (hr : r₀ ≤ r) (i j : κ) :
    (E.page r hr).d i j = 0 ↔ (E'.page r hr).d i j = 0 := by
  have : IsIso ((e.hom.hom r hr).f i) :=
    ((pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) i).mapIso e).isIso_hom
  have : IsIso ((e.hom.hom r hr).f j) :=
    ((pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) j).mapIso e).isIso_hom
  have hcomm := (e.hom.hom r hr).comm i j
  exact ⟨fun h ↦ (cancel_epi ((e.hom.hom r hr).f i)).mp (by rw [comp_zero, hcomm, h, zero_comp]),
    fun h ↦ (cancel_mono ((e.hom.hom r hr).f j)).mp (by rw [zero_comp, ← hcomm, h, comp_zero])⟩

/-- Isomorphic spectral sequences stabilise at the same positions and pages. -/
theorem stabilisesAt_iff_of_iso (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ E'.StabilisesAt pq s hs := by
  simp only [StabilisesAt, HomologicalComplex.dFrom, HomologicalComplex.dTo,
    page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are regular at the same positions. -/
theorem isRegularAt_iff_of_iso (pq : κ) : E.IsRegularAt pq ↔ E'.IsRegularAt pq := by
  simp only [IsRegularAt, HomologicalComplex.dFrom, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are coregular at the same positions. -/
theorem isCoregularAt_iff_of_iso (pq : κ) : E.IsCoregularAt pq ↔ E'.IsCoregularAt pq := by
  simp only [IsCoregularAt, HomologicalComplex.dTo, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences degenerate at the same pages. -/
theorem degeneratesAt_iff_of_iso (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ E'.DegeneratesAt s hs := by
  simp only [DegeneratesAt, page_d_eq_zero_iff_of_iso e]

end

end Stabilisation

end CategoryTheory.SpectralSequence
