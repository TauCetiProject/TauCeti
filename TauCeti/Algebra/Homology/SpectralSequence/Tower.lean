/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Subquotient

/-!
# Cycle and boundary towers, stabilisation, and degeneration of spectral sequences

Given a spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C` and a position
`pq : κ`, each page `r ≥ r₀` is the homology of the previous page, so `(E.page r).X pq` is
canonically presented as a subquotient `Z_r(pq) / B_r(pq)` of the first-page object
`(E.page r₀).X pq`. Composing `ShortComplex.homologyPresentation` along `E.iso` by induction on
`r ≥ r₀` produces:

* `CategoryTheory.SpectralSequence.pagePresentation`: the canonical `SubquotientPresentation` of
  `(E.page r).X pq` inside `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.cyclesSubobject` (`Z_r(pq)`) and
  `CategoryTheory.SpectralSequence.boundariesSubobject` (`B_r(pq)`): the descending tower of cycles
  and ascending tower of boundaries, satisfying `B_r ≤ B_{r+1} ≤ Z_{r+1} ≤ Z_r`.
* `CategoryTheory.SpectralSequence.fromPage`: rebasing a spectral sequence to start at a later
  page `s ≥ r₀`, compatible with `pagePresentation` via composition of subquotient presentations.
* `CategoryTheory.SpectralSequence.StabilisesAt`, `IsRegularAt`, `IsCoregularAt`, and
  `DegeneratesAt`: differential-vanishing criteria characterised by eventual constancy of the
  cycle and boundary towers.
* `CategoryTheory.SpectralSequence.pageXIsoOfStabilises`: the canonical isomorphism
  `(E.page s).X pq ≅ (E.page r).X pq` for `r ≥ s` at a stabilising position, compatible with
  `pagePresentation`, composition, and morphisms of spectral sequences.

## References

* Stacks Project, Tag 011N (Section 12.20, *Spectral sequences*) and Tag 0BDV (Lemma 12.24.8).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.SpectralSequence

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section FromPage

/-- Rebase a spectral sequence `E` starting at page `r₀` to start at a later page `s ≥ r₀`. -/
abbrev fromPage (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

@[simp]
theorem fromPage_page (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) :
    (E.fromPage s hs).page r hr = E.page r (hs.trans hr) :=
  rfl

@[simp]
theorem fromPage_iso (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s)
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r') (hr : s ≤ r) :
    (E.fromPage s hs).iso r r' pq hrr' hr = E.iso r r' pq hrr' (hs.trans hr) :=
  rfl

/-- Restrict a morphism of spectral sequences to start at a later page `s ≥ r₀`. -/
@[expose]
def Hom.fromPage {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
theorem Hom.fromPage_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) :
    (f.fromPage s hs).hom r hr = f.hom r (hs.trans hr) :=
  rfl

/-- Rebasing spectral sequences from page `r₀` to page `s ≥ r₀`, as a functor. -/
@[expose, simps]
def fromPageFunctor (C : Type u) [Category.{v} C] [Abelian C] {κ : Type*}
    (c : ℤ → ComplexShape κ) (r₀ s : ℤ) (hs : r₀ ≤ s := by lia) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := f.fromPage s hs

theorem fromPage_fromPage (E : SpectralSequence C c r₀) (s t : ℤ) (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).fromPage t hst = E.fromPage t (hs.trans hst) :=
  rfl

end FromPage

section Tower

/-- The canonical subquotient presentation of `(E.page r).X pq` inside `(E.page r₀).X pq`, built
by induction on `r ≥ r₀` from the identity presentation on page `r₀` and
`ShortComplex.homologyPresentation` transported along `E.iso`. -/
noncomputable def pagePresentation (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    TauCeti.SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq) :=
  Int.leInduction
    (motive := fun r hr ↦
      TauCeti.SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq))
    (TauCeti.SubquotientPresentation.id ((E.page r₀).X pq))
    (fun s hs p ↦
      p.comp ((((E.page s hs).sc pq).homologyPresentation).transIso
        (E.iso s (s + 1) pq rfl hs)))
    r hr

@[simp]
theorem pagePresentation_base (E : SpectralSequence C c r₀) (pq : κ) :
    E.pagePresentation pq r₀ le_rfl =
      TauCeti.SubquotientPresentation.id ((E.page r₀).X pq) :=
  Int.leInduction_base _ _

theorem pagePresentation_add_one (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).comp
        ((((E.page r hr).sc pq).homologyPresentation).transIso
          (E.iso r (r + 1) pq rfl hr)) :=
  Int.leInduction_add_one _ _ r hr

/-- The `r`-cycle subobject `Z_r(pq) ≤ (E.page r₀).X pq` at position `pq`. -/
noncomputable abbrev cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).Z

/-- The `r`-boundary subobject `B_r(pq) ≤ (E.page r₀).X pq` at position `pq`. -/
noncomputable abbrev boundariesSubobject (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).B

@[simp]
theorem cyclesSubobject_base (E : SpectralSequence C c r₀) (pq : κ) :
    E.cyclesSubobject pq r₀ le_rfl = ⊤ := by
  rw [cyclesSubobject, pagePresentation_base]

@[simp]
theorem boundariesSubobject_base (E : SpectralSequence C c r₀) (pq : κ) :
    E.boundariesSubobject pq r₀ le_rfl = ⊥ := by
  rw [boundariesSubobject, pagePresentation_base]

/-- On page `r + 1`, the cycle subobject `Z_{r+1}(pq)` is the preimage under `pagePresentation` of
the kernel of the differential leaving `pq` on page `r`. -/
theorem cyclesSubobject_add_one (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).dFrom pq)) := by
  rw [cyclesSubobject, pagePresentation_add_one E pq r hr]
  rfl

/-- On page `r + 1`, the boundary subobject `B_{r+1}(pq)` is the preimage under `pagePresentation`
of the image of the differential entering `pq` on page `r`. -/
theorem boundariesSubobject_add_one (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r hr).dTo pq)) := by
  rw [boundariesSubobject, pagePresentation_add_one E pq r hr]
  rfl

/-- On every page `r ≥ r₀`, boundaries lie inside cycles: `B_r(pq) ≤ Z_r(pq)`. -/
theorem boundariesSubobject_le_cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).le

/-- The cycle tower decreases at each page: `Z_{r+1}(pq) ≤ Z_r(pq)`. -/
theorem cyclesSubobject_add_one_le (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r hr := by
  rw [cyclesSubobject_add_one E pq r hr]
  exact (E.pagePresentation pq r hr).preimage_le _

/-- The boundary tower increases at each page: `B_r(pq) ≤ B_{r+1}(pq)`. -/
theorem le_boundariesSubobject_add_one (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
  rw [boundariesSubobject_add_one E pq r hr]
  exact (E.pagePresentation pq r hr).le_preimage _

/-- The cycle tower `r ↦ Z_r(pq)` is antitone. -/
theorem cyclesSubobject_anti (E : SpectralSequence C c r₀) (pq : κ) {r₁ r₂ : ℤ}
    (h₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    E.cyclesSubobject pq r₂ (h₁.trans h₁₂) ≤ E.cyclesSubobject pq r₁ h₁ := by
  induction r₂, h₁₂ using Int.leInduction with
  | base => exact le_rfl
  | succ r h ih => exact (E.cyclesSubobject_add_one_le pq r (h₁.trans h)).trans ih

/-- The boundary tower `r ↦ B_r(pq)` is monotone. -/
theorem boundariesSubobject_mono (E : SpectralSequence C c r₀) (pq : κ) {r₁ r₂ : ℤ}
    (h₁ : r₀ ≤ r₁) (h₁₂ : r₁ ≤ r₂) :
    E.boundariesSubobject pq r₁ h₁ ≤ E.boundariesSubobject pq r₂ (h₁.trans h₁₂) := by
  induction r₂, h₁₂ using Int.leInduction with
  | base => exact le_rfl
  | succ r h ih => exact ih.trans (E.le_boundariesSubobject_add_one pq r (h₁.trans h))

/-- Every boundary subobject `B_{r₁}(pq)` lies below every cycle subobject `Z_{r₂}(pq)`. -/
theorem boundariesSubobject_le_cyclesSubobject_of_any (E : SpectralSequence C c r₀) (pq : κ)
    (r₁ r₂ : ℤ) (h₁ : r₀ ≤ r₁ := by lia) (h₂ : r₀ ≤ r₂ := by lia) :
    E.boundariesSubobject pq r₁ h₁ ≤ E.cyclesSubobject pq r₂ h₂ :=
  (E.boundariesSubobject_mono pq h₁ (le_max_left r₁ r₂)).trans
    ((E.boundariesSubobject_le_cyclesSubobject pq (max r₁ r₂) (h₁.trans (le_max_left r₁ r₂))).trans
      (E.cyclesSubobject_anti pq h₂ (le_max_right r₁ r₂)))

/-- The differential `dFrom pq` on page `r` vanishes if and only if every differential leaving `pq`
on page `r` vanishes. -/
theorem page_dFrom_eq_zero_iff (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    (E.page r hr).dFrom pq = 0 ↔ ∀ pq' : κ, (E.page r hr).d pq pq' = 0 := by
  constructor
  · intro h pq'
    by_cases hrel : (c r).Rel pq pq'
    · rw [← (c r).next_eq' hrel]
      exact h
    · exact (E.page r hr).shape pq pq' hrel
  · intro h
    exact h ((c r).next pq)

/-- The differential `dTo pq` on page `r` vanishes if and only if every differential entering `pq`
on page `r` vanishes. -/
theorem page_dTo_eq_zero_iff (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    (E.page r hr).dTo pq = 0 ↔ ∀ pq' : κ, (E.page r hr).d pq' pq = 0 := by
  constructor
  · intro h pq'
    by_cases hrel : (c r).Rel pq' pq
    · rw [← (c r).prev_eq' hrel]
      exact h
    · exact (E.page r hr).shape pq' pq hrel
  · intro h
    exact h ((c r).prev pq)

/-- `Z_{r+1}(pq) = Z_r(pq)` if and only if the differential of page `r` leaving `pq` vanishes. -/
theorem cyclesSubobject_add_one_eq_iff (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      (E.page r hr).dFrom pq = 0 := by
  rw [cyclesSubobject_add_one E pq r hr, (E.pagePresentation pq r hr).preimage_eq_Z_iff]
  exact kernelSubobject_eq_top_iff _

/-- `B_{r+1}(pq) = B_r(pq)` if and only if the differential of page `r` entering `pq` vanishes. -/
theorem boundariesSubobject_add_one_eq_iff (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      (E.page r hr).dTo pq = 0 := by
  rw [boundariesSubobject_add_one E pq r hr, (E.pagePresentation pq r hr).preimage_eq_B_iff]
  exact imageSubobject_eq_bot_iff _

/-- The object `(E.page r).X pq` vanishes if and only if `B_r(pq) = Z_r(pq)`. -/
theorem isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject (E : SpectralSequence C c r₀)
    (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    IsZero ((E.page r hr).X pq) ↔ E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).isZero_iff

private theorem mapInduced_pagePresentation_base {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) :
    ∃ (hZ : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.cyclesSubobject pq r₀ le_rfl) ≤
        E'.cyclesSubobject pq r₀ le_rfl)
      (hB : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.boundariesSubobject pq r₀ le_rfl) ≤
        E'.boundariesSubobject pq r₀ le_rfl),
      (E.pagePresentation pq r₀ le_rfl).mapInduced (E'.pagePresentation pq r₀ le_rfl)
        ((f.hom r₀ le_rfl).f pq) hZ hB = (f.hom r₀ le_rfl).f pq := by
  let f₀ : (E.page r₀ le_rfl).X pq ⟶ (E'.page r₀ le_rfl).X pq := (f.hom r₀ le_rfl).f pq
  have hZ₀ : (Subobject.exists f₀).obj (E.cyclesSubobject pq r₀ le_rfl) ≤
      E'.cyclesSubobject pq r₀ le_rfl := by
    rw [cyclesSubobject_base, cyclesSubobject_base]
    exact le_top
  have hB₀ : (Subobject.exists f₀).obj (E.boundariesSubobject pq r₀ le_rfl) ≤
      E'.boundariesSubobject pq r₀ le_rfl := by
    rw [boundariesSubobject_base, boundariesSubobject_base,
      (Subobject.existsPullbackAdj f₀).gc.l_bot]
  refine ⟨hZ₀, hB₀, ?_⟩
  have heq :
      (E.pagePresentation pq r₀ le_rfl).mapInduced (E'.pagePresentation pq r₀ le_rfl)
          f₀ hZ₀ hB₀ =
        (TauCeti.SubquotientPresentation.id ((E.page r₀ le_rfl).X pq)).mapInduced
          (TauCeti.SubquotientPresentation.id ((E'.page r₀ le_rfl).X pq))
          f₀ le_top
          (by rw [(Subobject.existsPullbackAdj f₀).gc.l_bot]) := by
    simp only [pagePresentation_base]
  rw [heq]
  symm
  refine (TauCeti.SubquotientPresentation.id ((E.page r₀ le_rfl).X pq)).mapInduced_unique _
    f₀ _ _ ?_
  rw [TauCeti.SubquotientPresentation.id_π, TauCeti.SubquotientPresentation.id_π]
  exact (TauCeti.SubquotientPresentation.liftZ_comp_arrow
    (TauCeti.SubquotientPresentation.id ((E.page r₀ le_rfl).X pq))
    (TauCeti.SubquotientPresentation.id ((E'.page r₀ le_rfl).X pq)) f₀ le_top).symm

private theorem mapInduced_pagePresentation_step {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hZ : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.cyclesSubobject pq r hr) ≤
      E'.cyclesSubobject pq r hr)
    (hB : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr)
    (hmap : (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr)
      ((f.hom r₀ le_rfl).f pq) hZ hB = (f.hom r hr).f pq) :
    ∃ (hZ' : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj
        (E.cyclesSubobject pq (r + 1) (Int.le_add_one hr)) ≤
        E'.cyclesSubobject pq (r + 1) (Int.le_add_one hr))
      (hB' : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj
        (E.boundariesSubobject pq (r + 1) (Int.le_add_one hr)) ≤
        E'.boundariesSubobject pq (r + 1) (Int.le_add_one hr)),
      (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).mapInduced
        (E'.pagePresentation pq (r + 1) (Int.le_add_one hr))
        ((f.hom r₀ le_rfl).f pq) hZ' hB' = (f.hom (r + 1) (Int.le_add_one hr)).f pq := by
  let f₀ : (E.page r₀ le_rfl).X pq ⟶ (E'.page r₀ le_rfl).X pq := (f.hom r₀ le_rfl).f pq
  let φ : (E.page r hr).sc pq ⟶ (E'.page r hr).sc pq :=
    (HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)
  let g : (E.page r hr).X pq ⟶ (E'.page r hr).X pq :=
    (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr) f₀ hZ hB
  have hτ₂ : φ.τ₂ = g := hmap.symm
  have hZ_step :
      (Subobject.exists g).obj (kernelSubobject ((E.page r hr).sc pq).g) ≤
        kernelSubobject ((E'.page r hr).sc pq).g := by
    rw [← hτ₂]
    exact ShortComplex.exists_kernelSubobject_le φ
  have hB_step :
      (Subobject.exists g).obj (imageSubobject ((E.page r hr).sc pq).f) ≤
        imageSubobject ((E'.page r hr).sc pq).f := by
    rw [← hτ₂]
    exact ShortComplex.exists_imageSubobject_le φ
  have hZ' : (Subobject.exists f₀).obj
      (E.cyclesSubobject pq (r + 1) (Int.le_add_one hr)) ≤
      E'.cyclesSubobject pq (r + 1) (Int.le_add_one hr) := by
    rw [cyclesSubobject_add_one E pq r hr, cyclesSubobject_add_one E' pq r hr]
    exact ((E.pagePresentation pq r hr).exists_preimage_le_preimage_iff
      (E'.pagePresentation pq r hr) f₀ hZ hB _ _).mpr hZ_step
  have hB' : (Subobject.exists f₀).obj
      (E.boundariesSubobject pq (r + 1) (Int.le_add_one hr)) ≤
      E'.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
    rw [boundariesSubobject_add_one E pq r hr, boundariesSubobject_add_one E' pq r hr]
    exact ((E.pagePresentation pq r hr).exists_preimage_le_preimage_iff
      (E'.pagePresentation pq r hr) f₀ hZ hB _ _).mpr hB_step
  refine ⟨hZ', hB', ?_⟩
  have hcomp :=
    (E.pagePresentation pq r hr).mapInduced_comp_presentation
      (E'.pagePresentation pq r hr)
      ((((E.page r hr).sc pq).homologyPresentation).transIso (E.iso r (r + 1) pq rfl hr))
      ((((E'.page r hr).sc pq).homologyPresentation).transIso (E'.iso r (r + 1) pq rfl hr))
      f₀ hZ hB hZ_step hB_step
  have htrans :=
    ((E.page r hr).sc pq).homologyPresentation.mapInduced_transIso
      ((E'.page r hr).sc pq).homologyPresentation
      (E.iso r (r + 1) pq rfl hr) (E'.iso r (r + 1) pq rfl hr)
      g hZ_step hB_step
  have hhom :
      ((E.page r hr).sc pq).homologyPresentation.mapInduced
          ((E'.page r hr).sc pq).homologyPresentation g hZ_step hB_step =
        HomologicalComplex.homologyMap (f.hom r hr) pq := by
    dsimp only [HomologicalComplex.homologyMap]
    simpa only [← hτ₂] using ShortComplex.mapInduced_homologyPresentation φ
  have heq :
      (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).mapInduced
          (E'.pagePresentation pq (r + 1) (Int.le_add_one hr)) f₀ hZ' hB' =
        ((E.pagePresentation pq r hr).comp
          ((((E.page r hr).sc pq).homologyPresentation).transIso
            (E.iso r (r + 1) pq rfl hr))).mapInduced
          ((E'.pagePresentation pq r hr).comp
            ((((E'.page r hr).sc pq).homologyPresentation).transIso
              (E'.iso r (r + 1) pq rfl hr)))
          f₀
          (((E.pagePresentation pq r hr).exists_preimage_le_preimage_iff
            (E'.pagePresentation pq r hr) f₀ hZ hB _ _).mpr hZ_step)
          (((E.pagePresentation pq r hr).exists_preimage_le_preimage_iff
            (E'.pagePresentation pq r hr) f₀ hZ hB _ _).mpr hB_step) := by
    simp only [pagePresentation_add_one E pq r hr, pagePresentation_add_one E' pq r hr]
  rw [heq, hcomp, htrans, hhom, f.comm r (r + 1) pq rfl hr, Iso.inv_hom_id_assoc]

private theorem mapInduced_pagePresentation_aux {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    ∃ (hZ : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.cyclesSubobject pq r hr) ≤
        E'.cyclesSubobject pq r hr)
      (hB : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.boundariesSubobject pq r hr) ≤
        E'.boundariesSubobject pq r hr),
      (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr)
        ((f.hom r₀ le_rfl).f pq) hZ hB = (f.hom r hr).f pq := by
  induction r, hr using Int.leInduction with
  | base => exact mapInduced_pagePresentation_base f pq
  | succ r hr ih =>
    obtain ⟨hZ, hB, hmap⟩ := ih
    exact mapInduced_pagePresentation_step f pq r hr hZ hB hmap

/-- Naturality of the cycle tower: a morphism `f : E ⟶ E'` maps `Z_r(E, pq)` into `Z_r(E', pq)`
via direct image along the first-page component `(f.hom r₀).f pq`. -/
theorem Hom.exists_cyclesSubobject_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) ≤
      E'.cyclesSubobject pq r hr :=
  (mapInduced_pagePresentation_aux f pq r hr).choose

/-- Naturality of the boundary tower: a morphism `f : E ⟶ E'` maps `B_r(E, pq)` into `B_r(E', pq)`
via direct image along the first-page component `(f.hom r₀).f pq`. -/
theorem Hom.exists_boundariesSubobject_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  (mapInduced_pagePresentation_aux f pq r hr).choose_spec.choose

/-- Adjoint form of naturality for cycles: `Z_r(E, pq)` lies below the pullback of `Z_r(E', pq)`
along `(f.hom r₀).f pq`. -/
theorem Hom.cyclesSubobject_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.cyclesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesSubobject pq r hr) :=
  (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le.mp
    (f.exists_cyclesSubobject_le pq r hr)

/-- Adjoint form of naturality for boundaries: `B_r(E, pq)` lies below the pullback of `B_r(E', pq)`
along `(f.hom r₀).f pq`. -/
theorem Hom.boundariesSubobject_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.boundariesSubobject pq r hr) :=
  (Subobject.existsPullbackAdj ((f.hom r₀).f pq)).gc.le_iff_le.mp
    (f.exists_boundariesSubobject_le pq r hr)

/-- The morphism induced by the first-page component `(f.hom r₀).f pq` on `pagePresentation` is the
page-`r` component `(f.hom r).f pq`. -/
theorem Hom.mapInduced_pagePresentation {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (E.pagePresentation pq r hr).mapInduced (E'.pagePresentation pq r hr) ((f.hom r₀).f pq)
        (f.exists_cyclesSubobject_le pq r hr) (f.exists_boundariesSubobject_le pq r hr) =
      (f.hom r hr).f pq :=
  (mapInduced_pagePresentation_aux f pq r hr).choose_spec.choose_spec

/-- An isomorphism `e : E ≅ E'` of spectral sequences carries `Z_r(E, pq)` onto `Z_r(E', pq)` under
the first-page isomorphism `(e.hom.hom r₀).f pq`. -/
theorem exists_cyclesSubobject_eq_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr := by
  refine le_antisymm (e.hom.exists_cyclesSubobject_le pq r hr) ?_
  have h := (Subobject.exists ((e.hom.hom r₀).f pq)).monotone
    (e.inv.exists_cyclesSubobject_le pq r hr)
  rw [← Subobject.exists_comp] at h
  have hid : (e.inv.hom r₀).f pq ≫ (e.hom.hom r₀).f pq = 𝟙 _ := by
    have := congrArg (fun u : E' ⟶ E' ↦ (u.hom r₀).f pq) e.inv_hom_id
    simpa only [comp_hom, id_hom, HomologicalComplex.comp_f, HomologicalComplex.id_f] using this
  rwa [hid, Subobject.exists_iso_map, Subobject.map_id] at h

/-- An isomorphism `e : E ≅ E'` of spectral sequences carries `B_r(E, pq)` onto `B_r(E', pq)` under
the first-page isomorphism `(e.hom.hom r₀).f pq`. -/
theorem exists_boundariesSubobject_eq_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    (Subobject.exists ((e.hom.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr := by
  refine le_antisymm (e.hom.exists_boundariesSubobject_le pq r hr) ?_
  have h := (Subobject.exists ((e.hom.hom r₀).f pq)).monotone
    (e.inv.exists_boundariesSubobject_le pq r hr)
  rw [← Subobject.exists_comp] at h
  have hid : (e.inv.hom r₀).f pq ≫ (e.hom.hom r₀).f pq = 𝟙 _ := by
    have := congrArg (fun u : E' ⟶ E' ↦ (u.hom r₀).f pq) e.inv_hom_id
    simpa only [comp_hom, id_hom, HomologicalComplex.comp_f, HomologicalComplex.id_f] using this
  rwa [hid, Subobject.exists_iso_map, Subobject.map_id] at h

/-- Rebasing compatibility for `pagePresentation`: presenting page `r ≥ s` inside page `r₀` is
the composition of presenting page `s` inside page `r₀` with presenting page `r` inside page `s`
for `E.fromPage s hs`. -/
theorem pagePresentation_eq_comp_fromPage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).comp ((E.fromPage s hs).pagePresentation pq r hsr) := by
  induction r, hsr using Int.leInduction with
  | base =>
    rw [pagePresentation_base, TauCeti.SubquotientPresentation.comp_id]
  | succ r hsr ih =>
    rw [pagePresentation_add_one E pq r (hs.trans hsr),
      pagePresentation_add_one (E.fromPage s hs) pq r hsr, ih,
      TauCeti.SubquotientPresentation.comp_assoc]

/-- Rebasing compatibility for cycles: `Z_r(E, pq)` is the preimage under `E.pagePresentation pq s`
of `Z_r(E.fromPage s, pq)`. -/
theorem cyclesSubobject_eq_preimage_fromPage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesSubobject pq r hsr) :=
  congrArg TauCeti.SubquotientPresentation.Z (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

/-- Rebasing compatibility for boundaries: `B_r(E, pq)` is the preimage under
`E.pagePresentation pq s` of `B_r(E.fromPage s, pq)`. -/
theorem boundariesSubobject_eq_preimage_fromPage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSubobject pq r hsr) :=
  congrArg TauCeti.SubquotientPresentation.B (E.pagePresentation_eq_comp_fromPage pq s hs r hsr)

end Tower

section Stabilisation

/-- `E` *stabilises at `pq` from page `s`* if on every page `r ≥ s`, both the differential leaving
`pq` and the differential entering `pq` vanish. -/
@[expose]
def StabilisesAt (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) : Prop :=
  ∀ (r : ℤ) (hsr : s ≤ r),
    (E.page r (hs.trans hsr)).dFrom pq = 0 ∧ (E.page r (hs.trans hsr)).dTo pq = 0

/-- `E` is *regular at `pq`* if the differentials leaving `pq` vanish from some page onward. -/
@[expose]
def IsRegularAt (E : SpectralSequence C c r₀) (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0

/-- `E` is *coregular at `pq`* if the differentials entering `pq` vanish from some page onward. -/
@[expose]
def IsCoregularAt (E : SpectralSequence C c r₀) (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0

/-- `E` *degenerates at page `s`* if every differential on every page `r ≥ s` vanishes. -/
@[expose]
def DegeneratesAt (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s := by lia) : Prop :=
  ∀ (r : ℤ) (hsr : s ≤ r) (i j : κ), (E.page r (hs.trans hsr)).d i j = 0

theorem StabilisesAt.dFrom_eq_zero {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dFrom pq = 0 :=
  (h r hsr).1

theorem StabilisesAt.dTo_eq_zero {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) {r : ℤ} (hsr : s ≤ r) :
    (E.page r (hs.trans hsr)).dTo pq = 0 :=
  (h r hsr).2

theorem StabilisesAt.d_out {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq pq' = 0 :=
  (E.page_dFrom_eq_zero_iff pq r (hs.trans hsr)).mp (h.dFrom_eq_zero hsr) pq'

theorem StabilisesAt.d_in {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) {r : ℤ} (hsr : s ≤ r) (pq' : κ) :
    (E.page r (hs.trans hsr)).d pq' pq = 0 :=
  (E.page_dTo_eq_zero_iff pq r (hs.trans hsr)).mp (h.dTo_eq_zero hsr) pq'

theorem stabilisesAt_iff_forall_d_eq_zero (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔
      ∀ (r : ℤ) (hsr : s ≤ r) (pq' : κ),
        (E.page r (hs.trans hsr)).d pq pq' = 0 ∧ (E.page r (hs.trans hsr)).d pq' pq = 0 := by
  refine ⟨fun h r hsr pq' ↦ ⟨h.d_out hsr pq', h.d_in hsr pq'⟩, fun h r hsr ↦ ?_⟩
  exact ⟨(E.page_dFrom_eq_zero_iff pq r (hs.trans hsr)).mpr (fun pq' ↦ (h r hsr pq').1),
    (E.page_dTo_eq_zero_iff pq r (hs.trans hsr)).mpr (fun pq' ↦ (h r hsr pq').2)⟩

/-- Stabilisation from page `s` persists to every later page `s' ≥ s`. -/
theorem StabilisesAt.of_le {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) {s' : ℤ} (hss' : s ≤ s') :
    E.StabilisesAt pq s' (hs.trans hss') :=
  fun r hs'r ↦ h r (hss'.trans hs'r)

theorem StabilisesAt.isRegularAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) : E.IsRegularAt pq :=
  ⟨s, hs, fun r hsr ↦ (h r hsr).1⟩

theorem StabilisesAt.isCoregularAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.StabilisesAt pq s hs) : E.IsCoregularAt pq :=
  ⟨s, hs, fun r hsr ↦ (h r hsr).2⟩

/-- `E` is both regular and coregular at `pq` if and only if it stabilises at `pq` from some
page. -/
theorem isRegularAt_and_isCoregularAt_iff_exists_stabilisesAt (E : SpectralSequence C c r₀)
    (pq : κ) :
    E.IsRegularAt pq ∧ E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), E.StabilisesAt pq s hs := by
  constructor
  · rintro ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, _, h₂⟩⟩
    exact ⟨max s₁ s₂, hs₁.trans (le_max_left s₁ s₂), fun r hr ↦
      ⟨h₁ r ((le_max_left s₁ s₂).trans hr), h₂ r ((le_max_right s₁ s₂).trans hr)⟩⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨h.isRegularAt, h.isCoregularAt⟩

/-- Degeneration at page `s` persists to every later page `s' ≥ s`. -/
theorem DegeneratesAt.of_le {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.DegeneratesAt s hs) {s' : ℤ} (hss' : s ≤ s') :
    E.DegeneratesAt s' (hs.trans hss') :=
  fun r hs'r i j ↦ h r (hss'.trans hs'r) i j

/-- Degeneration at page `s` implies stabilisation at every position from page `s`. -/
theorem DegeneratesAt.stabilisesAt {E : SpectralSequence C c r₀} {s : ℤ} {hs : r₀ ≤ s}
    (h : E.DegeneratesAt s hs) (pq : κ) :
    E.StabilisesAt pq s hs :=
  fun r hsr ↦ ⟨h r hsr pq _, h r hsr _ pq⟩

/-- `E` degenerates at page `s` if and only if it stabilises at every position from page `s`. -/
theorem degeneratesAt_iff_forall_stabilisesAt (E : SpectralSequence C c r₀) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ ∀ pq : κ, E.StabilisesAt pq s hs :=
  ⟨fun h pq ↦ h.stabilisesAt pq, fun h _ hsr i j ↦ (h i).d_out hsr j⟩

/-- If all differentials leaving `pq` vanish from page `s` onward, then `Z_r(pq) = Z_s(pq)` for all
`r ≥ s`. -/
theorem cyclesSubobject_eq_of_forall_dFrom_eq_zero (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0)
    (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih =>
    rw [(E.cyclesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- If all differentials entering `pq` vanish from page `s` onward, then `B_r(pq) = B_s(pq)` for
all `r ≥ s`. -/
theorem boundariesSubobject_eq_of_forall_dTo_eq_zero (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) (h : ∀ (r : ℤ) (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0)
    (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ t hst ih =>
    rw [(E.boundariesSubobject_add_one_eq_iff pq t (hs.trans hst)).mpr (h t hst), ih]

/-- `E` is regular at `pq` if and only if the cycle tower `r ↦ Z_r(pq)` is eventually constant. -/
theorem isRegularAt_iff_eventually_const_cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ) :
    E.IsRegularAt pq ↔
      ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
        E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, fun r hsr ↦ E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs h r hsr⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, fun r hsr ↦ (E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp ?_⟩
    rw [h (r + 1) (Int.le_add_one hsr), h r hsr]

/-- `E` is coregular at `pq` if and only if the boundary tower `r ↦ B_r(pq)` is eventually
constant. -/
theorem isCoregularAt_iff_eventually_const_boundariesSubobject (E : SpectralSequence C c r₀)
    (pq : κ) :
    E.IsCoregularAt pq ↔
      ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ (r : ℤ) (hsr : s ≤ r),
        E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, fun r hsr ↦ E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs h r hsr⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, fun r hsr ↦ (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp ?_⟩
    rw [h (r + 1) (Int.le_add_one hsr), h r hsr]

/-- `E` stabilises at `pq` from page `s` if and only if both `Z_r(pq)` and `B_r(pq)` are constant
for `r ≥ s`. -/
theorem stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject
    (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔
      ∀ (r : ℤ) (hsr : s ≤ r),
        E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs ∧
          E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  constructor
  · intro h r hsr
    exact ⟨E.cyclesSubobject_eq_of_forall_dFrom_eq_zero pq hs (fun t hst ↦ (h t hst).1) r hsr,
      E.boundariesSubobject_eq_of_forall_dTo_eq_zero pq hs (fun t hst ↦ (h t hst).2) r hsr⟩
  · intro h r hsr
    refine ⟨(E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp ?_,
      (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).mp ?_⟩
    · rw [(h (r + 1) (Int.le_add_one hsr)).1, (h r hsr).1]
    · rw [(h (r + 1) (Int.le_add_one hsr)).2, (h r hsr).2]

theorem StabilisesAt.cyclesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).1

theorem StabilisesAt.boundariesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    {hs : r₀ ≤ s} (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  ((E.stabilisesAt_iff_const_cyclesSubobject_and_boundariesSubobject pq s hs).mp h r hsr).2

theorem DegeneratesAt.cyclesSubobject_eq_top {E : SpectralSequence C c r₀}
    (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.cyclesSubobject pq r hr = ⊤ := by
  rw [(h.stabilisesAt pq).cyclesSubobject_eq r hr, cyclesSubobject_base]

theorem DegeneratesAt.boundariesSubobject_eq_bot {E : SpectralSequence C c r₀}
    (h : E.DegeneratesAt r₀ le_rfl) (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    E.boundariesSubobject pq r hr = ⊥ := by
  rw [(h.stabilisesAt pq).boundariesSubobject_eq r hr, boundariesSubobject_base]

theorem stabilisesAt_fromPage_iff (E : SpectralSequence C c r₀) (pq : κ) (s t : ℤ)
    (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).StabilisesAt pq t hst ↔ E.StabilisesAt pq t (hs.trans hst) :=
  Iff.rfl

theorem isRegularAt_fromPage_iff (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsRegularAt pq ↔ E.IsRegularAt pq := by
  constructor
  · rintro ⟨t, hst, h⟩
    exact ⟨t, hs.trans hst, h⟩
  · rintro ⟨t, _, h⟩
    exact ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩

theorem isCoregularAt_fromPage_iff (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    (E.fromPage s hs).IsCoregularAt pq ↔ E.IsCoregularAt pq := by
  constructor
  · rintro ⟨t, hst, h⟩
    exact ⟨t, hs.trans hst, h⟩
  · rintro ⟨t, _, h⟩
    exact ⟨max s t, le_max_left s t, fun r hr ↦ h r ((le_max_right s t).trans hr)⟩

theorem degeneratesAt_fromPage_iff (E : SpectralSequence C c r₀) (s t : ℤ)
    (hs : r₀ ≤ s) (hst : s ≤ t) :
    (E.fromPage s hs).DegeneratesAt t hst ↔ E.DegeneratesAt t (hs.trans hst) :=
  Iff.rfl

/-- Isomorphic spectral sequences have the same vanishing differentials on every page. -/
theorem page_d_eq_zero_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (r : ℤ) (hr : r₀ ≤ r) (i j : κ) :
    (E.page r hr).d i j = 0 ↔ (E'.page r hr).d i j = 0 := by
  have hi : IsIso ((e.hom.hom r hr).f i) :=
    ((pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) i).mapIso e).isIso_hom
  have hj : IsIso ((e.hom.hom r hr).f j) :=
    ((pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) j).mapIso e).isIso_hom
  have hcomm := (e.hom.hom r hr).comm i j
  constructor
  · intro h
    rw [h, zero_comp] at hcomm
    exact (cancel_epi ((e.hom.hom r hr).f i)).mp (by rw [comp_zero]; exact hcomm)
  · intro h
    rw [h, comp_zero] at hcomm
    exact (cancel_mono ((e.hom.hom r hr).f j)).mp (by rw [zero_comp]; exact hcomm.symm)

/-- Isomorphic spectral sequences stabilise at the same positions and pages. -/
theorem stabilisesAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    E.StabilisesAt pq s hs ↔ E'.StabilisesAt pq s hs := by
  simp only [StabilisesAt, HomologicalComplex.dFrom, HomologicalComplex.dTo,
    page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are regular at the same positions. -/
theorem isRegularAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) :
    E.IsRegularAt pq ↔ E'.IsRegularAt pq := by
  simp only [IsRegularAt, HomologicalComplex.dFrom, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences are coregular at the same positions. -/
theorem isCoregularAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) :
    E.IsCoregularAt pq ↔ E'.IsCoregularAt pq := by
  simp only [IsCoregularAt, HomologicalComplex.dTo, page_d_eq_zero_iff_of_iso e]

/-- Isomorphic spectral sequences degenerate at the same pages. -/
theorem degeneratesAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (s : ℤ)
    (hs : r₀ ≤ s := by lia) :
    E.DegeneratesAt s hs ↔ E'.DegeneratesAt s hs := by
  simp only [DegeneratesAt, page_d_eq_zero_iff_of_iso e]

/-- When `E` stabilises at `pq` from page `s`, the canonical isomorphism
`(E.page s).X pq ≅ (E.page r).X pq` for `r ≥ s`, built by composing the page-to-page homology
identifications. -/
noncomputable def pageXIsoOfStabilises (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq :=
  Int.leInduction
    (motive := fun r hsr ↦ (E.page s hs).X pq ≅ (E.page r (hs.trans hsr)).X pq)
    (Iso.refl _)
    (fun t hst e ↦
      e ≪≫
        (((E.page t (hs.trans hst)).sc pq).cyclesIsoX₂ (h.dFrom_eq_zero hst)).symm ≪≫
        ((E.page t (hs.trans hst)).sc pq).asIsoHomologyπ (h.dTo_eq_zero hst) ≪≫
        E.iso t (t + 1) pq rfl (hs.trans hst))
    r hsr

@[simp]
theorem pageXIsoOfStabilises_self (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) :
    E.pageXIsoOfStabilises pq s hs h s le_rfl = Iso.refl _ :=
  Int.leInduction_base _ _

theorem pageXIsoOfStabilises_add_one (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ)
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (t : ℤ) (hst : s ≤ t) :
    E.pageXIsoOfStabilises pq s hs h (t + 1) (Int.le_add_one hst) =
      E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        (((E.page t (hs.trans hst)).sc pq).cyclesIsoX₂ (h.dFrom_eq_zero hst)).symm ≪≫
        ((E.page t (hs.trans hst)).sc pq).asIsoHomologyπ (h.dTo_eq_zero hst) ≪≫
        E.iso t (t + 1) pq rfl (hs.trans hst) :=
  Int.leInduction_add_one _ _ t hst

/-- When `E` stabilises at `pq` from page `s`, `pagePresentation` on page `r ≥ s` is the
page-`s` presentation transported along `pageXIsoOfStabilises`. -/
theorem pagePresentation_eq_transIso_pageXIsoOfStabilises (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).transIso (E.pageXIsoOfStabilises pq s hs h r hsr) := by
  induction r, hsr using Int.leInduction with
  | base =>
    rw [pageXIsoOfStabilises_self, TauCeti.SubquotientPresentation.transIso_refl]
  | succ t hst ih =>
    rw [pagePresentation_add_one E pq t (hs.trans hst), ih,
      pageXIsoOfStabilises_add_one E pq s hs h t hst,
      ShortComplex.homologyPresentation_eq_id_transIso _ (h.dTo_eq_zero hst) (h.dFrom_eq_zero hst),
      TauCeti.SubquotientPresentation.transIso_trans,
      TauCeti.SubquotientPresentation.comp_transIso,
      TauCeti.SubquotientPresentation.comp_id,
      TauCeti.SubquotientPresentation.transIso_trans]
    simp only [Iso.trans_assoc]

/-- Composition compatibility of `pageXIsoOfStabilises` for `s ≤ t ≤ r`. -/
theorem pageXIsoOfStabilises_trans (E : SpectralSequence C c r₀) (pq : κ) {s t r : ℤ}
    (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (hst : s ≤ t) (htr : t ≤ r) :
    E.pageXIsoOfStabilises pq s hs h t hst ≪≫
        E.pageXIsoOfStabilises pq t (hs.trans hst) (h.of_le hst) r htr =
      E.pageXIsoOfStabilises pq s hs h r (hst.trans htr) := by
  induction r, htr using Int.leInduction with
  | base =>
    rw [pageXIsoOfStabilises_self, Iso.trans_refl]
  | succ u htu ih =>
    rw [pageXIsoOfStabilises_add_one E pq t (hs.trans hst) (h.of_le hst) u htu,
      pageXIsoOfStabilises_add_one E pq s hs h u (hst.trans htu), ← Iso.trans_assoc, ih]

/-- Naturality of `pageXIsoOfStabilises` with respect to morphisms of spectral sequences. -/
@[reassoc]
theorem Hom.pageXIsoOfStabilises_naturality {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (h : E.StabilisesAt pq s hs) (h' : E'.StabilisesAt pq s hs)
    (r : ℤ) (hsr : s ≤ r) :
    (f.hom s hs).f pq ≫ (E'.pageXIsoOfStabilises pq s hs h' r hsr).hom =
      (E.pageXIsoOfStabilises pq s hs h r hsr).hom ≫ (f.hom r (hs.trans hsr)).f pq := by
  have hmap := f.mapInduced_pagePresentation pq r (hs.trans hsr)
  have hmaps := f.mapInduced_pagePresentation pq s hs
  have heq :
      (E.pagePresentation pq r (hs.trans hsr)).mapInduced
          (E'.pagePresentation pq r (hs.trans hsr)) ((f.hom r₀).f pq)
          (f.exists_cyclesSubobject_le pq r (hs.trans hsr))
          (f.exists_boundariesSubobject_le pq r (hs.trans hsr)) =
        ((E.pagePresentation pq s hs).transIso (E.pageXIsoOfStabilises pq s hs h r hsr)).mapInduced
          ((E'.pagePresentation pq s hs).transIso (E'.pageXIsoOfStabilises pq s hs h' r hsr))
          ((f.hom r₀).f pq)
          (f.exists_cyclesSubobject_le pq s hs)
          (f.exists_boundariesSubobject_le pq s hs) := by
    simp only [pagePresentation_eq_transIso_pageXIsoOfStabilises E pq s hs h r hsr,
      pagePresentation_eq_transIso_pageXIsoOfStabilises E' pq s hs h' r hsr]
  rw [heq, TauCeti.SubquotientPresentation.mapInduced_transIso, hmaps] at hmap
  rw [← hmap, Iso.hom_inv_id_assoc]

theorem pageXIsoOfStabilises_fromPage (E : SpectralSequence C c r₀) (pq : κ) {s t r : ℤ}
    (hs : r₀ ≤ s) (hst : s ≤ t) (h : E.StabilisesAt pq t (hs.trans hst)) (htr : t ≤ r) :
    (E.fromPage s hs).pageXIsoOfStabilises pq t hst
        ((E.stabilisesAt_fromPage_iff pq s t hs hst).mpr h) r htr =
      E.pageXIsoOfStabilises pq t (hs.trans hst) h r htr := by
  induction r, htr using Int.leInduction with
  | base =>
    rw [pageXIsoOfStabilises_self, pageXIsoOfStabilises_self]
  | succ u htu ih =>
    rw [pageXIsoOfStabilises_add_one (E.fromPage s hs) pq t hst
        ((E.stabilisesAt_fromPage_iff pq s t hs hst).mpr h) u htu,
      pageXIsoOfStabilises_add_one E pq t (hs.trans hst) h u htu, ih]

end Stabilisation

end CategoryTheory.SpectralSequence
