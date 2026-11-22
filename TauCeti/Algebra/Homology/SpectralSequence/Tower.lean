/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.ShortComplex.Subquotient

/-!
# Cycle and boundary towers of a spectral sequence

For a spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C` and a position
`pq : κ`, each page `(E.page r hr).X pq` is inductively presented as a subquotient of the initial
object `(E.page r₀).X pq` (`CategoryTheory.SpectralSequence.pagePresentation`). Its top and bottom
subobjects form the cycle and boundary towers
`B_{r₀} ≤ B_{r₀ + 1} ≤ … ≤ Z_{r₀ + 1} ≤ Z_{r₀}` in `Subobject ((E.page r₀).X pq)`:

* `CategoryTheory.SpectralSequence.cyclesSubobject`: the decreasing tower `Z_r(pq)`, starting at
  `⊤` and pulling back `kernelSubobject ((E.page r hr).dFrom pq)` at each step;
* `CategoryTheory.SpectralSequence.boundariesSubobject`: the increasing tower `B_r(pq)`, starting
  at `⊥` and pulling back `imageSubobject ((E.page r hr).dTo pq)` at each step.

## Main declarations

* `CategoryTheory.SpectralSequence.fromPage`: rebasing a spectral sequence to start at a later
  page `s ≥ r₀`.
* `CategoryTheory.SpectralSequence.pagePresentation`,
  `CategoryTheory.SpectralSequence.cyclesSubobject`,
  `CategoryTheory.SpectralSequence.boundariesSubobject`: the inductive presentations and towers,
  together with monotonicity, vanishing characterizations (`cyclesSubobject_add_one_eq_iff`,
  `boundariesSubobject_add_one_eq_iff`, `isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject`),
  naturality (`Hom.pagePresentation_map`), rebasing (`pagePresentation_eq_trans_fromPage`), and
  invariance under isomorphisms of spectral sequences.

## References

* The Stacks Project, *Homological Algebra*, Section 12.20, Tag 011N.
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for spectral sequences*,
  Lemma 2.2 (2024).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section FromPage

/-- Rebase a spectral sequence `E` starting at page `r₀` so that it starts at a later page
`s ≥ r₀`. -/
abbrev fromPage (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) : SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

@[simp]
lemma fromPage_page (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.fromPage s hs).page r hr = E.page r (hs.trans hr) :=
  rfl

@[simp]
lemma fromPage_iso (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) (r r' : ℤ) (pq : κ)
    (hrr' : r + 1 = r') (hr : s ≤ r) :
    (E.fromPage s hs).iso r r' pq hrr' hr = E.iso r r' pq hrr' (hs.trans hr) :=
  rfl

/-- Restrict a morphism of spectral sequences `f : E ⟶ E'` to the rebased spectral sequences
starting at page `s ≥ r₀`. -/
abbrev Hom.fromPageMap {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s) :
    E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
lemma Hom.fromPageMap_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) :
    (f.fromPageMap s hs).hom r hr = f.hom r (hs.trans hr) :=
  rfl

variable (C c)

/-- Rebasing spectral sequences from page `r₀` to a later page `s ≥ r₀`, as a functor. -/
@[expose, simps]
def fromPageFunctor (s : ℤ) (hs : r₀ ≤ s) :
    SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := f.fromPageMap s hs

end FromPage

section Tower

variable (E : SpectralSequence C c r₀)

/-- The canonical subquotient presentation of the object `(E.page r hr).X pq` inside the initial
object `(E.page r₀).X pq`, constructed by induction on `r ≥ r₀`. At `r = r₀` it is the identity
presentation; in the inductive step it composes with the homology presentation of page `r`
transported along `E.iso r (r + 1) pq`. -/
noncomputable def pagePresentation (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    TauCeti.SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq) :=
  Int.leInduction
    (motive := fun r hr ↦
      TauCeti.SubquotientPresentation ((E.page r₀).X pq) ((E.page r hr).X pq))
    (TauCeti.SubquotientPresentation.refl ((E.page r₀).X pq))
    (fun r hr p ↦
      p.trans (((E.page r hr).sc pq).homologyPresentation.mapIso (E.iso r (r + 1) pq rfl hr)))
    r hr

@[simp]
lemma pagePresentation_base (pq : κ) :
    E.pagePresentation pq r₀ le_rfl = TauCeti.SubquotientPresentation.refl ((E.page r₀).X pq) :=
  Int.leInduction_base _ _

lemma pagePresentation_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).trans
        (((E.page r hr).sc pq).homologyPresentation.mapIso (E.iso r (r + 1) pq rfl hr)) :=
  Int.leInduction_add_one _ _ r hr

/-- The `r`-th cycle subobject `Z_r(pq)` of `(E.page r₀).X pq`, namely the larger subobject of
`E.pagePresentation pq r hr`. -/
noncomputable abbrev cyclesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).Z

/-- The `r`-th boundary subobject `B_r(pq)` of `(E.page r₀).X pq`, namely the smaller subobject of
`E.pagePresentation pq r hr`. -/
noncomputable abbrev boundariesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀).X pq) :=
  (E.pagePresentation pq r hr).B

@[simp]
lemma cyclesSubobject_base (pq : κ) :
    E.cyclesSubobject pq r₀ le_rfl = ⊤ := by
  rw [cyclesSubobject, pagePresentation_base, TauCeti.SubquotientPresentation.refl_Z]

@[simp]
lemma boundariesSubobject_base (pq : κ) :
    E.boundariesSubobject pq r₀ le_rfl = ⊥ := by
  rw [boundariesSubobject, pagePresentation_base, TauCeti.SubquotientPresentation.refl_B]

/-- On page `r + 1`, the cycle subobject `Z_{r+1}(pq)` is the preimage along the page-`r`
presentation of the kernel of the leaving differential `(E.page r hr).dFrom pq`. -/
lemma cyclesSubobject_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).dFrom pq)) := by
  rw [cyclesSubobject, E.pagePresentation_add_one pq r hr]
  rfl

/-- On page `r + 1`, the boundary subobject `B_{r+1}(pq)` is the preimage along the page-`r`
presentation of the image of the entering differential `(E.page r hr).dTo pq`. -/
lemma boundariesSubobject_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r hr).dTo pq)) := by
  rw [boundariesSubobject, E.pagePresentation_add_one pq r hr]
  rfl

/-- Description of the projection of `E.pagePresentation pq (r + 1)` in terms of the page-`r`
presentation, the homology presentation of page `r`, and `E.iso r (r + 1) pq`. -/
lemma pagePresentation_add_one_π (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).π =
      Subobject.ofLE (E.cyclesSubobject pq (r + 1) (Int.le_add_one hr))
          ((E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).dFrom pq)))
          (E.cyclesSubobject_add_one pq r hr).le ≫
        (E.pagePresentation pq r hr).preimageπ (kernelSubobject ((E.page r hr).dFrom pq)) ≫
        ((E.page r hr).sc pq).homologyPresentation.π ≫ (E.iso r (r + 1) pq rfl hr).hom := by
  let p := E.pagePresentation pq r hr
  let sc := (E.page r hr).sc pq
  have h1 : ∀ (q : TauCeti.SubquotientPresentation ((E.page r₀).X pq)
        ((E.page (r + 1) (Int.le_add_one hr)).X pq))
      (hq : q = p.trans (sc.homologyPresentation.mapIso (E.iso r (r + 1) pq rfl hr))),
      q.π = Subobject.ofLE q.Z (p.preimage (kernelSubobject ((E.page r hr).dFrom pq)))
          (by rw [hq]; rfl) ≫
        p.preimageπ (kernelSubobject ((E.page r hr).dFrom pq)) ≫
        sc.homologyPresentation.π ≫ (E.iso r (r + 1) pq rfl hr).hom := by
    rintro _ rfl
    rw [TauCeti.SubquotientPresentation.π_trans', TauCeti.SubquotientPresentation.π_mapIso]
    rfl
  exact h1 _ (E.pagePresentation_add_one pq r hr)

lemma boundariesSubobject_le_cyclesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).le

lemma boundariesSubobject_le_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
  rw [boundariesSubobject_add_one]
  exact (E.pagePresentation pq r hr).B_le_preimage _

lemma cyclesSubobject_add_one_le (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r hr := by
  rw [cyclesSubobject_add_one]
  exact (E.pagePresentation pq r hr).preimage_le_Z _

/-- The boundary tower `r ↦ B_r(pq)` is increasing. -/
lemma boundariesSubobject_le_of_le (pq : κ) {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq r' (hr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ r' hrr' ih =>
    exact ih.trans (E.boundariesSubobject_le_add_one pq r' (hr.trans hrr'))

/-- The cycle tower `r ↦ Z_r(pq)` is decreasing. -/
lemma cyclesSubobject_le_of_le (pq : κ) {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.cyclesSubobject pq r' (hr.trans hrr') ≤ E.cyclesSubobject pq r hr := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ r' hrr' ih =>
    exact (E.cyclesSubobject_add_one_le pq r' (hr.trans hrr')).trans ih

/-- Every boundary subobject `B_r(pq)` lies below every cycle subobject `Z_{r'}(pq)`. -/
lemma boundariesSubobject_le_cyclesSubobject_of_le (pq : κ) (r r' : ℤ)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r' hr' :=
  (E.boundariesSubobject_le_of_le pq hr (le_max_left r r')).trans
    ((E.boundariesSubobject_le_cyclesSubobject pq (max r r') (hr.trans (le_max_left r r'))).trans
      (E.cyclesSubobject_le_of_le pq hr' (le_max_right r r')))

/-- `Z_{r+1}(pq) = Z_r(pq)` if and only if the leaving differential on page `r` at `pq`
vanishes. -/
theorem cyclesSubobject_add_one_eq_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      (E.page r hr).dFrom pq = 0 := by
  rw [E.cyclesSubobject_add_one pq r hr]
  dsimp only [cyclesSubobject]
  rw [← (E.pagePresentation pq r hr).preimage_top,
    (E.pagePresentation pq r hr).preimage_inj, kernelSubobject_eq_top_iff]

/-- `B_{r+1}(pq) = B_r(pq)` if and only if the entering differential on page `r` at `pq`
vanishes. -/
theorem boundariesSubobject_add_one_eq_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      (E.page r hr).dTo pq = 0 := by
  rw [E.boundariesSubobject_add_one pq r hr]
  dsimp only [boundariesSubobject]
  rw [← (E.pagePresentation pq r hr).preimage_bot,
    (E.pagePresentation pq r hr).preimage_inj, imageSubobject_eq_bot_iff]

/-- If the leaving differential at `pq` vanishes on all pages `t` with `s ≤ t < r`, then
`Z_r(pq) = Z_s(pq)`. -/
lemma cyclesSubobject_eq_of_dFrom_eq_zero (pq : κ) {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r)
    (h : ∀ t (hst : s ≤ t), t < r → (E.page t (hs.trans hst)).dFrom pq = 0) :
    E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ r hsr ih =>
    rw [(E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).2
        (h r hsr (Int.lt_add_one_iff.2 le_rfl)),
      ih (fun t hst htr ↦ h t hst (htr.trans (Int.lt_add_one_iff.2 le_rfl)))]

/-- If the entering differential at `pq` vanishes on all pages `t` with `s ≤ t < r`, then
`B_r(pq) = B_s(pq)`. -/
lemma boundariesSubobject_eq_of_dTo_eq_zero (pq : κ) {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r)
    (h : ∀ t (hst : s ≤ t), t < r → (E.page t (hs.trans hst)).dTo pq = 0) :
    E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ r hsr ih =>
    rw [(E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).2
        (h r hsr (Int.lt_add_one_iff.2 le_rfl)),
      ih (fun t hst htr ↦ h t hst (htr.trans (Int.lt_add_one_iff.2 le_rfl)))]

/-- If all leaving differentials at `pq` on pages `< r` vanish, then `Z_r(pq) = ⊤`. -/
lemma cyclesSubobject_eq_top_of_dFrom_eq_zero (pq : κ) {r : ℤ} (hr : r₀ ≤ r)
    (h : ∀ t (ht : r₀ ≤ t), t < r → (E.page t ht).dFrom pq = 0) :
    E.cyclesSubobject pq r hr = ⊤ := by
  simpa using E.cyclesSubobject_eq_of_dFrom_eq_zero pq le_rfl hr h

/-- If all entering differentials at `pq` on pages `< r` vanish, then `B_r(pq) = ⊥`. -/
lemma boundariesSubobject_eq_bot_of_dTo_eq_zero (pq : κ) {r : ℤ} (hr : r₀ ≤ r)
    (h : ∀ t (ht : r₀ ≤ t), t < r → (E.page t ht).dTo pq = 0) :
    E.boundariesSubobject pq r hr = ⊥ := by
  simpa using E.boundariesSubobject_eq_of_dTo_eq_zero pq le_rfl hr h

/-- The object `(E.page r hr).X pq` is zero if and only if `B_r(pq) = Z_r(pq)`. -/
theorem isZero_page_X_iff_boundariesSubobject_eq_cyclesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r hr).X pq) ↔ E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).isZero_iff_B_eq_Z

end Tower

section Naturality

variable {E E' : SpectralSequence C c r₀}

private lemma naturality_step (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hB : (E'.boundariesSubobject pq r hr).Factors
      ((E.boundariesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq))
    (hZ : (E'.cyclesSubobject pq r hr).Factors
      ((E.cyclesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq))
    (hmap : (E.pagePresentation pq r hr).map (E'.pagePresentation pq r hr)
      ((f.hom r₀).f pq) hB hZ = (f.hom r hr).f pq) :
    ∃ (hB' : (E'.boundariesSubobject pq (r + 1) (Int.le_add_one hr)).Factors
          ((E.boundariesSubobject pq (r + 1) (Int.le_add_one hr)).arrow ≫ (f.hom r₀).f pq))
      (hZ' : (E'.cyclesSubobject pq (r + 1) (Int.le_add_one hr)).Factors
          ((E.cyclesSubobject pq (r + 1) (Int.le_add_one hr)).arrow ≫ (f.hom r₀).f pq)),
      (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).map
        (E'.pagePresentation pq (r + 1) (Int.le_add_one hr))
        ((f.hom r₀).f pq) hB' hZ' = (f.hom (r + 1) (Int.le_add_one hr)).f pq := by
  let p := E.pagePresentation pq r hr
  let p' := E'.pagePresentation pq r hr
  let φ : (E.page r hr).sc pq ⟶ (E'.page r hr).sc pq :=
    (HomologicalComplex.shortComplexFunctor C (c r) pq).map (f.hom r hr)
  have hτ₂ : φ.τ₂ = (f.hom r hr).f pq := rfl
  let q₀ := ((E.page r hr).sc pq).homologyPresentation
  let q₀' := ((E'.page r hr).sc pq).homologyPresentation
  have hI : q₀'.B.Factors (q₀.B.arrow ≫ p.map p' ((f.hom r₀).f pq) hB hZ) := by
    rw [hmap, ← hτ₂]
    exact ShortComplex.factors_imageSubobject_map φ
  have hK : q₀'.Z.Factors (q₀.Z.arrow ≫ p.map p' ((f.hom r₀).f pq) hB hZ) := by
    rw [hmap, ← hτ₂]
    exact ShortComplex.factors_kernelSubobject_map φ
  let q := q₀.mapIso (E.iso r (r + 1) pq rfl hr)
  let q' := q₀'.mapIso (E'.iso r (r + 1) pq rfl hr)
  have hB' : (E'.boundariesSubobject pq (r + 1) (Int.le_add_one hr)).Factors
      ((E.boundariesSubobject pq (r + 1) (Int.le_add_one hr)).arrow ≫ (f.hom r₀).f pq) := by
    rw [boundariesSubobject_add_one, boundariesSubobject_add_one]
    exact p.factors_preimage_of_factors_map p' ((f.hom r₀).f pq) hB hZ hI
  have hZ' : (E'.cyclesSubobject pq (r + 1) (Int.le_add_one hr)).Factors
      ((E.cyclesSubobject pq (r + 1) (Int.le_add_one hr)).arrow ≫ (f.hom r₀).f pq) := by
    rw [cyclesSubobject_add_one, cyclesSubobject_add_one]
    exact p.factors_preimage_of_factors_map p' ((f.hom r₀).f pq) hB hZ hK
  refine ⟨hB', hZ', ?_⟩
  have hcomp := TauCeti.SubquotientPresentation.trans_map p p' q q' ((f.hom r₀).f pq) hB hZ hI hK
  have hqmap : q.map q' (p.map p' ((f.hom r₀).f pq) hB hZ) hI hK =
      (f.hom (r + 1) (Int.le_add_one hr)).f pq := by
    dsimp only [q, q']
    rw [TauCeti.SubquotientPresentation.map_mapIso]
    have hsc : q₀.map q₀' (p.map p' ((f.hom r₀).f pq) hB hZ) hI hK =
        HomologicalComplex.homologyMap (f.hom r hr) pq := by
      have h1 : ∀ (g : (E.page r hr).X pq ⟶ (E'.page r hr).X pq) (_ : g = φ.τ₂) h1 h2,
          q₀.map q₀' g h1 h2 = ShortComplex.homologyMap φ := by
        rintro _ rfl _ _
        exact ShortComplex.homologyPresentation_map φ
      exact h1 _ hmap hI hK
    rw [hsc, f.comm r (r + 1) pq rfl hr, Iso.inv_hom_id_assoc]
  have hstepE := E.pagePresentation_add_one pq r hr
  have hstepE' := E'.pagePresentation_add_one pq r hr
  simpa only [hstepE, hstepE', hqmap] using hcomp

private lemma naturality_aux (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    ∃ (hB : (E'.boundariesSubobject pq r hr).Factors
          ((E.boundariesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq))
      (hZ : (E'.cyclesSubobject pq r hr).Factors
          ((E.cyclesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq)),
      (E.pagePresentation pq r hr).map (E'.pagePresentation pq r hr)
        ((f.hom r₀).f pq) hB hZ = (f.hom r hr).f pq := by
  induction r, hr using Int.leInduction with
  | base =>
    refine ⟨?_, ?_, ?_⟩
    · rw [boundariesSubobject_base, boundariesSubobject_base, ← Subobject.le_pullback_iff]
      exact bot_le
    · rw [cyclesSubobject_base, cyclesSubobject_base]
      exact Subobject.top_factors _
    · have h1 : ∀ (p : TauCeti.SubquotientPresentation ((E.page r₀).X pq) ((E.page r₀).X pq))
          (p' : TauCeti.SubquotientPresentation ((E'.page r₀).X pq) ((E'.page r₀).X pq))
          (_ : p = TauCeti.SubquotientPresentation.refl _)
          (_ : p' = TauCeti.SubquotientPresentation.refl _) hB hZ,
          p.map p' ((f.hom r₀).f pq) hB hZ = (f.hom r₀).f pq := by
        rintro _ _ rfl rfl hB hZ
        exact TauCeti.SubquotientPresentation.map_refl _ hB hZ
      exact h1 _ _ (E.pagePresentation_base pq) (E'.pagePresentation_base pq) _ _
  | succ r hr ih =>
    obtain ⟨hB, hZ, hmap⟩ := ih
    exact naturality_step f pq r hr hB hZ hmap

/-- A morphism of spectral sequences carries `B_r(E, pq)` into `B_r(E', pq)` (in `Factors` form). -/
lemma Hom.factors_boundariesSubobject (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E'.boundariesSubobject pq r hr).Factors
      ((E.boundariesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq) :=
  (naturality_aux f pq r hr).choose

/-- A morphism of spectral sequences carries `Z_r(E, pq)` into `Z_r(E', pq)` (in `Factors` form). -/
lemma Hom.factors_cyclesSubobject (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E'.cyclesSubobject pq r hr).Factors
      ((E.cyclesSubobject pq r hr).arrow ≫ (f.hom r₀).f pq) :=
  (naturality_aux f pq r hr).choose_spec.choose

/-- **Naturality on boundaries.** The direct image of `B_r(E, pq)` along `(f.hom r₀).f pq` lies
below `B_r(E', pq)`. -/
lemma Hom.exists_boundariesSubobject_le (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.exists ((f.hom r₀).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  (Subobject.exists_le_iff _ _ _).2 (f.factors_boundariesSubobject pq r hr)

/-- **Naturality on cycles.** `Z_r(E, pq)` lies below the pullback of `Z_r(E', pq)` along
`(f.hom r₀).f pq`. -/
lemma Hom.cyclesSubobject_le_pullback (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀).f pq)).obj (E'.cyclesSubobject pq r hr) :=
  (Subobject.le_pullback_iff _ _ _).2 (f.factors_cyclesSubobject pq r hr)

/-- **Naturality of presentations.** The morphism induced by `(f.hom r₀).f pq` between the page-`r`
presentations of `E` and `E'` at `pq` is `(f.hom r hr).f pq`. -/
theorem Hom.pagePresentation_map (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).map (E'.pagePresentation pq r hr) ((f.hom r₀).f pq)
        (f.factors_boundariesSubobject pq r hr) (f.factors_cyclesSubobject pq r hr) =
      (f.hom r hr).f pq :=
  (naturality_aux f pq r hr).choose_spec.choose_spec

/-- The component isomorphism `(E.page r hr).X pq ≅ (E'.page r hr).X pq` induced by an isomorphism
of spectral sequences `e : E ≅ E'`. -/
def pageXIsoOfIso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (E.page r hr).X pq ≅ (E'.page r hr).X pq :=
  (pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) pq).mapIso e

@[simp]
lemma pageXIsoOfIso_hom (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (pageXIsoOfIso e r hr pq).hom = (e.hom.hom r hr).f pq :=
  (rfl)

@[simp]
lemma pageXIsoOfIso_inv (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (pageXIsoOfIso e r hr pq).inv = (e.inv.hom r hr).f pq :=
  (rfl)

/-- Isomorphic spectral sequences have corresponding cycle towers under the first-page
isomorphism. -/
lemma map_cyclesSubobject_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr := by
  let g := pageXIsoOfIso e r₀ le_rfl pq
  have h1 : (Subobject.map g.hom).obj (E.cyclesSubobject pq r hr) ≤ E'.cyclesSubobject pq r hr :=
    ((Subobject.mapPullbackAdj g.hom).gc _ _).2 (e.hom.cyclesSubobject_le_pullback pq r hr)
  have h2 : (Subobject.map g.inv).obj (E'.cyclesSubobject pq r hr) ≤ E.cyclesSubobject pq r hr :=
    ((Subobject.mapPullbackAdj g.inv).gc _ _).2 (e.inv.cyclesSubobject_le_pullback pq r hr)
  exact le_antisymm h1
    (((Subobject.mapIsoToOrderIso g).apply_symm_apply _).symm.le.trans
      ((Subobject.mapIsoToOrderIso g).monotone h2))

/-- Isomorphic spectral sequences have corresponding boundary towers under the first-page
isomorphism. -/
lemma map_boundariesSubobject_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr := by
  let g := pageXIsoOfIso e r₀ le_rfl pq
  have h1 : (Subobject.map g.hom).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
    ((Subobject.mapPullbackAdj g.hom).gc _ _).2
      ((Subobject.le_pullback_iff _ _ _).2 (e.hom.factors_boundariesSubobject pq r hr))
  have h2 : (Subobject.map g.inv).obj (E'.boundariesSubobject pq r hr) ≤
      E.boundariesSubobject pq r hr :=
    ((Subobject.mapPullbackAdj g.inv).gc _ _).2
      ((Subobject.le_pullback_iff _ _ _).2 (e.inv.factors_boundariesSubobject pq r hr))
  exact le_antisymm h1
    (((Subobject.mapIsoToOrderIso g).apply_symm_apply _).symm.le.trans
      ((Subobject.mapIsoToOrderIso g).monotone h2))

end Naturality

section Rebasing

variable (E : SpectralSequence C c r₀)

/-- **Rebasing presentations.** For `s ≥ r₀` and `r ≥ s`, the page-`r` presentation of `E` inside
page `r₀` is the composite of the page-`s` presentation of `E` with the page-`r` presentation of
`E.fromPage s hs`. -/
theorem pagePresentation_eq_trans_fromPage (s : ℤ) (hs : r₀ ≤ s) (pq : κ)
    (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).trans ((E.fromPage s hs).pagePresentation pq r hsr) := by
  induction r, hsr using Int.leInduction with
  | base =>
    rw [pagePresentation_base, TauCeti.SubquotientPresentation.trans_refl]
  | succ r hsr ih =>
    rw [E.pagePresentation_add_one pq r (hs.trans hsr), ih,
      (E.fromPage s hs).pagePresentation_add_one pq r hsr,
      TauCeti.SubquotientPresentation.trans_assoc]

/-- **Rebasing the cycle tower.** For `s ≥ r₀` and `r ≥ s`, `Z_r(pq)` is the preimage along the
page-`s` presentation of the `r`-th cycle subobject of `E.fromPage s hs`. -/
lemma cyclesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (pq : κ) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).cyclesSubobject pq r hsr) :=
  congrArg TauCeti.SubquotientPresentation.Z (E.pagePresentation_eq_trans_fromPage s hs pq r hsr)

/-- **Rebasing the boundary tower.** For `s ≥ r₀` and `r ≥ s`, `B_r(pq)` is the preimage along the
page-`s` presentation of the `r`-th boundary subobject of `E.fromPage s hs`. -/
lemma boundariesSubobject_eq_preimage_fromPage (s : ℤ) (hs : r₀ ≤ s) (pq : κ) (r : ℤ)
    (hsr : s ≤ r) :
    E.boundariesSubobject pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).preimage ((E.fromPage s hs).boundariesSubobject pq r hsr) :=
  congrArg TauCeti.SubquotientPresentation.B
    (E.pagePresentation_eq_trans_fromPage s hs pq r hsr)

end Rebasing

end CategoryTheory.SpectralSequence
