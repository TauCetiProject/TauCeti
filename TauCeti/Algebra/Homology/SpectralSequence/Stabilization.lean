/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.Algebra.Homology.SpectralSequence.Tower

/-!
# Stabilization, regularity and degeneration of spectral sequences

A spectral sequence `E : SpectralSequence C c r₀` *stabilizes at `pq` from page `s`* (`s ≥ r₀`)
when for every `r ≥ s` both the differential leaving `pq` and the differential entering `pq` on
page `r` vanish (`CategoryTheory.SpectralSequence.StabilizesAt`). It is *regular at `pq`*
(`CategoryTheory.SpectralSequence.IsRegularAt`) when the differentials leaving `pq` vanish on all
sufficiently large pages, *coregular at `pq`* (`CategoryTheory.SpectralSequence.IsCoregularAt`) when
the differentials entering `pq` vanish on all sufficiently large pages, and *degenerates at
page `s`* (`CategoryTheory.SpectralSequence.DegeneratesAt`) when every differential of every
page `r ≥ s` vanishes.

Through the cycle and boundary towers of `TauCeti.Algebra.Homology.SpectralSequence.Tower`,
regularity at `pq` is equivalent to the cycle tower `Z_r(pq)` being eventually constant
(`CategoryTheory.SpectralSequence.isRegularAt_iff_cyclesSubobject_const`), and coregularity at
`pq` to the boundary tower `B_r(pq)` being eventually constant
(`CategoryTheory.SpectralSequence.isCoregularAt_iff_boundariesSubobject_const`). Regularity and
coregularity together imply stabilization from some page
(`CategoryTheory.SpectralSequence.IsRegularAt.exists_stabilizesAt`), and degeneration at page `s` is
equivalent to stabilization at every position from page `s`
(`CategoryTheory.SpectralSequence.degeneratesAt_iff_forall_stabilizesAt`). All four properties are
invariant under isomorphisms of spectral sequences.

When `E` stabilizes at `pq` from page `s`, composing the homology identifications along pages
`s ≤ k < r` yields canonical isomorphisms
`h.pageXIso r hr hsr : (E.page s h.le).X pq ≅ (E.page r hr).X pq`
(`CategoryTheory.SpectralSequence.StabilizesAt.pageXIso`), which agree with the canonical
subquotient identifications `SubquotientPresentation.isoOfEq`
(`CategoryTheory.SpectralSequence.StabilizesAt.pageXIso_eq_isoOfEq`), compose functorially
(`CategoryTheory.SpectralSequence.StabilizesAt.pageXIso_trans`), and are natural in morphisms of
spectral sequences (`CategoryTheory.SpectralSequence.StabilizesAt.pageXIso_hom_naturality`).

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N), the discussion of degeneration
  and stabilization after Definition 20.1.
* [Stacks, Tag 0BDV](https://stacks.math.columbia.edu/tag/0BDV), Lemma 24.8 (1) and (2).
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits TauCeti

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Predicates

variable (E : SpectralSequence C c r₀)

/-- `E` **stabilizes at `pq` from page `s`** when `r₀ ≤ s` and on every page `r ≥ s` both the
differential leaving `pq` and the differential entering `pq` vanish. -/
structure StabilizesAt (pq : κ) (s : ℤ) : Prop where
  /-- The starting page `s` is at least the initial page `r₀`. -/
  le : r₀ ≤ s
  /-- Every differential leaving `pq` on a page `r ≥ s` vanishes. -/
  dFrom_eq_zero : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0
  /-- Every differential entering `pq` on a page `r ≥ s` vanishes. -/
  dTo_eq_zero : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0

/-- `E` is **regular at `pq`** when the differential leaving `pq` vanishes on all sufficiently
large pages. -/
def IsRegularAt (pq : κ) : Prop :=
  ∃ s : ℤ, r₀ ≤ s ∧ ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0

lemma isRegularAt_iff (pq : κ) :
    E.IsRegularAt pq ↔
      ∃ s : ℤ, r₀ ≤ s ∧ ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0 :=
  Iff.rfl

/-- `E` is **coregular at `pq`** when the differential entering `pq` vanishes on all sufficiently
large pages. -/
def IsCoregularAt (pq : κ) : Prop :=
  ∃ s : ℤ, r₀ ≤ s ∧ ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0

lemma isCoregularAt_iff (pq : κ) :
    E.IsCoregularAt pq ↔
      ∃ s : ℤ, r₀ ≤ s ∧ ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0 :=
  Iff.rfl

/-- `E` **degenerates at page `s`** when `r₀ ≤ s` and every differential of every page `r ≥ s`
vanishes. -/
structure DegeneratesAt (s : ℤ) : Prop where
  /-- The starting page `s` is at least the initial page `r₀`. -/
  le : r₀ ≤ s
  /-- Every differential on every page `r ≥ s` vanishes. -/
  d_eq_zero : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → ∀ pq pq' : κ, (E.page r hr).d pq pq' = 0

end Predicates

section Basic

variable {E : SpectralSequence C c r₀} {pq : κ} {s s' : ℤ}

/-- Stabilization from page `s` implies stabilization from every later page `s' ≥ s`. -/
lemma StabilizesAt.mono (h : E.StabilizesAt pq s) (hss' : s ≤ s') : E.StabilizesAt pq s' where
  le := h.le.trans hss'
  dFrom_eq_zero _ hr hs'r := h.dFrom_eq_zero hr (hss'.trans hs'r)
  dTo_eq_zero _ hr hs'r := h.dTo_eq_zero hr (hss'.trans hs'r)

lemma StabilizesAt.isRegularAt (h : E.StabilizesAt pq s) : E.IsRegularAt pq :=
  ⟨s, h.le, h.dFrom_eq_zero⟩

lemma StabilizesAt.isCoregularAt (h : E.StabilizesAt pq s) : E.IsCoregularAt pq :=
  ⟨s, h.le, h.dTo_eq_zero⟩

/-- Regularity and coregularity at `pq` together imply stabilization at `pq` from some page. -/
lemma IsRegularAt.exists_stabilizesAt (hreg : E.IsRegularAt pq) (hcoreg : E.IsCoregularAt pq) :
    ∃ s : ℤ, E.StabilizesAt pq s := by
  obtain ⟨s₁, hs₁, h₁⟩ := hreg
  obtain ⟨s₂, _, h₂⟩ := hcoreg
  exact ⟨max s₁ s₂, le_sup_of_le_left hs₁, fun _ hr hsr ↦ h₁ hr ((le_max_left _ _).trans hsr),
    fun _ hr hsr ↦ h₂ hr ((le_max_right _ _).trans hsr)⟩

/-- Degeneration at page `s` implies degeneration at every later page `s' ≥ s`. -/
lemma DegeneratesAt.mono (h : E.DegeneratesAt s) (hss' : s ≤ s') : E.DegeneratesAt s' where
  le := h.le.trans hss'
  d_eq_zero _ hr hs'r := h.d_eq_zero hr (hss'.trans hs'r)

/-- Degeneration at page `s` implies stabilization at every position from page `s`. -/
lemma DegeneratesAt.stabilizesAt (h : E.DegeneratesAt s) (pq : κ) : E.StabilizesAt pq s where
  le := h.le
  dFrom_eq_zero _ hr hsr := h.d_eq_zero hr hsr pq _
  dTo_eq_zero _ hr hsr := h.d_eq_zero hr hsr _ pq

/-- For `s ≥ r₀`, `E` degenerates at page `s` if and only if it stabilizes at every position from
page `s`. -/
lemma degeneratesAt_iff_forall_stabilizesAt (hs : r₀ ≤ s) :
    E.DegeneratesAt s ↔ ∀ pq : κ, E.StabilizesAt pq s := by
  refine ⟨fun h pq ↦ h.stabilizesAt pq, fun h ↦ ⟨hs, fun r hr hsr pq pq' ↦ ?_⟩⟩
  by_cases hrel : (c r).Rel pq pq'
  · rw [← (E.page r hr).dFrom_comp_xNextIso hrel, (h pq).dFrom_eq_zero hr hsr, zero_comp]
  · exact (E.page r hr).shape pq pq' hrel

/-- If `(E.page r).X pq` is zero, then `E` stabilizes at `pq` from page `r`. -/
lemma stabilizesAt_of_isZero {r : ℤ} (hr : r₀ ≤ r) (h : IsZero ((E.page r hr).X pq)) :
    E.StabilizesAt pq r where
  le := hr
  dFrom_eq_zero _ _ hrr' := (E.isZero_page_X_of_le hr h _ hrr').eq_of_src _ _
  dTo_eq_zero _ _ hrr' := (E.isZero_page_X_of_le hr h _ hrr').eq_of_tgt _ _

end Basic

section Towers

variable (E : SpectralSequence C c r₀) (pq : κ)

/-- If the differential leaving `pq` vanishes on all pages from `s` on, then the cycles `Z_r(pq)`
agree with `Z_s(pq)` for all `r ≥ s`. -/
lemma cyclesSubobject_eq_of_dFrom_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0)
    {r : ℤ} (hr : r₀ ≤ r) (hsr : s ≤ r) :
    E.cyclesSubobject pq r hr = E.cyclesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ k hk ih =>
    exact ((E.cyclesSubobject_add_one_eq_iff pq k (hs.trans hk)).2 (h (hs.trans hk) hk)).trans
      (ih (hs.trans hk))

/-- If the differential entering `pq` vanishes on all pages from `s` on, then the boundaries
`B_r(pq)` agree with `B_s(pq)` for all `r ≥ s`. -/
lemma boundariesSubobject_eq_of_dTo_eq_zero {s : ℤ} (hs : r₀ ≤ s)
    (h : ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0)
    {r : ℤ} (hr : r₀ ≤ r) (hsr : s ≤ r) :
    E.boundariesSubobject pq r hr = E.boundariesSubobject pq s hs := by
  induction r, hsr using Int.leInduction with
  | base => rfl
  | succ k hk ih =>
    exact ((E.boundariesSubobject_add_one_eq_iff pq k (hs.trans hk)).2 (h (hs.trans hk) hk)).trans
      (ih (hs.trans hk))

/-- The differential leaving `pq` vanishes on all pages from `s` on if and only if the cycle tower
is constant from `s` on. -/
lemma forall_dFrom_eq_zero_iff_cyclesSubobject_eq {s : ℤ} (hs : r₀ ≤ s) :
    (∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0) ↔
      ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r →
        E.cyclesSubobject pq r hr = E.cyclesSubobject pq s hs := by
  refine ⟨fun h r hr hsr ↦ E.cyclesSubobject_eq_of_dFrom_eq_zero pq hs h hr hsr,
    fun h r hr hsr ↦ ?_⟩
  rw [← E.cyclesSubobject_add_one_eq_iff pq r hr, h (Int.le_add_one hr) (Int.le_add_one hsr),
    h hr hsr]

/-- The differential entering `pq` vanishes on all pages from `s` on if and only if the boundary
tower is constant from `s` on. -/
lemma forall_dTo_eq_zero_iff_boundariesSubobject_eq {s : ℤ} (hs : r₀ ≤ s) :
    (∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0) ↔
      ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r →
        E.boundariesSubobject pq r hr = E.boundariesSubobject pq s hs := by
  refine ⟨fun h r hr hsr ↦ E.boundariesSubobject_eq_of_dTo_eq_zero pq hs h hr hsr,
    fun h r hr hsr ↦ ?_⟩
  rw [← E.boundariesSubobject_add_one_eq_iff pq r hr, h (Int.le_add_one hr) (Int.le_add_one hsr),
    h hr hsr]

/-- `E` is regular at `pq` if and only if the cycle tower `Z_r(pq)` is eventually constant. -/
lemma isRegularAt_iff_cyclesSubobject_const :
    E.IsRegularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r →
      E.cyclesSubobject pq r hr = E.cyclesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, (E.forall_dFrom_eq_zero_iff_cyclesSubobject_eq pq hs).1 h⟩,
    fun ⟨s, hs, h⟩ ↦ ⟨s, hs, (E.forall_dFrom_eq_zero_iff_cyclesSubobject_eq pq hs).2 h⟩⟩

/-- `E` is coregular at `pq` if and only if the boundary tower `B_r(pq)` is eventually constant. -/
lemma isCoregularAt_iff_boundariesSubobject_const :
    E.IsCoregularAt pq ↔ ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r →
      E.boundariesSubobject pq r hr = E.boundariesSubobject pq s hs :=
  ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, (E.forall_dTo_eq_zero_iff_boundariesSubobject_eq pq hs).1 h⟩,
    fun ⟨s, hs, h⟩ ↦ ⟨s, hs, (E.forall_dTo_eq_zero_iff_boundariesSubobject_eq pq hs).2 h⟩⟩

variable {E pq}

lemma StabilizesAt.cyclesSubobject_eq {s : ℤ} (h : E.StabilizesAt pq s) {r : ℤ} (hr : r₀ ≤ r)
    (hsr : s ≤ r) :
    E.cyclesSubobject pq r hr = E.cyclesSubobject pq s h.le :=
  E.cyclesSubobject_eq_of_dFrom_eq_zero pq h.le h.dFrom_eq_zero hr hsr

lemma StabilizesAt.boundariesSubobject_eq {s : ℤ} (h : E.StabilizesAt pq s) {r : ℤ} (hr : r₀ ≤ r)
    (hsr : s ≤ r) :
    E.boundariesSubobject pq r hr = E.boundariesSubobject pq s h.le :=
  E.boundariesSubobject_eq_of_dTo_eq_zero pq h.le h.dTo_eq_zero hr hsr

/-- `E` stabilizes at `pq` from page `s` if and only if `r₀ ≤ s` and both the cycle tower
`Z_r(pq)` and the boundary tower `B_r(pq)` are constant from page `s` on. -/
lemma stabilizesAt_iff_cyclesSubobject_and_boundariesSubobject_eq {s : ℤ} :
    E.StabilizesAt pq s ↔ ∃ hs : r₀ ≤ s,
      (∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r → E.cyclesSubobject pq r hr = E.cyclesSubobject pq s hs) ∧
      (∀ ⦃r : ℤ⦄ (hr : r₀ ≤ r), s ≤ r →
        E.boundariesSubobject pq r hr = E.boundariesSubobject pq s hs) := by
  refine ⟨fun h ↦ ⟨h.le, fun _ hr hsr ↦ h.cyclesSubobject_eq hr hsr,
    fun _ hr hsr ↦ h.boundariesSubobject_eq hr hsr⟩, fun ⟨hs, hZ, hB⟩ ↦ ?_⟩
  exact ⟨hs, (E.forall_dFrom_eq_zero_iff_cyclesSubobject_eq pq hs).2 hZ,
    (E.forall_dTo_eq_zero_iff_boundariesSubobject_eq pq hs).2 hB⟩

end Towers

section Iso

variable {E E' : SpectralSequence C c r₀}

private lemma d_eq_zero_of_iso (e : E ≅ E') {r : ℤ} (hr : r₀ ≤ r) {i j : κ}
    (h : (E.page r hr).d i j = 0) : (E'.page r hr).d i j = 0 := by
  calc (E'.page r hr).d i j
      = ((e.inv.hom r hr).f i ≫ (e.hom.hom r hr).f i) ≫ (E'.page r hr).d i j := by simp
    _ = (e.inv.hom r hr).f i ≫ (E.page r hr).d i j ≫ (e.hom.hom r hr).f j := by
        rw [Category.assoc, (e.hom.hom r hr).comm]
    _ = 0 := by rw [h, zero_comp, comp_zero]

lemma StabilizesAt.of_iso {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) (e : E ≅ E') :
    E'.StabilizesAt pq s where
  le := h.le
  dFrom_eq_zero _ hr hsr := d_eq_zero_of_iso e hr (h.dFrom_eq_zero hr hsr)
  dTo_eq_zero _ hr hsr := d_eq_zero_of_iso e hr (h.dTo_eq_zero hr hsr)

lemma stabilizesAt_iff_of_iso (e : E ≅ E') (pq : κ) (s : ℤ) :
    E.StabilizesAt pq s ↔ E'.StabilizesAt pq s :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma IsRegularAt.of_iso {pq : κ} (h : E.IsRegularAt pq) (e : E ≅ E') : E'.IsRegularAt pq :=
  let ⟨s, hs, h'⟩ := h
  ⟨s, hs, fun _ hr hsr ↦ d_eq_zero_of_iso e hr (h' hr hsr)⟩

lemma isRegularAt_iff_of_iso (e : E ≅ E') (pq : κ) : E.IsRegularAt pq ↔ E'.IsRegularAt pq :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma IsCoregularAt.of_iso {pq : κ} (h : E.IsCoregularAt pq) (e : E ≅ E') : E'.IsCoregularAt pq :=
  let ⟨s, hs, h'⟩ := h
  ⟨s, hs, fun _ hr hsr ↦ d_eq_zero_of_iso e hr (h' hr hsr)⟩

lemma isCoregularAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.IsCoregularAt pq ↔ E'.IsCoregularAt pq :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma DegeneratesAt.of_iso {s : ℤ} (h : E.DegeneratesAt s) (e : E ≅ E') : E'.DegeneratesAt s where
  le := h.le
  d_eq_zero _ hr hsr pq pq' := d_eq_zero_of_iso e hr (h.d_eq_zero hr hsr pq pq')

lemma degeneratesAt_iff_of_iso (e : E ≅ E') (s : ℤ) : E.DegeneratesAt s ↔ E'.DegeneratesAt s :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

end Iso

section StabilizingIso

variable {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}

/-- The canonical isomorphism `(E.page s h.le).X pq ≅ (E.page r hr).X pq` for `r ≥ s` when `E`
stabilizes at `pq` from page `s`: at each step `k` between `s` and `r`, both differentials at `pq`
vanish, so the object at `pq` is its own homology, which is identified with the next page. -/
noncomputable def StabilizesAt.pageXIso (h : E.StabilizesAt pq s) (r : ℤ) (hr : r₀ ≤ r)
    (hsr : s ≤ r) : (E.page s h.le).X pq ≅ (E.page r hr).X pq :=
  Int.leInduction (motive := fun r hsr ↦ (E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq)
    (Iso.refl _)
    (fun k hk e ↦ e ≪≫
      (E.page k (h.le.trans hk)).XIsoHomologyOfDEqZero pq (h.dTo_eq_zero (h.le.trans hk) hk)
        (h.dFrom_eq_zero (h.le.trans hk) hk) ≪≫
      E.iso k (k + 1) pq rfl (h.le.trans hk))
    r hsr

/-- On page `s` itself, `StabilizesAt.pageXIso` is the identity. -/
@[simp]
lemma StabilizesAt.pageXIso_self (h : E.StabilizesAt pq s) :
    h.pageXIso s h.le le_rfl = Iso.refl _ :=
  Int.leInduction_base _ _

/-- Passing from page `r` to page `r + 1` composes `StabilizesAt.pageXIso` with the homology
identification of page `r`. -/
lemma StabilizesAt.pageXIso_add_one (h : E.StabilizesAt pq s) (r : ℤ) (hr : r₀ ≤ r)
    (hsr : s ≤ r) :
    h.pageXIso (r + 1) (Int.le_add_one hr) (Int.le_add_one hsr) =
      h.pageXIso r hr hsr ≪≫
        (E.page r hr).XIsoHomologyOfDEqZero pq (h.dTo_eq_zero hr hsr) (h.dFrom_eq_zero hr hsr) ≪≫
        E.iso r (r + 1) pq rfl hr :=
  Int.leInduction_add_one _ _ r hsr

private lemma pageXIso_step_eq_isoOfEq (r : ℤ) (hr : r₀ ≤ r) (hFrom : (E.page r hr).dFrom pq = 0)
    (hTo : (E.page r hr).dTo pq = 0) :
    (E.page r hr).XIsoHomologyOfDEqZero pq hTo hFrom ≪≫ E.iso r (r + 1) pq rfl hr =
      (E.pagePresentation pq r hr).isoOfEq (E.pagePresentation pq (r + 1) (Int.le_add_one hr))
        ((E.pagePresentation_B pq r hr).trans
          (((E.boundariesSubobject_add_one_eq_iff pq r hr).2 hTo).symm.trans
            (E.pagePresentation_B pq (r + 1) (Int.le_add_one hr)).symm))
        ((E.pagePresentation_Z pq r hr).trans
          (((E.cyclesSubobject_add_one_eq_iff pq r hr).2 hFrom).symm.trans
            (E.pagePresentation_Z pq (r + 1) (Int.le_add_one hr)).symm)) := by
  have hZ : (E.pagePresentation pq r hr).Z =
      (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).Z :=
    (E.pagePresentation_Z pq r hr).trans
      (((E.cyclesSubobject_add_one_eq_iff pq r hr).2 hFrom).symm.trans
        (E.pagePresentation_Z pq (r + 1) (Int.le_add_one hr)).symm)
  have hZ' : (E.pagePresentation pq r hr).Z =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).sc pq).g) := by
    rw [E.pagePresentation_Z pq r hr,
      ← (E.cyclesSubobject_add_one_eq_iff pq r hr).2 hFrom,
      E.cyclesSubobject_add_one pq r hr, HomologicalComplex.shortComplexFunctor_obj_g]
  have ofLE_π_eq : ∀ {P₁ P₂ : SubquotientPresentation ((E.page r₀).X pq)
        ((E.page (r + 1) (Int.le_add_one hr)).X pq)} (hP : P₁ = P₂)
      {S : Subobject ((E.page r₀).X pq)} (hS : S ≤ P₁.Z),
      Subobject.ofLE S P₁.Z hS ≫ P₁.π =
        Subobject.ofLE S P₂.Z (hS.trans_eq (congrArg SubquotientPresentation.Z hP)) ≫ P₂.π := by
    rintro P₁ P₂ rfl S hS
    simp
  have hπ' : Subobject.ofLE _ _ hZ.le ≫ (E.pagePresentation pq (r + 1) (Int.le_add_one hr)).π =
      Subobject.ofLE _ _ hZ'.le ≫
        (E.pagePresentation pq r hr).preimageπ (kernelSubobject ((E.page r hr).sc pq).g) ≫
        ((E.page r hr).sc pq).kernelSubobjectIsoCycles.hom ≫
        ((E.page r hr).sc pq).homologyπ ≫ (E.iso r (r + 1) pq rfl hr).hom := by
    rw [ofLE_π_eq (E.pagePresentation_add_one pq r hr) hZ.le,
      SubquotientPresentation.π_mapIso', SubquotientPresentation.π_trans',
      ShortComplex.π_homologyPresentation',
      SubquotientPresentation.preimageπ_ofLE_assoc (E.pagePresentation pq r hr)
        (ShortComplex.homologyPresentation_Z ((E.page r hr).sc pq)).le]
    simp only [Category.assoc, Subobject.ofLE_comp_ofLE_assoc]
  have hp : (E.pagePresentation pq r hr).π ≫
      ((E.page r hr).iCyclesIso pq ((c r).next pq) rfl hFrom).inv =
      Subobject.ofLE _ _ hZ'.le ≫
        (E.pagePresentation pq r hr).preimageπ (kernelSubobject ((E.page r hr).sc pq).g) ≫
        ((E.page r hr).sc pq).kernelSubobjectIsoCycles.hom := by
    have h_ic : ((E.page r hr).sc pq).iCycles = (E.page r hr).iCycles pq := rfl
    rw [← cancel_mono ((E.page r hr).iCycles pq), Category.assoc, Category.assoc, Category.assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id, ← h_ic,
      ShortComplex.kernelSubobjectIsoCycles_hom_iCycles, SubquotientPresentation.preimageπ_arrow,
      Subobject.ofLE_comp_ofLE_assoc, Subobject.ofLE_refl, Category.id_comp]
  have h_hπ : ((E.page r hr).sc pq).homologyπ = (E.page r hr).homologyπ pq := rfl
  ext
  rw [← cancel_epi (E.pagePresentation pq r hr).π, SubquotientPresentation.π_isoOfEq_hom, hπ',
    Iso.trans_hom, HomologicalComplex.XIsoHomologyOfDEqZero_hom]
  simp only [← Category.assoc]
  rw [hp]
  simp only [Category.assoc, h_hπ]

/-- `StabilizesAt.pageXIso` coincides with the canonical isomorphism between subquotient
presentations with equal subobjects. -/
lemma StabilizesAt.pageXIso_eq_isoOfEq (h : E.StabilizesAt pq s) (r : ℤ) (hr : r₀ ≤ r)
    (hsr : s ≤ r) :
    h.pageXIso r hr hsr =
      (E.pagePresentation pq s h.le).isoOfEq (E.pagePresentation pq r hr)
        ((E.pagePresentation_B pq s h.le).trans
          ((h.boundariesSubobject_eq hr hsr).symm.trans (E.pagePresentation_B pq r hr).symm))
        ((E.pagePresentation_Z pq s h.le).trans
          ((h.cyclesSubobject_eq hr hsr).symm.trans (E.pagePresentation_Z pq r hr).symm)) := by
  induction r, hsr using Int.leInduction with
  | base =>
    rw [pageXIso_self, SubquotientPresentation.isoOfEq_refl]
  | succ k hk ih =>
    rw [pageXIso_add_one h k (h.le.trans hk) hk, ih (h.le.trans hk),
      pageXIso_step_eq_isoOfEq k (h.le.trans hk) (h.dFrom_eq_zero _ hk) (h.dTo_eq_zero _ hk),
      SubquotientPresentation.isoOfEq_trans]

/-- Composition compatibility for `StabilizesAt.pageXIso`. -/
lemma StabilizesAt.pageXIso_trans (h : E.StabilizesAt pq s) {r₁ r₂ : ℤ} (hr₁ : r₀ ≤ r₁)
    (hr₂ : r₀ ≤ r₂) (hsr₁ : s ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    h.pageXIso r₁ hr₁ hsr₁ ≪≫ (h.mono hsr₁).pageXIso r₂ hr₂ hr₁₂ =
      h.pageXIso r₂ hr₂ (hsr₁.trans hr₁₂) := by
  rw [h.pageXIso_eq_isoOfEq r₁ hr₁ hsr₁, (h.mono hsr₁).pageXIso_eq_isoOfEq r₂ hr₂ hr₁₂,
    h.pageXIso_eq_isoOfEq r₂ hr₂ (hsr₁.trans hr₁₂), SubquotientPresentation.isoOfEq_trans]

/-- Naturality of `StabilizesAt.pageXIso` in morphisms of spectral sequences. -/
@[reassoc]
lemma StabilizesAt.pageXIso_hom_naturality {E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s) (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) :
    (h.pageXIso r hr hsr).hom ≫ (f.hom r hr).f pq =
      (f.hom s h.le).f pq ≫ (h'.pageXIso r hr hsr).hom := by
  rw [h.pageXIso_eq_isoOfEq r hr hsr, h'.pageXIso_eq_isoOfEq r hr hsr]
  exact (E.pagePresentation_mapsTo pq f s h.le).isoOfEq_hom
    (E.pagePresentation_mapsTo pq f r hr) _ _ _ _

end StabilizingIso

end CategoryTheory.SpectralSequence
