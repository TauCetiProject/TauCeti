/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Stabilization.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Tower

/-!
# Stabilization and regularity of spectral sequences

This file defines the regularity and coregularity conditions on the differentials of a spectral
sequence `E : SpectralSequence C c r₀` and relates stabilization (`StabilizesAt` and
`pageXIsoOfStabilizesAt`, from `TauCeti.Algebra.Homology.SpectralSequence.Stabilization.Basic`)
to the cycle and boundary towers of `TauCeti.Algebra.Homology.SpectralSequence.Tower`:

* `CategoryTheory.SpectralSequence.IsRegularAt`: the leaving differentials at `pq` vanish on all
  sufficiently large pages, equivalently the cycle tower `Z_r(pq)` is eventually constant
  (`isRegularAt_iff_eventually_cyclesSubobject_eq`).
* `CategoryTheory.SpectralSequence.IsCoregularAt`: the entering differentials at `pq` vanish on
  all sufficiently large pages, equivalently the boundary tower `B_r(pq)` is eventually constant
  (`isCoregularAt_iff_eventually_boundariesSubobject_eq`).
* Compatibility of `CategoryTheory.SpectralSequence.pageXIsoOfStabilizesAt` with composition,
  subquotient presentations, and morphisms of spectral sequences (`pageXIsoOfStabilizesAt_trans`,
  `pageXIsoOfStabilizesAt_eq_isoOfEq`, `pageXIsoOfStabilizesAt_hom_naturality`).

## References

* The Stacks Project, *Homological Algebra*, Section 12.20 and Lemma 12.24.8, Tags 011O, 0BDV.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Definitions

variable (E : SpectralSequence C c r₀)

/-- A spectral sequence `E` is **regular at `pq`** if the differentials leaving `pq` vanish on all
sufficiently large pages. -/
def IsRegularAt (pq : κ) : Prop :=
  ∃ s, ∃ hs : r₀ ≤ s, ∀ r (hsr : s ≤ r), (E.page r (hs.trans hsr)).dFrom pq = 0

/-- A spectral sequence `E` is **coregular at `pq`** if the differentials entering `pq` vanish on
all sufficiently large pages. -/
def IsCoregularAt (pq : κ) : Prop :=
  ∃ s, ∃ hs : r₀ ≤ s, ∀ r (hsr : s ≤ r), (E.page r (hs.trans hsr)).dTo pq = 0

variable {E}

lemma StabilizesAt.isRegularAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) :
    E.IsRegularAt pq :=
  ⟨s, h.le, h.dFrom_eq_zero⟩

lemma StabilizesAt.isCoregularAt {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) :
    E.IsCoregularAt pq :=
  ⟨s, h.le, h.dTo_eq_zero⟩

/-- A spectral sequence is both regular and coregular at `pq` if and only if it stabilizes at `pq`
from some page. -/
theorem isRegularAt_and_isCoregularAt_iff_exists_stabilizesAt (E : SpectralSequence C c r₀)
    (pq : κ) :
    (E.IsRegularAt pq ∧ E.IsCoregularAt pq) ↔ ∃ s, E.StabilizesAt pq s := by
  refine ⟨?_, fun ⟨_, h⟩ ↦ ⟨h.isRegularAt, h.isCoregularAt⟩⟩
  rintro ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, _, h₂⟩⟩
  refine ⟨max s₁ s₂, hs₁.trans (le_max_left s₁ s₂), fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · exact h₁ r ((le_max_left s₁ s₂).trans hr)
  · exact h₂ r ((le_max_right s₁ s₂).trans hr)

end Definitions

section TowerCharacterization

variable (E : SpectralSequence C c r₀)

/-- If `E` stabilizes at `pq` from page `s`, then `Z_r(pq) = Z_s(pq)` for all `r ≥ s`. -/
lemma StabilizesAt.cyclesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (h.le.trans hsr) = E.cyclesSubobject pq s h.le :=
  E.cyclesSubobject_eq_of_dFrom_eq_zero pq h.le hsr fun t hst _ ↦ h.dFrom_eq_zero t hst

/-- If `E` stabilizes at `pq` from page `s`, then `B_r(pq) = B_s(pq)` for all `r ≥ s`. -/
lemma StabilizesAt.boundariesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (h.le.trans hsr) = E.boundariesSubobject pq s h.le :=
  E.boundariesSubobject_eq_of_dTo_eq_zero pq h.le hsr fun t hst _ ↦ h.dTo_eq_zero t hst

/-- **Regularity via the cycle tower.** `E` is regular at `pq` if and only if the cycle tower
`r ↦ Z_r(pq)` is eventually constant. -/
theorem isRegularAt_iff_eventually_cyclesSubobject_eq (pq : κ) :
    E.IsRegularAt pq ↔
      ∃ s, ∃ hs : r₀ ≤ s, ∀ r (hsr : s ≤ r),
        E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, fun r hsr ↦ E.cyclesSubobject_eq_of_dFrom_eq_zero pq hs hsr
      fun t hst _ ↦ h t hst⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, fun r hsr ↦ (E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).1 ?_⟩
    rw [h (r + 1) (Int.le_add_one hsr), h r hsr]

/-- **Coregularity via the boundary tower.** `E` is coregular at `pq` if and only if the boundary
tower `r ↦ B_r(pq)` is eventually constant. -/
theorem isCoregularAt_iff_eventually_boundariesSubobject_eq (pq : κ) :
    E.IsCoregularAt pq ↔
      ∃ s, ∃ hs : r₀ ≤ s, ∀ r (hsr : s ≤ r),
        E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, fun r hsr ↦ E.boundariesSubobject_eq_of_dTo_eq_zero pq hs hsr
      fun t hst _ ↦ h t hst⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, fun r hsr ↦ (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).1 ?_⟩
    rw [h (r + 1) (Int.le_add_one hsr), h r hsr]

/-- `E` stabilizes at `pq` from page `s` if and only if both `Z_r(pq)` and `B_r(pq)` are constant
for `r ≥ s`. -/
theorem stabilizesAt_iff_cyclesSubobject_and_boundariesSubobject_eq (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    E.StabilizesAt pq s ↔
      (∀ r (hsr : s ≤ r), E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs) ∧
      (∀ r (hsr : s ≤ r), E.boundariesSubobject pq r (hs.trans hsr) =
        E.boundariesSubobject pq s hs) := by
  refine ⟨fun h ↦ ⟨h.cyclesSubobject_eq, h.boundariesSubobject_eq⟩, fun ⟨hZ, hB⟩ ↦ ?_⟩
  refine ⟨hs, fun r hsr ↦ ?_, fun r hsr ↦ ?_⟩
  · exact (E.cyclesSubobject_add_one_eq_iff pq r (hs.trans hsr)).1
      (by rw [hZ (r + 1) (Int.le_add_one hsr), hZ r hsr])
  · exact (E.boundariesSubobject_add_one_eq_iff pq r (hs.trans hsr)).1
      (by rw [hB (r + 1) (Int.le_add_one hsr), hB r hsr])

end TowerCharacterization

section StabilizationIso

variable (E : SpectralSequence C c r₀)

/-- The one-step isomorphism `pageXStepIso` agrees with the canonical comparison isomorphism
between the page-`r` and page-`(r + 1)` subquotient presentations. -/
lemma pageXStepIso_eq_isoOfEq (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (hdTo : (E.page r hr).dTo pq = 0) (hdFrom : (E.page r hr).dFrom pq = 0) :
    E.pageXStepIso pq r hr hdTo hdFrom =
      (E.pagePresentation pq r hr).isoOfEq
        (E.pagePresentation pq (r + 1) (Int.le_add_one hr))
        ((E.boundariesSubobject_add_one_eq_iff pq r hr).2 hdTo).symm
        ((E.cyclesSubobject_add_one_eq_iff pq r hr).2 hdFrom).symm := by
  let p := E.pagePresentation pq r hr
  let p' := E.pagePresentation pq (r + 1) (Int.le_add_one hr)
  let sc := (E.page r hr).sc pq
  have hstep : p.mapIso (E.pageXStepIso pq r hr hdTo hdFrom) = p' := by
    have he : E.pageXStepIso pq r hr hdTo hdFrom =
        (E.page r hr).XIsoHomologyOfDEqZero pq hdTo hdFrom ≪≫ E.iso r (r + 1) pq rfl hr :=
      Iso.ext (E.pageXStepIso_hom pq r hr hdTo hdFrom)
    have hsc : sc.homologyPresentation = (TauCeti.SubquotientPresentation.refl sc.X₂).mapIso
        ((E.page r hr).XIsoHomologyOfDEqZero pq hdTo hdFrom) := by
      rw [HomologicalComplex.XIsoHomologyOfDEqZero_eq_shortComplex,
        ← ShortComplex.homologyPresentation_isoOfEq_of_eq_zero sc hdTo hdFrom,
        TauCeti.SubquotientPresentation.mapIso_isoOfEq]
    rw [show p' = p.trans (sc.homologyPresentation.mapIso (E.iso r (r + 1) pq rfl hr)) from
        E.pagePresentation_add_one pq r hr,
      hsc, TauCeti.SubquotientPresentation.mapIso_mapIso, ← he,
      TauCeti.SubquotientPresentation.trans_mapIso,
      show TauCeti.SubquotientPresentation.refl sc.X₂ =
        TauCeti.SubquotientPresentation.refl ((E.page r hr).X pq) from rfl,
      TauCeti.SubquotientPresentation.trans_refl]
  exact p.eq_isoOfEq_of_mapIso_eq hstep _ _

/-- The stabilization isomorphism `pageXIsoOfStabilizesAt` agrees with the canonical comparison
isomorphism `SubquotientPresentation.isoOfEq` between the page-`s` and page-`r` presentations. -/
theorem pageXIsoOfStabilizesAt_eq_isoOfEq {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    (r : ℤ) (hsr : s ≤ r) :
    E.pageXIsoOfStabilizesAt h r hsr =
      (E.pagePresentation pq s h.le).isoOfEq
        (E.pagePresentation pq r (h.le.trans hsr))
        (h.boundariesSubobject_eq r hsr).symm
        (h.cyclesSubobject_eq r hsr).symm := by
  induction r, hsr using Int.leInduction with
  | base =>
    ext
    rw [pageXIsoOfStabilizesAt_self, ← cancel_epi (E.pagePresentation pq s h.le).π,
      TauCeti.SubquotientPresentation.π_isoOfEq_hom, Subobject.ofLE_refl, Category.id_comp,
      Iso.refl_hom, Category.comp_id]
  | succ r hsr ih =>
    rw [E.pageXIsoOfStabilizesAt_add_one h r hsr, ih,
      E.pageXStepIso_eq_isoOfEq pq r (h.le.trans hsr) (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr),
      TauCeti.SubquotientPresentation.isoOfEq_trans]

/-- Compatibility of `pageXIsoOfStabilizesAt` with the subquotient presentation projections. -/
@[reassoc]
lemma π_comp_pageXIsoOfStabilizesAt_hom {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s)
    (r : ℤ) (hsr : s ≤ r) :
    (E.pagePresentation pq s h.le).π ≫ (E.pageXIsoOfStabilizesAt h r hsr).hom =
      Subobject.ofLE (E.cyclesSubobject pq s h.le) (E.cyclesSubobject pq r (h.le.trans hsr))
          (h.cyclesSubobject_eq r hsr).symm.le ≫
        (E.pagePresentation pq r (h.le.trans hsr)).π := by
  rw [pageXIsoOfStabilizesAt_eq_isoOfEq, TauCeti.SubquotientPresentation.π_isoOfEq_hom]

/-- **Composition compatibility.** The stabilization isomorphisms compose transitively. -/
theorem pageXIsoOfStabilizesAt_trans {pq : κ} {s r t : ℤ} (h : E.StabilizesAt pq s)
    (hsr : s ≤ r) (hrt : r ≤ t) :
    E.pageXIsoOfStabilizesAt h r hsr ≪≫ E.pageXIsoOfStabilizesAt (h.mono hsr) t hrt =
      E.pageXIsoOfStabilizesAt h t (hsr.trans hrt) := by
  simp only [pageXIsoOfStabilizesAt_eq_isoOfEq, TauCeti.SubquotientPresentation.isoOfEq_trans]

/-- **Naturality of stabilization isomorphisms.** A morphism `f : E ⟶ E'` between spectral
sequences that both stabilize at `pq` from page `s` commutes with the canonical stabilization
isomorphisms. -/
theorem pageXIsoOfStabilizesAt_hom_naturality {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    (E.pageXIsoOfStabilizesAt h r hsr).hom ≫ (f.hom r (h.le.trans hsr)).f pq =
      (f.hom s h.le).f pq ≫ (E'.pageXIsoOfStabilizesAt h' r hsr).hom := by
  rw [pageXIsoOfStabilizesAt_eq_isoOfEq, pageXIsoOfStabilizesAt_eq_isoOfEq,
    ← f.pagePresentation_map pq r (h.le.trans hsr), ← f.pagePresentation_map pq s h.le]
  exact TauCeti.SubquotientPresentation.isoOfEq_hom_comp_map _ _ _ _ ((f.hom r₀).f pq) _ _ _ _

end StabilizationIso

section IsoInvariance

variable {E E' : SpectralSequence C c r₀}

/-- Stabilization at `pq` from page `s` is invariant under isomorphisms of spectral sequences. -/
theorem stabilizesAt_iff_of_iso (e : E ≅ E') (pq : κ) (s : ℤ) :
    E.StabilizesAt pq s ↔ E'.StabilizesAt pq s := by
  constructor <;> intro h <;>
    refine ⟨h.le, fun r hsr ↦ ?_, fun r hsr ↦ ?_⟩
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq _).1 (h.dFrom_eq_zero r hsr)
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) _ pq).1 (h.dTo_eq_zero r hsr)
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq _).2 (h.dFrom_eq_zero r hsr)
  · exact (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) _ pq).2 (h.dTo_eq_zero r hsr)

/-- Regularity at `pq` is invariant under isomorphisms of spectral sequences. -/
theorem isRegularAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.IsRegularAt pq ↔ E'.IsRegularAt pq := by
  constructor <;> rintro ⟨s, hs, h⟩ <;> refine ⟨s, hs, fun r hsr ↦ ?_⟩
  · exact (page_d_eq_zero_iff_of_iso e r (hs.trans hsr) pq _).1 (h r hsr)
  · exact (page_d_eq_zero_iff_of_iso e r (hs.trans hsr) pq _).2 (h r hsr)

/-- Coregularity at `pq` is invariant under isomorphisms of spectral sequences. -/
theorem isCoregularAt_iff_of_iso (e : E ≅ E') (pq : κ) :
    E.IsCoregularAt pq ↔ E'.IsCoregularAt pq := by
  constructor <;> rintro ⟨s, hs, h⟩ <;> refine ⟨s, hs, fun r hsr ↦ ?_⟩
  · exact (page_d_eq_zero_iff_of_iso e r (hs.trans hsr) _ pq).1 (h r hsr)
  · exact (page_d_eq_zero_iff_of_iso e r (hs.trans hsr) _ pq).2 (h r hsr)

end IsoInvariance

end CategoryTheory.SpectralSequence
