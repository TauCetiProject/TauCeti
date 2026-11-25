/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.BidegreeAssignment
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

/-!
# Bounded spectral sequences and differential vanishing

With respect to a bidegree assignment `A : TauCeti.BidegreeAssignment c r₀`, a spectral sequence
`E : SpectralSequence C c r₀` is:

* **bounded below** (`CategoryTheory.SpectralSequence.IsBoundedBelow`) if in each total degree `n`
  the first page vanishes in all sufficiently high filtration degrees `fil pq ≥ β`;
* **bounded above** (`CategoryTheory.SpectralSequence.IsBoundedAbove`) if in each total degree `n`
  the first page vanishes in all sufficiently low filtration degrees `fil pq ≤ α`;
* **bounded** (`CategoryTheory.SpectralSequence.IsBounded`) if it is both bounded below and bounded
  above, equivalently if each total degree has only finitely many nonzero first-page positions
  (`CategoryTheory.SpectralSequence.isBounded_iff_finite_nonZero`).

Because differentials of page `r ≥ r₀` raise total degree by `1` and filtration degree by
`r - A.e`, and zero objects persist to later pages
(`CategoryTheory.SpectralSequence.isZero_page_X_of_le`):

* a bound below `β` forces the leaving differential `(E.page r hr).dFrom pq` to vanish for every
  `r ≥ β (deg pq + 1) - fil pq + A.e`
  (`CategoryTheory.SpectralSequence.page_dFrom_eq_zero_of_boundedBelow`);
* a bound above `α` forces the entering differential `(E.page r hr).dTo pq` to vanish for every
  `r ≥ fil pq - α (deg pq - 1) + A.e`
  (`CategoryTheory.SpectralSequence.page_dTo_eq_zero_of_boundedAbove`);
* together, they yield canonical survival isomorphisms `(E.page r').X pq ≅ (E.page s).X pq` for
  all `r' ≥ s` (`CategoryTheory.SpectralSequence.pageXIsoOfBounded`).

We also derive the first-quadrant stabilization bound `r > max p (q + 1)`
(`CategoryTheory.SpectralSequence.pageXIsoOfFirstQuadrant`), automatic boundedness for
`CohomologicalSpectralSequenceNat` and `CohomologicalSpectralSequenceFin`, stabilization from
finiteness in the adjacent total degrees `n - 1` and `n + 1`, and global degeneration of a
finitely supported page (`CategoryTheory.SpectralSequence.page_d_eq_zero_of_finset_support`).

## References

* Stacks Project, Tag 0BDU (Definition 24.7: bounded below, bounded above, bounded spectral
  sequences) and Tag 0BDV (Lemma 24.8: finiteness in each total degree, regularity, and
  coregularity).
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ}
  {r₀ : ℤ}

/-! ### Boundedness predicates -/

/-- A spectral sequence `E` is **bounded below** with respect to a bidegree assignment `A` if in
each total degree `n` there is an integer `β` such that the first page vanishes at every position
of total degree `n` and filtration degree at least `β`. -/
def IsBoundedBelow (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) : Prop :=
  ∀ n : ℤ, ∃ β : ℤ,
    ∀ pq : κ, A.deg pq = n → β ≤ A.fil pq → IsZero ((E.page r₀ le_rfl).X pq)

/-- Characterization of `IsBoundedBelow` as a per-total-degree filtration upper bound. -/
lemma isBoundedBelow_iff (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) :
    E.IsBoundedBelow A ↔
      ∀ n : ℤ, ∃ β : ℤ,
        ∀ pq : κ, A.deg pq = n → β ≤ A.fil pq → IsZero ((E.page r₀ le_rfl).X pq) := Iff.rfl

/-- A spectral sequence `E` is **bounded above** with respect to a bidegree assignment `A` if in
each total degree `n` there is an integer `α` such that the first page vanishes at every position
of total degree `n` and filtration degree at most `α`. -/
def IsBoundedAbove (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) : Prop :=
  ∀ n : ℤ, ∃ α : ℤ,
    ∀ pq : κ, A.deg pq = n → A.fil pq ≤ α → IsZero ((E.page r₀ le_rfl).X pq)

/-- Characterization of `IsBoundedAbove` as a per-total-degree filtration lower bound. -/
lemma isBoundedAbove_iff (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) :
    E.IsBoundedAbove A ↔
      ∀ n : ℤ, ∃ α : ℤ,
        ∀ pq : κ, A.deg pq = n → A.fil pq ≤ α → IsZero ((E.page r₀ le_rfl).X pq) := Iff.rfl

/-- A spectral sequence `E` is **bounded** with respect to a bidegree assignment `A` if it is both
bounded below and bounded above. -/
def IsBounded (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) : Prop :=
  E.IsBoundedBelow A ∧ E.IsBoundedAbove A

/-- Characterization of `IsBounded` as the conjunction of `IsBoundedBelow` and
`IsBoundedAbove`. -/
lemma isBounded_iff (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀) :
    E.IsBounded A ↔ E.IsBoundedBelow A ∧ E.IsBoundedAbove A := Iff.rfl

/-- A bounded spectral sequence is bounded below. -/
lemma IsBounded.isBoundedBelow {E : SpectralSequence C c r₀} {A : BidegreeAssignment c r₀}
    (h : E.IsBounded A) : E.IsBoundedBelow A :=
  ((E.isBounded_iff A).1 h).1

/-- A bounded spectral sequence is bounded above. -/
lemma IsBounded.isBoundedAbove {E : SpectralSequence C c r₀} {A : BidegreeAssignment c r₀}
    (h : E.IsBounded A) : E.IsBoundedAbove A :=
  ((E.isBounded_iff A).1 h).2

/-- `E` is bounded below if and only if there is a function `β : ℤ → ℤ` such that the first page
vanishes at every position `pq` with `β (A.deg pq) ≤ A.fil pq`. -/
lemma isBoundedBelow_iff_exists_fun (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) :
    E.IsBoundedBelow A ↔
      ∃ β : ℤ → ℤ,
        ∀ pq : κ, β (A.deg pq) ≤ A.fil pq → IsZero ((E.page r₀ le_rfl).X pq) := by
  rw [isBoundedBelow_iff]
  constructor
  · intro h
    choose β hβ using h
    exact ⟨β, fun pq hpq ↦ hβ (A.deg pq) pq rfl hpq⟩
  · rintro ⟨β, hβ⟩ n
    exact ⟨β n, fun pq hdeg hfil ↦ hβ pq (hdeg ▸ hfil)⟩

/-- `E` is bounded above if and only if there is a function `α : ℤ → ℤ` such that the first page
vanishes at every position `pq` with `A.fil pq ≤ α (A.deg pq)`. -/
lemma isBoundedAbove_iff_exists_fun (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) :
    E.IsBoundedAbove A ↔
      ∃ α : ℤ → ℤ,
        ∀ pq : κ, A.fil pq ≤ α (A.deg pq) → IsZero ((E.page r₀ le_rfl).X pq) := by
  rw [isBoundedAbove_iff]
  constructor
  · intro h
    choose α hα using h
    exact ⟨α, fun pq hpq ↦ hα (A.deg pq) pq rfl hpq⟩
  · rintro ⟨α, hα⟩ n
    exact ⟨α n, fun pq hdeg hfil ↦ hα pq (hdeg ▸ hfil)⟩

/-- Boundedness below is preserved under isomorphisms of spectral sequences. -/
lemma isBoundedBelow_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    {A : BidegreeAssignment c r₀} (h : E.IsBoundedBelow A) : E'.IsBoundedBelow A := by
  rw [isBoundedBelow_iff] at h ⊢
  intro n
  obtain ⟨β, hβ⟩ := h n
  exact ⟨β, fun pq hdeg hfil ↦
    (hβ pq hdeg hfil).of_iso
      (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀).mapIso iso) pq).symm⟩

/-- Isomorphic spectral sequences are simultaneously bounded below. -/
lemma isBoundedBelow_iff_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    (A : BidegreeAssignment c r₀) : E.IsBoundedBelow A ↔ E'.IsBoundedBelow A :=
  ⟨isBoundedBelow_of_iso iso, isBoundedBelow_of_iso iso.symm⟩

/-- Boundedness above is preserved under isomorphisms of spectral sequences. -/
lemma isBoundedAbove_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    {A : BidegreeAssignment c r₀} (h : E.IsBoundedAbove A) : E'.IsBoundedAbove A := by
  rw [isBoundedAbove_iff] at h ⊢
  intro n
  obtain ⟨α, hα⟩ := h n
  exact ⟨α, fun pq hdeg hfil ↦
    (hα pq hdeg hfil).of_iso
      (HomologicalComplex.Hom.isoApp ((pageFunctor C c r₀ r₀).mapIso iso) pq).symm⟩

/-- Isomorphic spectral sequences are simultaneously bounded above. -/
lemma isBoundedAbove_iff_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    (A : BidegreeAssignment c r₀) : E.IsBoundedAbove A ↔ E'.IsBoundedAbove A :=
  ⟨isBoundedAbove_of_iso iso, isBoundedAbove_of_iso iso.symm⟩

/-- Boundedness is preserved under isomorphisms of spectral sequences. -/
lemma isBounded_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    {A : BidegreeAssignment c r₀} (h : E.IsBounded A) : E'.IsBounded A :=
  (E'.isBounded_iff A).2 ⟨isBoundedBelow_of_iso iso h.isBoundedBelow,
    isBoundedAbove_of_iso iso h.isBoundedAbove⟩

/-- Isomorphic spectral sequences are simultaneously bounded. -/
lemma isBounded_iff_of_iso {E E' : SpectralSequence C c r₀} (iso : E ≅ E')
    (A : BidegreeAssignment c r₀) : E.IsBounded A ↔ E'.IsBounded A :=
  ⟨isBounded_of_iso iso, isBounded_of_iso iso.symm⟩

/-- A spectral sequence whose first page vanishes at every position is bounded. -/
lemma isBounded_of_isZero (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (h : ∀ pq : κ, IsZero ((E.page r₀ le_rfl).X pq)) : E.IsBounded A := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  exact ⟨fun _ ↦ ⟨0, fun pq _ _ ↦ h pq⟩, fun _ ↦ ⟨0, fun pq _ _ ↦ h pq⟩⟩

/-- If total degree `n` has only finitely many nonzero first-page positions, then there is an upper
bound `β` on their filtration degrees. -/
lemma exists_bound_below_of_finite (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (n : ℤ)
    (hfin : Set.Finite {pq : κ | A.deg pq = n ∧ ¬ IsZero ((E.page r₀ le_rfl).X pq)}) :
    ∃ β : ℤ,
      ∀ pq : κ, A.deg pq = n → β ≤ A.fil pq → IsZero ((E.page r₀ le_rfl).X pq) := by
  let s := hfin.toFinset
  by_cases hs : s.Nonempty
  · refine ⟨(s.image A.fil).max' (hs.image _) + 1, fun pq hdeg hfil ↦ ?_⟩
    by_contra hnz
    have hmem : pq ∈ s := hfin.mem_toFinset.2 ⟨hdeg, hnz⟩
    have hle : A.fil pq ≤ (s.image A.fil).max' (hs.image _) :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hmem)
    lia
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    refine ⟨0, fun pq hdeg _ ↦ ?_⟩
    by_contra hnz
    have : pq ∈ s := hfin.mem_toFinset.2 ⟨hdeg, hnz⟩
    simp [hs] at this

/-- If total degree `n` has only finitely many nonzero first-page positions, then there is a lower
bound `α` on their filtration degrees. -/
lemma exists_bound_above_of_finite (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (n : ℤ)
    (hfin : Set.Finite {pq : κ | A.deg pq = n ∧ ¬ IsZero ((E.page r₀ le_rfl).X pq)}) :
    ∃ α : ℤ,
      ∀ pq : κ, A.deg pq = n → A.fil pq ≤ α → IsZero ((E.page r₀ le_rfl).X pq) := by
  let s := hfin.toFinset
  by_cases hs : s.Nonempty
  · refine ⟨(s.image A.fil).min' (hs.image _) - 1, fun pq hdeg hfil ↦ ?_⟩
    by_contra hnz
    have hmem : pq ∈ s := hfin.mem_toFinset.2 ⟨hdeg, hnz⟩
    have hle : (s.image A.fil).min' (hs.image _) ≤ A.fil pq :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmem)
    lia
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    refine ⟨0, fun pq hdeg _ ↦ ?_⟩
    by_contra hnz
    have : pq ∈ s := hfin.mem_toFinset.2 ⟨hdeg, hnz⟩
    simp [hs] at this

/-- **Boundedness equals finiteness in each total degree** (Stacks Project, Tag 0BDV,
Lemma 24.8 (3)). A spectral sequence is bounded with respect to `A` if and only if each total
degree contains only finitely many positions where the first page is nonzero. -/
theorem isBounded_iff_finite_nonZero (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) :
    E.IsBounded A ↔
      ∀ n : ℤ,
        Set.Finite {pq : κ | A.deg pq = n ∧ ¬ IsZero ((E.page r₀ le_rfl).X pq)} := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  constructor
  · rintro ⟨hbel, habv⟩ n
    obtain ⟨β, hβ⟩ := hbel n
    obtain ⟨α, hα⟩ := habv n
    refine Set.Finite.of_finite_image (f := A.fil) ?_ ?_
    · refine (Finset.Ioo α β).finite_toSet.subset ?_
      rintro _ ⟨pq, ⟨hdeg, hnz⟩, rfl⟩
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      exact ⟨not_le.1 fun h ↦ hnz (hα pq hdeg h), not_le.1 fun h ↦ hnz (hβ pq hdeg h)⟩
    · intro pq₁ h₁ pq₂ h₂ hfil
      exact A.injective (Prod.ext hfil (h₁.1.trans h₂.1.symm))
  · intro hfin
    exact ⟨fun n ↦ E.exists_bound_below_of_finite A n (hfin n),
      fun n ↦ E.exists_bound_above_of_finite A n (hfin n)⟩

/-! ### Vanishing of leaving and entering differentials -/

/-- If `E` is bounded below with respect to `A`, then at every position `pq` all sufficiently late
leaving differentials vanish. -/
theorem exists_dFrom_eq_zero_of_isBoundedBelow {E : SpectralSequence C c r₀}
    {A : BidegreeAssignment c r₀} (h : E.IsBoundedBelow A) (pq : κ) :
    ∃ s : ℤ, r₀ ≤ s ∧
      ∀ (r : ℤ) (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dFrom pq = 0 := by
  obtain ⟨β, hβ⟩ := (E.isBoundedBelow_iff A).1 h (A.deg pq + 1)
  refine ⟨max r₀ (β - A.fil pq + A.e), le_max_left _ _, fun r hr hsr ↦ ?_⟩
  exact E.page_dFrom_eq_zero_of_isZero_of_le_fil A le_rfl pq β hβ r hr hr
    ((le_max_right _ _).trans hsr)

/-- If `E` is bounded above with respect to `A`, then at every position `pq` all sufficiently late
entering differentials vanish. -/
theorem exists_dTo_eq_zero_of_isBoundedAbove {E : SpectralSequence C c r₀}
    {A : BidegreeAssignment c r₀} (h : E.IsBoundedAbove A) (pq : κ) :
    ∃ s : ℤ, r₀ ≤ s ∧
      ∀ (r : ℤ) (hr : r₀ ≤ r), s ≤ r → (E.page r hr).dTo pq = 0 := by
  obtain ⟨α, hα⟩ := (E.isBoundedAbove_iff A).1 h (A.deg pq - 1)
  refine ⟨max r₀ (A.fil pq - α + A.e), le_max_left _ _, fun r hr hsr ↦ ?_⟩
  exact E.page_dTo_eq_zero_of_isZero_of_fil_le A le_rfl pq α hα r hr hr
    ((le_max_right _ _).trans hsr)

/-! ### Survival isomorphisms on later pages -/

/-- **Survival of bounded positions.** Given a lower vanishing bound `β` in degree `A.deg pq + 1`
and an upper vanishing bound `α` in degree `A.deg pq - 1` on the first page, once `s ≥ r₀`
satisfies both `β - A.fil pq + A.e ≤ s` and `A.fil pq - α + A.e ≤ s`, the object at `pq`
survives unchanged to every later page `r' ≥ s`. -/
noncomputable def pageXIsoOfBounded (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (pq : κ) (β α : ℤ)
    (hβ : ∀ pq' : κ,
      A.deg pq' = A.deg pq + 1 → β ≤ A.fil pq' → IsZero ((E.page r₀ le_rfl).X pq'))
    (hα : ∀ pq' : κ,
      A.deg pq' = A.deg pq - 1 → A.fil pq' ≤ α → IsZero ((E.page r₀ le_rfl).X pq'))
    (s : ℤ) (hs : r₀ ≤ s)
    (hsβ : β - A.fil pq + A.e ≤ s) (hsα : A.fil pq - α + A.e ≤ s)
    (r' : ℤ) (hsr' : s ≤ r') :
    (E.page r' (hs.trans hsr')).X pq ≅ (E.page s hs).X pq :=
  E.pageXIsoOfLEOfIsZero hs (fun t hst pq' hrel ↦ by
    refine E.isZero_page_X_of_le le_rfl ?_ s hs
    rcases hrel with hrel | hrel
    · have hdeg := A.deg_rel t (hs.trans hst) pq pq' hrel
      have hfil := A.fil_rel t (hs.trans hst) pq pq' hrel
      exact hβ pq' hdeg (by lia)
    · have hdeg := A.deg_rel t (hs.trans hst) pq' pq hrel
      have hfil := A.fil_rel t (hs.trans hst) pq' pq hrel
      exact hα pq' (by lia) (by lia)) r' hsr'

/-- `pageXIsoOfBounded` coincides with `pageXIsoOfLEOfIsZero`. -/
lemma pageXIsoOfBounded_eq_pageXIsoOfLEOfIsZero (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) (pq : κ) (β α : ℤ)
    (hβ : ∀ pq' : κ,
      A.deg pq' = A.deg pq + 1 → β ≤ A.fil pq' → IsZero ((E.page r₀ le_rfl).X pq'))
    (hα : ∀ pq' : κ,
      A.deg pq' = A.deg pq - 1 → A.fil pq' ≤ α → IsZero ((E.page r₀ le_rfl).X pq'))
    (s : ℤ) (hs : r₀ ≤ s)
    (hsβ : β - A.fil pq + A.e ≤ s) (hsα : A.fil pq - α + A.e ≤ s)
    (h : ∀ t, s ≤ t → ∀ pq', (c t).Rel pq pq' ∨ (c t).Rel pq' pq → IsZero ((E.page s hs).X pq'))
    (r' : ℤ) (hsr' : s ≤ r') :
    E.pageXIsoOfBounded A pq β α hβ hα s hs hsβ hsα r' hsr' =
      E.pageXIsoOfLEOfIsZero hs h r' hsr' := by
  unfold pageXIsoOfBounded
  rfl

/-- On page `s` itself, `pageXIsoOfBounded` is the identity isomorphism. -/
@[simp]
lemma pageXIsoOfBounded_self (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (pq : κ) (β α : ℤ)
    (hβ : ∀ pq' : κ,
      A.deg pq' = A.deg pq + 1 → β ≤ A.fil pq' → IsZero ((E.page r₀ le_rfl).X pq'))
    (hα : ∀ pq' : κ,
      A.deg pq' = A.deg pq - 1 → A.fil pq' ≤ α → IsZero ((E.page r₀ le_rfl).X pq'))
    (s : ℤ) (hs : r₀ ≤ s)
    (hsβ : β - A.fil pq + A.e ≤ s) (hsα : A.fil pq - α + A.e ≤ s) :
    E.pageXIsoOfBounded A pq β α hβ hα s hs hsβ hsα s le_rfl = Iso.refl _ :=
  E.pageXIsoOfLEOfIsZero_self hs _

/-- From page `r'` to page `r' + 1`, `pageXIsoOfBounded` composes with the identification of page
`r' + 1` with the homology of page `r'` and then with `pageXIsoOfBounded` at `r'`. -/
lemma pageXIsoOfBounded_add_one (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (pq : κ) (β α : ℤ)
    (hβ : ∀ pq' : κ,
      A.deg pq' = A.deg pq + 1 → β ≤ A.fil pq' → IsZero ((E.page r₀ le_rfl).X pq'))
    (hα : ∀ pq' : κ,
      A.deg pq' = A.deg pq - 1 → A.fil pq' ≤ α → IsZero ((E.page r₀ le_rfl).X pq'))
    (s : ℤ) (hs : r₀ ≤ s)
    (hsβ : β - A.fil pq + A.e ≤ s) (hsα : A.fil pq - α + A.e ≤ s)
    (r' : ℤ) (hsr' : s ≤ r') :
    E.pageXIsoOfBounded A pq β α hβ hα s hs hsβ hsα (r' + 1) (Int.le_add_one hsr') =
      (E.iso r' (r' + 1) pq rfl (hs.trans hsr')).symm ≪≫
        ((E.page r' (hs.trans hsr')).isoHomologyπ _ pq rfl
          (E.page_dTo_eq_zero_of_isZero_of_fil_le A le_rfl pq α hα r' (hs.trans hsr')
            (hs.trans hsr') (by lia))).symm ≪≫
        (E.page r' (hs.trans hsr')).iCyclesIso pq _ rfl
          (E.page_dFrom_eq_zero_of_isZero_of_le_fil A le_rfl pq β hβ r' (hs.trans hsr')
            (hs.trans hsr') (by lia)) ≪≫
        E.pageXIsoOfBounded A pq β α hβ hα s hs hsβ hsα r' hsr' :=
  E.pageXIsoOfLEOfIsZero_add_one hs _ r' hsr'

/-- If only finitely many positions in the adjacent total degrees `A.deg pq + 1` and
`A.deg pq - 1` are nonzero on the first page, then `pq` stabilizes at some page `s ≥ r₀`: its
object on every later page `r' ≥ s` is isomorphic to its object on page `s`. -/
theorem exists_pageXIso_of_finite (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (pq : κ)
    (hfin_succ : Set.Finite
      {pq' : κ | A.deg pq' = A.deg pq + 1 ∧ ¬ IsZero ((E.page r₀ le_rfl).X pq')})
    (hfin_pred : Set.Finite
      {pq' : κ | A.deg pq' = A.deg pq - 1 ∧ ¬ IsZero ((E.page r₀ le_rfl).X pq')}) :
    ∃ s : ℤ, ∃ hs : r₀ ≤ s,
      ∀ (r' : ℤ) (hsr' : s ≤ r'),
        Nonempty ((E.page r' (hs.trans hsr')).X pq ≅ (E.page s hs).X pq) := by
  obtain ⟨β, hβ⟩ := E.exists_bound_below_of_finite A (A.deg pq + 1) hfin_succ
  obtain ⟨α, hα⟩ := E.exists_bound_above_of_finite A (A.deg pq - 1) hfin_pred
  refine ⟨max r₀ (max (β - A.fil pq + A.e) (A.fil pq - α + A.e)), le_max_left _ _,
    fun r' hsr' ↦ ?_⟩
  exact ⟨E.pageXIsoOfBounded A pq β α hβ hα _ (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    r' hsr'⟩

/-- If `E` is bounded with respect to `A`, then every position `pq` stabilizes at some page
`s ≥ r₀`. -/
theorem exists_pageXIso_of_isBounded {E : SpectralSequence C c r₀}
    {A : BidegreeAssignment c r₀} (h : E.IsBounded A) (pq : κ) :
    ∃ s : ℤ, ∃ hs : r₀ ≤ s,
      ∀ (r' : ℤ) (hsr' : s ≤ r'),
        Nonempty ((E.page r' (hs.trans hsr')).X pq ≅ (E.page s hs).X pq) :=
  E.exists_pageXIso_of_finite A pq
    ((E.isBounded_iff_finite_nonZero A).1 h (A.deg pq + 1))
    ((E.isBounded_iff_finite_nonZero A).1 h (A.deg pq - 1))

/-! ### First-quadrant and finite-row spectral sequences -/

/-- A cohomological spectral sequence whose first page vanishes outside the first quadrant
`p ≥ 0, q ≥ 0` is bounded with respect to `BidegreeAssignment.cohomological r₀`. -/
lemma isBounded_of_firstQuadrant (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q))) :
    E.IsBounded (BidegreeAssignment.cohomological r₀) := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  refine ⟨fun n ↦ ⟨n + 1, fun ⟨p, q⟩ hdeg hfil ↦ ?_⟩,
    fun _ ↦ ⟨-1, fun ⟨p, q⟩ _ hfil ↦ ?_⟩⟩
  · simp only [BidegreeAssignment.cohomological_deg,
      BidegreeAssignment.cohomological_fil] at hdeg hfil
    exact hE p q (Or.inr (by lia))
  · simp only [BidegreeAssignment.cohomological_fil] at hfil
    exact hE p q (Or.inl (by lia))

/-- Every first-quadrant cohomological spectral sequence indexed by `ℕ × ℕ` is bounded with
respect to `BidegreeAssignment.cohomologicalNat r₀`. -/
lemma isBounded_cohomologicalNat (E : CohomologicalSpectralSequenceNat C r₀) :
    E.IsBounded (BidegreeAssignment.cohomologicalNat r₀) := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  refine ⟨fun n ↦ ⟨n + 1, fun ⟨p, q⟩ hdeg hfil ↦ ?_⟩,
    fun _ ↦ ⟨-1, fun ⟨p, q⟩ _ hfil ↦ ?_⟩⟩
  · simp only [BidegreeAssignment.cohomologicalNat_deg,
      BidegreeAssignment.cohomologicalNat_fil] at hdeg hfil
    lia
  · simp only [BidegreeAssignment.cohomologicalNat_fil] at hfil
    lia

/-- Every cohomological spectral sequence on `l` rows (`ℤ × Fin l`) is bounded with respect to
`BidegreeAssignment.cohomologicalFin l r₀`. -/
lemma isBounded_cohomologicalFin {l : ℕ} (E : CohomologicalSpectralSequenceFin C l r₀) :
    E.IsBounded (BidegreeAssignment.cohomologicalFin l r₀) := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  refine ⟨fun n ↦ ⟨n + 1, fun ⟨p, ⟨q, hq⟩⟩ hdeg hfil ↦ ?_⟩,
    fun n ↦ ⟨n - (l : ℤ), fun ⟨p, ⟨q, hq⟩⟩ hdeg hfil ↦ ?_⟩⟩
  · simp only [BidegreeAssignment.cohomologicalFin_deg,
      BidegreeAssignment.cohomologicalFin_fil] at hdeg hfil
    lia
  · simp only [BidegreeAssignment.cohomologicalFin_deg,
      BidegreeAssignment.cohomologicalFin_fil] at hdeg hfil
    lia

/-- Every first-quadrant homological spectral sequence indexed by `ℕ × ℕ` is bounded with respect
to `BidegreeAssignment.homologicalNat r₀`. -/
lemma isBounded_homologicalNat
    (E : SpectralSequence C (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) r₀) :
    E.IsBounded (BidegreeAssignment.homologicalNat r₀) := by
  rw [isBounded_iff, isBoundedBelow_iff, isBoundedAbove_iff]
  refine ⟨fun _ ↦ ⟨1, fun ⟨p, q⟩ _ hfil ↦ ?_⟩,
    fun n ↦ ⟨n - 1, fun ⟨p, q⟩ hdeg hfil ↦ ?_⟩⟩
  · simp only [BidegreeAssignment.homologicalNat_fil] at hfil
    lia
  · simp only [BidegreeAssignment.homologicalNat_deg,
      BidegreeAssignment.homologicalNat_fil] at hdeg hfil
    lia

/-- In a first-quadrant cohomological spectral sequence, the differential leaving `(p, q)` on
page `r ≥ r₀` vanishes whenever `q + 1 < r`. -/
lemma dFrom_eq_zero_of_firstQuadrant (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q r : ℤ) (hr : r₀ ≤ r) (hqr : q + 1 < r) :
    (E.page r hr).dFrom (p, q) = 0 :=
  E.page_dFrom_eq_zero_of_boundedBelow (BidegreeAssignment.cohomological r₀) (fun n ↦ n + 1)
    (fun ⟨a, b⟩ h ↦ hE a b (Or.inr (by simp at h; lia))) (p, q) r hr (by simp; lia)

/-- In a first-quadrant cohomological spectral sequence, the differential entering `(p, q)` on
page `r ≥ r₀` vanishes whenever `p < r`. -/
lemma dTo_eq_zero_of_firstQuadrant (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q r : ℤ) (hr : r₀ ≤ r) (hpr : p < r) :
    (E.page r hr).dTo (p, q) = 0 :=
  E.page_dTo_eq_zero_of_boundedAbove (BidegreeAssignment.cohomological r₀) (fun _ ↦ -1)
    (fun ⟨a, b⟩ h ↦ hE a b (Or.inl (by simp at h; lia))) (p, q) r hr (by simp; lia)

/-- **First-quadrant stabilization.** In a first-quadrant cohomological spectral sequence, once
`s ≥ r₀` satisfies `max p (q + 1) < s`, the object at `(p, q)` survives unchanged to every
later page `r' ≥ s`. -/
noncomputable def pageXIsoOfFirstQuadrant (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q s : ℤ) (hs : r₀ ≤ s) (hspq : max p (q + 1) < s) (r' : ℤ) (hsr' : s ≤ r') :
    (E.page r' (hs.trans hsr')).X (p, q) ≅ (E.page s hs).X (p, q) :=
  E.pageXIsoOfBounded (BidegreeAssignment.cohomological r₀) (p, q) (p + q + 2) (-1)
    (fun ⟨a, b⟩ hdeg hfil ↦ by
      simp only [BidegreeAssignment.cohomological_deg, BidegreeAssignment.cohomological_fil]
        at hdeg hfil
      exact hE a b (Or.inr (by lia)))
    (fun ⟨a, b⟩ _ hfil ↦ by
      simp only [BidegreeAssignment.cohomological_fil] at hfil
      exact hE a b (Or.inl (by lia)))
    s hs (by simp; lia) (by simp; lia) r' hsr'

/-- `pageXIsoOfFirstQuadrant` coincides with `pageXIsoOfLEOfIsZero`. -/
lemma pageXIsoOfFirstQuadrant_eq_pageXIsoOfLEOfIsZero (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q s : ℤ) (hs : r₀ ≤ s) (hspq : max p (q + 1) < s)
    (h : ∀ t, s ≤ t → ∀ pq',
      (ComplexShape.up' (⟨t, 1 - t⟩ : ℤ × ℤ)).Rel (p, q) pq' ∨
        (ComplexShape.up' (⟨t, 1 - t⟩ : ℤ × ℤ)).Rel pq' (p, q) →
      IsZero ((E.page s hs).X pq'))
    (r' : ℤ) (hsr' : s ≤ r') :
    E.pageXIsoOfFirstQuadrant hE p q s hs hspq r' hsr' =
      E.pageXIsoOfLEOfIsZero hs h r' hsr' := by
  unfold pageXIsoOfFirstQuadrant pageXIsoOfBounded
  rfl

/-- On page `s` itself, `pageXIsoOfFirstQuadrant` is the identity isomorphism. -/
@[simp]
lemma pageXIsoOfFirstQuadrant_self (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q s : ℤ) (hs : r₀ ≤ s) (hspq : max p (q + 1) < s) :
    E.pageXIsoOfFirstQuadrant hE p q s hs hspq s le_rfl = Iso.refl _ :=
  E.pageXIsoOfBounded_self _ _ _ _ _ _ s hs _ _

/-- From page `r'` to page `r' + 1`, `pageXIsoOfFirstQuadrant` composes with the identification of
page `r' + 1` with the homology of page `r'` and then with `pageXIsoOfFirstQuadrant` at `r'`. -/
lemma pageXIsoOfFirstQuadrant_add_one (E : CohomologicalSpectralSequence C r₀)
    (hE : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page r₀ le_rfl).X (p, q)))
    (p q s : ℤ) (hs : r₀ ≤ s) (hspq : max p (q + 1) < s) (r' : ℤ) (hsr' : s ≤ r') :
    E.pageXIsoOfFirstQuadrant hE p q s hs hspq (r' + 1) (Int.le_add_one hsr') =
      (E.iso r' (r' + 1) (p, q) rfl (hs.trans hsr')).symm ≪≫
        ((E.page r' (hs.trans hsr')).isoHomologyπ _ (p, q) rfl
          (E.dTo_eq_zero_of_firstQuadrant hE p q r' (hs.trans hsr') (by lia))).symm ≪≫
        (E.page r' (hs.trans hsr')).iCyclesIso (p, q) _ rfl
          (E.dFrom_eq_zero_of_firstQuadrant hE p q r' (hs.trans hsr') (by lia)) ≪≫
        E.pageXIsoOfFirstQuadrant hE p q s hs hspq r' hsr' :=
  E.pageXIsoOfBounded_add_one _ _ _ _ _ _ s hs _ _ r' hsr'

/-! ### Degeneration of a finitely supported page -/

/-- **Degeneration from finite support on a page.** Suppose page `r` vanishes outside a finite set
`s` whose filtration degrees lie in `[a, b]`. Then every differential on every page `r' ≥ r`
with `b - a + A.e < r'` vanishes. -/
theorem page_d_eq_zero_of_finset_support (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (a b : ℤ) (hf : ∀ pq ∈ s, a ≤ A.fil pq ∧ A.fil pq ≤ b)
    (r' : ℤ) (hrr' : r ≤ r') (hgt : b - a + A.e < r') (pq pq' : κ) :
    (E.page r' (hr.trans hrr')).d pq pq' = 0 := by
  by_cases hrel : (c r').Rel pq pq'
  · by_cases hmem : pq ∈ s
    · have hfil := A.fil_rel r' (hr.trans hrr') pq pq' hrel
      have hbounds := hf pq hmem
      have hnot : pq' ∉ s := fun hmem' ↦ by
        have := (hf pq' hmem').2
        lia
      exact E.page_d_eq_zero_of_le hr (Or.inr (hs pq' hnot)) r' hrr'
    · exact E.page_d_eq_zero_of_le hr (Or.inl (hs pq hmem)) r' hrr'
  · exact (E.page r' (hr.trans hrr')).shape pq pq' hrel

/-- If page `r` has only finitely many nonzero positions, then `E` degenerates from some page
`R ≥ r` on: every differential on every page `r' ≥ R` vanishes. -/
theorem exists_page_d_eq_zero_of_finset_support (E : SpectralSequence C c r₀)
    (A : BidegreeAssignment c r₀) (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq)) :
    ∃ R : ℤ, r ≤ R ∧ ∀ (r' : ℤ) (hr' : r₀ ≤ r'), R ≤ r' → ∀ pq pq' : κ,
      (E.page r' hr').d pq pq' = 0 := by
  by_cases hne : s.Nonempty
  · let a := (s.image A.fil).min' (hne.image _)
    let b := (s.image A.fil).max' (hne.image _)
    refine ⟨max r (b - a + A.e + 1), le_max_left _ _, fun r' _ hRr' pq pq' ↦ ?_⟩
    exact E.page_d_eq_zero_of_finset_support A r hr s hs a b
      (fun pq hpq ↦ ⟨Finset.min'_le _ _ (Finset.mem_image_of_mem _ hpq),
        Finset.le_max' _ _ (Finset.mem_image_of_mem _ hpq)⟩)
      r' ((le_max_left _ _).trans hRr') (by lia) pq pq'
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine ⟨r, le_rfl, fun r' _ hrr' pq pq' ↦ ?_⟩
    exact E.page_d_eq_zero_of_le hr (Or.inl (hs pq (by simp [hne]))) r' hrr'

end CategoryTheory.SpectralSequence
