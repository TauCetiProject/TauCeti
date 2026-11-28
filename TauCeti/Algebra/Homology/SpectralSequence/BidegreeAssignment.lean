/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

/-!
# Bidegree assignments and bounded spectral sequences

The positions of the pages of a spectral sequence `E : SpectralSequence C c r₀` form an arbitrary
type `κ`: `ℤ × ℤ` for Mathlib's cohomological spectral sequences, `ℕ × ℕ` for first-quadrant ones,
`ℤ × Fin l` for those lying on finitely many rows. Boundedness, convergence and Euler
characteristics are nevertheless phrased in terms of two integers attached to each position: its
*filtration degree* and its *total degree*. A **bidegree assignment**
(`TauCeti.BidegreeAssignment c r₀`) records them, as functions `fil` and `deg` on `κ` which
together determine a position, along with an integer `e`, the *page offset*, such that every
differential of the page `r ≥ r₀` raises `deg` by `1` and `fil` by `r - e`. It depends only on the
complex shapes `c r`, so one assignment serves every spectral sequence of that shape, in
particular every spectral sequence isomorphic to a given one.

The standard assignments are:

* `TauCeti.BidegreeAssignment.cohomological`, `TauCeti.BidegreeAssignment.cohomologicalNat` and
  `TauCeti.BidegreeAssignment.cohomologicalFin`: `(p, q) ↦ (p, p + q)` with `e = 0` for the
  cohomological shapes, whose differential on page `r` has bidegree `(r, 1 - r)`;
* `TauCeti.BidegreeAssignment.homological` and `TauCeti.BidegreeAssignment.homologicalNat`:
  `(p, q) ↦ (-p, -p - q)` with `e = 0` for the homological shapes, whose differential on page `r`
  has bidegree `(-r, r - 1)`;
* `TauCeti.BidegreeAssignment.decreasingFiltration`: `(a, b) ↦ (-b - 1, a + b)` with `e = 1` for
  the cohomological shapes, the filtration degree of the spectral sequence of a filtered complex
  in the native positions of Mathlib's recipe `coreE₂Cohomological`, where the classical object
  `E_r^{p,q}` of a decreasing filtration sits on page `r + 1` at `(2p + q + 1, -p - 1)`.

An assignment pulls back along a shift of the pages and an injective map of positions carrying
the shapes into each other (`TauCeti.BidegreeAssignment.comap`), as in
`CategoryTheory.SpectralSequence.reindex`; pulling back is functorial
(`TauCeti.BidegreeAssignment.comap_zero_id`, `TauCeti.BidegreeAssignment.comap_comap`).

The second part proves that boundedness makes the differentials at a position vanish from some
page on. A differential of the page `r` leaving `pq` ends at the position of total degree
`deg pq + 1` and filtration degree `fil pq + r - e`; if an earlier page vanishes there, so does
every later page (`CategoryTheory.SpectralSequence.isZero_page_X_of_le`), and the differential is
zero.
Hence:

* `CategoryTheory.SpectralSequence.page_dFrom_eq_zero_of_boundedBelow`: if the first page vanishes
  at every position `pq` with `β (deg pq) ≤ fil pq`, the differential leaving `pq` vanishes on
  every page `r ≥ β (deg pq + 1) - fil pq + e`;
* `CategoryTheory.SpectralSequence.page_dTo_eq_zero_of_boundedAbove`: if the first page vanishes
  at every position `pq` with `fil pq ≤ α (deg pq)`, the differential entering `pq` vanishes on
  every page `r ≥ fil pq - α (deg pq - 1) + e`;
* `CategoryTheory.SpectralSequence.exists_page_dFrom_eq_zero_of_finite` and
  `CategoryTheory.SpectralSequence.exists_page_dTo_eq_zero_of_finite`: if only finitely many
  positions of total degree `deg pq + 1` (respectively `deg pq - 1`) are nonzero on some page, the
  differential leaving (respectively entering) `pq` vanishes on all large pages.

Each is derived from a form, starting from an arbitrary page, that bounds the filtration degree in
the single total degree the differential reaches
(`CategoryTheory.SpectralSequence.page_dFrom_eq_zero_of_isZero_of_le_fil`,
`CategoryTheory.SpectralSequence.page_dTo_eq_zero_of_isZero_of_fil_le`).

## References

* [Stacks, *Homological Algebra*, Section 24, the filtration, complementary and total degrees
  after Definition 24.1 (Tag 012L), and Lemma 24.2 (Tag 012M), the bidegree `(r, 1 - r)` of the
  differentials](https://stacks.math.columbia.edu/tag/012K)
* [Stacks, *Homological Algebra*, Definition 24.7 (Tag 0BDU) and Lemma 24.8 (Tag 0BDV), bounded
  spectral sequences](https://stacks.math.columbia.edu/tag/012K)
-/

public section

namespace TauCeti

open CategoryTheory

/-- A **bidegree assignment** for spectral sequences whose page `r` has the complex shape `c r`
(`r ≥ r₀`): integer functions `fil` (the filtration degree) and `deg` (the total degree) on the
positions, which together determine a position, and an integer `e` (the page offset), such that
every differential of the page `r` raises `deg` by `1` and `fil` by `r - e`. -/
@[ext]
structure BidegreeAssignment {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ) where
  /-- The filtration degree of a position. -/
  fil : κ → ℤ
  /-- The total degree of a position. -/
  deg : κ → ℤ
  /-- The page offset: the differential of the page `r` raises `fil` by `r - e`. -/
  e : ℤ
  /-- A position is determined by its filtration and total degrees. -/
  injective : Function.Injective fun pq : κ ↦ (fil pq, deg pq)
  /-- Every differential raises the total degree by one. -/
  deg_rel : ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → deg pq' = deg pq + 1
  /-- The differential of the page `r` raises the filtration degree by `r - e`. -/
  fil_rel : ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → fil pq' = fil pq + r - e

namespace BidegreeAssignment

variable {κ κ' : Type*} {c : ℤ → ComplexShape κ} {c' : ℤ → ComplexShape κ'} {r₀ r₀' : ℤ}

/-- **Pulling back a bidegree assignment.** If an injective map `f : κ' → κ` carries the shape
`c' r` into the shape `c (r + d)` of the page `r + d` for every `r`, a bidegree assignment for `c`
from the page `r₀ ≤ r₀' + d` gives one for `c'` from the page `r₀'`, with the same degrees read
through `f` and the page offset decreased by `d`. This is the assignment of the reindexed spectral
sequence `CategoryTheory.SpectralSequence.reindex d f`. -/
@[expose, simps]
def comap (A : BidegreeAssignment c r₀) (d : ℤ) (f : κ' → κ) (hf : Function.Injective f)
    (hrel : ∀ r i j, (c' r).Rel i j → (c (r + d)).Rel (f i) (f j)) (hd : r₀ ≤ r₀' + d) :
    BidegreeAssignment c' r₀' where
  fil i := A.fil (f i)
  deg i := A.deg (f i)
  e := A.e - d
  injective := A.injective.comp hf
  deg_rel r hr i j h := A.deg_rel (r + d) (by lia) _ _ (hrel r i j h)
  fil_rel r hr i j h := by
    rw [A.fil_rel (r + d) (by lia) _ _ (hrel r i j h)]
    lia

/-- Pulling back along the identity of the positions with no page shift does nothing. -/
lemma comap_zero_id (A : BidegreeAssignment c r₀) :
    A.comap 0 id Function.injective_id (fun r i j h ↦ by rwa [add_zero]) (add_zero r₀).ge = A := by
  ext <;> simp

/-- Pulling back twice is pulling back once, along the composite map of positions and the total
page shift. -/
lemma comap_comap {κ'' : Type*} {c'' : ℤ → ComplexShape κ''} {r₀'' : ℤ}
    (A : BidegreeAssignment c r₀) (d : ℤ) (f : κ' → κ) (hf : Function.Injective f)
    (hrel : ∀ r i j, (c' r).Rel i j → (c (r + d)).Rel (f i) (f j)) (hd : r₀ ≤ r₀' + d)
    (d' : ℤ) (f' : κ'' → κ') (hf' : Function.Injective f')
    (hrel' : ∀ r i j, (c'' r).Rel i j → (c' (r + d')).Rel (f' i) (f' j)) (hd' : r₀' ≤ r₀'' + d') :
    (A.comap d f hf hrel hd).comap d' f' hf' hrel' hd' =
      A.comap (d + d') (f ∘ f') (hf.comp hf')
        (fun r i j h ↦ by
          simpa only [add_assoc, add_comm d', Function.comp_apply] using hrel _ _ _ (hrel' r i j h))
        (by lia) := by
  ext <;> simp [sub_sub]

/-- The **cohomological** bidegree assignment `(p, q) ↦ (p, p + q)`, with page offset `0`, for the
cohomological shapes `ComplexShape.up' (r, 1 - r)` of
`CategoryTheory.CohomologicalSpectralSequence`: the differential `E_r^{p,q} ⟶ E_r^{p+r,q-r+1}`
raises the filtration degree `p` by `r` and the total degree `p + q` by `1`. -/
@[expose, simps]
def cohomological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  e := 0
  injective := fun ⟨p, q⟩ ⟨p', q'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia
  fil_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia

/-- The **cohomological** bidegree assignment `(p, q) ↦ (p, p + q)`, with page offset `0`, for the
first-quadrant cohomological shapes `ComplexShape.spectralSequenceNat (r, 1 - r)` of
`CategoryTheory.CohomologicalSpectralSequenceNat`. -/
@[expose, simps]
def cohomologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  e := 0
  injective := fun ⟨p, q⟩ ⟨p', q'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia
  fil_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

/-- The **cohomological** bidegree assignment `(p, q) ↦ (p, p + q)`, with page offset `0`, for the
cohomological shapes `ComplexShape.spectralSequenceFin l (r, 1 - r)` on `ℤ × Fin l` of
`CategoryTheory.CohomologicalSpectralSequenceFin`. -/
@[expose, simps]
def cohomologicalFin (l : ℕ) (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  e := 0
  injective := fun ⟨p, q⟩ ⟨p', q'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceFin_rel_iff] at h
    lia
  fil_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceFin_rel_iff] at h
    lia

/-- The **homological** bidegree assignment `(p, q) ↦ (-p, -p - q)`, with page offset `0`, for the
homological shapes `ComplexShape.up' (-r, r - 1)`: the differential
`E^r_{p,q} ⟶ E^r_{p-r,q+r-1}` lowers the homological filtration degree `p` by `r` and the
homological total degree `p + q` by `1`, so it raises their negatives, the cohomological degrees,
by `r` and `1`. -/
@[expose, simps]
def homological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀ where
  fil pq := -pq.1
  deg pq := -pq.1 - pq.2
  e := 0
  injective := fun ⟨p, q⟩ ⟨p', q'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia
  fil_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia

/-- The **homological** bidegree assignment `(p, q) ↦ (-p, -p - q)`, with page offset `0`, for the
first-quadrant homological shapes `ComplexShape.spectralSequenceNat (-r, r - 1)`, those of the
spectral sequence of Mathlib's recipe `coreE₂HomologicalNat`. -/
@[expose, simps]
def homologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) r₀ where
  fil pq := -(pq.1 : ℤ)
  deg pq := -(pq.1 : ℤ) - pq.2
  e := 0
  injective := fun ⟨p, q⟩ ⟨p', q'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia
  fil_rel := by
    rintro r - ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

/-- The **decreasing-filtration** bidegree assignment `(a, b) ↦ (-b - 1, a + b)`, with page offset
`1`, for the cohomological shapes `ComplexShape.up' (r, 1 - r)`. These are the native positions of
the spectral sequence of a spectral object for Mathlib's recipe `coreE₂Cohomological`, such as
`CochainComplex.spectralSequence` of an increasing filtration `G` of a cochain complex: for the
decreasing filtration `F^p = G_{-p}`, the classical object `E_r^{p,q}` sits on page `r + 1` at
`(2p + q + 1, -p - 1)`, whose filtration degree here is `p` and whose total degree is `p + q`. The
differential of page `r` raises `fil` by `r - 1`, as the classical differential of page `r - 1`
raises `p` by `r - 1`. -/
@[expose, simps]
def decreasingFiltration (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ where
  fil pq := -pq.2 - 1
  deg pq := pq.1 + pq.2
  e := 1
  injective := fun ⟨a, b⟩ ⟨a', b'⟩ h ↦ by
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel := by
    rintro r - ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia
  fil_rel := by
    rintro r - ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia

end BidegreeAssignment

end TauCeti

namespace CategoryTheory.SpectralSequence

open Limits TauCeti

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)

/-- **The leaving differential vanishes past a bound on the filtration degree.** If the page `s`
vanishes at every position of total degree `deg pq + 1` and filtration degree at least `b`, the
differential leaving `pq` vanishes on every page `r ≥ s` with `r ≥ b - fil pq + e`: it ends at the
position of total degree `deg pq + 1` and filtration degree `fil pq + r - e ≥ b`. -/
lemma page_dFrom_eq_zero_of_isZero_of_le_fil {s : ℤ} (hs : r₀ ≤ s) (pq : κ) (b : ℤ)
    (hb : ∀ pq', A.deg pq' = A.deg pq + 1 → b ≤ A.fil pq' → IsZero ((E.page s hs).X pq'))
    (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) (hrb : b - A.fil pq + A.e ≤ r) :
    (E.page r hr).dFrom pq = 0 := by
  by_cases hrel : (c r).Rel pq ((c r).next pq)
  · rw [HomologicalComplex.dFrom_eq _ hrel,
      E.page_d_eq_zero_of_le hs (Or.inr (hb _ (A.deg_rel r hr _ _ hrel)
        (by rw [A.fil_rel r hr _ _ hrel]; lia))) r hsr, zero_comp]
  · exact HomologicalComplex.dFrom_eq_zero _ hrel

/-- **The entering differential vanishes past a bound on the filtration degree.** If the page `s`
vanishes at every position of total degree `deg pq - 1` and filtration degree at most `a`, the
differential entering `pq` vanishes on every page `r ≥ s` with `r ≥ fil pq - a + e`: it starts at
the position of total degree `deg pq - 1` and filtration degree `fil pq - r + e ≤ a`. -/
lemma page_dTo_eq_zero_of_isZero_of_fil_le {s : ℤ} (hs : r₀ ≤ s) (pq : κ) (a : ℤ)
    (ha : ∀ pq', A.deg pq' = A.deg pq - 1 → A.fil pq' ≤ a → IsZero ((E.page s hs).X pq'))
    (r : ℤ) (hr : r₀ ≤ r) (hsr : s ≤ r) (hra : A.fil pq - a + A.e ≤ r) :
    (E.page r hr).dTo pq = 0 := by
  by_cases hrel : (c r).Rel ((c r).prev pq) pq
  · rw [HomologicalComplex.dTo_eq _ hrel,
      E.page_d_eq_zero_of_le hs (Or.inl (ha _ (by rw [A.deg_rel r hr _ _ hrel]; lia)
        (by have := A.fil_rel r hr _ _ hrel; lia))) r hsr, comp_zero]
  · exact HomologicalComplex.dTo_eq_zero _ hrel

/-- **Bounded below implies that the leaving differentials vanish eventually** (Stacks, Tag 0BDV,
Lemma 24.8 (4)). Let `β : ℤ → ℤ` be a bound below for the first page: it vanishes at every position
`pq` with `β (deg pq) ≤ fil pq`. Then the differential leaving `pq` vanishes on every page
`r ≥ r₀` with `β (deg pq + 1) - fil pq + e ≤ r`. -/
lemma page_dFrom_eq_zero_of_boundedBelow (β : ℤ → ℤ)
    (hβ : ∀ pq, β (A.deg pq) ≤ A.fil pq → IsZero ((E.page r₀).X pq)) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) (hrβ : β (A.deg pq + 1) - A.fil pq + A.e ≤ r) :
    (E.page r hr).dFrom pq = 0 :=
  E.page_dFrom_eq_zero_of_isZero_of_le_fil A le_rfl pq _
    (fun pq' hpq' h ↦ hβ pq' (by rwa [hpq'])) r hr hr hrβ

/-- **Bounded above implies that the entering differentials vanish eventually** (Stacks, Tag 0BDV,
Lemma 24.8 (5)). Let `α : ℤ → ℤ` be a bound above for the first page: it vanishes at every position
`pq` with `fil pq ≤ α (deg pq)`. Then the differential entering `pq` vanishes on every page
`r ≥ r₀` with `fil pq - α (deg pq - 1) + e ≤ r`. -/
lemma page_dTo_eq_zero_of_boundedAbove (α : ℤ → ℤ)
    (hα : ∀ pq, A.fil pq ≤ α (A.deg pq) → IsZero ((E.page r₀).X pq)) (pq : κ) (r : ℤ)
    (hr : r₀ ≤ r) (hrα : A.fil pq - α (A.deg pq - 1) + A.e ≤ r) :
    (E.page r hr).dTo pq = 0 :=
  E.page_dTo_eq_zero_of_isZero_of_fil_le A le_rfl pq _
    (fun pq' hpq' h ↦ hα pq' (by rwa [hpq'])) r hr hr hrα

/-- **Finitely many nonzero positions in the next total degree.** If only finitely many positions
of total degree `deg pq + 1` are nonzero on the page `s`, the differential leaving `pq` vanishes
on every page from some page on. -/
lemma exists_page_dFrom_eq_zero_of_finite {s : ℤ} (hs : r₀ ≤ s) (pq : κ)
    (hfin : {pq' | A.deg pq' = A.deg pq + 1 ∧ ¬IsZero ((E.page s hs).X pq')}.Finite) :
    ∃ t : ℤ, ∀ (r : ℤ) (hr : r₀ ≤ r), t ≤ r → (E.page r hr).dFrom pq = 0 := by
  obtain ⟨M, hM⟩ := (hfin.image A.fil).bddAbove
  refine ⟨max s (M + 1 - A.fil pq + A.e), fun r hr hrt ↦
    E.page_dFrom_eq_zero_of_isZero_of_le_fil A hs pq (M + 1) (fun pq' hpq' h ↦ ?_) r hr
      (le_of_max_le_left hrt) (le_of_max_le_right hrt)⟩
  by_contra hz
  have := hM ⟨pq', ⟨hpq', hz⟩, rfl⟩
  lia

/-- **Finitely many nonzero positions in the previous total degree.** If only finitely many
positions of total degree `deg pq - 1` are nonzero on the page `s`, the differential entering
`pq` vanishes on every page from some page on. -/
lemma exists_page_dTo_eq_zero_of_finite {s : ℤ} (hs : r₀ ≤ s) (pq : κ)
    (hfin : {pq' | A.deg pq' = A.deg pq - 1 ∧ ¬IsZero ((E.page s hs).X pq')}.Finite) :
    ∃ t : ℤ, ∀ (r : ℤ) (hr : r₀ ≤ r), t ≤ r → (E.page r hr).dTo pq = 0 := by
  obtain ⟨M, hM⟩ := (hfin.image A.fil).bddBelow
  refine ⟨max s (A.fil pq - (M - 1) + A.e), fun r hr hrt ↦
    E.page_dTo_eq_zero_of_isZero_of_fil_le A hs pq (M - 1) (fun pq' hpq' h ↦ ?_) r hr
      (le_of_max_le_left hrt) (le_of_max_le_right hrt)⟩
  by_contra hz
  have := hM ⟨pq', ⟨hpq', hz⟩, rfl⟩
  lia

end CategoryTheory.SpectralSequence
