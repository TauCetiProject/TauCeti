/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Bidegree assignments for spectral sequences

A **bidegree assignment** (`CategoryTheory.SpectralSequence.BidegreeAssignment`) for page shapes
`c : ℤ → ComplexShape κ` starting at page `r₀ : ℤ` with page offset `e : ℤ` equips `κ` with
integer-valued filtration degree `fil` and total degree `deg`, jointly injective, such that every
differential of page `r ≥ r₀` raises `deg` by `1` and raises `fil` by `r - e`.

This packages the degree bookkeeping shared by standard spectral sequence indexing conventions:

* `BidegreeAssignment.cohomological`, `BidegreeAssignment.cohomologicalNat`, and
  `BidegreeAssignment.cohomologicalFin`: `(p, q) ↦ (p, p + q)` with `e = 0` for the cohomological
  shapes `ComplexShape.up' (r, 1 - r)`, `ComplexShape.spectralSequenceNat (r, 1 - r)`, and
  `ComplexShape.spectralSequenceFin l (r, 1 - r)`.
* `BidegreeAssignment.homological` and `BidegreeAssignment.homologicalNat`:
  `(p, q) ↦ (-p, -p - q)` with `e = 0` for the homological shapes `ComplexShape.up' (-r, r - 1)`
  and `ComplexShape.spectralSequenceNat (-r, r - 1)`.
* `BidegreeAssignment.ofLE`: restricts a bidegree assignment to a later starting page `r₀' ≥ r₀`,
  preserving `e`.
* `BidegreeAssignment.reindex`: transports a bidegree assignment along a page shift `d : ℤ` and
  position bijection `f : κ' ≃ κ`, shifting the offset `e` to `e - d`.

## References

* Stacks Project, Tag 012L (filtration, complementary, and total degrees of a spectral sequence)
  and Tag 012M (bidegree of differentials).
-/

public section

namespace CategoryTheory.SpectralSequence

/-- A **bidegree assignment** for spectral sequences whose `r`th page has shape `c r`
(`r₀ ≤ r`) and page offset `e`: integer functions `fil` (filtration degree) and `deg` (total
degree) on the positions `κ`, jointly injective, such that every differential on page `r ≥ r₀`
raises `deg` by `1` and raises `fil` by `r - e`. -/
@[ext]
structure BidegreeAssignment {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ e : ℤ) where
  /-- The filtration degree of a position. -/
  fil : κ → ℤ
  /-- The total degree of a position. -/
  deg : κ → ℤ
  /-- A position is uniquely determined by its filtration and total degrees. -/
  injective : Function.Injective fun pq : κ ↦ (fil pq, deg pq)
  /-- Every differential on page `r ≥ r₀` raises the total degree by `1`. -/
  deg_rel : ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → deg pq' = deg pq + 1
  /-- Every differential on page `r ≥ r₀` raises the filtration degree by `r - e`. -/
  fil_rel :
    ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → fil pq' = fil pq + r - e

namespace BidegreeAssignment

section General

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ e : ℤ} (A : BidegreeAssignment c r₀ e)

/-- Two positions with the same filtration degree and total degree are equal. -/
lemma eq_of_fil_eq_of_deg_eq {pq pq' : κ} (hfil : A.fil pq = A.fil pq')
    (hdeg : A.deg pq = A.deg pq') : pq = pq' :=
  A.injective (Prod.ext hfil hdeg)

/-- A differential entering `pq` on page `r ≥ r₀` starts in total degree `A.deg pq - 1`. -/
lemma deg_rel_prev {r : ℤ} (hr : r₀ ≤ r) {pq' pq : κ} (h : (c r).Rel pq' pq) :
    A.deg pq' = A.deg pq - 1 := by
  have := A.deg_rel r hr pq' pq h
  lia

/-- A differential entering `pq` on page `r ≥ r₀` starts in filtration degree
`A.fil pq - r + e`. -/
lemma fil_rel_prev {r : ℤ} (hr : r₀ ≤ r) {pq' pq : κ} (h : (c r).Rel pq' pq) :
    A.fil pq' = A.fil pq - r + e := by
  have := A.fil_rel r hr pq' pq h
  lia

/-- Restrict a bidegree assignment from starting page `r₀` to a later starting page
`r₀' ≥ r₀`, preserving the page offset `e`. -/
def ofLE {r₀' : ℤ} (h : r₀ ≤ r₀') : BidegreeAssignment c r₀' e where
  fil := A.fil
  deg := A.deg
  injective := A.injective
  deg_rel r hr := A.deg_rel r (h.trans hr)
  fil_rel r hr := A.fil_rel r (h.trans hr)

@[simp]
lemma ofLE_fil {r₀' : ℤ} (h : r₀ ≤ r₀') (pq : κ) : (A.ofLE h).fil pq = A.fil pq := (rfl)

@[simp]
lemma ofLE_deg {r₀' : ℤ} (h : r₀ ≤ r₀') (pq : κ) : (A.ofLE h).deg pq = A.deg pq := (rfl)

/-- Transport a bidegree assignment along a reindexing of page shapes by a page shift `d : ℤ` and
position bijection `f : κ' ≃ κ`. The filtration and total degrees compose with `f`, and the page
offset shifts from `e` to `e - d`. -/
def reindex {κ' : Type*} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ} (d : ℤ) (f : κ' ≃ κ)
    (hf : ∀ r, r₀' ≤ r → ∀ i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j))
    (hd : r₀ ≤ r₀' + d) : BidegreeAssignment c' r₀' (e - d) where
  fil pq := A.fil (f pq)
  deg pq := A.deg (f pq)
  injective := A.injective.comp f.injective
  deg_rel r hr i j hij := A.deg_rel (r + d) (by lia) (f i) (f j) ((hf r hr i j).1 hij)
  fil_rel r hr i j hij := by
    have := A.fil_rel (r + d) (by lia) (f i) (f j) ((hf r hr i j).1 hij)
    lia

@[simp]
lemma reindex_fil {κ' : Type*} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ} (d : ℤ)
    (f : κ' ≃ κ)
    (hf : ∀ r, r₀' ≤ r → ∀ i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j))
    (hd : r₀ ≤ r₀' + d) (pq : κ') :
    (A.reindex d f hf hd).fil pq = A.fil (f pq) := (rfl)

@[simp]
lemma reindex_deg {κ' : Type*} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ} (d : ℤ)
    (f : κ' ≃ κ)
    (hf : ∀ r, r₀' ≤ r → ∀ i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j))
    (hd : r₀ ≤ r₀' + d) (pq : κ') :
    (A.reindex d f hf hd).deg pq = A.deg (f pq) := (rfl)

end General

/-! ### Standard bidegree assignments -/

/-- The standard cohomological bidegree assignment `(p, q) ↦ (p, p + q)` with page offset `0` for
`CohomologicalSpectralSequence` (`ComplexShape.up' (r, 1 - r)` on `ℤ × ℤ`). -/
def cohomological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ 0 where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  injective := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel r _ pq pq' h := by
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := pq'
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia
  fil_rel r _ pq pq' h := by
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := pq'
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia

@[simp] lemma cohomological_fil (r₀ : ℤ) (pq : ℤ × ℤ) :
    (cohomological r₀).fil pq = pq.1 := (rfl)
@[simp] lemma cohomological_deg (r₀ : ℤ) (pq : ℤ × ℤ) :
    (cohomological r₀).deg pq = pq.1 + pq.2 := (rfl)

/-- The standard cohomological bidegree assignment `(p, q) ↦ (p, p + q)` with page offset `0` for
`CohomologicalSpectralSequenceNat` (`ComplexShape.spectralSequenceNat (r, 1 - r)` on `ℕ × ℕ`). -/
def cohomologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) r₀ 0 where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  injective := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia
  fil_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

@[simp] lemma cohomologicalNat_fil (r₀ : ℤ) (pq : ℕ × ℕ) :
    (cohomologicalNat r₀).fil pq = (pq.1 : ℤ) := (rfl)
@[simp] lemma cohomologicalNat_deg (r₀ : ℤ) (pq : ℕ × ℕ) :
    (cohomologicalNat r₀).deg pq = (pq.1 : ℤ) + (pq.2 : ℤ) := (rfl)

/-- On `ℕ × ℕ`, the pairs `(p, n)` realised as `(fil pq, deg pq)` by `cohomologicalNat` are
precisely those with `0 ≤ p ≤ n`. -/
lemma exists_cohomologicalNat_iff (r₀ : ℤ) (p n : ℤ) :
    (∃ pq : ℕ × ℕ, (cohomologicalNat r₀).fil pq = p ∧
        (cohomologicalNat r₀).deg pq = n) ↔ 0 ≤ p ∧ p ≤ n := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl, rfl⟩
    simp only [cohomologicalNat_fil, cohomologicalNat_deg]
    lia
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨p.toNat, (n - p).toNat⟩, by simp only [cohomologicalNat_fil]; lia,
      by simp only [cohomologicalNat_deg]; lia⟩

/-- The standard cohomological bidegree assignment `(p, q) ↦ (p, p + q)` with page offset `0` for
`CohomologicalSpectralSequenceFin` (`ComplexShape.spectralSequenceFin l (r, 1 - r)` on
`ℤ × Fin l`). -/
def cohomologicalFin (l : ℕ) (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩) r₀ 0 where
  fil pq := pq.1
  deg pq := pq.1 + pq.2.1
  injective := by
    rintro ⟨p, ⟨q, hq⟩⟩ ⟨p', ⟨q', hq'⟩⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> dsimp <;> lia
  deg_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceFin_rel_iff] at h
    lia
  fil_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceFin_rel_iff] at h
    lia

@[simp] lemma cohomologicalFin_fil (l : ℕ) (r₀ : ℤ) (pq : ℤ × Fin l) :
    (cohomologicalFin l r₀).fil pq = pq.1 := (rfl)
@[simp] lemma cohomologicalFin_deg (l : ℕ) (r₀ : ℤ) (pq : ℤ × Fin l) :
    (cohomologicalFin l r₀).deg pq = pq.1 + (pq.2.1 : ℤ) := (rfl)

/-- The standard homological bidegree assignment `(p, q) ↦ (-p, -p - q)` with page offset `0` for
the homological shape `ComplexShape.up' (-r, r - 1)` on `ℤ × ℤ`. -/
def homological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀ 0 where
  fil pq := -pq.1
  deg pq := -pq.1 - pq.2
  injective := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel r _ pq pq' h := by
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := pq'
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia
  fil_rel r _ pq pq' h := by
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := pq'
    simp only [ComplexShape.up', Prod.mk_add_mk, Prod.mk.injEq] at h
    lia

@[simp] lemma homological_fil (r₀ : ℤ) (pq : ℤ × ℤ) :
    (homological r₀).fil pq = -pq.1 := (rfl)
@[simp] lemma homological_deg (r₀ : ℤ) (pq : ℤ × ℤ) :
    (homological r₀).deg pq = -pq.1 - pq.2 := (rfl)

/-- The standard homological first-quadrant bidegree assignment `(p, q) ↦ (-p, -p - q)` with page
offset `0` for `ComplexShape.spectralSequenceNat (-r, r - 1)` on `ℕ × ℕ`. -/
def homologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) r₀ 0 where
  fil pq := -(pq.1 : ℤ)
  deg pq := -(pq.1 : ℤ) - (pq.2 : ℤ)
  injective := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> lia
  deg_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia
  fil_rel r _ pq pq' h := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
    lia

@[simp] lemma homologicalNat_fil (r₀ : ℤ) (pq : ℕ × ℕ) :
    (homologicalNat r₀).fil pq = -(pq.1 : ℤ) := (rfl)
@[simp] lemma homologicalNat_deg (r₀ : ℤ) (pq : ℕ × ℕ) :
    (homologicalNat r₀).deg pq = -(pq.1 : ℤ) - (pq.2 : ℤ) := (rfl)

end BidegreeAssignment

end CategoryTheory.SpectralSequence
