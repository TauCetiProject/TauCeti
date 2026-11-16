/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Bidegree assignments and Euler characteristic signs for spectral sequences

A **bidegree assignment** (`CategoryTheory.SpectralSequence.BidegreeAssignment`) for page shapes
`c : ℤ → ComplexShape κ` starting at page `r₀ : ℤ` equips `κ` with integer-valued filtration
degree `fil` and total degree `deg`, jointly injective, together with a page offset `e : ℤ`, such
that every differential of page `r ≥ r₀` raises `deg` by `1` and raises `fil` by `r - e`.

This packages the degree bookkeeping shared by all standard spectral sequence indexing conventions:

* `BidegreeAssignment.cohomological`, `BidegreeAssignment.cohomologicalNat`, and
  `BidegreeAssignment.cohomologicalFin`: `(p, q) ↦ (p, p + q)` with `e = 0` for the cohomological
  shapes `ComplexShape.up' (r, 1 - r)`, `ComplexShape.spectralSequenceNat (r, 1 - r)`, and
  `ComplexShape.spectralSequenceFin l (r, 1 - r)`.
* `BidegreeAssignment.homological` and `BidegreeAssignment.homologicalNat`:
  `(p, q) ↦ (-p, -p - q)` with `e = 0` for the homological shapes `ComplexShape.up' (-r, r - 1)`
  and `ComplexShape.spectralSequenceNat (-r, r - 1)`.
* `BidegreeAssignment.classicalFiltered`: `(p, q) ↦ (-q - 1, p + q)` with `e = 1` for the native
  `E₂` cohomological coordinates of the spectral sequence of an increasingly filtered complex.
* `BidegreeAssignment.reindex`: transports a bidegree assignment along a page shift `d : ℤ` and
  position bijection `f : κ' ≃ κ`, shifting the offset `e` to `e - d`.
* `BidegreeAssignment.eulerCharSigns`: equips each page shape `c r` (`r₀ ≤ r`) with alternating
  signs `pq ↦ (-1)^(A.deg pq)`.

We also register `ComplexShape.EulerCharSigns` instances `pq ↦ (-1)^(p + q)` for the standard
cohomological and homological spectral sequence page shapes.

## References

* Stacks Project, Tag 012L (filtration, complementary, and total degrees of a spectral sequence)
  and Tag 012M (bidegree of differentials).
-/

public section

namespace ComplexShape

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.up' (r, 1 - r)` of a cohomological spectral sequence. -/
instance eulerCharSignsUp'Cohomological (r : ℤ) :
    (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {a b} h := by
    obtain ⟨p, q⟩ := a
    obtain ⟨p', q'⟩ := b
    simp only [up', Prod.mk_add_mk, Prod.mk.injEq] at h
    have hsum : p' + q' = p + q + 1 := by lia
    rw [hsum, Int.negOnePow_succ]

@[simp↓]
lemma eulerCharSignsUp'Cohomological_χ (r : ℤ) (pq : ℤ × ℤ) :
    (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).χ pq = (pq.1 + pq.2).negOnePow := rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.up' (-r, r - 1)` of a homological spectral sequence. -/
instance eulerCharSignsUp'Homological (r : ℤ) :
    (up' (⟨-r, r - 1⟩ : ℤ × ℤ)).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {a b} h := by
    obtain ⟨p, q⟩ := a
    obtain ⟨p', q'⟩ := b
    simp only [up', Prod.mk_add_mk, Prod.mk.injEq] at h
    have hsum : p + q = p' + q' + 1 := by lia
    rw [hsum, Int.negOnePow_succ, neg_neg]

@[simp↓]
lemma eulerCharSignsUp'Homological_χ (r : ℤ) (pq : ℤ × ℤ) :
    (up' (⟨-r, r - 1⟩ : ℤ × ℤ)).χ pq = (pq.1 + pq.2).negOnePow := rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceNat (r, 1 - r)` of a first-quadrant cohomological spectral
sequence. -/
instance eulerCharSignsSpectralSequenceNatCohomological (r : ℤ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).EulerCharSigns where
  χ pq := ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow
  χ_next {a b} h := by
    simp only [spectralSequenceNat_rel_iff] at h
    have hsum : (b.1 : ℤ) + (b.2 : ℤ) = (a.1 : ℤ) + (a.2 : ℤ) + 1 := by lia
    rw [hsum, Int.negOnePow_succ]

@[simp↓]
lemma eulerCharSignsSpectralSequenceNatCohomological_χ (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).χ pq = ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow := rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceNat (-r, r - 1)` of a first-quadrant homological spectral
sequence. -/
instance eulerCharSignsSpectralSequenceNatHomological (r : ℤ) :
    (spectralSequenceNat ⟨-r, r - 1⟩).EulerCharSigns where
  χ pq := ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow
  χ_next {a b} h := by
    simp only [spectralSequenceNat_rel_iff] at h
    have hsum : (a.1 : ℤ) + (a.2 : ℤ) = (b.1 : ℤ) + (b.2 : ℤ) + 1 := by lia
    rw [hsum, Int.negOnePow_succ, neg_neg]

@[simp↓]
lemma eulerCharSignsSpectralSequenceNatHomological_χ (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat ⟨-r, r - 1⟩).χ pq = ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow := rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceFin l (r, 1 - r)` of a cohomological spectral sequence on `l`
rows. -/
instance eulerCharSignsSpectralSequenceFinCohomological (l : ℕ) (r : ℤ) :
    (spectralSequenceFin l ⟨r, 1 - r⟩).EulerCharSigns where
  χ pq := (pq.1 + (pq.2.1 : ℤ)).negOnePow
  χ_next {a b} h := by
    simp only [spectralSequenceFin_rel_iff] at h
    have hsum : b.1 + (b.2.1 : ℤ) = a.1 + (a.2.1 : ℤ) + 1 := by lia
    rw [hsum, Int.negOnePow_succ]

@[simp↓]
lemma eulerCharSignsSpectralSequenceFinCohomological_χ (l : ℕ) (r : ℤ) (pq : ℤ × Fin l) :
    (spectralSequenceFin l ⟨r, 1 - r⟩).χ pq = (pq.1 + (pq.2.1 : ℤ)).negOnePow := rfl

end ComplexShape

namespace CategoryTheory.SpectralSequence

/-- A **bidegree assignment** for spectral sequences whose `r`th page has shape `c r`
(`r₀ ≤ r`): integer functions `fil` (filtration degree) and `deg` (total degree) on the positions
`κ`, jointly injective, together with an integer `e` (the page offset), such that every
differential on page `r ≥ r₀` raises `deg` by `1` and raises `fil` by `r - e`. -/
@[ext]
structure BidegreeAssignment {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ) where
  /-- The filtration degree of a position. -/
  fil : κ → ℤ
  /-- The total degree of a position. -/
  deg : κ → ℤ
  /-- The page offset: the differential of page `r` raises `fil` by `r - e`. -/
  e : ℤ
  /-- A position is uniquely determined by its filtration and total degrees. -/
  injective : Function.Injective fun pq : κ ↦ (fil pq, deg pq)
  /-- Every differential on page `r ≥ r₀` raises the total degree by `1`. -/
  deg_rel : ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → deg pq' = deg pq + 1
  /-- Every differential on page `r ≥ r₀` raises the filtration degree by `r - e`. -/
  fil_rel :
    ∀ r : ℤ, r₀ ≤ r → ∀ pq pq' : κ, (c r).Rel pq pq' → fil pq' = fil pq + r - e

namespace BidegreeAssignment

section General

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ} (A : BidegreeAssignment c r₀)

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
`A.fil pq - r + A.e`. -/
lemma fil_rel_prev {r : ℤ} (hr : r₀ ≤ r) {pq' pq : κ} (h : (c r).Rel pq' pq) :
    A.fil pq' = A.fil pq - r + A.e := by
  have := A.fil_rel r hr pq' pq h
  lia

/-- The alternating signs `pq ↦ (-1)^(A.deg pq)` induced by a bidegree assignment on page `r`
(`r₀ ≤ r`). -/
@[instance_reducible]
def eulerCharSigns (r : ℤ) (hr : r₀ ≤ r) : (c r).EulerCharSigns where
  χ pq := (A.deg pq).negOnePow
  χ_next h := by
    rw [A.deg_rel r hr _ _ h, Int.negOnePow_succ]

@[simp]
lemma eulerCharSigns_χ (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (A.eulerCharSigns r hr).χ pq = (A.deg pq).negOnePow := (rfl)

/-- Restrict a bidegree assignment from starting page `r₀` to a later starting page
`r₀' ≥ r₀`. -/
def ofLE {r₀' : ℤ} (h : r₀ ≤ r₀') : BidegreeAssignment c r₀' where
  fil := A.fil
  deg := A.deg
  e := A.e
  injective := A.injective
  deg_rel r hr := A.deg_rel r (h.trans hr)
  fil_rel r hr := A.fil_rel r (h.trans hr)

@[simp]
lemma ofLE_fil {r₀' : ℤ} (h : r₀ ≤ r₀') (pq : κ) : (A.ofLE h).fil pq = A.fil pq := (rfl)

@[simp]
lemma ofLE_deg {r₀' : ℤ} (h : r₀ ≤ r₀') (pq : κ) : (A.ofLE h).deg pq = A.deg pq := (rfl)

@[simp]
lemma ofLE_e {r₀' : ℤ} (h : r₀ ≤ r₀') : (A.ofLE h).e = A.e := (rfl)

/-- Transport a bidegree assignment along a reindexing of page shapes by a page shift `d : ℤ` and
position bijection `f : κ' ≃ κ`. The filtration and total degrees compose with `f`, and the page
offset shifts from `e` to `e - d`. -/
def reindex {κ' : Type*} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ} (d : ℤ) (f : κ' ≃ κ)
    (hf : ∀ r, r₀' ≤ r → ∀ i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j))
    (hd : r₀ ≤ r₀' + d) : BidegreeAssignment c' r₀' where
  fil pq := A.fil (f pq)
  deg pq := A.deg (f pq)
  e := A.e - d
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

@[simp]
lemma reindex_e {κ' : Type*} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ} (d : ℤ)
    (f : κ' ≃ κ)
    (hf : ∀ r, r₀' ≤ r → ∀ i j, (c' r).Rel i j ↔ (c (r + d)).Rel (f i) (f j))
    (hd : r₀ ≤ r₀' + d) :
    (A.reindex d f hf hd).e = A.e - d := (rfl)

end General

/-! ### Standard bidegree assignments -/

/-- The standard cohomological bidegree assignment `(p, q) ↦ (p, p + q)` with page offset `0` for
`CohomologicalSpectralSequence` (`ComplexShape.up' (r, 1 - r)` on `ℤ × ℤ`). -/
def cohomological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  e := 0
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
@[simp] lemma cohomological_e (r₀ : ℤ) : (cohomological r₀).e = 0 := (rfl)

/-- The standard cohomological bidegree assignment `(p, q) ↦ (p, p + q)` with page offset `0` for
`CohomologicalSpectralSequenceNat` (`ComplexShape.spectralSequenceNat (r, 1 - r)` on `ℕ × ℕ`). -/
def cohomologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2
  e := 0
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
@[simp] lemma cohomologicalNat_e (r₀ : ℤ) : (cohomologicalNat r₀).e = 0 := (rfl)

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
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩) r₀ where
  fil pq := pq.1
  deg pq := pq.1 + pq.2.1
  e := 0
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
@[simp] lemma cohomologicalFin_e (l : ℕ) (r₀ : ℤ) : (cohomologicalFin l r₀).e = 0 := (rfl)

/-- The standard homological bidegree assignment `(p, q) ↦ (-p, -p - q)` with page offset `0` for
the homological shape `ComplexShape.up' (-r, r - 1)` on `ℤ × ℤ`. -/
def homological (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) r₀ where
  fil pq := -pq.1
  deg pq := -pq.1 - pq.2
  e := 0
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
@[simp] lemma homological_e (r₀ : ℤ) : (homological r₀).e = 0 := (rfl)

/-- The standard homological first-quadrant bidegree assignment `(p, q) ↦ (-p, -p - q)` with page
offset `0` for `ComplexShape.spectralSequenceNat (-r, r - 1)` on `ℕ × ℕ`. -/
def homologicalNat (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) r₀ where
  fil pq := -(pq.1 : ℤ)
  deg pq := -(pq.1 : ℤ) - (pq.2 : ℤ)
  e := 0
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
@[simp] lemma homologicalNat_e (r₀ : ℤ) : (homologicalNat r₀).e = 0 := (rfl)

/-- The classical filtered-complex bidegree assignment `(p, q) ↦ (-q - 1, p + q)` with page offset
`1` on the native `E₂` cohomological coordinates `ComplexShape.up' (r, 1 - r)` of the spectral
sequence of an increasingly filtered complex (`coreE₂Cohomological`). -/
def classicalFiltered (r₀ : ℤ) :
    BidegreeAssignment (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) r₀ where
  fil pq := -pq.2 - 1
  deg pq := pq.1 + pq.2
  e := 1
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

@[simp] lemma classicalFiltered_fil (r₀ : ℤ) (pq : ℤ × ℤ) :
    (classicalFiltered r₀).fil pq = -pq.2 - 1 := (rfl)
@[simp] lemma classicalFiltered_deg (r₀ : ℤ) (pq : ℤ × ℤ) :
    (classicalFiltered r₀).deg pq = pq.1 + pq.2 := (rfl)
@[simp] lemma classicalFiltered_e (r₀ : ℤ) : (classicalFiltered r₀).e = 1 := (rfl)

end BidegreeAssignment

end CategoryTheory.SpectralSequence
