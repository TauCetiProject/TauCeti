/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Homology.SpectralSequence.Bidegree

/-!
# Euler characteristic signs for spectral sequence pages

This file equips the standard cohomological and homological spectral sequence page shapes with the
alternating total-degree signs `pq ↦ (-1)^(p + q)` (`ComplexShape.EulerCharSigns`), and constructs
the alternating total-degree signs `pq ↦ (-1)^(A.deg pq)` induced on every page `r ≥ r₀` by a
`CategoryTheory.SpectralSequence.BidegreeAssignment` (`BidegreeAssignment.eulerCharSigns`).
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

namespace CategoryTheory.SpectralSequence.BidegreeAssignment

/-- The alternating signs `pq ↦ (-1)^(A.deg pq)` induced by a bidegree assignment on page `r`
(`r₀ ≤ r`). -/
@[instance_reducible]
def eulerCharSigns {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ e : ℤ}
    (A : BidegreeAssignment c r₀ e) (r : ℤ) (hr : r₀ ≤ r) : (c r).EulerCharSigns where
  χ pq := (A.deg pq).negOnePow
  χ_next h := by
    rw [A.deg_rel r hr _ _ h, Int.negOnePow_succ]

@[simp]
lemma eulerCharSigns_χ {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ e : ℤ}
    (A : BidegreeAssignment c r₀ e) (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (A.eulerCharSigns r hr).χ pq = (A.deg pq).negOnePow := (rfl)

end CategoryTheory.SpectralSequence.BidegreeAssignment
