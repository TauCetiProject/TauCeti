/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Homology.SpectralSequence.BidegreeAssignment

/-!
# Euler characteristic signs for spectral sequence pages

This file equips the standard cohomological and homological spectral sequence page shapes with the
alternating total-degree signs `pq ↦ (-1)^(p + q)` (`ComplexShape.EulerCharSigns`), and constructs
the alternating total-degree signs `pq ↦ (-1)^(A.deg pq)` induced on every page `r ≥ r₀` by a
`TauCeti.BidegreeAssignment` (`TauCeti.BidegreeAssignment.eulerCharSigns`).
-/

public section

namespace TauCeti.BidegreeAssignment

/-- The alternating signs `pq ↦ (-1)^(A.deg pq)` induced by a bidegree assignment on page `r`
(`r₀ ≤ r`). -/
@[expose, instance_reducible]
def eulerCharSigns {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    (A : BidegreeAssignment c r₀) (r : ℤ) (hr : r₀ ≤ r) : (c r).EulerCharSigns where
  χ pq := (A.deg pq).negOnePow
  χ_next h := by
    rw [A.deg_rel r hr _ _ h, Int.negOnePow_succ]

@[simp]
lemma eulerCharSigns_χ {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    (A : BidegreeAssignment c r₀) (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (A.eulerCharSigns r hr).χ pq = (A.deg pq).negOnePow := (rfl)

end TauCeti.BidegreeAssignment

namespace ComplexShape

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.up' (r, 1 - r)` of a cohomological spectral sequence. -/
instance eulerCharSignsUp'Cohomological (r : ℤ) :
    (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).EulerCharSigns :=
  (TauCeti.BidegreeAssignment.cohomological r).eulerCharSigns r le_rfl

@[simp↓]
lemma eulerCharSignsUp'Cohomological_χ (r : ℤ) (pq : ℤ × ℤ) :
    (up' (⟨r, 1 - r⟩ : ℤ × ℤ)).χ pq = (pq.1 + pq.2).negOnePow := by rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.up' (-r, r - 1)` of a homological spectral sequence. -/
instance eulerCharSignsUp'Homological (r : ℤ) :
    (up' (⟨-r, r - 1⟩ : ℤ × ℤ)).EulerCharSigns :=
  (TauCeti.BidegreeAssignment.homological r).eulerCharSigns r le_rfl

@[simp↓]
lemma eulerCharSignsUp'Homological_χ (r : ℤ) (pq : ℤ × ℤ) :
    (up' (⟨-r, r - 1⟩ : ℤ × ℤ)).χ pq = (pq.1 + pq.2).negOnePow := by
  -- Unfold `eulerCharSignsUp'Homological` to its `BidegreeAssignment.eulerCharSigns` instance.
  change @EulerCharSigns.χ _ _
    ((TauCeti.BidegreeAssignment.homological r).eulerCharSigns r le_rfl) pq = _
  rw [TauCeti.BidegreeAssignment.eulerCharSigns_χ (TauCeti.BidegreeAssignment.homological r) r
    le_rfl, TauCeti.BidegreeAssignment.homological_deg, sub_eq_add_neg, ← neg_add,
    Int.negOnePow_neg]

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceNat (r, 1 - r)` of a first-quadrant cohomological spectral
sequence. -/
instance eulerCharSignsSpectralSequenceNatCohomological (r : ℤ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).EulerCharSigns :=
  (TauCeti.BidegreeAssignment.cohomologicalNat r).eulerCharSigns r le_rfl

@[simp↓]
lemma eulerCharSignsSpectralSequenceNatCohomological_χ (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat ⟨r, 1 - r⟩).χ pq = ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow := by rfl

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceNat (-r, r - 1)` of a first-quadrant homological spectral
sequence. -/
instance eulerCharSignsSpectralSequenceNatHomological (r : ℤ) :
    (spectralSequenceNat ⟨-r, r - 1⟩).EulerCharSigns :=
  (TauCeti.BidegreeAssignment.homologicalNat r).eulerCharSigns r le_rfl

@[simp↓]
lemma eulerCharSignsSpectralSequenceNatHomological_χ (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat ⟨-r, r - 1⟩).χ pq = ((pq.1 : ℤ) + (pq.2 : ℤ)).negOnePow := by
  -- Unfold `eulerCharSignsSpectralSequenceNatHomological` to `BidegreeAssignment.eulerCharSigns`.
  change @EulerCharSigns.χ _ _
    ((TauCeti.BidegreeAssignment.homologicalNat r).eulerCharSigns r le_rfl) pq = _
  rw [TauCeti.BidegreeAssignment.eulerCharSigns_χ
      (TauCeti.BidegreeAssignment.homologicalNat r) r le_rfl,
    TauCeti.BidegreeAssignment.homologicalNat_deg, sub_eq_add_neg, ← neg_add, Int.negOnePow_neg]

/-- Alternating total-degree signs `(p, q) ↦ (-1)^(p + q)` for the `r`th page shape
`ComplexShape.spectralSequenceFin l (r, 1 - r)` of a cohomological spectral sequence on `l`
rows. -/
instance eulerCharSignsSpectralSequenceFinCohomological (l : ℕ) (r : ℤ) :
    (spectralSequenceFin l ⟨r, 1 - r⟩).EulerCharSigns :=
  (TauCeti.BidegreeAssignment.cohomologicalFin l r).eulerCharSigns r le_rfl

@[simp↓]
lemma eulerCharSignsSpectralSequenceFinCohomological_χ (l : ℕ) (r : ℤ) (pq : ℤ × Fin l) :
    (spectralSequenceFin l ⟨r, 1 - r⟩).χ pq = (pq.1 + (pq.2.val : ℤ)).negOnePow := by rfl

end ComplexShape
