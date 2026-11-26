/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Comatrix
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Covector commutators of quantum minors

A covector component with index `c` commutes with a quantum minor unless the column tuple
contains `c`. If it occurs once, the commutator deletes that column and contracts the signed
cofactors with the covector on the right. This is the cofactor rule used when a quantum minor
is bordered by a covector. The normalization is that of L. Alpöge's covector commutator in
`Formalism/HermitianCurvature/StatementQr.lean`.
-/

public section

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

/-- A covector component whose index is absent from the column tuple commutes with the minor. -/
theorem quantumMinor_lie_covector_of_notMem_range (E : Matrix ι ι A) (u : K)
    (a b : Fin n → ι) (η : ι → A) {c : ι} (hc : c ∉ Set.range b)
    (hη : ∀ i j, ⁅E (a i) (b j), η c⁆ = if b j = c then η (a i) else 0) :
    ⁅E.quantumMinor u a b, η c⁆ = 0 := by
  apply commute_iff_lie_eq.mp (E.commute_quantumMinor u a b fun i j ↦ ?_)
  have hne : b j ≠ c := fun h ↦ hc ⟨j, h⟩
  exact commute_iff_lie_eq.mpr (by simpa [hne] using hη i j)

/-- If the index of a covector component occurs only at column `k`, its commutator with the
minor is the signed cofactor expansion along `k`, with the covector on the right. Neither
injectivity of the row tuple nor distinctness of any of the other columns is required. -/
theorem quantumMinor_lie_covector (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations) (u : K)
    (a b : Fin (n + 1) → ι) (η : ι → A) (k : Fin (n + 1))
    (hb : ∀ j, b j = b k → j = k)
    (hη : ∀ i j, ⁅E (a i) (b j), η (b k)⁆ = if b j = b k then η (a i) else 0) :
    ⁅E.quantumMinor u a b, η (b k)⁆ =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (k.val + i.val) •
        (E.quantumMinor u (i.removeNth a) (k.removeNth b) * η (a i)) := by
  -- Put the only entry that can contribute to the bracket on the right of each cofactor.
  have hdet := E.quantumMinor_comatrix hE u a b k k
  rw [ite_eq_left rfl] at hdet
  rw [← hdet, sum_lie (L := A) (M := A)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [zsmul_lie (L := A) (M := A)]
  congr 1
  have hC : Commute (E.quantumMinor u (i.removeNth a) (k.removeNth b)) (η (b k)) := by
    apply E.commute_quantumMinor
    intro r s
    have hne : b (k.succAbove s) ≠ b k := fun h ↦ k.succAbove_ne s (hb _ h)
    apply commute_iff_lie_eq.mpr
    simpa [Fin.removeNth, hne] using hη (i.succAbove r) (k.succAbove s)
  have hscalar :
      ⁅(if a i = b k then algebraMap K A (u - (n : K)) else 0), η (b k)⁆ = 0 := by
    apply commute_iff_lie_eq.mp
    split_ifs
    · exact Algebra.commutes _ _
    · exact Commute.zero_left _
  have hentry :
      ⁅(if a i = b k then algebraMap K A (u - (n : K)) else 0) + E (a i) (b k), η (b k)⁆ =
        η (a i) := by
    rw [add_lie (L := A) (M := A), hscalar, hη i k, ite_eq_left rfl, zero_add]
  rw [← hentry]
  simp only [Ring.lie_def, mul_sub, ← mul_assoc, hC.eq]

end Matrix
