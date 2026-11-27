/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.FullColumns
public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.Basis
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal

/-!
# Full columns of standard bideterminants

Let `ν` be a Young diagram `μ` with `d` columns of the full height `N` prepended, both with at most
`N` rows, and let `x` be the `N × n` matrix of variables, `N ≤ n`. A semistandard tableau of shape
`ν` with entries smaller than `N` holds `0, …, N - 1` in each of these columns, so their minors
are all the minor `Δ` of `x` on all rows and the first `N` columns. The bideterminant of the
tableau is therefore `Δ ^ d` times the bideterminant of the tableau of shape `μ` obtained by
deleting the full columns (`TauCeti.BoundedSSYT.fullColumnsEquiv`).

## Main results

* `TauCeti.DualWeylModule.bideterminant_ssytFilling_eq_pow_mul`: full columns split off as a power
  of the leading maximal minor.

## References

* C. De Concini, D. Eisenbud, C. Procesi, *Young diagrams and determinantal varieties*,
  Invent. Math. **56** (1980), 129-165.
-/

public section

namespace TauCeti

open MvPolynomial Matrix Finset

namespace DualWeylModule

variable {R : Type*} [CommRing R] {N n d : ℕ} {μ ν : YoungDiagram}

/-- **Full columns split off as a power of the leading minor.** Let `ν` be `μ` with `d` columns of
the full height `N` prepended, both with at most `N` rows, and `N ≤ n`. The bideterminant of a
tableau `T` of shape `ν` with entries smaller than `N` is `Δ ^ d` times the bideterminant of the
tableau of shape `μ` obtained by deleting these columns, `Δ` the minor of the `N × n` matrix of
variables on all rows and the first `N` columns. -/
theorem bideterminant_ssytFilling_eq_pow_mul (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ i < N, ν.rowLen i = μ.rowLen i + d) (hN : N ≤ n) (T : BoundedSSYT N ν) :
    bideterminant R ν (hν.trans hN) (ssytFilling T) =
      mvPolynomialMinor R id (Fin.castLE hN) ^ d *
        bideterminant R μ (hμ.trans hN)
          (ssytFilling (BoundedSSYT.fullColumnsEquiv hμ hν h T)) := by
  have hK : ν.rowLen 0 ≤ d + μ.rowLen 0 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · rw [YoungDiagram.rowLen_eq_zero_iff.mpr hν]
      exact Nat.zero_le _
    · rw [h 0 hN0]
      omega
  rw [bideterminant_eq_prod_range R ν _ _ hK, Finset.prod_range_add,
    bideterminant_eq_prod_range R μ _ _ le_rfl]
  congr 1
  · -- The first `d` columns are full, and the tableau holds `0, …, N - 1` in each of them.
    calc ∏ j ∈ range d, columnMinor R ν (hν.trans hN) (ssytFilling T) j
        = ∏ _j ∈ range d, mvPolynomialMinor R id (Fin.castLE hN) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hc := YoungDiagram.colLen_eq_of_rowLen_eq_add hν h (Finset.mem_range.mp hj)
          rw [columnMinor_def]
          refine mvPolynomialMinor_castLE_congr hc (fun a => Fin.ext ?_) _ _
          have ha : (a : ℕ) < N := hc ▸ a.isLt
          have hc' : (N - 1, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
          simpa using BoundedSSYT.val_eq_of_mem_of_lt T hc' ha
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  · -- The remaining columns are those of `μ`.
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [columnMinor_def, columnMinor_def]
    refine mvPolynomialMinor_castLE_congr
      (by rw [add_comm]; exact YoungDiagram.colLen_add_of_rowLen_eq_add hμ hν h j)
      (fun a => Fin.ext ?_) _ _
    simp [add_comm]

end DualWeylModule

end TauCeti
