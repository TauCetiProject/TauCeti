/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CharPowerSeries.Basic

/-!
# Principal-minor series under diagonal intertwining

If `A i j * d j = d i * B i j` and every `d i` is regular, corresponding principal
minors of `A` and `B` agree. Consequently their fixed-cardinality minor families have the
same summability, and their principal-minor coefficients and power series are equal.

This applies to matrices on arbitrary index types over commutative topological rings,
including rings with zero divisors. The diagonal entries need not be units. In particular,
the result can compare Fredholm determinants through a diagonal map without a bounded
inverse. It makes no assertion about bounded operators or equality of spectra.

The series equality holds even without summability, since the summands agree termwise.
The summability equivalence allows convergence established for one matrix to pass to the
other, so that both series represent the convergent principal-minor sums.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5, for the principal-minor determinant.
-/

public section

namespace Matrix

variable {ι R : Type*} [DecidableEq ι] [CommRing R] [TopologicalSpace R]
  {A B : Matrix ι ι R} {d : ι → R}

/-- Regular diagonal intertwining preserves summability of the principal minors of each
fixed cardinality. Thus convergence need only be checked on one of the two matrices. -/
theorem summable_principalMinor_iff_of_diagonal_intertwining
    (hd : ∀ i, IsRegular (d i)) (h : ∀ i j, A i j * d j = d i * B i j) (n : ℕ) :
    (Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s) ↔
      Summable fun s : {s : Finset ι // s.card = n} ↦ B.principalMinor s := by
  have hminor (s : Finset ι) : A.principalMinor s = B.principalMinor s :=
    principalMinor_eq_of_diagonal_intertwining s (fun i ↦ hd i) (fun i j ↦ h i j)
  simp_rw [hminor]

/-- Regular diagonal intertwining preserves every coefficient of the principal-minor
series. No division by a diagonal entry or convergence assumption is required. -/
theorem charCoeff_eq_of_diagonal_intertwining
    (hd : ∀ i, IsRegular (d i)) (h : ∀ i j, A i j * d j = d i * B i j) (n : ℕ) :
    A.charCoeff n = B.charCoeff n := by
  rw [charCoeff_def, charCoeff_def]
  congr 1
  exact tsum_congr fun s ↦
    principalMinor_eq_of_diagonal_intertwining s.1 (fun i ↦ hd i) (fun i j ↦ h i j)

/-- Regular diagonal intertwining preserves the principal-minor power series. When the
minor sums converge, this identifies their Fredholm determinants without requiring the
diagonal map to have a bounded inverse. -/
theorem charPowerSeries_eq_of_diagonal_intertwining
    (hd : ∀ i, IsRegular (d i)) (h : ∀ i j, A i j * d j = d i * B i j) :
    A.charPowerSeries = B.charPowerSeries := by
  ext n
  simpa only [coeff_charPowerSeries] using charCoeff_eq_of_diagonal_intertwining hd h n

end Matrix
