/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
public import TauCeti.Algebra.Homology.EulerCharacteristic.HomologicalComplex
public import TauCeti.AlgebraicTopology.Cellular.Projective

import TauCeti.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Euler--Poincaré for cellular chains

For a relative CW complex `(X, A)` and a coefficient module `M` over a ring `k`, the cellular
chain group `Hₙ(Xⁿ, Xⁿ⁻¹; M)` is the direct sum of one copy of `M` for each `n`-cell
(`TauCeti.cellularChainGroupIso`), hence free or projective when `M` is
(`TauCeti.free_cellularChainGroup`, `TauCeti.moduleProjective_cellularChainGroup`).  This file
draws the numerical and finiteness consequences.

* The Euler characteristic of a relative CW complex is the alternating count of its cells
  (`TauCeti.cwEulerChar`).
* The cellular chain group is finitely generated when `M` is and there are finitely many `n`-cells
  (`TauCeti.finite_cellularChainGroup`). For free `M` it satisfies
  `finrank = #(n-cells) · finrank M` with no finiteness hypothesis
  (`TauCeti.finrank_cellularChainGroup`, `TauCeti.finrank_cellularChainComplex_X`); both sides are
  `0` in the infinite case. For finitely generated (not necessarily free) `M` over a ring
  satisfying the strong rank condition and rank--nullity, the same formula holds in any degree
  with finitely many cells (`TauCeti.finrank_cellularChainGroup_of_finite`,
  `TauCeti.finrank_cellularChainComplex_X_of_finite`).
* The Euler characteristic of the cellular chain complex is `finrank M · cwEulerChar C`, both for
  free coefficients over a ring with the strong rank condition with no finiteness hypothesis
  (`TauCeti.eulerChar_cellularChainComplex`), and for finitely generated coefficients over a ring
  with the strong rank condition and rank--nullity on a relative CW complex of finite type
  (`TauCeti.eulerChar_cellularChainComplex_of_finiteType`).
* Over a noetherian ring, the cellular homology in degree `n` of a complex with finitely many
  `n`-cells is finitely generated when `M` is (`TauCeti.finite_cellularHomology`).
* **Euler--Poincaré.**  Over any ring satisfying the strong rank condition and rank--nullity (such
  as a division ring or a commutative domain), for a finitely generated coefficient module `M` and
  a complex with finitely many cells through degree `n`, the alternating sum of the finranks of
  the cellular homology up to degree `n`, when there are no `(n + 1)`-cells, equals `finrank k M`
  times the alternating count of the cells of dimension at most `n`
  (`TauCeti.sum_range_finrank_cellularHomology`).  For a finite complex this is the equality of
  the homology Euler characteristic of the cellular chain complex with `finrank k M` times the
  alternating count of all cells, `finrank k M · cwEulerChar C`
  (`TauCeti.homologyEulerChar_cellularChainComplex`).

The statements concern the cellular chain complex itself; its identification with singular
homology is what turns them into statements about the space.  The coefficient ring `k` may live
in an arbitrary universe via `TauCeti.moduleCat_ab4OfSize`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology Topology.RelCWComplex DirectSum

universe w u

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The **Euler characteristic** of a relative CW complex `(C, D)`: the alternating count
`∑ₙ (-1)ⁿ · #(n-cells)` of its relative cells.  It is meant for finite complexes, where the sum has
finite support; for an absolute CW complex it is the Euler characteristic of `C`. -/
def cwEulerChar : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (cell C n)

theorem cwEulerChar_def : cwEulerChar C = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (cell C n) :=
  (rfl)

/-- The alternating cell count of a complex with no cells in dimensions `n ≥ N` is the finite sum
`∑_{n < N} (-1)ⁿ · #(n-cells)`. -/
theorem cwEulerChar_eq_sum_range {N : ℕ} (h : ∀ n, N ≤ n → IsEmpty (cell C n)) :
    cwEulerChar C = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * Nat.card (cell C n) :=
  finsum_eq_sum_of_support_subset _ fun n hn ↦ by
    by_contra hN
    have := h n (by simpa using hN)
    simp at hn

variable [T2Space X]

section Ring

variable {k : Type u} [Ring k] (M : ModuleCat.{w} k)

open scoped Classical in
/-- The cellular chain group in degree `n`, as a `k`-module, is the direct sum of one copy of `M`
for each `n`-cell. -/
private def cellularChainGroupLinearEquiv (n : ℕ) :
    (cellularChainGroup C M n : ModuleCat k) ≃ₗ[k] ⨁ _ : cell C n, M :=
  (cellularChainGroupIso C M n ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv

/-- With finitely generated coefficients, the cellular chain group in a degree with finitely many
cells is finitely generated. -/
instance finite_cellularChainGroup [Module.Finite k M] (n : ℕ) [Finite (cell C n)] :
    Module.Finite k (cellularChainGroup C M n : ModuleCat k) :=
  .equiv (cellularChainGroupLinearEquiv C M n).symm

/-- The degree-`i` term of the cellular chain complex is finitely generated when `M` is and there
are finitely many `i`-cells. -/
theorem finite_cellularChainComplex_X [Module.Finite k M] (i : ℕ) [Finite (cell C i)] :
    Module.Finite k ((cellularChainComplex C M).X i) := by
  rw [cellularChainComplex_X]
  infer_instance

/-- For free coefficients `M`, the cellular chain group in degree `n` satisfies
`finrank = Nat.card (cell C n) * finrank k M`. No finiteness is assumed: if there are infinitely
many `n`-cells or `M` is not finitely generated, both sides are `0` by the conventions for
`Module.finrank` and `Nat.card`. -/
theorem finrank_cellularChainGroup [StrongRankCondition k] [Module.Free k M] (n : ℕ) :
    finrank k (cellularChainGroup C M n : ModuleCat k) = Nat.card (cell C n) * finrank k M := by
  rw [(cellularChainGroupLinearEquiv C M n).finrank_eq, Module.finrank, rank_directSum,
    Cardinal.sum_const, Cardinal.toNat_mul, Cardinal.toNat_lift, Cardinal.toNat_lift,
    Module.finrank, Nat.card]

/-- For free coefficients `M`, the degree-`i` term of the cellular chain complex satisfies
`finrank = Nat.card (cell C i) * finrank k M`. No finiteness is assumed: if there are infinitely
many `i`-cells or `M` is not finitely generated, both sides are `0`. -/
theorem finrank_cellularChainComplex_X [StrongRankCondition k] [Module.Free k M] (i : ℕ) :
    finrank k ((cellularChainComplex C M).X i) = Nat.card (cell C i) * finrank k M := by
  rw [cellularChainComplex_X, finrank_cellularChainGroup]

/-- For free coefficients `M`, the Euler characteristic `∑ᶠ i, (-1)ⁱ · finrank k (Cᵢ)` of the
cellular chain complex is `finrank k M · cwEulerChar C`. No finiteness is assumed: both sides are
sums over all degrees with the `finsum` convention (an infinite support gives `0`), and it is the
expected identity when `M` is finitely generated and every degree has finitely many cells, with
finitely many nonempty degrees. -/
theorem eulerChar_cellularChainComplex [StrongRankCondition k] [Module.Free k M] :
    (cellularChainComplex C M).eulerChar =
      finrank k M * cwEulerChar C := by
  rw [ChainComplex.eulerChar_eq_finsum_finrank, cwEulerChar, mul_finsum]
  refine finsum_congr fun i ↦ ?_
  rw [finrank_cellularChainComplex_X]
  push_cast
  ring

/-- Over a noetherian ring, with finitely generated coefficients, the cellular homology in a degree
with finitely many cells is finitely generated. -/
theorem finite_cellularHomology [IsNoetherianRing k] [Module.Finite k M] (n : ℕ)
    [Finite (cell C n)] : Module.Finite k ((cellularChainComplex C M).homology n) :=
  have : Module.Finite k ((cellularChainComplex C M).sc n).X₂ := by
    rw [HomologicalComplex.shortComplexFunctor_obj_X₂, cellularChainComplex_X]
    infer_instance
  ((cellularChainComplex C M).sc n).finite_homology

end Ring

section RankNullity

variable {k : Type u} [Ring k] [StrongRankCondition k] [HasRankNullity.{w} k]
  (M : ModuleCat.{w} k) [Module.Finite k M]

/-- For finitely generated coefficients `M` over a ring satisfying the strong rank condition and
rank--nullity, if there are finitely many `n`-cells then the cellular chain group in degree `n`
satisfies `finrank = Nat.card (cell C n) * finrank k M`. -/
theorem finrank_cellularChainGroup_of_finite (n : ℕ) [Finite (cell C n)] :
    finrank k (cellularChainGroup C M n : ModuleCat k) = Nat.card (cell C n) * finrank k M := by
  let _ : Fintype (cell C n) := Fintype.ofFinite (cell C n)
  rw [(cellularChainGroupIso C M n).toLinearEquiv.finrank_eq, ModuleCat.finrank_sigma,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- For finitely generated coefficients `M` over a ring satisfying the strong rank condition and
rank--nullity, if there are finitely many `i`-cells then the degree-`i` term of the cellular chain
complex satisfies `finrank = Nat.card (cell C i) * finrank k M`. -/
theorem finrank_cellularChainComplex_X_of_finite (i : ℕ) [Finite (cell C i)] :
    finrank k ((cellularChainComplex C M).X i) = Nat.card (cell C i) * finrank k M := by
  rw [cellularChainComplex_X, finrank_cellularChainGroup_of_finite]

/-- For finitely generated coefficients `M` over a ring satisfying the strong rank condition and
rank--nullity, the Euler characteristic `∑ᶠ i, (-1)ⁱ · finrank k (Cᵢ)` of the cellular chain
complex of a relative CW complex of finite type (`RelCWComplex.FiniteType C`) is
`finrank k M · cwEulerChar C`. Both sides are `finsum`s over all degrees (an infinite support gives
`0`). -/
theorem eulerChar_cellularChainComplex_of_finiteType [RelCWComplex.FiniteType C] :
    (cellularChainComplex C M).eulerChar =
      finrank k M * cwEulerChar C := by
  rw [HomologicalComplex.eulerChar, GradedObject.eulerChar, cwEulerChar, mul_finsum]
  refine finsum_congr fun i ↦ ?_
  have := FiniteType.finite_cell (C := C) (D := D) i
  rw [finrank_cellularChainComplex_X_of_finite]
  simp only [ComplexShape.eulerCharSignsDownNat_χ, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  push_cast
  ring

/-- **Euler--Poincaré for cellular chains.**  For a relative CW complex with finitely many cells
through degree `n` and a finitely generated coefficient module `M` over a ring satisfying the
strong rank condition and rank--nullity, if there are no `(n + 1)`-cells, then the alternating sum
of the finranks of the cellular homology groups in degrees at most `n` is `finrank k M` times the
alternating count of the cells of dimension at most `n`. -/
theorem sum_range_finrank_cellularHomology {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : IsEmpty (cell C (n + 1))) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * finrank k ((cellularChainComplex C M).homology i) =
      finrank k M * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * Nat.card (cell C i) := by
  have hfinite' : ∀ i ≤ n, Module.Finite k ((cellularChainComplex C M).X i) :=
    fun i hi ↦
      have := hfinite i hi
      finite_cellularChainComplex_X C M i
  have hX : IsZero ((cellularChainComplex C M).X (n + 1)) := by
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C (n + 1) M
  have hsum := (cellularChainComplex C M).sum_range_finrank_X_eq_sum_range_finrank_homology
    hfinite' (hX.eq_of_src _ 0)
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have := hfinite i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [finrank_cellularChainComplex_X_of_finite]
  push_cast
  ring

/-- **Euler--Poincaré for a finite relative CW complex.**  The alternating sum of the finranks of
the cellular homology groups of a finite relative CW complex, with coefficients in a finitely
generated module `M` over a ring satisfying the strong rank condition and rank--nullity, is
`finrank k M` times the alternating count of its cells. -/
theorem homologyEulerChar_cellularChainComplex [RelCWComplex.Finite C] :
    (cellularChainComplex C M).homologyEulerChar =
      finrank k M * cwEulerChar C := by
  have (i : ℕ) : Module.Finite k ((cellularChainComplex C M).X i) :=
    have := FiniteType.finite_cell (C := C) (D := D) i
    finite_cellularChainComplex_X C M i
  rw [← HomologicalComplex.eulerChar_eq_homologyEulerChar (cellularChainComplex C M)
      (HomologicalComplex.finite_not_isZero_X_of_eventually_isZero _
        (by simpa [cellularChainComplex_X] using eventually_isZero_cellularChainGroup C M)),
    eulerChar_cellularChainComplex_of_finiteType]

end RankNullity

end TauCeti
