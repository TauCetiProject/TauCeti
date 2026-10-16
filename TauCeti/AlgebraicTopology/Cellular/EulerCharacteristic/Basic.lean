/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import TauCeti.Algebra.Homology.EulerCharacteristic.ChainComplex
public import TauCeti.AlgebraicTopology.Cellular.Coproduct

/-!
# Euler--Poincaré for cellular chains

For a relative CW complex `(X, A)` and a coefficient module `M` over a ring `k`, the cellular
chain group `Hₙ(Xⁿ, Xⁿ⁻¹; M)` is the direct sum of one copy of `M` for each `n`-cell
(`TauCeti.cellularChainGroupIso`).  This file draws the numerical and finiteness consequences.

* The Euler characteristic of a relative CW complex is the alternating count of its cells
  (`TauCeti.cwEulerChar`).
* The cellular chain group is free when `M` is, finitely generated when `M` is and there are
  finitely many `n`-cells, and then has rank `#(n-cells) · rank M`
  (`TauCeti.finrank_cellularChainGroup`).
* Over a noetherian ring, the cellular homology in degree `n` of a complex with finitely many
  `n`-cells is finitely generated when `M` is (`TauCeti.finite_cellularHomology`).
* **Euler--Poincaré.**  Over a division ring, for a finite-dimensional coefficient module `M` and
  a complex with finitely many cells through degree `n`, the alternating sum of the dimensions of
  the cellular homology up to degree `n`, when there are no `(n + 1)`-cells, equals `dim M` times
  the alternating count of the cells of dimension at most `n`
  (`TauCeti.sum_range_finrank_cellularHomology`).  For a finite complex this is the equality of
  the homology Euler characteristic of the cellular chain complex with `dim M` times the
  alternating count of all cells, `dim M · cwEulerChar C`
  (`TauCeti.homologyEulerChar_cellularChainComplex`).

The statements concern the cellular chain complex itself; its identification with singular
homology is what turns them into statements about the space.  The coefficient ring lives in the
universe of the space, where Mathlib provides the exactness of coproducts of modules that
`TauCeti.cellularChainGroupIso` needs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology Topology.RelCWComplex DirectSum

universe w

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

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

open scoped Classical in
/-- The cellular chain group in degree `n`, as a `k`-module, is the direct sum of one copy of `M`
for each `n`-cell. -/
private def cellularChainGroupLinearEquiv (n : ℕ) :
    (cellularChainGroup C M n : ModuleCat k) ≃ₗ[k] ⨁ _ : cell C n, M :=
  (cellularChainGroupIso C M n ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv

/-- With free coefficients, the cellular chain groups are free. -/
instance free_cellularChainGroup [Module.Free k M] (n : ℕ) :
    Module.Free k (cellularChainGroup C M n : ModuleCat k) :=
  .of_equiv (cellularChainGroupLinearEquiv C M n).symm

/-- With finitely generated coefficients, the cellular chain group in a degree with finitely many
cells is finitely generated. -/
instance finite_cellularChainGroup [Module.Finite k M] (n : ℕ) [Finite (cell C n)] :
    Module.Finite k (cellularChainGroup C M n : ModuleCat k) :=
  .equiv (cellularChainGroupLinearEquiv C M n).symm

/-- The rank of the cellular chain group in degree `n` is the number of `n`-cells times the rank
of the coefficient module. -/
theorem finrank_cellularChainGroup [StrongRankCondition k] [Module.Free k M] [Module.Finite k M]
    (n : ℕ) [Finite (cell C n)] :
    finrank k (cellularChainGroup C M n : ModuleCat k) = Nat.card (cell C n) * finrank k M := by
  have := Fintype.ofFinite (cell C n)
  rw [(cellularChainGroupLinearEquiv C M n).finrank_eq, finrank_directSum, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]

/-- Over a noetherian ring, with finitely generated coefficients, the cellular homology in a degree
with finitely many cells is finitely generated. -/
theorem finite_cellularHomology [IsNoetherianRing k] [Module.Finite k M] (n : ℕ)
    [Finite (cell C n)] : Module.Finite k ((cellularChainComplex C M).homology n) :=
  have : Module.Finite k ((cellularChainComplex C M).sc n).X₂ := by
    rw [HomologicalComplex.shortComplexFunctor_obj_X₂, cellularChainComplex_X]
    infer_instance
  ((cellularChainComplex C M).sc n).finite_homology

end Ring

variable {k : Type w} [DivisionRing k] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- The terms of the cellular chain complex of a complex of finite type are finite-dimensional. -/
private theorem finite_cellularChainComplex_X [FiniteType C] (i : ℕ) :
    Module.Finite k ((cellularChainComplex C M).X i) := by
  have := FiniteType.finite_cell (C := C) (D := D) i
  rw [cellularChainComplex_X]
  infer_instance

/-- The dimension of the degree-`i` term of the cellular chain complex. -/
private theorem finrank_cellularChainComplex_X (i : ℕ) [Finite (cell C i)] :
    finrank k ((cellularChainComplex C M).X i) = Nat.card (cell C i) * finrank k M := by
  rw [cellularChainComplex_X, finrank_cellularChainGroup]

/-- **Euler--Poincaré for cellular chains.**  For a relative CW complex with finitely many cells
through degree `n` and a finite-dimensional coefficient module `M`, if there are no `(n + 1)`-cells,
then the alternating sum of the dimensions of the cellular homology groups in degrees at most `n`
is `dim M` times the alternating count of the cells of dimension at most `n`. -/
theorem sum_range_finrank_cellularHomology {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : IsEmpty (cell C (n + 1))) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * finrank k ((cellularChainComplex C M).homology i) =
      finrank k M * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * Nat.card (cell C i) := by
  have hfinite' : ∀ i ≤ n, Module.Finite k ((cellularChainComplex C M).X i) := by
    intro i hi
    let _ := hfinite i hi
    rw [cellularChainComplex_X]
    infer_instance
  have hX : IsZero ((cellularChainComplex C M).X (n + 1)) := by
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C (n + 1) M
  rw [← (cellularChainComplex C M).sum_range_finrank_X_eq_sum_range_finrank_homology hfinite'
      (hX.eq_of_src _ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  let _ := hfinite i (by simp at hi; omega)
  rw [finrank_cellularChainComplex_X]
  push_cast
  ring

/-- The Euler characteristic of the cellular chain complex of a finite relative CW complex is
`dim M` times the alternating count of its cells. -/
theorem eulerChar_cellularChainComplex [RelCWComplex.Finite C] :
    (cellularChainComplex C M).eulerChar =
      finrank k M * cwEulerChar C := by
  obtain ⟨n, hn⟩ :=
    Filter.eventually_atTop.1 (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  have hcell : ∀ i ∉ Finset.range n, IsEmpty (cell C i) := fun i hi ↦
    hn i (by simpa using hi)
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ (Finset.range n)
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun i hi ↦
        have := hcell i hi
        ModuleCat.finrank_eq_zero_of_isZero
          (by rw [cellularChainComplex_X]; exact isZero_cellularChainGroup C i M)),
    cwEulerChar_eq_sum_range C hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let _ := FiniteType.finite_cell (C := C) (D := D) i
  rw [finrank_cellularChainComplex_X]
  simp only [ComplexShape.eulerCharSignsDownNat_χ, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  push_cast
  ring

/-- **Euler--Poincaré for a finite relative CW complex.**  The alternating sum of the dimensions
of the cellular homology groups of a finite relative CW complex, with coefficients in a
finite-dimensional module `M`, is `dim M` times the alternating count of its cells. -/
theorem homologyEulerChar_cellularChainComplex [RelCWComplex.Finite C] :
    (cellularChainComplex C M).homologyEulerChar =
      finrank k M * cwEulerChar C := by
  have := finite_cellularChainComplex_X C M
  rw [← ChainComplex.eulerChar_eq_homologyEulerChar _
      (by simpa only [cellularChainComplex_X] using eventually_isZero_cellularChainGroup C M),
    eulerChar_cellularChainComplex]

end TauCeti
