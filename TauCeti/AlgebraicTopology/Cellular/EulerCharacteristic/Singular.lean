/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Basic
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# Singular Euler--Poincaré for finite CW pairs

The cellular--singular comparison transfers finite generation and Euler--Poincaré from
cellular chains to relative singular homology. For a finite relative CW complex `(C, D)`
and a finite-dimensional coefficient module `M` over a division ring `k`, the alternating
sum of the dimensions of `Hₙ(C, D; M)` is `dim M` times the alternating count of relative
cells. The singular homology groups are finite-dimensional and vanish in all sufficiently
large degrees, so the sum has finite support.

Finite generation over a noetherian ring needs only finitely many cells in the degree in
question, in addition to the finite-dimensional CW structure required by the comparison.
Vanishing in a degree with no cells works for any coefficient object in an abelian category
with coproducts exact for the cell sets. The ordinary singular homology statements are
obtained from the quotient map for the empty subspace, not from a separate comparison.

The source is A. Hatcher, *Algebraic Topology*, Section 2.2, Theorems 2.35 and 2.44.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] [FiniteDimensional C]

section Vanishing

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A)

/-- Relative singular homology of a finite-dimensional CW pair vanishes in any degree
in which the relative CW structure has no cells. -/
theorem isZero_singularHomology_complexBasePair_of_isEmpty_cell (n : ℕ)
    [IsEmpty (cell C n)] : IsZero ((complexBasePair C).singularHomology R n) := by
  have hX : IsZero ((cellularChainComplex C R).X n) := by
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C n R
  exact (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology.of_iso
    (cellularSingularHomologyIso C R n).symm

/-- Relative singular homology of a finite-dimensional CW pair vanishes in all sufficiently
large degrees, without any finiteness assumption on the number of cells in each degree. -/
theorem eventually_isZero_singularHomology_complexBasePair :
    ∀ᶠ n in Filter.atTop, IsZero ((complexBasePair C).singularHomology R n) :=
  FiniteDimensional.eventually_isEmpty_cell.mono fun n hn ↦
    have : IsEmpty (cell C n) := hn
    isZero_singularHomology_complexBasePair_of_isEmpty_cell C R n

end Vanishing

section Ring

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- Over a noetherian ring, relative singular homology of a finite-dimensional CW pair is
finitely generated in each degree with finitely many cells, for finitely generated coefficients. -/
theorem finite_singularHomology_complexBasePair [IsNoetherianRing k] [Module.Finite k M]
    (n : ℕ) [Finite (cell C n)] :
    Module.Finite k ((complexBasePair C).singularHomology M n : ModuleCat k) :=
  have := finite_cellularHomology C M n
  Module.Finite.equiv (cellularSingularHomologyIso C M n).toLinearEquiv

end Ring

section DivisionRing

variable {k : Type w} [DivisionRing k] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- The truncated singular Euler--Poincaré formula. Only the cells through degree `n` need
be finite; absence of `(n + 1)`-cells makes the truncated alternating sums agree. -/
theorem sum_range_finrank_singularHomology_complexBasePair {n : ℕ}
    (hfinite : ∀ i ≤ n, Finite (cell C i)) (hn : IsEmpty (cell C (n + 1))) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * finrank k ((complexBasePair C).singularHomology M i : ModuleCat k) =
      finrank k M * ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * Nat.card (cell C i) := by
  simp_rw [← (cellularSingularHomologyIso C M _).toLinearEquiv.finrank_eq]
  exact sum_range_finrank_cellularHomology C M hfinite hn

omit [RelCWComplex.FiniteDimensional C] in
/-- **Euler--Poincaré for relative singular homology.** For a finite relative CW complex,
the alternating sum of the dimensions of relative singular homology is the coefficient
dimension times the alternating count of relative cells. Both sums have finite support. -/
theorem finsum_finrank_singularHomology_complexBasePair [RelCWComplex.Finite C] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k ((complexBasePair C).singularHomology M i : ModuleCat k) =
      finrank k M * ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * Nat.card (cell C i) := by
  simp_rw [← (cellularSingularHomologyIso C M _).toLinearEquiv.finrank_eq]
  simpa only [HomologicalComplex.homologyEulerChar, GradedObject.eulerChar,
    ComplexShape.eulerCharSignsDownNat_χ, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one] using homologyEulerChar_cellularChainComplex C M

end DivisionRing

end Relative

section Absolute

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

section Ring

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k)

/-- Over a noetherian ring, ordinary singular homology of a finite-dimensional CW complex is
finitely generated in each degree with finitely many cells, for finitely generated coefficients. -/
theorem finite_singularHomology_of_cwComplex [RelCWComplex.FiniteDimensional C]
    [IsNoetherianRing k] [Module.Finite k M] (n : ℕ) [Finite (cell C n)] :
    Module.Finite k
      (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) n).obj M).obj
        (TopCat.of C)) :=
  have := finite_singularHomology_complexBasePair C M n
  Module.Finite.equiv
    (asIso ((complexBasePair C).singularHomologyπ (C := ModuleCat.{w} k) M n)).symm.toLinearEquiv

end Ring

variable {k : Type w} [DivisionRing k] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- **Euler--Poincaré for ordinary singular homology.** For a finite CW complex with
finite-dimensional coefficients over a division ring, the alternating homology dimensions
equal the coefficient dimension times the alternating cell count. -/
theorem finsum_finrank_singularHomology_of_finite_cwComplex [RelCWComplex.Finite C] :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
        (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) i).obj M).obj
          (TopCat.of C)) =
      finrank k M * ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * Nat.card (cell C i) := by
  calc
    _ = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        finrank k ((complexBasePair C).singularHomology M i : ModuleCat k) :=
      finsum_congr fun i ↦ congrArg (fun d : ℕ ↦ (-1 : ℤ) ^ i * d)
        (asIso ((complexBasePair C).singularHomologyπ
          (C := ModuleCat.{w} k) M i)).toLinearEquiv.finrank_eq
    _ = _ := finsum_finrank_singularHomology_complexBasePair C M

end Absolute

end TauCeti
