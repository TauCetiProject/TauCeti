/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.Coproduct
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Homology of a CW complex where the cellular differentials vanish

Let `(C, D)` be a relative CW complex. A cellular differential `Cₙ₊₁(C, D; R) ⟶ Cₙ(C, D; R)`
vanishes as soon as one of its two chain groups does, that is when there are no `n`-cells or no
`(n + 1)`-cells (`TauCeti.cellularChainComplex_d_eq_zero_of_isEmpty_cell`). So if each of the two
differentials `Cₙ₊₁ ⟶ Cₙ` and `Cₙ ⟶ Cₙ₋₁` joins a degree without cells, for instance when `C` has
no cells in the degrees `n - 1` and `n + 1`, the cellular homology in degree `n` is the cellular
chain group (`HomologicalComplex.XIsoHomologyOfDEqZero`), a coproduct of one copy of `R` for each
`n`-cell (`TauCeti.cellularChainGroupIso`).

For an absolute CW complex the cellular–singular comparison turns this into a computation of
singular homology: `Hₙ(C; R) ≅ ∐_{n-cells} R` (`TauCeti.singularHomologyIsoSigmaOfIsEmptyCell`),
and the same holds for every space homotopy equivalent to `C`
(`ContinuousMap.HomotopyEquiv.singularHomologyIsoSigmaOfIsEmptyCell`). This is the cellular form
of the lacunary principle: a complex with no cells in any two consecutive dimensions, such as
complex projective space with its cells in even dimensions, has in every degree the free homology
on its cells of that dimension.

## Main declarations

* `TauCeti.cellularChainComplex_d_eq_zero_of_isEmpty_cell`: the cellular differential out of
  degree `n + 1` vanishes when there are no `n`-cells or no `(n + 1)`-cells.
* `TauCeti.singularHomologyIsoSigmaOfIsEmptyCell`: when both cellular differentials at degree `n`
  join a degree without cells, `Hₙ(C; R)` is the coproduct of one copy of `R` for each `n`-cell.
* `ContinuousMap.HomotopyEquiv.singularHomologyIsoSigmaOfIsEmptyCell`: the same for a space
  homotopy equivalent to a CW complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.35 and the examples following it.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **A cellular differential next to a degree without cells vanishes.** The differential
`Cₙ₊₁(C, D; R) ⟶ Cₙ(C, D; R)` of the cellular chain complex is zero when there are no `n`-cells or
no `(n + 1)`-cells, since one of the two chain groups is then zero. -/
theorem cellularChainComplex_d_eq_zero_of_isEmpty_cell (n : ℕ)
    (h : IsEmpty (cell C n) ∨ IsEmpty (cell C (n + 1))) :
    (cellularChainComplex C R).d (n + 1) n = 0 := by
  rcases h with h | h
  · have hX : IsZero ((cellularChainComplex C R).X n) := by
      rw [cellularChainComplex_X]
      exact isZero_cellularChainGroup C n R
    exact hX.eq_of_tgt _ _
  · have hX : IsZero ((cellularChainComplex C R).X (n + 1)) := by
      rw [cellularChainComplex_X]
      exact isZero_cellularChainGroup C (n + 1) R
    exact hX.eq_of_src _ _

/-- If each of the two cellular differentials at degree `n` joins a degree without cells, every
cellular differential into or out of degree `n` vanishes. -/
private theorem cellularChainComplex_d_eq_zero_of_lacunary (n : ℕ)
    (h : ∀ m, m + 1 = n ∨ m = n → IsEmpty (cell C m) ∨ IsEmpty (cell C (m + 1))) {i j : ℕ}
    (hij : i = n ∨ j = n) : (cellularChainComplex C R).d i j = 0 := by
  by_cases hrel : (ComplexShape.down ℕ).Rel i j
  · -- In `ComplexShape.down ℕ` the relation `Rel i j` says `j + 1 = i`.
    obtain rfl : i = j + 1 := hrel.symm
    exact cellularChainComplex_d_eq_zero_of_isEmpty_cell C R j (h j hij)
  · exact (cellularChainComplex C R).shape i j hrel

end Relative

section Absolute

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- **Singular homology where the cellular differentials vanish.** If each of the two cellular
differentials at degree `n` of the CW complex `C` joins a degree without cells, for instance when
`C` has no cells in the degrees `n - 1` and `n + 1`, then `Hₙ(C; R)` is the coproduct of one copy
of `R` for each `n`-cell. As for the cellular–singular comparison
`TauCeti.cellularSingularHomologyIsoOfCWComplex`, the inclusion of the `(n + 1)`-skeleton must
induce an isomorphism on `Hₙ`, which holds for every finite-dimensional complex. -/
def singularHomologyIsoSigmaOfIsEmptyCell (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)]
    (h : ∀ m, m + 1 = n ∨ m = n → IsEmpty (cell C m) ∨ IsEmpty (cell C (m + 1))) :
    ((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of C) ≅
      ∐ fun _ : cell C n ↦ R :=
  (cellularSingularHomologyIsoOfCWComplex C R n).symm ≪≫
    ((cellularChainComplex C R).XIsoHomologyOfDEqZero n
      (cellularChainComplex_d_eq_zero_of_lacunary C R n h (.inr rfl))
      (cellularChainComplex_d_eq_zero_of_lacunary C R n h (.inl rfl))).symm ≪≫
    eqToIso (cellularChainComplex_X C R n) ≪≫ cellularChainGroupIso C R n

end Absolute

end TauCeti

namespace ContinuousMap.HomotopyEquiv

open TauCeti

variable {Y X : Type w} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C] (e : ContinuousMap.HomotopyEquiv Y C)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]

/-- **Singular homology of a CW model where the cellular differentials vanish.** If `Y` is
homotopy equivalent to a CW complex `C` each of whose two cellular differentials at degree `n` joins
a degree without cells, then `Hₙ(Y; R)` is the coproduct of one copy of `R` for each `n`-cell of
`C`, provided the inclusion of the `(n + 1)`-skeleton of `C` induces an isomorphism on `Hₙ`, as it
does for every finite-dimensional complex. -/
def singularHomologyIsoSigmaOfIsEmptyCell (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)]
    (h : ∀ m, m + 1 = n ∨ m = n → IsEmpty (cell C m) ∨ IsEmpty (cell C (m + 1))) :
    ((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of Y) ≅
      ∐ fun _ : cell C n ↦ R :=
  e.singularHomologyIso R n ≪≫ TauCeti.singularHomologyIsoSigmaOfIsEmptyCell C R n h

end ContinuousMap.HomotopyEquiv
