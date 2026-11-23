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
# Homology of a CW complex in a degree without neighbouring cells

Let `(C, D)` be a relative CW complex and `n` a degree such that, of the dimensions `n` and
`n + 1`, one carries no cells, and likewise of `n - 1` and `n` when `n ≥ 1`. Then both cellular
differentials at `Cₙ(C, D; R)` vanish, since one end of each is zero
(`TauCeti.cellularChainComplex_d_eq_zero_of_isEmpty_or`), so cellular homology in degree `n` is
the cellular chain group, a coproduct of one copy of the coefficients `R` for each `n`-cell
(`TauCeti.cellularHomologyIsoSigma`). This is the *lacunary principle* for CW complexes: in a degree
whose neighbouring dimensions carry no cells (or which carries none itself), homology is free on the
`n`-cells, with coefficients in any abelian category whose coproducts indexed by the `n`-cells are
exact (automatic for finitely many `n`-cells), integral coefficients included.

Through the cellular–singular comparison the same holds for the singular homology of a space `Y`
homotopy equivalent to an absolute CW complex `C`
(`ContinuousMap.HomotopyEquiv.singularHomologyIsoSigma`), for instance of a manifold through the
CW model of a Morse function on it: `Hₙ(Y; R) ≅ ∐_{n-cells} R`. This needs coproducts indexed by
the cells of every dimension to be exact, and the `(n + 1)`-skeleton comparison of `C` to induce an
isomorphism on `Hₙ`, as it does when `C` is finite-dimensional or sequential colimits in `A` are
exact. The complex projective spaces, with one cell in each even dimension, are the basic example.

## Main declarations

* `TauCeti.cellularChainComplex_d_eq_zero_of_isEmpty_or`: a cellular differential vanishes when
  its source or its target dimension carries no cells.
* `TauCeti.cellularHomologyIsoSigma`: cellular homology in a degree without neighbouring cells is
  the coproduct of one copy of `R` for each cell of that degree.
* `ContinuousMap.HomotopyEquiv.singularHomologyIsoSigma`: the same for the singular homology of a
  space homotopy equivalent to a CW complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.35 and Example 2.36 (the lacunary principle in the cellular computation of
  the homology of complex projective space).
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **A cellular differential between a dimension without cells and any other vanishes.** If there
are no `i`-cells or no `j`-cells, the differential `Cᵢ(C, D; R) ⟶ Cⱼ(C, D; R)` of the cellular chain
complex is zero, since its source or its target is the zero object. -/
theorem cellularChainComplex_d_eq_zero_of_isEmpty_or {i j : ℕ}
    (h : IsEmpty (cell C i) ∨ IsEmpty (cell C j)) : (cellularChainComplex C R).d i j = 0 := by
  have hX (k : ℕ) [IsEmpty (cell C k)] : IsZero ((cellularChainComplex C R).X k) := by
    rw [cellularChainComplex_X]
    exact isZero_cellularChainGroup C k R
  rcases h with h | h
  · exact (hX i).eq_of_src _ _
  · exact (hX j).eq_of_tgt _ _

/-- **The lacunary principle for cellular homology.** If of the dimensions `n` and `n + 1` one
carries no cells, and likewise of `m` and `n` whenever `n = m + 1`, then the cellular homology
`Hₙ` of a relative CW complex is the coproduct of one copy of the coefficients `R` for each
`n`-cell: both cellular differentials at `Cₙ` vanish. -/
def cellularHomologyIsoSigma (n : ℕ) [HasExactColimitsOfShape (Discrete (cell C n)) A]
    (hsucc : IsEmpty (cell C n) ∨ IsEmpty (cell C (n + 1)))
    (hpred : ∀ m, m + 1 = n → IsEmpty (cell C m) ∨ IsEmpty (cell C n)) :
    (cellularChainComplex C R).homology n ≅ ∐ fun _ : cell C n ↦ R :=
  ((cellularChainComplex C R).XIsoHomologyOfDEqZero n
      (cellularChainComplex_d_eq_zero_of_isEmpty_or C R <| by
        rw [ChainComplex.prev]
        exact hsucc.symm)
      (by
        -- The only differential out of degree `n` goes to degree `n - 1`, when `n ≥ 1`.
        by_cases hrel : (ComplexShape.down ℕ).Rel n ((ComplexShape.down ℕ).next n)
        · exact cellularChainComplex_d_eq_zero_of_isEmpty_or C R (hpred _ hrel).symm
        · exact (cellularChainComplex C R).shape _ _ hrel)).symm ≪≫
    eqToIso (cellularChainComplex_X C R n) ≪≫ cellularChainGroupIso C R n

/-- The isomorphism `TauCeti.cellularHomologyIsoSigma` sends the class of a cellular cycle to the
cycle itself, read in the coproduct through `TauCeti.cellularChainGroupIso`. -/
@[reassoc (attr := simp)]
lemma homologyπ_comp_cellularHomologyIsoSigma_hom (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C n)) A]
    (hsucc : IsEmpty (cell C n) ∨ IsEmpty (cell C (n + 1)))
    (hpred : ∀ m, m + 1 = n → IsEmpty (cell C m) ∨ IsEmpty (cell C n)) :
    (cellularChainComplex C R).homologyπ n ≫ (cellularHomologyIsoSigma C R n hsucc hpred).hom =
      (cellularChainComplex C R).iCycles n ≫ eqToHom (cellularChainComplex_X C R n) ≫
        (cellularChainGroupIso C R n).hom := by
  simp [cellularHomologyIsoSigma]

end Relative

end TauCeti

namespace ContinuousMap.HomotopyEquiv

open TauCeti

variable {Y X : Type w} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C] (e : ContinuousMap.HomotopyEquiv Y C)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The lacunary principle for a CW model.** Let `Y` be homotopy equivalent to a CW complex `C`.
If of the dimensions `n` and `n + 1` one carries no cells of `C`, and likewise of `m` and `n`
whenever `n = m + 1`, then `Hₙ(Y; R)` is the coproduct of one copy of the coefficients `R` for each
`n`-cell of `C`. The `(n + 1)`-skeleton comparison must induce an isomorphism on `Hₙ`, as it does
for every finite-dimensional `C` and, when sequential colimits are exact in `A`, for every `C`. -/
def singularHomologyIsoSigma (n : ℕ) [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap (skeletonBasePairToComplex C (n + 1))
      R n)]
    (hsucc : IsEmpty (cell C n) ∨ IsEmpty (cell C (n + 1)))
    (hpred : ∀ m, m + 1 = n → IsEmpty (cell C m) ∨ IsEmpty (cell C n)) :
    ((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of Y) ≅
      ∐ fun _ : cell C n ↦ R :=
  e.singularHomologyIso R n ≪≫ (cellularSingularHomologyIsoOfCWComplex C R n).symm ≪≫
    cellularHomologyIsoSigma C R n hsucc hpred

/-- The isomorphism `ContinuousMap.HomotopyEquiv.singularHomologyIsoSigma` is the homotopy
invariance isomorphism, followed by the cellular–singular comparison and the cellular lacunary
isomorphism `TauCeti.cellularHomologyIsoSigma`. -/
@[reassoc]
lemma singularHomologyIsoSigma_hom (n : ℕ) [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A]
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap (skeletonBasePairToComplex C (n + 1))
      R n)]
    (hsucc : IsEmpty (cell C n) ∨ IsEmpty (cell C (n + 1)))
    (hpred : ∀ m, m + 1 = n → IsEmpty (cell C m) ∨ IsEmpty (cell C n)) :
    (e.singularHomologyIsoSigma R n hsucc hpred).hom =
      (e.singularHomologyIso R n).hom ≫ (cellularSingularHomologyIsoOfCWComplex C R n).inv ≫
        (cellularHomologyIsoSigma C R n hsucc hpred).hom := by
  simp only [singularHomologyIsoSigma, Iso.trans_hom, Iso.symm_hom]

end ContinuousMap.HomotopyEquiv
