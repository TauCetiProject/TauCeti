/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Cellular incidence coefficients

The cellular chain groups with coefficients in a ring have bases indexed by the actual cells.
This file puts the cellular differential in those coordinates. Each boundary column is a
finitely supported function on the cells in the preceding dimension, even for an infinite CW
complex. The incidence coefficients reconstruct the differential, and consecutive columns
satisfy the finite-sum relation expressing that its square is zero.

The columns are also identified with the attaching maps: send the reduced fundamental class of
the boundary sphere through the attaching map, pass to skeletal relative homology, and take
cellular coordinates. This is the homological coefficient formula; identifying it with the
geometric degree of a sphere map obtained by collapsing the other cells is a separate result.
The bases use the disk and sphere generators of `cellularChainGroupIso`, including their signed
reduced degree-zero convention.

The coefficient ring and the ambient space lie in the same universe, as in Mathlib's exact
coproduct interface for modules. No finite-cell or finite-dimensional hypothesis is imposed.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the cellular boundary formula.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (R : Type w) [Ring R]

open scoped Classical in
/-- The cellular basis over `R`: the vector of a cell is the image of the fundamental class
of its characteristic disk pair. -/
def cellularChainBasis (n : ℕ) :
    Module.Basis (cell C n) R (cellularChainGroup C (ModuleCat.of R R) n : ModuleCat R) :=
  .ofRepr ((cellularChainGroupIso C (ModuleCat.of R R) n ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv.trans
      (finsuppLEquivDirectSum R R (cell C n)).symm)

open scoped Classical in
/-- The cellular basis coordinates are the coproduct coordinates of the characteristic cells. -/
lemma cellularChainBasis_repr (n : ℕ) :
    (cellularChainBasis C R n).repr =
      (cellularChainGroupIso C (ModuleCat.of R R) n ≪≫
        ModuleCat.coprodIsoDirectSum _).toLinearEquiv.trans
          (finsuppLEquivDirectSum R R (cell C n)).symm := (rfl)

/-- A cellular basis vector is the image of `1` in its cell's coproduct summand. -/
@[simp]
lemma cellularChainBasis_apply (n : ℕ) (j : cell C n) :
    cellularChainBasis C R n j =
      (cellularChainGroupIso C (ModuleCat.of R R) n).inv
        (Sigma.ι (fun _ : cell C n ↦ ModuleCat.of R R) j 1) := by
  classical
  apply (cellularChainBasis C R n).repr.injective
  rw [Module.Basis.repr_self, cellularChainBasis_repr]
  rw [LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, Iso.trans_hom,
    ModuleCat.comp_apply]
  simp only [Iso.inv_hom_id_apply,
    ModuleCat.ι_coprodIsoDirectSum_hom_apply (fun _ : cell C n ↦ ModuleCat.of R R) j,
    finsuppLEquivDirectSum_symm_lof]

/-- The boundary column of an `(n + 1)`-cell, with finite support on the `n`-cells. -/
def cellularBoundaryColumn (n : ℕ) (j : cell C (n + 1)) : cell C n →₀ R :=
  (cellularChainBasis C R n).repr
    (cellularDifferential C (ModuleCat.of R R) n (cellularChainBasis C R (n + 1) j))

/-- Boundary columns are the cellular coordinates of the differential on basis vectors. -/
lemma cellularBoundaryColumn_def (n : ℕ) (j : cell C (n + 1)) :
    cellularBoundaryColumn C R n j =
      (cellularChainBasis C R n).repr
        (cellularDifferential C (ModuleCat.of R R) n
          (cellularChainBasis C R (n + 1) j)) := (rfl)

/-- The incidence coefficient in row `i` and column `j` of the cellular differential. Over
`ℤ` these are the integral cellular incidence numbers. -/
def cellularIncidence (n : ℕ) (i : cell C n) (j : cell C (n + 1)) : R :=
  cellularBoundaryColumn C R n j i

/-- An incidence coefficient is the corresponding coordinate of the differential of a cell. -/
lemma cellularIncidence_def (n : ℕ) (i : cell C n) (j : cell C (n + 1)) :
    cellularIncidence C R n i j =
      (cellularChainBasis C R n).repr
        (cellularDifferential C (ModuleCat.of R R) n
          (cellularChainBasis C R (n + 1) j)) i := (rfl)

@[simp]
lemma cellularBoundaryColumn_apply (n : ℕ) (i : cell C n) (j : cell C (n + 1)) :
    cellularBoundaryColumn C R n j i = cellularIncidence C R n i j := (rfl)

/-- **The attaching-map formula in cellular coordinates.** A boundary column is obtained by
sending the reduced sphere generator through the attaching map and into skeletal relative
homology, then taking cellular coordinates. -/
lemma cellularBoundaryColumn_eq_attaching (n : ℕ) (j : cell C (n + 1)) :
    cellularBoundaryColumn C R n j =
      (cellularChainBasis C R n).repr
        (skeletonPairπ C (ModuleCat.of R R) n
          (SSet.homologyMap (TopCat.toSSet.map (cellAttachingMap C j)) (ModuleCat.of R R) n
            ((reducedSingularHomologyι (ModuleCat.of R R) n).app
              (TopCat.diskBoundary.{w} (n + 1))
                ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1)))) := by
  rw [cellularBoundaryColumn_def, cellularChainBasis_apply]
  congr 1
  exact ConcreteCategory.congr_hom
    (ι_cellularChainGroupIso_inv_comp_cellularDifferential C (ModuleCat.of R R) n j) 1

/-- The differential on a cell is the finite sum of its incidence coefficients times the
basis vectors of the preceding dimension. -/
lemma cellularDifferential_basis (n : ℕ) (j : cell C (n + 1)) :
    cellularDifferential C (ModuleCat.of R R) n (cellularChainBasis C R (n + 1) j) =
      (cellularBoundaryColumn C R n j).sum
        (fun i a ↦ a • cellularChainBasis C R n i) := by
  exact ((cellularChainBasis C R n).linearCombination_repr _).symm

/-- Cellular coordinates of the differential of an arbitrary chain are the finite linear
combination of its boundary columns. -/
lemma cellularChainBasis_repr_differential (n : ℕ)
    (x : (cellularChainGroup C (ModuleCat.of R R) (n + 1) : ModuleCat R)) :
    (cellularChainBasis C R n).repr (cellularDifferential C (ModuleCat.of R R) n x) =
      ((cellularChainBasis C R (n + 1)).repr x).sum
        (fun j a ↦ a • cellularBoundaryColumn C R n j) := by
  conv_lhs => rw [← (cellularChainBasis C R (n + 1)).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smul,
    cellularBoundaryColumn_def]

/-- Each coordinate of a cellular boundary is the finite sum of the source coordinates times
the corresponding incidence coefficients. -/
lemma cellularChainBasis_repr_differential_apply (n : ℕ)
    (x : (cellularChainGroup C (ModuleCat.of R R) (n + 1) : ModuleCat R)) (i : cell C n) :
    (cellularChainBasis C R n).repr (cellularDifferential C (ModuleCat.of R R) n x) i =
      ∑ j ∈ ((cellularChainBasis C R (n + 1)).repr x).support,
        (cellularChainBasis C R (n + 1)).repr x j * cellularIncidence C R n i j := by
  rw [cellularChainBasis_repr_differential]
  simp [Finsupp.sum]

/-- The cellular differential vanishes exactly when all its incidence coefficients vanish. -/
@[simp]
lemma cellularDifferential_eq_zero_iff (n : ℕ) :
    cellularDifferential C (ModuleCat.of R R) n = 0 ↔
      ∀ (i : cell C n) (j : cell C (n + 1)), cellularIncidence C R n i j = 0 := by
  constructor
  · intro h i j
    rw [← cellularBoundaryColumn_apply, cellularBoundaryColumn_def, h]
    simp
  · intro h
    apply ModuleCat.hom_ext
    apply (cellularChainBasis C R (n + 1)).ext
    intro j
    apply (cellularChainBasis C R n).repr.injective
    simp only [map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [← cellularBoundaryColumn_def]
    ext i
    exact h i j

/-- The finite-support column formula for `d² = 0`. -/
lemma cellularBoundaryColumn_sum_smul (n : ℕ) (j : cell C (n + 2)) :
    (cellularBoundaryColumn C R (n + 1) j).sum
      (fun i a ↦ a • cellularBoundaryColumn C R n i) = 0 := by
  rw [cellularBoundaryColumn_def, ← cellularChainBasis_repr_differential]
  have h := congrArg (fun f ↦ f.hom (cellularChainBasis C R (n + 2) j))
    (cellularDifferential_comp_cellularDifferential C (ModuleCat.of R R) n)
  exact (congrArg (cellularChainBasis C R n).repr h).trans (map_zero _)

/-- For each pair of cells two dimensions apart, the finite sum of the products of the two
intermediate incidence coefficients is zero. The order of multiplication also works over
noncommutative coefficient rings. -/
lemma sum_cellularIncidence_mul (n : ℕ) (k : cell C n) (j : cell C (n + 2)) :
    ∑ i ∈ (cellularBoundaryColumn C R (n + 1) j).support,
      cellularIncidence C R (n + 1) i j * cellularIncidence C R n k i = 0 := by
  have h := congrArg (fun f : cell C n →₀ R ↦ f k)
    (cellularBoundaryColumn_sum_smul C R n j)
  simpa [Finsupp.sum, Finsupp.sum_apply] using h

end TauCeti
