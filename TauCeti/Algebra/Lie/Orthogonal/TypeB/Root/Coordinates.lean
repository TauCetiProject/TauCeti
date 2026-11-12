/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Block
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Coordinates
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.GeneratorRelations
import Mathlib.LinearAlgebra.Pi

/-!
# Native matrix root coordinates for the split odd orthogonal Lie algebra

The two short-root families, all difference-root matrices (including the individual diagonal
matrices), and the positive and negative sum-root families form a module basis of the split
odd orthogonal Lie algebra. Coordinates read independent matrix entries, and reconstruction
uses no division by two. The only coefficient-ring requirement is injectivity of doubling.

The construction composes `LieAlgebra.Orthogonal.typeB.blockEquiv` with the even orthogonal
coordinates `TauCeti.TypeDStd.rootEntryEquiv`. The negative sum-root family retains the reversed
indices of that basis. The numbered simple root vectors are basis members; the simple coroots
are explicit combinations of the individual diagonal members, not those members themselves.
In positive rank this matters over the integers: the simple coroots have diagonal index two.
These coordinates support matrix comparisons for fixed Lie algebras of diagram automorphisms.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Plate II.
* V. G. Kac, *Infinite Dimensional Lie Algebras*, §7.9.
-/

public section

namespace TauCeti.TypeBStd

open LieAlgebra.Orthogonal

variable {R ι : Type*} [CommRing R] [LinearOrder ι] [Fintype ι]

/-- Short positive and negative roots, followed by the even orthogonal entry indices. -/
abbrev RootEntryIndex (ι : Type*) [LT ι] := ι ⊕ (ι ⊕ TypeDStd.RootEntryIndex ι)

/-- Independent matrix-entry coordinates on the split odd orthogonal Lie algebra.
Doubling need only be injective; two need not be a unit. -/
def rootEntryEquiv (h2 : IsRegular (2 : R)) :
    typeB ι R ≃ₗ[R] (RootEntryIndex ι → R) :=
  (typeB.blockEquiv h2).trans
    (((LinearEquiv.refl R (ι → R)).prodCongr
      (((LinearEquiv.refl R (ι → R)).prodCongr
        (TypeDStd.rootEntryEquiv (fun x hx => h2.left (by simpa [two_mul] using hx)))).trans
        (LinearEquiv.sumArrowLequivProdArrow ι (TypeDStd.RootEntryIndex ι) R R).symm)).trans
      (LinearEquiv.sumArrowLequivProdArrow ι (ι ⊕ TypeDStd.RootEntryIndex ι) R R).symm)

/-- Positive short-root coordinates negate the last part of the anisotropic row. -/
@[simp] theorem rootEntryEquiv_apply_inl (h2 : IsRegular (2 : R))
    (X : typeB ι R) (i : ι) :
    rootEntryEquiv h2 X (.inl i) = -X.val (.inl ()) (.inr (.inr i)) := by
  simp [rootEntryEquiv]

/-- Negative short-root coordinates read the first part of the anisotropic row. -/
@[simp] theorem rootEntryEquiv_apply_inr_inl (h2 : IsRegular (2 : R))
    (X : typeB ι R) (i : ι) :
    rootEntryEquiv h2 X (.inr (.inl i)) = X.val (.inl ()) (.inr (.inl i)) := by
  simp [rootEntryEquiv]

/-- The remaining coordinates are precisely the even orthogonal block coordinates. -/
@[simp] theorem rootEntryEquiv_apply_inr_inr (h2 : IsRegular (2 : R))
    (X : typeB ι R) (p : TypeDStd.RootEntryIndex ι) :
    rootEntryEquiv h2 X (.inr (.inr p)) =
      TypeDStd.rootEntryEquiv (fun x hx => h2.left (by simpa [two_mul] using hx))
        (typeB.toTypeD X) p := by
  simp [rootEntryEquiv]

/-- Reconstruct a matrix by its short-root coordinates and its even orthogonal block. -/
theorem rootEntryEquiv_symm_apply (h2 : IsRegular (2 : R)) (a : RootEntryIndex ι → R) :
    (rootEntryEquiv h2).symm a =
      (∑ i, a (.inl i) • typeBShortRootGenerator i) +
      (∑ i, a (.inr (.inl i)) • typeBShortNegativeRootGenerator i) +
      typeB.ofTypeD ((TypeDStd.rootEntryEquiv
        (fun x hx => h2.left (by simpa [two_mul] using hx))).symm
          (fun p => a (.inr (.inr p)))) := by
  simp only [rootEntryEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, typeB.blockEquiv_symm_apply]
  congr 2

/-- A full matrix root basis, with individual hyperbolic diagonals as the Cartan members. -/
noncomputable def rootEntryBasis (h2 : IsRegular (2 : R)) :
    Module.Basis (RootEntryIndex ι) R (typeB ι R) :=
  Module.Basis.ofEquivFun (rootEntryEquiv h2)

/-- Basis coordinates are the independent matrix entries. -/
@[simp] theorem rootEntryBasis_repr (h2 : IsRegular (2 : R))
    (X : typeB ι R) (p : RootEntryIndex ι) :
    (rootEntryBasis h2).repr X p = rootEntryEquiv h2 X p :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

/-- The first basis family is the positive short-root family. -/
@[simp] theorem rootEntryBasis_inl (h2 : IsRegular (2 : R)) (i : ι) :
    rootEntryBasis h2 (.inl i) = typeBShortRootGenerator i := by
  classical
  apply (rootEntryEquiv h2).injective
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  have h := typeB.blockEquiv_shortRootGenerator h2 i
  ext (j | (j | p)) <;> simp [rootEntryEquiv, h, Pi.single_apply]

/-- The second basis family is the negative short-root family. -/
@[simp] theorem rootEntryBasis_inr_inl (h2 : IsRegular (2 : R)) (i : ι) :
    rootEntryBasis h2 (.inr (.inl i)) = typeBShortNegativeRootGenerator i := by
  classical
  apply (rootEntryEquiv h2).injective
  rw [rootEntryBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  have h := typeB.blockEquiv_shortNegativeRootGenerator h2 i
  ext (j | (j | p)) <;> simp [rootEntryEquiv, h, Pi.single_apply]

private theorem rootEntryBasis_inr_inr (h2 : IsRegular (2 : R))
    (p : TypeDStd.RootEntryIndex ι) :
    rootEntryBasis h2 (.inr (.inr p)) =
      typeB.ofTypeD (TypeDStd.rootEntryBasis
        (fun x hx => h2.left (by simpa [two_mul] using hx)) p) := by
  classical
  apply (rootEntryEquiv h2).injective
  simp only [rootEntryBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  ext (i | (i | q)) <;>
    simp [rootEntryEquiv, ← TypeDStd.rootEntryBasis_repr, Pi.single_apply,
      Finsupp.single_apply, eq_comm]

/-- Off-diagonal difference-root matrices are basis members. -/
@[simp] theorem rootEntryBasis_difference (h2 : IsRegular (2 : R)) (i j : ι) (hij : i ≠ j) :
    rootEntryBasis h2 (.inr (.inr (.inl (i, j)))) =
      typeBDifferenceRootGenerator i j hij := by
  simp [rootEntryBasis_inr_inr, hij]

/-- A diagonal basis member has one positive and one negative hyperbolic diagonal entry. -/
@[simp] theorem rootEntryBasis_diagonal (h2 : IsRegular (2 : R)) (i : ι) :
    rootEntryBasis h2 (.inr (.inr (.inl (i, i)))) =
      (typeBDiagonalEquiv (Pi.single i 1) : typeBDiagonalCartan R ι) := by
  simp [rootEntryBasis_inr_inr, TypeDStd.differenceRootGenerator_self_eq_typeDDiagonalEquiv,
    coe_typeDDiagonalEquiv_apply, coe_typeBDiagonalEquiv_apply]

/-- Positive sum-root matrices are basis members at strictly ordered pairs. -/
@[simp] theorem rootEntryBasis_sum (h2 : IsRegular (2 : R))
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inr (.inr (.inl p)))) =
      typeBSumRootGenerator p.val.1 p.val.2 := by
  simp [rootEntryBasis_inr_inr]

/-- Negative sum-root basis members retain the reversed order of the two indices. -/
@[simp] theorem rootEntryBasis_negSum (h2 : IsRegular (2 : R))
    (p : {p : ι × ι // p.1 < p.2}) :
    rootEntryBasis h2 (.inr (.inr (.inr (.inr p)))) =
      typeBSumNegativeRootGenerator p.val.2 p.val.1 := by
  simp [rootEntryBasis_inr_inr]

section Numbered

variable {n : ℕ} (h2 : IsRegular (2 : R))

/-- A simple coroot has only diagonal coordinates, given by its Bourbaki coordinate vector. -/
theorem simpleCorootGenerator_eq_sum_basis (i : Fin (n + 1)) :
    typeBSimpleCorootGenerator (K := R) i =
      ∑ j, typeBSimpleCorootCoordinate (K := R) i j •
        rootEntryBasis h2 (.inr (.inr (.inl (j, j)))) := by
  simp only [rootEntryBasis_diagonal, typeBSimpleCorootGenerator_eq_diagonal]
  simpa [typeBDiagonalCartanBasis_repr_apply, coe_typeBDiagonalCartanBasis_apply,
    typeBDiagonalMatrix_apply] using congrArg
      (fun x : typeBDiagonalCartan R (Fin (n + 1)) => (x : typeB (Fin (n + 1)) R))
      ((typeBDiagonalCartanBasis (K := R)).sum_repr
        (typeBDiagonalEquiv (typeBSimpleCorootCoordinate i))).symm

end Numbered

end TauCeti.TypeBStd
