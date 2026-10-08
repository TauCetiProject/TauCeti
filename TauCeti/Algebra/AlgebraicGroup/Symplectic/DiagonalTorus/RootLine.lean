/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.RootDatum
public import TauCeti.Algebra.Lie.Symplectic.RootLine

/-!
# Symplectic root lines and the characters of matrix entries

An entry of a normalized symplectic root matrix is nonzero exactly when the difference
of its two paired standard weights is that root of the diagonal root datum. The test
uses the integral matrix, so its support remains meaningful in characteristic two.
Consequently a symplectic Lie matrix with entries only of a specified root character
is a unique scalar multiple of the corresponding normalized root matrix, over every
commutative coefficient ring.

This identifies the character-based root lines with the support-based root lines used
by root-subgroup differentials. Together with an entrywise adjoint-weight criterion it
recognizes the root spaces which a symplectic pinning must trivialize.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.

The scalar-multiple recognition uses
`TauCeti.GLSymplecticFin.RootSubgroupIndex.existsUnique_eq_tangentMatrix_iff`.
-/

public section

namespace TauCeti.Symplectic

open GLSymplecticFin

universe u

variable {m : ℕ}

/-- The integral character of a paired coordinate of the standard symplectic representation.
The two halves have weights `eᵢ` and `-eᵢ`; a matrix entry `(a, b)` has character
`pairedCoordinateWeight a - pairedCoordinateWeight b`. -/
noncomputable def pairedCoordinateWeight : (Fin m ⊕ Fin m) → (ULift.{u} (Fin m) →₀ ℤ) :=
  Sum.elim (fun i ↦ Finsupp.single (ULift.up i) 1)
    (fun i ↦ Finsupp.single (ULift.up i) (-1))

/-- A coordinate in the first half has the positive standard weight. -/
@[simp]
theorem pairedCoordinateWeight_inl (i : Fin m) :
    pairedCoordinateWeight.{u} (Sum.inl i) = Finsupp.single (ULift.up i) 1 :=
  (rfl)

/-- A coordinate in the second half has the negative standard weight. -/
@[simp]
theorem pairedCoordinateWeight_inr (i : Fin m) :
    pairedCoordinateWeight.{u} (Sum.inr i) = Finsupp.single (ULift.up i) (-1) :=
  (rfl)

/-- The root occupying a matrix position, with diagonal entries having weight zero. -/
private def rootAtEntry : (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Option (RootSubgroupIndex m)
  | .inl a, .inl b => if h : a = b then none else some (.difference a b h)
  | .inr a, .inr b => if h : a = b then none else some (.difference b a (Ne.symm h))
  | .inl a, .inr b =>
      if h : a = b then some (.positiveLong a)
      else if h' : a < b then some (.positiveSum a b h')
      else some (.positiveSum b a (lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)))
  | .inr a, .inl b =>
      if h : a = b then some (.negativeLong a)
      else if h' : a < b then some (.negativeSum a b h')
      else some (.negativeSum b a (lt_of_le_of_ne (le_of_not_gt h') (Ne.symm h)))

private theorem rootAtEntry_eq_some_iff (root : RootSubgroupIndex m)
    (a b : Fin m ⊕ Fin m) :
    rootAtEntry a b = some root ↔ root.tangentMatrix (1 : ℤ) a b ≠ 0 := by
  cases root <;> cases a <;> cases b <;>
    simp only [rootAtEntry] <;> split_ifs <;>
    simp_all [RootSubgroupIndex.tangentMatrix_positiveLong,
      RootSubgroupIndex.tangentMatrix_negativeLong,
      RootSubgroupIndex.tangentMatrix_difference,
      RootSubgroupIndex.tangentMatrix_positiveSum,
      RootSubgroupIndex.tangentMatrix_negativeSum, Matrix.single_apply] <;> grind

private theorem rootAtEntry_eq_some_iff_root (root : RootSubgroupIndex m)
    (a b : Fin m ⊕ Fin m) :
    rootAtEntry a b = some root ↔
      (diagonalRootDatum.{u} m).root root =
        pairedCoordinateWeight a - pairedCoordinateWeight b := by
  have hr (r : RootSubgroupIndex m) : some r = some root ↔
      (diagonalRootDatum.{u} m).root root = (diagonalRootDatum.{u} m).root r := by
    rw [Option.some.injEq, ← (diagonalRootDatum.{u} m).root.injective.eq_iff, eq_comm]
  have hn (i : Fin m) :
      -Finsupp.single (ULift.up.{u} i) (1 : ℤ) + -Finsupp.single (ULift.up i) 1 =
        -Finsupp.single (ULift.up i) 2 := by
    rw [← neg_add, ← Finsupp.single_add]
    norm_num
  have hzero := (diagonalRootDatum.{u} m).ne_zero root
  cases a <;> cases b <;> simp only [rootAtEntry] <;> split_ifs <;> subst_vars <;>
    simp only [hr, pairedCoordinateWeight_inl, pairedCoordinateWeight_inr,
      diagonalRootDatum_root_positiveLong, diagonalRootDatum_root_negativeLong,
      diagonalRootDatum_root_difference, diagonalRootDatum_root_positiveSum,
      diagonalRootDatum_root_negativeSum] <;>
    simp [hzero, hn, Finsupp.single_neg, sub_eq_add_neg, ← Finsupp.single_add,
      add_comm]

/-- The integral support of a normalized root matrix consists exactly of the entries
whose paired-weight difference is that root of the symplectic diagonal root datum. -/
theorem tangentMatrix_apply_ne_zero_iff_root_eq (root : RootSubgroupIndex m)
    (a b : Fin m ⊕ Fin m) :
    root.tangentMatrix (1 : ℤ) a b ≠ 0 ↔
      (diagonalRootDatum.{u} m).root root =
        pairedCoordinateWeight a - pairedCoordinateWeight b := by
  rw [← rootAtEntry_eq_some_iff, rootAtEntry_eq_some_iff_root]

/-- A normalized integral root matrix vanishes exactly at entries whose paired-weight
difference is not its root of the symplectic diagonal root datum. -/
theorem tangentMatrix_apply_eq_zero_iff_root_ne (root : RootSubgroupIndex m)
    (a b : Fin m ⊕ Fin m) :
    root.tangentMatrix (1 : ℤ) a b = 0 ↔
      (diagonalRootDatum.{u} m).root root ≠
        pairedCoordinateWeight a - pairedCoordinateWeight b := by
  simpa only [not_not] using
    not_congr (tangentMatrix_apply_ne_zero_iff_root_eq.{u} root a b)

/-- A symplectic Lie matrix has entries only of a given root character exactly when
it is a unique scalar multiple of that root's normalized matrix. This holds over
arbitrary commutative rings, including in characteristic two. -/
theorem existsUnique_eq_tangentMatrix_iff
    {R : Type*} [CommRing R] (root : RootSubgroupIndex m)
    {A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R}
    (hA : A ∈ LieAlgebra.Symplectic.sp (Fin m) R) :
    (∃! c : R, A = root.tangentMatrix c) ↔
      ∀ a b, (diagonalRootDatum.{u} m).root root ≠
          pairedCoordinateWeight a - pairedCoordinateWeight b → A a b = 0 := by
  rw [root.existsUnique_eq_tangentMatrix_iff hA]
  apply forall_congr' fun a ↦ forall_congr' fun b ↦ ?_
  apply imp_congr ?_ Iff.rfl
  exact tangentMatrix_apply_eq_zero_iff_root_ne.{u} root a b


end TauCeti.Symplectic
