/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Double-bond commutators in the type-B spin carrier

For a long simple root `α` and the adjacent short simple root `β`, write `E` and `F` for their
integral matrices in the spin lattice. The group commutator of the corresponding root points is

`1 + (s * t) • ⁅E, F⁆ + (s * t²) • (F * E * F)`.

The last summand is the `α + 2β` correction. It must not be discarded in characteristic two:
although the iterated Lie bracket is `-2 • (F * E * F)`, the group formula has no factor two.
The positive and negative formulas below require only the one directed Cartan entry giving
`⁅E, ⁅E, F⁆⁆ = 0`, so they also apply to single bonds. At the terminal double bond, take `i` to
be the long node and `j` the short node. The Cartan matrix has roots as rows; the Serre system
uses its transpose.

All vanishing products are proved in the integral lattice before changing coefficients. The
formulas therefore hold over arbitrary commutative rings, including nonreduced rings. They
compute matrices of actual carrier points, but do not construct the two nonsimple root subgroup
schemes or identify the carrier with an independently pinned simply connected group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.

The lattice transport uses the existing integral Kostant root operators; the group calculation
uses `Units.val_commutatorElement_eq_one_add_lie_add`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {n : ℕ}

private noncomputable abbrev rootOp (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  kostantRootOperator (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) k

private noncomputable abbrev rootAction (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily k))

private theorem operator_lie_lie_eq_zero (k l : Fin (n + 1) ⊕ Fin (n + 1))
    (hkl : ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
      ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
        TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) l⁆⁆ = 0) :
    ⁅rootOp k, ⁅rootOp k, rootOp l⁆⁆ = 0 := by
  -- Restriction to the invariant lattice preserves brackets, since its inclusion into the
  -- rational spin module is injective.
  have hlie : ⁅rootAction k, ⁅rootAction k, rootAction l⁆⁆ = 0 := by
    have h := congrArg ((rep n).toLieHom.comp
      (_root_.UniversalEnvelopingAlgebra.ι ℚ)) hkl
    simpa only [LieHom.map_lie, map_zero, LieHom.comp_apply, AlgHom.toLieHom_apply] using h
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    AddSubgroup.coe_sub, coe_kostantRootOperator_apply,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] using
    LinearMap.congr_fun hlie (v : _)

private theorem integral_relations (k l : Fin (n + 1) ⊕ Fin (n + 1))
    (hkl : ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
      ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
        TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) l⁆⁆ = 0) :
    rootIntMatrix n k * rootIntMatrix n k = 0 ∧
      rootIntMatrix n l * rootIntMatrix n l = 0 ∧
      rootIntMatrix n k * rootIntMatrix n l * rootIntMatrix n k = 0 := by
  have hbracket := operator_lie_lie_eq_zero k l hkl
  -- The basis matrix map preserves the integral operator brackets.
  have hmat : ⁅rootIntMatrix n k, ⁅rootIntMatrix n k, rootIntMatrix n l⁆⁆ = 0 := by
    have h := congrArg (LinearMap.toMatrix (latticeBasis n) (latticeBasis n)) hbracket
    simp only [Ring.lie_def, map_sub, LinearMap.toMatrix_mul, map_zero] at h
    simpa only [rootIntMatrix_eq_toMatrix, Ring.lie_def] using h
  exact ⟨rootIntMatrix_mul_self n k, rootIntMatrix_mul_self n l,
    Matrix.mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero _ _
      (rootIntMatrix_mul_self n k) hmat⟩

private theorem commutator_matrix (k l : Fin (n + 1) ⊕ Fin (n + 1))
    (hkl : ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
      ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k,
        TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) l⁆⁆ = 0)
    (A : Type u) [CommRing A] (s t : A) :
    ((⁅rootSubgroupPoints n k A (Multiplicative.ofAdd s),
        rootSubgroupPoints n l A (Multiplicative.ofAdd t)⁆ : points n A).val :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n k, rootIntMatrix n l⁆).map (Int.cast : ℤ → A) +
        (s * t ^ 2) •
          (rootIntMatrix n l * rootIntMatrix n k * rootIntMatrix n l).map
            (Int.cast : ℤ → A) := by
  let f : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ →+*
      Matrix (Fin (dimension n)) (Fin (dimension n)) A := (Int.castRingHom A).mapMatrix
  have hf (X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
      f X = X.map (Int.cast : ℤ → A) := by
    ext a b
    simp only [f, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  obtain ⟨hE, hF, hEFE⟩ := integral_relations k l hkl
  have hsq (X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ)
      (hX : X * X = 0) (a : A) : (a • f X) * (a • f X) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, ← map_mul, hX, map_zero, smul_zero]
  have htriple : (s • f (rootIntMatrix n k)) * (t • f (rootIntMatrix n l)) *
      (s • f (rootIntMatrix n k)) = 0 := by
    simp only [smul_mul_assoc, mul_smul_comm, ← map_mul, hEFE, map_zero, smul_zero]
  have h := Units.val_commutatorElement_eq_one_add_lie_add
    (rootSubgroupPoints n k A (Multiplicative.ofAdd s)).val
    (rootSubgroupPoints n l A (Multiplicative.ofAdd t)).val
    (s • f (rootIntMatrix n k)) (t • f (rootIntMatrix n l))
    (by rw [hf]; exact coe_rootSubgroupPoints_eq_one_add_smul _ _ _ _)
    (by rw [hf]; exact coe_rootSubgroupPoints_eq_one_add_smul _ _ _ _)
    (hsq _ hE s) (hsq _ hF t) htriple
  have hLie : ⁅s • f (rootIntMatrix n k), t • f (rootIntMatrix n l)⁆ =
      (s * t) • f ⁅rootIntMatrix n k, rootIntMatrix n l⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_sub, mul_comm t s]
  have hCubic : (t • f (rootIntMatrix n l)) * (s • f (rootIntMatrix n k)) *
      (t • f (rootIntMatrix n l)) =
        (s * t ^ 2) • f (rootIntMatrix n l * rootIntMatrix n k * rootIntMatrix n l) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_mul]
    congr 1
    ring
  rw [hLie, hCubic] at h
  -- The subgroup inclusion preserves the group commutator.
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hf] using h

/-- The positive simple-root commutator, with its quadratic correction in the second parameter.
The directed Cartan condition includes the terminal double bond with `i` long and `j` short. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_inl_of_cartan_eq_neg_one
    {i j : Fin (n + 1)} (hji : CartanMatrix.B (n + 1) j i = -1)
    (A : Type u) [CommRing A] (s t : A) :
    ((⁅rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd s),
        rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd t)⁆ : points n A).val :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n (.inl i), rootIntMatrix n (.inl j)⁆).map
        (Int.cast : ℤ → A) +
        (s * t ^ 2) •
          (rootIntMatrix n (.inl j) * rootIntMatrix n (.inl i) * rootIntMatrix n (.inl j)).map
            (Int.cast : ℤ → A) := by
  apply commutator_matrix
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inl, hji] using
    TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator (K := ℚ) i j

/-- The negative simple-root commutator, with the same integral cubic correction and directed
Cartan convention as the positive formula. No invertibility of two is required. -/
theorem coe_commutatorElement_rootSubgroupPoints_inr_inr_of_cartan_eq_neg_one
    {i j : Fin (n + 1)} (hji : CartanMatrix.B (n + 1) j i = -1)
    (A : Type u) [CommRing A] (s t : A) :
    ((⁅rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd s),
        rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd t)⁆ : points n A).val :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n (.inr i), rootIntMatrix n (.inr j)⁆).map
        (Int.cast : ℤ → A) +
        (s * t ^ 2) •
          (rootIntMatrix n (.inr j) * rootIntMatrix n (.inr i) * rootIntMatrix n (.inr j)).map
            (Int.cast : ℤ → A) := by
  apply commutator_matrix
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inr, hji] using
    TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
      (K := ℚ) i j

end TauCeti.TypeBSpinCarrier
