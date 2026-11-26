/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter

/-!
# Defect classes of blocks

Let `k` be a field, `G` a finite group, `e_B` a block idempotent of `k[G]` and
`λ_B : Z(k[G]) → k` a central character of the block, a `k`-algebra homomorphism with
`λ_B(e_B) = 1`. Write `e_B = ∑_C a_B(C) K_C` in the basis of class sums `K_C` of the centre. A
**defect class** of `B` is a conjugacy class `C` with `a_B(C) λ_B(K_C) ≠ 0` (Martínez,
Definition 3.2, p. 17).

Applying `λ_B` to `e_B = ∑_C a_B(C) K_C` gives `∑_C a_B(C) λ_B(K_C) = 1`, so every block with a
central character has a defect class; over an algebraically closed field every block has one.

The definition takes the homomorphism `λ` as an argument, since a central character need not
exist over a field that does not split `G`.

## Main definitions

* `TauCeti.IsDefectClass φ b C`: the conjugacy class `C` has `a_b(C) φ(K_C) ≠ 0`.

## Main results

* `TauCeti.isDefectClass_iff_ne_zero_and`: `C` is a defect class exactly when both factors
  `a_b(C)` and `φ(K_C)` are nonzero.
* `TauCeti.isDefectClass_mk_iff`: the condition read at a representative `g` of `C`.
* `TauCeti.exists_isDefectClass`: if `φ(b) = 1`, then `b` has a defect class for `φ`.
* `TauCeti.IsBlockIdempotent.exists_isDefectClass`: over an algebraically closed field, every
  block has a defect class for its central character.

## References

* A. Martínez, *Modular representation theory of finite groups*, Definition 3.2, p. 17.
-/

public section

namespace TauCeti

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

/-- A **defect class** of `b ∈ Z(k[G])` for a `k`-algebra homomorphism `φ : Z(k[G]) → k`: a
conjugacy class `C` whose coefficient `a_b(C)` in `b` and value `φ(K_C)` at the class sum have
nonzero product (Martínez, Definition 3.2, p. 17). The predicate is defined for every `φ`, but it
is Martínez's defect class only when `φ(b) = 1`, as for a block idempotent `b` with its central
character `φ`. -/
def IsDefectClass (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k)
    (b : Subalgebra.center k (MonoidAlgebra k G)) (C : ConjClasses G) : Prop :=
  classSumBasis.repr b C * φ (classSumCenter C) ≠ 0

/-- Unfolding lemma for `IsDefectClass`. -/
theorem isDefectClass_iff {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} {C : ConjClasses G} :
    IsDefectClass φ b C ↔ classSumBasis.repr b C * φ (classSumCenter C) ≠ 0 :=
  Iff.rfl

/-- `C` is a defect class of `b` for `φ` exactly when both the coefficient of `b` on `C` and the
value of `φ` at the class sum of `C` are nonzero. -/
theorem isDefectClass_iff_ne_zero_and {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} {C : ConjClasses G} :
    IsDefectClass φ b C ↔ classSumBasis.repr b C ≠ 0 ∧ φ (classSumCenter C) ≠ 0 :=
  mul_ne_zero_iff

/-- The coefficient of `b` on a defect class is nonzero. -/
theorem IsDefectClass.repr_ne_zero {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} {C : ConjClasses G} (h : IsDefectClass φ b C) :
    classSumBasis.repr b C ≠ 0 :=
  (isDefectClass_iff_ne_zero_and.1 h).1

/-- The value of `φ` at the class sum of a defect class is nonzero. -/
theorem IsDefectClass.apply_classSumCenter_ne_zero
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} {C : ConjClasses G} (h : IsDefectClass φ b C) :
    φ (classSumCenter C) ≠ 0 :=
  (isDefectClass_iff_ne_zero_and.1 h).2

/-- The coefficient of `b` at a representative `g` of a defect class is nonzero. -/
theorem IsDefectClass.coeff_ne_zero {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} {g : G}
    (h : IsDefectClass φ b (ConjClasses.mk g)) : (b : MonoidAlgebra k G).coeff g ≠ 0 := by
  simpa [classSumBasis_repr_apply, centerToConjClasses_mk] using h.repr_ne_zero

/-- The class of `g` is a defect class of `b` for `φ` exactly when the coefficient of `b` at `g`
times `φ` of the class sum of `g` is nonzero. -/
theorem isDefectClass_mk_iff {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (g : G) :
    IsDefectClass φ b (ConjClasses.mk g) ↔
      (b : MonoidAlgebra k G).coeff g * φ (classSumCenter (ConjClasses.mk g)) ≠ 0 := by
  rw [isDefectClass_iff, classSumBasis_repr_apply, centerToConjClasses_mk]

/-- **Defect classes exist.** If `φ(b) = 1`, for instance for a block idempotent `b` and its
central character `φ`, then `b` has a defect class for `φ`: applying `φ` to
`b = ∑_C a_b(C) K_C` gives `∑_C a_b(C) φ(K_C) = 1`. -/
theorem exists_isDefectClass {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hφ : φ b = 1) :
    ∃ C, IsDefectClass φ b C := by
  classical
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  by_contra! h
  have hb := congrArg φ (classSumBasis.sum_repr b)
  simp only [map_sum, map_smul, classSumBasis_apply, smul_eq_mul, hφ] at hb
  rw [Finset.sum_eq_zero fun C _ => not_not.1 (h C)] at hb
  exact zero_ne_one hb

/-- **Every block has a defect class.** Over an algebraically closed field, a block idempotent
of `k[G]` has a defect class for its central character. -/
theorem IsBlockIdempotent.exists_isDefectClass [IsAlgClosed k]
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) :
    ∃ C, IsDefectClass hb.centralCharacter b C :=
  TauCeti.exists_isDefectClass hb.centralCharacter_self

end TauCeti
