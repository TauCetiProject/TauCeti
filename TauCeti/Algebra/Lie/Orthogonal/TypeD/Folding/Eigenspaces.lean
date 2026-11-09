/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.GraphAutomorphism
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# The orthogonal eigenspace decomposition of the type-D graph involution

Exchange the two vectors of one hyperbolic pair in the standard even orthogonal module.
When two is invertible, their sum and difference, together with the unchanged hyperbolic
pairs, give coordinates adapted to this involution. The fixed space has exactly the native
odd orthogonal Gram matrix `LieAlgebra.Orthogonal.JB`; the anti-fixed line has Gram entry
`-2`. In particular the distinguished fixed vector has norm two, not norm one.

We index the distinguished pair by `none` and the remaining pairs by `some i`. The explicit
linear equivalence `typeDGraphSplit` and its inverse retain the scalar factors needed to
restrict skew-adjoint endomorphisms to the fixed space. The bilinear isometry
`typeDGraphSplitIsometry` records the orthogonal direct sum, and the two eigenspace
characterizations identify its summands with the actual coordinate-swap eigenspaces.
These statements include an empty set of remaining pairs and work over any commutative
ring in which two is invertible.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §8.2, for the
  orthogonal realization of the type-D diagram involution and its type-B fixed algebra.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

variable (I : Type*) (A : Type*) [CommRing A] [Invertible (2 : A)]

/-- Coordinates adapted to the swap of the distinguished hyperbolic pair: the first
summand is the fixed space, and the second is the anti-fixed line. -/
def typeDGraphSplit : (((Unit ⊕ (I ⊕ I)) → A) × A) ≃ₗ[A]
    ((Option I ⊕ Option I) → A) where
  toFun p
    | .inl none => p.1 (.inl ()) + p.2
    | .inr none => p.1 (.inl ()) - p.2
    | .inl (some i) => p.1 (.inr (.inl i))
    | .inr (some i) => p.1 (.inr (.inr i))
  invFun v := (fun
    | .inl _ => ⅟(2 : A) * (v (.inl none) + v (.inr none))
    | .inr (.inl i) => v (.inl (some i))
    | .inr (.inr i) => v (.inr (some i)),
    ⅟(2 : A) * (v (.inl none) - v (.inr none)))
  left_inv p := by
    apply Prod.ext
    · ext (u | (i | i))
      · cases u
        dsimp
        ring_nf
        simp [mul_assoc, mul_left_comm (⅟(2 : A))]
      · rfl
      · rfl
    · dsimp
      ring_nf
      simp [mul_assoc, mul_left_comm (⅟(2 : A))]
  right_inv v := by
    ext (i | i) <;> cases i <;> dsimp <;> ring_nf <;>
      simp [mul_assoc, mul_left_comm (⅟(2 : A))]
  map_add' p q := by
    ext (i | i) <;> cases i <;> dsimp <;> ring
  map_smul' a p := by
    ext (i | i) <;> cases i <;> dsimp <;> ring

/-- The positive distinguished coordinate is the sum of the new coordinates. -/
@[simp]
theorem typeDGraphSplit_inl_none (p : ((Unit ⊕ (I ⊕ I)) → A) × A) :
    typeDGraphSplit I A p (.inl none) = p.1 (.inl ()) + p.2 := (rfl)

@[simp]
theorem typeDGraphSplit_inr_none (p : ((Unit ⊕ (I ⊕ I)) → A) × A) :
    typeDGraphSplit I A p (.inr none) = p.1 (.inl ()) - p.2 := (rfl)

@[simp]
theorem typeDGraphSplit_inl_some (p : ((Unit ⊕ (I ⊕ I)) → A) × A) (i : I) :
    typeDGraphSplit I A p (.inl (some i)) = p.1 (.inr (.inl i)) := (rfl)

@[simp]
theorem typeDGraphSplit_inr_some (p : ((Unit ⊕ (I ⊕ I)) → A) × A) (i : I) :
    typeDGraphSplit I A p (.inr (some i)) = p.1 (.inr (.inr i)) := (rfl)

/-- The fixed distinguished coordinate is half the sum of the old coordinates. -/
@[simp]
theorem typeDGraphSplit_symm_fst_inl (v : (Option I ⊕ Option I) → A) (u : Unit) :
    ((typeDGraphSplit I A).symm v).1 (.inl u) =
      ⅟(2 : A) * (v (.inl none) + v (.inr none)) := (rfl)

@[simp]
theorem typeDGraphSplit_symm_fst_inr_inl (v : (Option I ⊕ Option I) → A) (i : I) :
    ((typeDGraphSplit I A).symm v).1 (.inr (.inl i)) = v (.inl (some i)) := (rfl)

@[simp]
theorem typeDGraphSplit_symm_fst_inr_inr (v : (Option I ⊕ Option I) → A) (i : I) :
    ((typeDGraphSplit I A).symm v).1 (.inr (.inr i)) = v (.inr (some i)) := (rfl)

/-- The anti-fixed coordinate is half the difference of the old coordinates. -/
@[simp]
theorem typeDGraphSplit_symm_snd (v : (Option I ⊕ Option I) → A) :
    ((typeDGraphSplit I A).symm v).2 =
      ⅟(2 : A) * (v (.inl none) - v (.inr none)) := (rfl)

variable [DecidableEq I]

/-- In the adapted coordinates the hyperbolic-pair swap acts by `(x,t) ↦ (x,-t)`. -/
theorem typeDGraphSplit_graphIndex (p : ((Unit ⊕ (I ⊕ I)) → A) × A) :
    (fun s => typeDGraphSplit I A p (typeDGraphIndex (none : Option I) s)) =
      typeDGraphSplit I A (p.1, -p.2) := by
  ext (i | i) <;> cases i <;> simp [sub_eq_add_neg]

/-- A vector is fixed by the hyperbolic-pair swap exactly when its anti-fixed coordinate
vanishes. -/
theorem comp_typeDGraphIndex_eq_self_iff (v : (Option I ⊕ Option I) → A) :
    (fun s => v (typeDGraphIndex (none : Option I) s)) = v ↔
      ((typeDGraphSplit I A).symm v).2 = 0 := by
  obtain ⟨p, rfl⟩ := (typeDGraphSplit I A).surjective v
  rw [typeDGraphSplit_graphIndex, (typeDGraphSplit I A).injective.eq_iff,
    LinearEquiv.symm_apply_apply, Prod.mk.injEq]
  simp only [true_and]
  constructor
  · intro h
    have htwo : (2 : A) * p.2 = 0 := by linear_combination -h
    exact (isUnit_of_invertible (2 : A)).mul_left_cancel (by simpa using htwo)
  · intro h
    simp [h]

/-- A vector is negated by the hyperbolic-pair swap exactly when its fixed-space
coordinate vanishes. -/
theorem comp_typeDGraphIndex_eq_neg_iff (v : (Option I ⊕ Option I) → A) :
    (fun s => v (typeDGraphIndex (none : Option I) s)) = -v ↔
      ((typeDGraphSplit I A).symm v).1 = 0 := by
  obtain ⟨p, rfl⟩ := (typeDGraphSplit I A).surjective v
  rw [typeDGraphSplit_graphIndex, ← map_neg,
    (typeDGraphSplit I A).injective.eq_iff, LinearEquiv.symm_apply_apply]
  have hp : -p = (-p.1, -p.2) := rfl
  rw [hp, Prod.mk.injEq]
  simp only [and_true]
  constructor
  · intro h
    ext i
    have htwo : (2 : A) * p.1 i = 0 := by
      have hi := congrFun h i
      simp only [Pi.neg_apply] at hi
      linear_combination hi
    exact (isUnit_of_invertible (2 : A)).mul_left_cancel (by simpa using htwo)
  · intro h
    simp [h]

variable [Fintype I]

/-- The adapted coordinates split the even orthogonal form into the native odd orthogonal
form and a line of norm `-2`. -/
@[simp]
theorem typeDGraphSplit_bilin (p q : ((Unit ⊕ (I ⊕ I)) → A) × A) :
    (JD (Option I) A).toBilin' (typeDGraphSplit I A p) (typeDGraphSplit I A q) =
      (JB I A).toBilin' p.1 q.1 - 2 * p.2 * q.2 := by
  simp [Matrix.toBilin'_apply', JD, JB, dotProduct, Matrix.mulVec,
    Matrix.fromBlocks, Fintype.sum_sum_type, Fintype.sum_option, Matrix.one_apply]
  ring

/-- The orthogonal direct-sum isometry associated to the graph involution. The first
factor has Gram matrix `JB` and the second has Gram entry `-2`. -/
def typeDGraphSplitIsometry :
    ((JB I A).toBilin'.prod ((-2 : A) • LinearMap.mul A A)).IsometryEquiv
      (JD (Option I) A).toBilin' where
  toLinearEquiv := typeDGraphSplit I A
  map_app' p q := by
    simp [LinearMap.BilinForm.prod_apply, sub_eq_add_neg, mul_assoc]

@[simp]
theorem typeDGraphSplitIsometry_apply (p : ((Unit ⊕ (I ⊕ I)) → A) × A) :
    typeDGraphSplitIsometry I A p = typeDGraphSplit I A p := (rfl)

@[simp]
theorem typeDGraphSplitIsometry_symm_apply (v : (Option I ⊕ Option I) → A) :
    (typeDGraphSplitIsometry I A).symm v = (typeDGraphSplit I A).symm v := (rfl)

end TauCeti
