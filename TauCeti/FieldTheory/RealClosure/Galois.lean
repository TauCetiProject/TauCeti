/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.FiniteExtension
public import TauCeti.FieldTheory.Galois.FixedField
public import Mathlib.GroupTheory.Nilpotent

/-! # The Galois-theoretic reduction for real closed fields

A finite Galois extension of a real closed field has a 2-group of automorphisms.
Over a square-closed intermediate extension it is trivial. These degree reductions
are used to prove algebraic closedness in `AlgebraicClosed.lean`.

## References

The Sylow 2-subgroup and index-two subgroup steps of the Artin–Schreier argument; see
Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Module IntermediateField

variable {R E : Type*} [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E] [IsGalois R E]

/-- A finite Galois extension of a real closed field has a 2-group as Galois group. -/
theorem isPGroup_two_algEquiv : IsPGroup 2 Gal(E/R) := by
  apply TauCeti.isPGroup_of_forall_finrank_eq_one_of_not_dvd (p := 2)
  intro F _ _ _ hnotdvd
  apply finrank_eq_one_of_odd
  rw [Nat.odd_iff]
  omega

/-- A square-closed field of characteristic different from two has no nontrivial finite
Galois extension whose Galois group is a 2-group. -/
theorem finrank_eq_one_of_isPGroup {K L : Type*} [Field K] [NeZero (2 : K)]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hsq : ∀ x : K, IsSquare x) (hG : IsPGroup 2 Gal(L/K)) :
    finrank K L = 1 := by
  have := hG.isNilpotent
  rcases hG.card_eq_or_dvd with hcard | hdvd
  · rwa [IsGalois.card_aut_eq_finrank] at hcard
  · obtain ⟨H, hH, _⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
    have hdim : finrank K (fixedField H) = 2 := by
      rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField, hH]
    exact (finrank_ne_two_of_forall_isSquare hsq hdim).elim

/-- Over a square-closed intermediate extension of a real closed field, every
finite Galois extension of the base becomes trivial. -/
theorem finrank_eq_one_of_isGalois_of_forall_isSquare {C : Type*} [Field C] [Algebra R C]
    [Algebra C E] [IsScalarTower R C E] (hsq : ∀ x : C, IsSquare x) :
    finrank C E = 1 := by
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap R C).injective
  have : FiniteDimensional C E := FiniteDimensional.right R C E
  have : IsGalois C E := IsGalois.tower_top_of_isGalois R C E
  exact finrank_eq_one_of_isPGroup hsq
    ((isPGroup_two_algEquiv (R := R) (E := E)).of_injective
      (AlgEquiv.restrictScalarsHom R) (AlgEquiv.restrictScalarsHom_injective R))

end TauCeti.RealClosure
