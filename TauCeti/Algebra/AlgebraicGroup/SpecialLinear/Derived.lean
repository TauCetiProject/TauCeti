/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Derived.Character
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Perfect
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Special linear groups are scheme-theoretically perfect

Over every field, the scheme-theoretic derived subgroup of `SLₙ` is the whole group.
Consequently every homomorphism from `SLₙ` to a commutative affine group is trivial,
and every character is one. These statements include all characteristics and ranks.

Perfectness of the matrix group over an algebraic closure, together with reduced finite-type
point separation, proves the equality of defining Hopf ideals. It is essential to pass to the
algebraic closure: `SL₂(𝔽₂)` and `SL₂(𝔽₃)` are not perfect as abstract groups. No assertion
of perfectness of rational-point groups over the original field is made here.

The proof follows the algebraic-closure point-separation argument of
`TauCeti.GeneralLinear.derivedDefiningIdeal_eq_specialLinear_definingHopfIdeal`, using
`Matrix.SpecialLinearGroup.commutator_eq_top` in place of the general-linear determinant kernel.
The universal property of the affine abelianization supplies the statement about commutative
images.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6d and 21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- **The scheme-theoretic derived subgroup of `SLₙ` is `SLₙ` over every field.**
The zero Hopf ideal defines the whole group, so this retains the full subgroup scheme structure,
including its points with values in nonreduced algebras. -/
@[simp]
theorem derivedDefiningIdeal_eq_bot :
    CommHopfAlgCat.derivedDefiningIdeal (R := k) (coordinateHopfAlgebra k n) = ⊥ := by
  classical
  let K := AlgebraicClosure k
  let _ : IsReduced (coordinateHopfAlgebra k n) := isReduced_of_smooth k _
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  have ha' : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin n) K) = ⊤ :=
    Matrix.SpecialLinearGroup.commutator_eq_top ha'.1 (sq_ne_one_iff.mpr ha'.2)
  let e := pointsMulEquiv (R := k) (A := K) n
  apply _root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_of_commutator_eq_top (K := K)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_commutator_eq_commutator e.surjective, hSL,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- Every homomorphism from `SLₙ` to a commutative affine group is trivial, in every
characteristic. The target need not be of finite type. -/
theorem hom_eq_unit_comp_counit {C : _root_.CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k C] (f : C ⟶ coordinateHopfAlgebra k n) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k (coordinateHopfAlgebra k n)).comp
        (Bialgebra.counitBialgHom k C)) := by
  let _ : Algebra.IsGeometricallyReduced k (coordinateHopfAlgebra k n) :=
    isGeometricallyReduced_of_smooth k _
  exact (_root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_iff_forall_hom_eq_unit_comp_counit
    (coordinateHopfAlgebra k n)).mp (derivedDefiningIdeal_eq_bot k n) C f

/-- The special linear group has no nontrivial algebraic characters over any field. -/
theorem groupLike_eq_one (x : GroupLike k (coordinateHopfAlgebra k n)) : x = 1 := by
  apply GroupLike.ext
  have hx := x.sub_one_mem_derivedDefiningIdeal
  rw [derivedDefiningIdeal_eq_bot, HopfIdeal.mem_bot, sub_eq_zero] at hx
  exact hx

end TauCeti.SpecialLinear
