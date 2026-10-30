/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Derived.Perfect
public import TauCeti.Algebra.AlgebraicGroup.Derived.Character
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Perfect
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Symplectic groups are scheme-theoretically perfect

Over every field, the scheme-theoretic derived subgroup of `Sp₂ₘ` is the whole group.
Consequently every homomorphism from `Sp₂ₘ` to a commutative affine group is trivial,
and every character is one. These statements include all characteristics and ranks, in
particular characteristic two.

Perfectness of the matrix group over an algebraic closure, together with reduced finite-type
point separation, proves the equality of defining Hopf ideals. It is essential to pass to the
algebraic closure: `Sp₂(𝔽₂)`, `Sp₂(𝔽₃)` and `Sp₄(𝔽₂)` are not perfect as abstract groups. No
assertion of perfectness of rational-point groups over the original field is made here.

## Main results

* `TauCeti.Symplectic.derivedDefiningIdeal_eq_bot`: the derived subgroup of `Sp₂ₘ` is `Sp₂ₘ`.
* `TauCeti.Symplectic.hom_eq_unit_comp_counit`: every homomorphism from `Sp₂ₘ` to a commutative
  affine group is trivial.
* `TauCeti.Symplectic.groupLike_eq_one`: `Sp₂ₘ` has no nontrivial characters.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6d and 21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 10.

The proof follows the special-linear argument
`TauCeti.SpecialLinear.derivedDefiningIdeal_eq_bot`, using
`TauCeti.GLSymplecticFin.commutator_eq_top` in place of perfectness of the special linear group.
-/

public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

variable (k : Type u) [Field k] (m : ℕ)

/-- **The scheme-theoretic derived subgroup of `Sp₂ₘ` is `Sp₂ₘ` over every field.**
The zero Hopf ideal defines the whole group, so this retains the full subgroup scheme structure,
including its points with values in nonreduced algebras. -/
@[simp]
theorem derivedDefiningIdeal_eq_bot :
    CommHopfAlgCat.derivedDefiningIdeal (R := k) (coordinateHopfAlgebra k m) = ⊥ := by
  classical
  let K := AlgebraicClosure k
  let _ : IsReduced (coordinateHopfAlgebra k m) := isReduced_of_smooth k _
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  have ha' : a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha
  have hSp : commutator (GLSymplecticFin m K) = ⊤ :=
    GLSymplecticFin.commutator_eq_top ha'.1 (sq_ne_one_iff.mpr ha'.2)
  let e := pointsMulEquiv k m (A := K)
  apply _root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_of_commutator_eq_top (K := K)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_commutator_eq_commutator e.surjective, hSp,
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

/-- Every homomorphism from `Sp₂ₘ` to a commutative affine group is trivial, in every
characteristic. The target need not be of finite type. -/
theorem hom_eq_unit_comp_counit {C : _root_.CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k C] (f : C ⟶ coordinateHopfAlgebra k m) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k (coordinateHopfAlgebra k m)).comp
        (Bialgebra.counitBialgHom k C)) := by
  let _ : Algebra.IsGeometricallyReduced k (coordinateHopfAlgebra k m) :=
    isGeometricallyReduced_of_smooth k _
  exact (_root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_iff_forall_hom_eq_unit_comp_counit
    (coordinateHopfAlgebra k m)).mp (derivedDefiningIdeal_eq_bot k m) C f

/-- The symplectic group has no nontrivial algebraic characters over any field. -/
theorem groupLike_eq_one (x : GroupLike k (coordinateHopfAlgebra k m)) : x = 1 := by
  apply GroupLike.ext
  have hx := x.sub_one_mem_derivedDefiningIdeal
  rw [derivedDefiningIdeal_eq_bot, HopfIdeal.mem_bot, sub_eq_zero] at hx
  exact hx

end TauCeti.Symplectic
