/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantField

/-!
# A rational place forces exact constants

A constant algebraic over the base field is regular at every place. At a rational place its
residue is the residue of a base-field element. Their difference is algebraic and has valuation
less than one, so it must vanish. Thus the existence of a rational place certifies exactness of
the constant field, including for composita with a completely split rational place.

Conversely, a place of a finite extension over a larger constant field forces that field to be
algebraic over the base.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.1 and Corollary 3.9.7.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- If `F / k` has a rational place, every element of `F` algebraic over `k` belongs to `k`.
No function-field or separability hypothesis is needed. -/
theorem isIntegrallyClosedIn_of_degree_eq_one (P : Place k F) (hP : P.degree = 1) :
    IsIntegrallyClosedIn k F := by
  rw [TauCeti.isIntegrallyClosedIn_iff_forall_isAlgebraic]
  intro x hx
  obtain ⟨c, hc⟩ := (P.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hP)
    x (P.mem_integers_of_mem_algebraicClosure (mem_algebraicClosure_iff.mpr hx))
  refine ⟨c, (sub_eq_zero.mp ?_).symm⟩
  by_contra hne
  have halg : IsAlgebraic k (x - algebraMap k F c) :=
    mem_algebraicClosure_iff.mp <| (algebraicClosure k F).sub_mem
      (mem_algebraicClosure_iff.mpr hx) ((algebraicClosure k F).algebraMap_mem c)
  rw [P.valuation_eq_one_of_isAlgebraic halg hne] at hc
  exact lt_irrefl _ hc

universe u u' v v'

/-- If a finite extension `F'` of a function field `F / k` has a place over `k'`, then it is a
function field over `k'`: the existence of a place forces `k'` to be algebraic over `k`. -/
theorem isFunctionField_of_place {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
    [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k' F']
    [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] (hF : IsFunctionField k F) (P' : Place k' F') :
    IsFunctionField k' F' := by
  have hFk : IsFunctionField k F' := hF.finite_extension
  have hnot : ¬ Algebra.IsAlgebraic k' F' := fun h ↦ by
    obtain ⟨t, ht⟩ := P'.ord_surjective 1
    exact P'.transcendental_of_ord_ne_zero (by rw [ht]; norm_num) (h.isAlgebraic t)
  have hadd := _root_.lift_trdeg_add_eq k k' F'
  rw [hFk.trdeg_eq_one, Cardinal.lift_one] at hadd
  have hb : 1 ≤ Cardinal.lift.{u', v'} (Algebra.trdeg k' F') := by
    rw [Cardinal.one_le_iff_ne_zero, Ne, Cardinal.lift_eq_zero, trdeg_eq_zero_iff]
    exact hnot
  have ha : Algebra.trdeg k k' = 0 := by
    by_contra ha
    have ha' : 1 ≤ Cardinal.lift.{v', u'} (Algebra.trdeg k k') := by
      rwa [Cardinal.one_le_iff_ne_zero, Ne, Cardinal.lift_eq_zero]
    have := add_le_add ha' hb
    rw [hadd] at this
    norm_num at this
  have : Algebra.IsAlgebraic k k' := trdeg_eq_zero_iff.1 ha
  exact hFk.of_isAlgebraic (k' := k')

end TauCeti.Place
