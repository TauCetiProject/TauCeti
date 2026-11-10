/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantField
import Mathlib.FieldTheory.FinTrdeg

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

universe u u' v'

/-- If `F' / k` is a function field and `F'` has a place over `k'`, then it is a function field
over `k'`: the existence of a place forces `k'` to be algebraic over `k`. -/
theorem isFunctionField_of_place {k : Type u} {k' : Type u'} {F' : Type v'}
    [Field k] [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
    [IsScalarTower k k' F'] (hFk : IsFunctionField k F') (P' : Place k' F') :
    IsFunctionField k' F' := by
  have hnot : ¬ Algebra.IsAlgebraic k' F' := fun h ↦ by
    obtain ⟨t, ht⟩ := P'.ord_surjective 1
    exact P'.transcendental_of_ord_ne_zero (by rw [ht]; norm_num) (h.isAlgebraic t)
  have : Algebra.EssFiniteType k F' := hFk.essFiniteType
  have : Algebra.EssFiniteType k' F' := Algebra.EssFiniteType.of_comp k k' F'
  have hb : 1 ≤ Algebra.trdeg k' F' := by
    rw [Cardinal.one_le_iff_ne_zero, Ne, trdeg_eq_zero_iff]
    exact hnot
  have : Algebra.IsAlgebraic k k' :=
    isAlgebraic_of_trdeg_le (hFk.trdeg_eq_one.trans_le hb) (trdeg_lt_aleph0 k' F')
  exact hFk.of_isAlgebraic (k' := k')

end TauCeti.Place
