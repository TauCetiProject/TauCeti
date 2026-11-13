/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Set.Card

/-!
# Coordinate rectangles in quadratic algebras

The elements whose two coordinates lie in prescribed sets form a rectangle under
`QuadraticAlgebra.equivProd`. Its cardinality is the product of the coordinate cardinalities.
A coefficient map injective on each coordinate set is injective on this rectangle,
without needing to be injective on the entire coefficient ring.
-/

public section

namespace QuadraticAlgebra

variable {R S : Type*} (a b : R)

/-- A coordinate rectangle is the image of the product of its coordinate sets under
the inverse coordinate equivalence. -/
theorem setOf_re_mem_im_mem_eq_image (U V : Set R) :
    {z : QuadraticAlgebra R a b | z.re ∈ U ∧ z.im ∈ V} =
      (equivProd a b).symm '' (U ×ˢ V) := by
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), ⟨hz.1, hz.2⟩, by simp only [equivProd_symm_apply, mk_eta]⟩
  · rintro ⟨p, hp, rfl⟩
    simpa only [Set.mem_ofPred_eq, equivProd_symm_apply, Set.mem_prod] using hp

/-- Finite coordinate sets give a finite rectangle in a quadratic algebra. -/
theorem finite_setOf_re_mem_im_mem {U V : Set R} (hU : U.Finite) (hV : V.Finite) :
    {z : QuadraticAlgebra R a b | z.re ∈ U ∧ z.im ∈ V}.Finite := by
  rw [setOf_re_mem_im_mem_eq_image]
  exact (hU.prod hV).image _

/-- The number of elements in a coordinate rectangle is the product of the numbers of
allowed coordinates. The statement uses the usual `ncard = 0` convention for infinite sets. -/
@[simp↓]
theorem ncard_setOf_re_mem_im_mem (U V : Set R) :
    {z : QuadraticAlgebra R a b | z.re ∈ U ∧ z.im ∈ V}.ncard = U.ncard * V.ncard := by
  rw [setOf_re_mem_im_mem_eq_image,
    Set.ncard_image_of_injective _ (equivProd a b).symm.injective, Set.ncard_prod]

variable [CommSemiring R] [CommSemiring S]

/-- A coefficient map injective on each coordinate set is injective on their rectangle. -/
theorem injOn_mapRingHom_setOf_re_mem_im_mem (f : R →+* S) {U V : Set R}
    (hU : Set.InjOn f U) (hV : Set.InjOn f V) :
    Set.InjOn (mapRingHom f a b)
      {z : QuadraticAlgebra R a b | z.re ∈ U ∧ z.im ∈ V} := by
  intro z hz w hw h
  ext
  · exact hU hz.1 hw.1 (by simpa using congrArg re h)
  · exact hV hz.2 hw.2 (by simpa using congrArg im h)

/-- A coefficient map injective on each coordinate set preserves the number of elements
of their rectangle. -/
theorem ncard_image_mapRingHom_setOf_re_mem_im_mem (f : R →+* S) {U V : Set R}
    (hU : Set.InjOn f U) (hV : Set.InjOn f V) :
    (mapRingHom f a b '' {z : QuadraticAlgebra R a b | z.re ∈ U ∧ z.im ∈ V}).ncard =
      U.ncard * V.ncard := by
  rw [(injOn_mapRingHom_setOf_re_mem_im_mem a b f hU hV).ncard_image,
    ncard_setOf_re_mem_im_mem]

end QuadraticAlgebra
