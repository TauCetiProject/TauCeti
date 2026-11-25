/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Principal
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.AlgebraicGeometry.StructureSheaf.Stalk.Basic

/-!
# The principal cycle of a prime element

Let `R` be a Noetherian domain and `p ∈ R` a prime element. The ideal `(p)` is a point of
`Spec R` of codimension one, by Krull's principal ideal theorem, and the principal cycle of `p`,
viewed as a rational function on `Spec R`, is the point cycle of `(p)`
(`AlgebraicCycle.div_eq_single_of_prime`): `p` is a uniformizer of the local ring at `(p)`, and a
unit in the local ring at every other codimension-one point, since a height-one prime containing
`p` is `(p)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, proof of Proposition 6.2.
-/

public section

open _root_.AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.AlgebraicCycle

variable {R : CommRingCat.{u}} [IsDomain R] [IsNoetherianRing R] {p : R}

/-- **The principal cycle of a prime element.** On the spectrum of a Noetherian domain `R`, the
principal cycle of a prime element `p`, viewed as a rational function, is the point cycle `[x]` of
the point `x = (p)`: `p` generates the maximal ideal of the local ring at `x`, and it is a unit in
the local ring at every other codimension-one point. -/
theorem div_eq_single_of_prime [DecidableEq (Spec R)] (hp : Prime p) {x : Spec R}
    (hx : x.asIdeal = Ideal.span {p}) {r : (Spec R).functionFieldˣ}
    (hr : (r : (Spec R).functionField) = algebraMap R (Spec R).functionField p) :
    div r = Function.locallyFinsuppWithin.single x 1 := by
  ext y
  rw [div_apply, Function.locallyFinsuppWithin.single_apply, hr]
  by_cases hy : coheight y = 1
  · have hb : StructureSheaf.toStalk R y p ≠ 0 := fun h ↦ IsFractionRing.to_map_eq_zero_iff.not.mpr
      hp.ne_zero (by rw [← StructureSheaf.algebraMap_functionField_toStalk y, h]; exact map_zero _)
    rw [← StructureSheaf.algebraMap_functionField_toStalk y]
    split_ifs with h
    · subst h
      refine Scheme.ord_algebraMap_stalk_eq_one hy (specializes_refl _) ?_
      rw [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id]
      exact StructureSheaf.maximalIdeal_stalk_eq_span hx
    · rw [Scheme.ord_algebraMap_stalk_eq_zero_iff hy (specializes_refl _) hb,
        TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id]
      -- a height-one prime containing the prime element `p` is `(p)`
      have := y.isPrime
      exact fun hmem ↦ h (PrimeSpectrum.ext ((Ideal.eq_span_singleton_of_height_eq_one
        (by rw [idealHeight_eq_coheight, hy])
        ((StructureSheaf.toStalk_mem_maximalIdeal_iff y p).mp hmem) hp).trans hx.symm))
  · -- the point `(p)` has codimension one by Krull's principal ideal theorem
    have hyx : y ≠ x := by
      rintro rfl
      refine hy ?_
      rw [← idealHeight_eq_coheight, hx]
      exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy, ite_eq_right hyx]

end TauCeti.AlgebraicGeometry.AlgebraicCycle
