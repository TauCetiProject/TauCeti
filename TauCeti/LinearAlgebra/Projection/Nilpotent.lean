/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Idempotents that agree up to nilpotents have isomorphic ranges

Let `e` and `f` be idempotent endomorphisms of a module such that `f e f - f` and `e f e - e` are
nilpotent. This holds, for instance, when `e - f` lies in a nilpotent two-sided ideal of a
subring of `Module.End R M` containing `e` and `f`, since `f e f - f = f (e - f) f` and
`e f e - e = -e (e - f) e`. Then `e` maps the range of `f` bijectively onto the range of `e`.

So a basis of the range of `f` is carried by `e` to a basis of the range of `e`. This is how a
basis of the image of a graded idempotent is lifted from its reduction modulo positive degrees:
there `f` is the degree-zero part of `e`, and `e` keeps whatever homogeneity the basis of the
range of `f` has.

## Main results

* `LinearMap.IsIdempotentElem.bijOn_range_of_isNilpotent`: under the above hypotheses, `e` is a
  bijection from `range f` onto `range e`.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, second edition, Graduate Texts in
  Mathematics 131, Springer (2001), §21, for idempotents that agree modulo a nil ideal.
-/

public section

open LinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `e` and `f` are idempotent endomorphisms with `f e f - f` and `e f e - e` nilpotent, then
`e` maps the range of `f` bijectively onto the range of `e`. -/
theorem LinearMap.IsIdempotentElem.bijOn_range_of_isNilpotent {e f : Module.End R M}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hfef : IsNilpotent (f * e * f - f)) (hefe : IsNilpotent (e * f * e - e)) :
    Set.BijOn e (range f) (range e) := by
  refine ⟨fun x _ ↦ mem_range_self e x, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · -- The unit `1 + (f e f - f)` kills `x - y`, which `f` fixes and `e` kills.
    have hz : f (x - y) = x - y := hf.mem_range_iff.1 (sub_mem hx hy)
    have hez : e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : (1 + (f * e * f - f)) (x - y) = 0 := by
      simp only [LinearMap.add_apply, one_apply_eq_self, LinearMap.sub_apply, mul_apply_eq_comp,
        hz, hez, map_zero, add_sub_cancel]
    rw [← sub_eq_zero]
    exact ((Module.End.isUnit_iff _).1 hfef.isUnit_one_add).injective (h0.trans (map_zero _).symm)
  · -- The unit `u = 1 + (e f e - e)` commutes with `e` and satisfies `u e = e f e`.
    set u := 1 + (e * f * e - e)
    have hu := (Module.End.isUnit_iff u).1 hefe.isUnit_one_add
    have hue : u * e = e * f * e := by
      simp only [u, add_mul, one_mul, sub_mul, mul_assoc, he.eq, add_sub_cancel]
    have heu : e * u = e * f * e := by
      simp only [u, mul_add, mul_one, mul_sub, ← mul_assoc, he.eq, add_sub_cancel]
    obtain ⟨z, rfl⟩ := hu.2 y
    -- `e z = z`, since `u (e z) = e (u z) = u z`.
    have hez : e z = z := hu.1 <| by
      rw [← mul_apply_eq_comp, hue, ← heu, mul_apply_eq_comp, he.mem_range_iff.1 hy]
    refine ⟨f (e z), mem_range_self f _, ?_⟩
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← hue, mul_apply_eq_comp, hez]
