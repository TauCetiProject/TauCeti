/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Ranges of idempotent endomorphisms

Two idempotent endomorphisms `P` and `Q` of a module with `P * Q = 0` and `Q * P = 0` split the
range of their sum: the range of `P + Q` is the sum of the ranges of `P` and `Q`, and these ranges
are independent. This is how ranks of spectral projections add over disjoint parts of the
spectrum.

Two idempotent endomorphisms `e` and `f` such that `f e f - f` and `e f e - e` are nilpotent have
isomorphic ranges: `e` maps the range of `f` bijectively onto the range of `e`. This holds, for
instance, when `e - f` lies in a nilpotent two-sided ideal of a subring of `Module.End R M`
containing `e` and `f`, since `f e f - f = f (e - f) f` and `e f e - e = -e (e - f) e`. So a basis
of the range of `f` is carried by `e` to a basis of the range of `e`. This is how a basis of the
image of a graded idempotent is lifted from its reduction modulo positive degrees: there `f` is
the degree-zero part of `e`, and `e` keeps whatever homogeneity the basis of the range of `f` has.

## Main results

* `IsIdempotentElem.disjoint_range_of_mul_eq_zero`: if `P` is idempotent and `P * Q = 0`, the
  ranges of `P` and `Q` meet only in `0`.
* `IsIdempotentElem.range_add_of_mul_eq_zero`: if `P` and `Q` are idempotent with `Q * P = 0` and
  `P * Q = 0`, the range of `P + Q` is the sum of their ranges.
* `LinearMap.IsIdempotentElem.bijOn_range_of_isNilpotent`: if `e` and `f` are idempotent with
  `f e f - f` and `e f e - e` nilpotent, `e` is a bijection from `range f` onto `range e`.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, second edition, Graduate Texts in
  Mathematics 131, Springer (2001), §21, for idempotents that agree modulo a nil ideal.
-/

public section

namespace IsIdempotentElem

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {P Q : Module.End R M}

/-- If `P` is idempotent and `P * Q = 0`, the ranges of `P` and `Q` meet only in `0`. -/
theorem disjoint_range_of_mul_eq_zero (hP : IsIdempotentElem P) (hPQ : P * Q = 0) :
    Disjoint (LinearMap.range P) (LinearMap.range Q) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨v, rfl⟩ ⟨w, hw⟩
  have h₁ : P (Q w) = 0 := congr($hPQ w)
  have h₂ : P (P v) = P v := congr($hP v)
  rw [← h₂, ← hw, h₁]

/-- If `P` and `Q` are idempotent with `Q * P = 0` and `P * Q = 0`, the range of `P + Q` is the
sum of the ranges of `P` and `Q`. -/
theorem range_add_of_mul_eq_zero (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hQP : Q * P = 0) (hPQ : P * Q = 0) :
    LinearMap.range (P + Q) = LinearMap.range P ⊔ LinearMap.range Q := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨P v, ?_⟩
    have h₁ : P (P v) = P v := congr($hP v)
    have h₂ : Q (P v) = 0 := congr($hQP v)
    simp [h₁, h₂]
  · rintro _ ⟨v, rfl⟩
    refine ⟨Q v, ?_⟩
    have h₁ : Q (Q v) = Q v := congr($hQ v)
    have h₂ : P (Q v) = 0 := congr($hPQ v)
    simp [h₁, h₂]

end IsIdempotentElem

section Nilpotent

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

end Nilpotent
