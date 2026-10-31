/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Colon ideals by one element

For an `R`-algebra `S`, the ideal `(N : x)` of a submodule `N` of an `S`-module commutes with
restricting scalars to `R`.

For an ideal `I` and an element `f` of a commutative ring, `I ∩ (f) = f · (I : f)`. When `f` is
regular this determines `(I : f)`: generators of `I ∩ (f)`, which an intersection computation
supplies, divided by `f` generate `(I : f)`.

## Main results

* `Submodule.comap_colon_singleton`: the ideal `(N : x)` of `R` is the preimage of the ideal
  `(N : x)` of `S`.
* `Ideal.inf_span_singleton_eq_span_singleton_mul_colon`: `I ∩ (f) = f · (I : f)`.
* `Ideal.colon_singleton_eq_of_inf_span_singleton_eq`: for regular `f`, if `I ∩ (f) = f · J`
  then `(I : f) = J`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §4,
  computing ideal quotients from intersections.
-/

public section

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a submodule `N` of an `S`-module `M` and `x ∈ M`, the ideal `(N : x)` of `R` is the
preimage of the ideal `(N : x)` of `S`. -/
theorem Submodule.comap_colon_singleton (N : Submodule S M) (x : M) :
    (N.colon {x}).comap (algebraMap R S) = (N.restrictScalars R).colon {x} := by
  ext r
  simp [Submodule.mem_colon_singleton]

namespace Ideal

variable {R : Type*} [CommSemiring R] {I J : Ideal R} {f : R}

/-- The intersection of an ideal `I` with the principal ideal `(f)` is `f` times the colon ideal
`(I : f)`. -/
theorem inf_span_singleton_eq_span_singleton_mul_colon (I : Ideal R) (f : R) :
    I ⊓ span {f} = span {f} * I.colon {f} := by
  ext x
  simp only [mem_inf, mem_span_singleton_mul, mem_span_singleton', Submodule.mem_colon_singleton,
    smul_eq_mul]
  constructor
  · rintro ⟨hx, a, rfl⟩
    exact ⟨a, hx, mul_comm f a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨mul_comm f a ▸ ha, a, mul_comm a f⟩

/-- **Colon ideals from intersections.** If `f` is regular and `I ∩ (f) = f · J`, then the colon
ideal `(I : f)` is `J`. -/
theorem colon_singleton_eq_of_inf_span_singleton_eq (hf : IsLeftRegular f)
    (h : I ⊓ span {f} = span {f} * J) : I.colon {f} = J := by
  rw [inf_span_singleton_eq_span_singleton_mul_colon, span_singleton_mul_eq_span_singleton_mul]
    at h
  refine le_antisymm (fun x hx ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨y, hy, hxy⟩ := h.1 x hx
    exact hf hxy ▸ hy
  · obtain ⟨x, hx, hxy⟩ := h.2 y hy
    exact hf hxy ▸ hx

end Ideal
