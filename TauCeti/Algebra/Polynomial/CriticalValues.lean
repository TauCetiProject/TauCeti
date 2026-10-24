/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Critical values of polynomials

The critical values of a polynomial `p` with coefficients in `R`, computed in an `R`-algebra
`S` that is a domain, are the values `p(x)` at the roots `x ∈ S` of the derivative `p′`. Over
an algebraically closed field of characteristic zero they are the finite branch values of the
map `x ↦ p(x)` of the projective line; the point at infinity, over which a polynomial of degree
at least two is always ramified, is not part of this set.

Following Mathlib's `Polynomial.rootSet`, the roots of the zero polynomial form the empty set,
so a polynomial with vanishing derivative has no critical values.

The chain rule `(p ∘ q)′ = (p′ ∘ q) · q′` gives the bookkeeping for composites used in Belyi's
construction: the critical values of `p ∘ q` lie in the image under `p` of the critical values
of `q` together with the critical values of `p`, with equality over an algebraically closed
field of characteristic zero when `p` and `q` are nonconstant.

## Main declarations

* `Polynomial.criticalValues`: the critical values of `p` in `S`.
* `Polynomial.criticalValues_comp_subset`: the critical values of a composite.
* `Polynomial.criticalValues_comp`: equality for nonconstant polynomials over a field of
  characteristic zero, computed in an algebraically closed field.

## References

* Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in
  Mathematics 106, Springer, 2009, Exercise 1.12 and its hint.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, §3.
-/

public section

open scoped Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

variable (S) in
/-- The critical values of `p` in `S`: the values of `p` at the roots of its derivative in `S`.
When `S` is an algebraically closed field of characteristic zero, these are the finite branch
values of `p` regarded as a self-map of the projective line. -/
noncomputable def criticalValues (p : R[X]) : Set S :=
  (fun x ↦ aeval x p) '' (derivative p).rootSet S

@[simp]
theorem mem_criticalValues {p : R[X]} {y : S} :
    y ∈ p.criticalValues S ↔ ∃ x ∈ (derivative p).rootSet S, aeval x p = y :=
  Iff.rfl

theorem aeval_mem_criticalValues {p : R[X]} {x : S} (hx : x ∈ (derivative p).rootSet S) :
    aeval x p ∈ p.criticalValues S :=
  Set.mem_image_of_mem _ hx

theorem criticalValues_finite (p : R[X]) : (p.criticalValues S).Finite :=
  ((derivative p).rootSet_finite S).image _

/-- A polynomial of degree at most one has no critical values. -/
theorem criticalValues_eq_empty_of_natDegree_le_one {p : R[X]} (hp : p.natDegree ≤ 1) :
    p.criticalValues S = ∅ := by
  rw [criticalValues, eq_C_of_natDegree_le_zero
    ((natDegree_derivative_le p).trans (Nat.sub_le_of_le_add hp)), rootSet_C, Set.image_empty]

@[simp]
theorem criticalValues_C (a : R) : (C a).criticalValues S = ∅ :=
  criticalValues_eq_empty_of_natDegree_le_one (by rw [natDegree_C]; exact zero_le_one)

@[simp]
theorem criticalValues_X : (X : R[X]).criticalValues S = ∅ :=
  criticalValues_eq_empty_of_natDegree_le_one natDegree_X_le

variable (S) in
/-- Critical values are unchanged by first extending the coefficients along a scalar tower. -/
@[simp]
theorem criticalValues_map {T : Type*} [CommRing T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S] (p : R[X]) :
    (p.map (algebraMap R T)).criticalValues S = p.criticalValues S := by
  simp [criticalValues, derivative_map, aeval_map_algebraMap]

/-- The critical values of `p ∘ q` lie in the image under `p` of the critical values of `q`,
together with the critical values of `p`. -/
theorem criticalValues_comp_subset (p q : R[X]) :
    (p.comp q).criticalValues S ⊆ (fun y ↦ aeval y p) '' q.criticalValues S ∪
      p.criticalValues S := by
  rintro _ ⟨x, hx, rfl⟩
  rw [derivative_comp, mem_rootSet', Polynomial.map_mul, map_mul, aeval_comp] at hx
  obtain ⟨hne, hx⟩ := hx
  rcases mul_eq_zero.mp hx with h | h
  · refine Or.inl ⟨aeval x q, aeval_mem_criticalValues ?_, (aeval_comp x).symm⟩
    exact mem_rootSet'.mpr ⟨left_ne_zero_of_mul hne, h⟩
  · simp only [aeval_comp]
    refine Or.inr (aeval_mem_criticalValues (mem_rootSet'.mpr ⟨fun h' ↦ ?_, h⟩))
    exact right_ne_zero_of_mul hne (by rw [map_comp, h', zero_comp])

/-- Over a field of characteristic zero, computed in an algebraically closed field, the critical
values of a composite of nonconstant polynomials are the image under `p` of the critical values
of `q`, together with the critical values of `p`. -/
theorem criticalValues_comp {K L : Type*} [Field K] [CharZero K] [Field L] [IsAlgClosed L]
    [Algebra K L] {p q : K[X]} (hp : 0 < p.natDegree) (hq : 0 < q.natDegree) :
    (p.comp q).criticalValues L = (fun y ↦ aeval y p) '' q.criticalValues L ∪
      p.criticalValues L := by
  refine (criticalValues_comp_subset p q).antisymm ?_
  have hp' : derivative p ≠ 0 := derivative_ne_zero.mpr hp.ne'
  have hq' : derivative q ≠ 0 := derivative_ne_zero.mpr hq.ne'
  have hpq : derivative (p.comp q) ≠ 0 := by
    rw [derivative_comp]
    refine mul_ne_zero hq' fun h ↦ ?_
    rcases comp_eq_zero_iff.mp h with h | ⟨-, h⟩
    · exact hp' h
    · rw [h, natDegree_C] at hq
      exact hq.false
  -- A root `x` of either factor of `(p′ ∘ q) · q′` is a root of `(p ∘ q)′`.
  have key : ∀ x : L, aeval x (derivative q) * aeval (aeval x q) (derivative p) = 0 →
      aeval (aeval x q) p ∈ (p.comp q).criticalValues L := fun x hx ↦ by
    rw [← aeval_comp]
    refine aeval_mem_criticalValues ((mem_rootSet_of_ne hpq).mpr ?_)
    rwa [derivative_comp, map_mul, aeval_comp]
  rintro _ (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact key x (by rw [aeval_eq_zero_of_mem_rootSet hx, zero_mul])
  · -- Every value of `q` is attained over the algebraically closed field `L`.
    obtain ⟨x, hx⟩ := IsAlgClosed.eval_surjective (p := q.map (algebraMap K L))
      (by rw [natDegree_map]; exact hq.ne') y
    have hxy : aeval x q = y := by rwa [← eval_map_algebraMap]
    rw [← hxy]
    exact key x (by rw [hxy, aeval_eq_zero_of_mem_rootSet hy, mul_zero])

end Polynomial
