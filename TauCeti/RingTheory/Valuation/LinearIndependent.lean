/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Linear independence from distinct valuations

Let `v` be a valuation on an algebra `B` over a commutative ring `A`, and let `f` be a family of
elements of `B`. Suppose that every nonzero scalar multiple `a • f i` has nonzero valuation, and
that multiples of two different members of the family never have the same valuation. Then `f` is
linearly independent over `A`: in a linear combination with a nonzero coefficient, the summand of
largest valuation is unique, so it dictates the valuation of the sum, which cannot vanish.

When `v` is trivial on `A`, the hypothesis only asks the members of the family to have pairwise
distinct nonzero valuations. When `v` is not trivial on `A`, it asks their valuations to lie in
different cosets of the image of `A`. This is how the value-group index of a valued field
extension, and with it the ramification index, is bounded by the degree of the extension.

Several valuations give a second criterion. If `v i` are valuations on an algebra over a field `K`,
all at most `1` on a valuation subring `O` of `K`, and `e i` is strictly the largest member of a
family `e` for `v i`, then `e` is linearly independent over `K`: in a relation, divide by a
coefficient dividing all the others in `O`, and the summand `e k` dominates for `v k`. This is how
the number of extensions of a valuation to a finite extension is bounded by the degree.

## Main results

* `Valuation.linearIndependent_of_map_smul_ne`: a family whose nonzero scalar multiples have
  nonzero valuations, distinct for different members, is linearly independent.
* `Valuation.linearIndependent_of_map_lt`: a family in which each member strictly dominates the
  others for its own valuation, the valuations being bounded on a common valuation subring of the
  scalars, is linearly independent.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II,
  Proposition 6.8, for the inequality `e f ≤ n` proved by this argument.
* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §3.2,
  for the bound on the number of extensions of a valuation by the degree.
-/

public section

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Elements whose multiples have distinct valuations are linearly independent.** If every
nonzero scalar multiple `a • f i` has nonzero valuation, and `v (a • f i) ≠ v (b • f j)` for
`i ≠ j` and nonzero scalars `a` and `b`, then `f` is linearly independent over `A`. -/
theorem linearIndependent_of_map_smul_ne {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) {ι : Type*} {f : ι → B} (hf : ∀ i (a : A), a ≠ 0 → v (a • f i) ≠ 0)
    (hne : ∀ i j, i ≠ j → ∀ a b : A, a ≠ 0 → b ≠ 0 → v (a • f i) ≠ v (b • f j)) :
    LinearIndependent A f := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  -- Restrict to the summands with nonzero coefficient; they have the same sum.
  set t := s.filter fun i ↦ g i ≠ 0 with ht
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have hsum' : ∑ i ∈ t, g i • f i = 0 := by
    rw [← hsum, ht]
    exact Finset.sum_filter_of_ne fun i _ h hg ↦ h (by rw [hg, zero_smul])
  -- The summand of largest valuation is unique, so it dictates the valuation of the sum.
  obtain ⟨j, hjt, hmax⟩ := t.exists_max_image (fun i ↦ v (g i • f i)) ⟨i, hit⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have hlt : ∀ i ∈ t \ {j}, v (g i • f i) < v (g j • f j) := fun i hi ↦ by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hmax i hi.1) (hne i j hi.2 _ _ (Finset.mem_filter.mp hi.1).2 hgj)
  have h := v.map_sum_eq_of_lt hjt hlt
  rw [hsum', v.map_zero] at h
  exact hf j (g j) hgj h.symm

/-- **Elements each dominating for its own valuation are linearly independent.** Let `v i` be
valuations on an algebra `C` over a field `K` with `v i ≤ 1` on a valuation subring `O` of `K`. If
`v i (e i) ≠ 0` and `v i (e j) < v i (e i)` for `j ≠ i`, then `e` is linearly independent over
`K`. -/
theorem linearIndependent_of_map_lt {K C : Type*} [Field K] [Ring C] [Algebra K C]
    {O : ValuationSubring K} {ι : Type*} {Γ : ι → Type*}
    [∀ i, LinearOrderedCommMonoidWithZero (Γ i)] (v : ∀ i, Valuation C (Γ i))
    (hO : ∀ i, ∀ a ∈ O, v i (algebraMap K C a) ≤ 1) {e : ι → C} (he : ∀ i, v i (e i) ≠ 0)
    (hlt : ∀ i j, j ≠ i → v i (e j) < v i (e i)) : LinearIndependent K e := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i₀ hi₀
  by_contra hne
  -- a coefficient `g k` dividing all the others in `O`
  obtain ⟨k, hks, hgk, hO'⟩ := O.exists_ne_zero_and_div_mem ⟨i₀, hi₀, hne⟩
  -- after dividing by `g k`, the summand `e k` dominates for `v k`
  have hsum : e k + ∑ i ∈ s.erase k, (g i / g k) • e i = 0 := by
    have h := congrArg ((g k)⁻¹ • ·) hg
    simp only [smul_zero, Finset.smul_sum, smul_smul] at h
    rw [← Finset.add_sum_erase _ _ hks, inv_mul_cancel₀ hgk, one_smul] at h
    simpa only [div_eq_inv_mul] using h
  have hlt' : v k (∑ i ∈ s.erase k, (g i / g k) • e i) < v k (e k) := by
    refine Valuation.map_sum_lt _ (he k) fun i hi ↦ ?_
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hO k _ (hO' i (Finset.mem_of_mem_erase hi))))
      (hlt k i (Finset.ne_of_mem_erase hi))
  have := (v k).map_add_eq_of_lt_left hlt'
  rw [hsum, map_zero] at this
  exact he k this.symm

end Valuation

end
