/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Function.Difference
public import TauCeti.Analysis.PositiveDefinite.Kernel.Shift
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic

/-!
# Time differences of bounded semigroup-group positive-definite functions

This file proves the alternating finite-difference property needed for the existence half of the
Berg--Christensen--Ressel representation theorem. If `F` is bounded and positive definite on the
involutive semigroup `ℝ≥0 × V`, then every iterated time difference built from

`(t, v) ↦ F (t, v) - F (t + h, v)`

is again positive definite.

The first time difference is obtained from `TauCeti.posSemidef_sub_comp_shift`: the BCR kernel of
a bounded positive-definite function is a bounded positive-definite kernel, the time shift is a
symmetric shift of it, and the shifted kernel is dominated by the kernel itself.

Applying Bochner's theorem to those differences makes the corresponding alternating differences
of the spatial Bochner measures positive, the time-regularity input required to assemble the BCR
representing measure.

An iterated time difference expands into the alternating binomial sum
`(t, v) ↦ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k • h, v)`, so that sum is positive definite too.
Positive definiteness is a statement about quadratic forms, not a pointwise sign: nonnegativity of
the values themselves is asserted only along the zero-spatial axis, where it becomes the classical
complete monotonicity of `t ↦ F (t, 0)` in the finite-difference sense. Those one-variable
statements are read off the differences built here in
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Time/Axis.lean`.

## Main declarations

* `TauCeti.timeDifference`: the one-step alternating time difference, the negative of Mathlib's
  forward difference `fwdDiff` applied in the time coordinate.
* `TauCeti.listTimeDifference`: the alternating difference along a finite list of time steps, and
  `TauCeti.iteratedTimeDifference`: its equal-step specialization.
* `TauCeti.iteratedTimeDifference_eq_alternating_sum`: the binomial expansion of an iterated time
  difference.
* `TauCeti.IsSemigroupGroupPD.timeDifference`: a bounded BCR-positive-definite function remains
  positive definite after subtracting a nonnegative forward time translate.
* `TauCeti.IsSemigroupGroupPD.listTimeDifference` and
  `TauCeti.IsSemigroupGroupPD.iteratedTimeDifference`: every alternating time difference of a
  bounded BCR-positive-definite function, along arbitrary or repeated steps, is positive definite,
  and `TauCeti.IsSemigroupGroupPD.alternating_sum` says the same in binomial form.
* `TauCeti.isBounded_range_listTimeDifference` and
  `TauCeti.isBounded_range_iteratedTimeDifference`: those differences stay bounded, so they can be
  differenced again.
* `TauCeti.continuous_listTimeDifference` and `TauCeti.continuous_iteratedTimeDifference`: those
  differences stay continuous, so Bochner's theorem applies to each of their time slices.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13 and its bounded-semigroup argument.
-/

public section

open ComplexConjugate InnerProductSpace Set
open scoped ComplexOrder NNReal Pointwise fwdDiff

namespace TauCeti

universe u

section

variable {V : Type u} {F : ℝ≥0 × V → ℂ}

/-- The first alternating time difference with step `h`:
`timeDifference h F (t, v) = F (t, v) - F (t + h, v)`. It is the negative of Mathlib's forward
difference `fwdDiff` applied in the time coordinate. -/
def timeDifference (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  fun p => -fwdDiff h (fun t => F (t, p.2)) p.1

/-- The first time difference evaluated at a point. -/
@[simp]
theorem timeDifference_apply (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) (p : ℝ≥0 × V) :
    timeDifference h F p = F p - F (p.1 + h, p.2) := by
  simp [timeDifference, fwdDiff]

/-- The time difference with step zero is the zero function. -/
@[simp]
theorem timeDifference_zero (F : ℝ≥0 × V → ℂ) : timeDifference 0 F = 0 := by
  ext p
  simp

/-- The alternating time difference along a finite list of steps, one application of
`timeDifference` per entry of the list. -/
def listTimeDifference (l : List ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  l.foldr timeDifference F

/-- Differencing along no steps at all is the identity. -/
@[simp]
theorem listTimeDifference_nil (F : ℝ≥0 × V → ℂ) : listTimeDifference [] F = F := by
  rw [listTimeDifference, List.foldr_nil]

/-- Differencing along `h :: l` is one further first difference with step `h`. -/
@[simp]
theorem listTimeDifference_cons (h : ℝ≥0) (l : List ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    listTimeDifference (h :: l) F = timeDifference h (listTimeDifference l F) := by
  rw [listTimeDifference, List.foldr_cons, ← listTimeDifference]

/-- The `n`-th alternating time difference, obtained by iterating `timeDifference h`. -/
def iteratedTimeDifference (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  (timeDifference h)^[n] F

/-- The zeroth time difference is the original function. -/
@[simp]
theorem iteratedTimeDifference_zero (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference 0 h F = F := by
  simp [iteratedTimeDifference]

/-- The successor time difference is one further first difference. -/
@[simp]
theorem iteratedTimeDifference_succ (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference (n + 1) h F = timeDifference h (iteratedTimeDifference n h F) := by
  simp only [iteratedTimeDifference, Function.iterate_succ_apply']

/-- Iterating the step `h` is differencing along the constant list of `n` copies of `h`. -/
theorem iteratedTimeDifference_eq_listTimeDifference (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference n h F = listTimeDifference (List.replicate n h) F := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedTimeDifference_succ, ih, List.replicate_succ, listTimeDifference_cons]

/-- At a fixed spatial coordinate, the `n`-th time difference is the alternating `n`-th forward
difference of the one-variable function `t ↦ F (t, v)`. This is the bridge to the generic
finite-difference theory of `TauCeti/Algebra/Group/ForwardDiff.lean`. -/
theorem iteratedTimeDifference_apply_eq_fwdDiff (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) (t : ℝ≥0)
    (v : V) :
    iteratedTimeDifference n h F (t, v)
      = (-1 : ℂ) ^ n * Δ_[h]^[n] (fun s : ℝ≥0 => F (s, v)) t := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
      have hsucc : iteratedTimeDifference (n + 1) h F
          = iteratedTimeDifference n h (timeDifference h F) :=
        Function.iterate_succ_apply _ _ _
      have hstep : (fun s : ℝ≥0 => timeDifference h F (s, v))
          = -Δ_[h] fun s : ℝ≥0 => F (s, v) := by
        funext s
        simp [timeDifference, fwdDiff]
      rw [hsucc, ih, hstep]
      exact congrFun (neg_one_pow_mul_fwdDiff_iter_succ n (fun s : ℝ≥0 => F (s, v)) h) t

/-- **The binomial expansion of an iterated time difference.** This is the form in which the
measure-theoretic half of the Berg--Christensen--Ressel representation slices the differences by
time. -/
theorem iteratedTimeDifference_eq_alternating_sum (n : ℕ) (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) :
    iteratedTimeDifference n h F = fun p : ℝ≥0 × V =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (p.1 + k • h, p.2) := by
  funext p
  obtain ⟨t, v⟩ := p
  rw [iteratedTimeDifference_apply_eq_fwdDiff, neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum]

/-- Boundedness is preserved by taking a first time difference. -/
theorem isBounded_range_timeDifference (hbounded : Bornology.IsBounded (range F)) (h : ℝ≥0) :
    Bornology.IsBounded (range (timeDifference h F)) :=
  (hbounded.sub hbounded).subset <| by
    rintro _ ⟨p, rfl⟩
    exact ⟨F p, mem_range_self p, F (p.1 + h, p.2), mem_range_self _,
      (timeDifference_apply h F p).symm⟩

/-- Boundedness is preserved by differencing along any finite list of steps. -/
theorem isBounded_range_listTimeDifference (hbounded : Bornology.IsBounded (range F))
    (l : List ℝ≥0) : Bornology.IsBounded (range (listTimeDifference l F)) := by
  induction l with
  | nil => simpa using hbounded
  | cons h l ih => simpa using isBounded_range_timeDifference ih h

/-- Boundedness is preserved by every iterated time difference. -/
theorem isBounded_range_iteratedTimeDifference (hbounded : Bornology.IsBounded (range F)) (n : ℕ)
    (h : ℝ≥0) : Bornology.IsBounded (range (iteratedTimeDifference n h F)) := by
  rw [iteratedTimeDifference_eq_listTimeDifference]
  exact isBounded_range_listTimeDifference hbounded _

section Continuity

variable [TopologicalSpace V]

/-- Continuity is preserved by taking a first time difference. -/
theorem continuous_timeDifference (hF : Continuous F) (h : ℝ≥0) :
    Continuous (timeDifference h F) := by
  rw [funext (timeDifference_apply h F)]
  exact hF.sub (hF.comp ((continuous_fst.add continuous_const).prodMk continuous_snd))

/-- Continuity is preserved by differencing along any finite list of steps. -/
theorem continuous_listTimeDifference (hF : Continuous F) (l : List ℝ≥0) :
    Continuous (listTimeDifference l F) := by
  induction l with
  | nil => simpa using hF
  | cons h l ih => simpa using continuous_timeDifference ih h

/-- Continuity is preserved by every iterated time difference. -/
theorem continuous_iteratedTimeDifference (hF : Continuous F) (n : ℕ) (h : ℝ≥0) :
    Continuous (iteratedTimeDifference n h F) := by
  rw [iteratedTimeDifference_eq_listTimeDifference]
  exact continuous_listTimeDifference hF _

end Continuity

end

variable {V : Type u} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

namespace IsSemigroupGroupPD

/-- A bounded BCR-positive-definite function remains positive definite after subtracting a forward
time translate. In other words, for every `h : ℝ≥0`, the first alternating time difference
`(t, v) ↦ F (t, v) - F (t + h, v)` is semigroup-group positive definite. -/
theorem timeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (h : ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.timeDifference h F) := by
  rw [isSemigroupGroupPD_iff_posSemidef] at hF ⊢
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  convert posSemidef_sub_comp_shift
    (K := fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)) (σ := fun p => (p.1 + h, p.2)) hF
    (fun p q => by simp only [add_right_comm p.1 h q.1, add_assoc]) (fun p => hC _ ⟨_, rfl⟩) using 2
  simp [add_right_comm]

/-- Every alternating time difference along a finite list of steps of a bounded
BCR-positive-definite function is again semigroup-group positive definite. -/
theorem listTimeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (l : List ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.listTimeDifference l F) := by
  induction l with
  | nil => simpa using hF
  | cons h l ih =>
      rw [TauCeti.listTimeDifference_cons]
      exact ih.timeDifference (isBounded_range_listTimeDifference hbounded l) h

/-- Every iterated alternating time difference of a bounded BCR-positive-definite function is
again semigroup-group positive definite. -/
theorem iteratedTimeDifference (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (n : ℕ) (h : ℝ≥0) :
    IsSemigroupGroupPD (TauCeti.iteratedTimeDifference n h F) := by
  rw [TauCeti.iteratedTimeDifference_eq_listTimeDifference]
  exact hF.listTimeDifference hbounded _

/-- **The alternating iterated time differences, expanded as binomial sums, are semigroup-group
positive definite.** This is `IsSemigroupGroupPD.iteratedTimeDifference` with the differencing
operator resolved into an explicit alternating sum over an arithmetic progression of times. -/
theorem alternating_sum (hF : IsSemigroupGroupPD F)
    (hbounded : Bornology.IsBounded (range F)) (n : ℕ) (h : ℝ≥0) :
    IsSemigroupGroupPD fun p : ℝ≥0 × V =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (p.1 + k • h, p.2) := by
  rw [← TauCeti.iteratedTimeDifference_eq_alternating_sum]
  exact hF.iteratedTimeDifference hbounded n h

end IsSemigroupGroupPD

end TauCeti
