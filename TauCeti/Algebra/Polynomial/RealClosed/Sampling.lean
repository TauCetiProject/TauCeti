/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sign
public import TauCeti.FieldTheory.RealClosure.AbstractRolle
import Mathlib.Order.Interval.Set.UnorderedInterval

/-! # Finite samples of the real line

`Polynomial.signSamples p` consists of the distinct roots of `p` and its derivative,
together with two points beyond all roots of `p`. For nonzero `p`, these points meet
every root and every complementary interval. More precisely, every point can be joined
to a sample by a root-free closed interval, unless it is itself a root sample.
This permits simultaneous sign sampling for any finite family of divisors of `p`,
including over non-Archimedean real closed fields.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, second edition](https://doi.org/10.1007/3-540-33099-2),
Chapter 10, for univariate sign determination using roots and complementary intervals.
-/

public section

namespace TauCeti

open Polynomial Finset Set

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Roots and critical points, augmented by two points beyond all the roots.
The zero polynomial has a finite sample set too; its infinite zero set is not represented. -/
noncomputable def _root_.Polynomial.signSamples (p : R[X]) : Finset R :=
  p.roots.toFinset ∪ p.derivative.roots.toFinset ∪
    {-((∑ x ∈ p.roots.toFinset, |x|) + 1), (∑ x ∈ p.roots.toFinset, |x|) + 1}

/-- Membership in the sample set, with the outer points stated explicitly. -/
@[simp]
theorem _root_.Polynomial.mem_signSamples (p : R[X]) (x : R) :
    x ∈ p.signSamples ↔ x ∈ p.roots.toFinset ∨ x ∈ p.derivative.roots.toFinset ∨
      x = -((∑ y ∈ p.roots.toFinset, |y|) + 1) ∨
      x = (∑ y ∈ p.roots.toFinset, |y|) + 1 := by
  classical
  simp only [Polynomial.signSamples, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, or_assoc]

/-- Constant polynomials have just the two outer samples. -/
@[simp]
theorem _root_.Polynomial.signSamples_of_natDegree_eq_zero (p : R[X])
    (hp : p.natDegree = 0) : p.signSamples = {-(1 : R), 1} := by
  rw [eq_C_of_natDegree_eq_zero hp]
  simp [Polynomial.signSamples]

/-- The zero polynomial has the two outer samples, rather than its entire zero set. -/
@[simp]
theorem _root_.Polynomial.signSamples_zero :
    (0 : R[X]).signSamples = {-(1 : R), 1} :=
  Polynomial.signSamples_of_natDegree_eq_zero 0 natDegree_zero

/-- There is always an outer sample, even when the polynomial has no roots. -/
theorem _root_.Polynomial.signSamples_nonempty (p : R[X]) : p.signSamples.Nonempty := by
  exact ⟨(∑ x ∈ p.roots.toFinset, |x|) + 1, (p.mem_signSamples _).mpr
    (Or.inr (Or.inr (Or.inr rfl)))⟩

end OrderedRing

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Every point is a root sample or shares a root-free closed interval with a sample.
Thus the samples meet all complementary intervals, without a completeness assumption. -/
theorem _root_.Polynomial.exists_mem_signSamples (p : R[X]) (hp : p ≠ 0) (x : R) :
    ∃ y ∈ p.signSamples, y = x ∨ ∀ z ∈ uIcc x y, p.eval z ≠ 0 := by
  classical
  let S := p.roots.toFinset
  let b : R := (∑ z ∈ S, |z|) + 1
  have hmem (z : R) : z ∈ S ↔ p.eval z = 0 := by simp [S, mem_roots hp]
  have hbound (z : R) (hz : z ∈ S) : -b < z ∧ z < b := by
    have hs : |z| ≤ ∑ w ∈ S, |w| := single_le_sum (fun w _ => abs_nonneg w) hz
    have h₁ := neg_abs_le z
    have h₂ := le_abs_self z
    dsimp [b]
    constructor <;> linarith
  by_cases hx : p.eval x = 0
  · exact ⟨x, (p.mem_signSamples x).mpr (Or.inl ((hmem x).mpr hx)), Or.inl rfl⟩
  -- Consecutive roots bound an interval sampled by Rolle; missing bounds give outer intervals.
  by_cases hleft : ∃ a ∈ S, a < x
  · by_cases hright : ∃ c ∈ S, x < c
    · obtain ⟨a, ha, hax, hprev⟩ := S.exists_next_left hleft
      obtain ⟨c, hc, hxc, hnext⟩ := S.exists_next_right hright
      obtain ⟨y, hy, hdy⟩ := p.exists_derivative_root_of_isRoot (hax.trans hxc)
        ((hmem a).mp ha) ((hmem c).mp hc)
      have hd : p.derivative ≠ 0 := derivative_ne_zero.mpr
        (p.natDegree_pos_of_eval₂_root hp (RingHom.id R) ((hmem a).mp ha)
          (fun _ h => h)).ne'
      refine ⟨y, (p.mem_signSamples y).mpr (Or.inr (Or.inl ?_)), Or.inr ?_⟩
      · simpa [mem_roots hd] using hdy
      · intro z hz hz0
        have hzS := (hmem z).mpr hz0
        have hzI : a < z ∧ z < c := by
          rcases mem_uIcc.mp hz with hz | hz <;> constructor <;> grind
        rcases lt_trichotomy z x with hzx | rfl | hxz
        · exact hzI.1.not_ge (hprev z hzS hzx)
        · exact hx hz0
        · exact hzI.2.not_ge (hnext z hzS hxz)
    · refine ⟨b, (p.mem_signSamples b).mpr (Or.inr (Or.inr (Or.inr rfl))), Or.inr ?_⟩
      intro z hz hz0
      have hzS := (hmem z).mpr hz0
      have hzb := (hbound z hzS).2
      have hzx : z ≤ x := le_of_not_gt (fun hxz => hright ⟨z, hzS, hxz⟩)
      rcases mem_uIcc.mp hz with hz | hz <;> grind
  · refine ⟨-b, (p.mem_signSamples (-b)).mpr (Or.inr (Or.inr (Or.inl rfl))), Or.inr ?_⟩
    intro z hz hz0
    have hzS := (hmem z).mpr hz0
    have hbz := (hbound z hzS).1
    have hxz : x ≤ z := le_of_not_gt (fun hzx => hleft ⟨z, hzS, hzx⟩)
    rcases mem_uIcc.mp hz with hz | hz <;> grind

end TauCeti
